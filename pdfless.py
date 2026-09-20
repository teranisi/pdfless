#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.9"
# dependencies = [
#     "pillow",
#     "pypdf",
#     "markdown",
#     "weasyprint",
# ]
# ///
"""pdfless - a less(1)-like full-screen PDF pager for terminals that
support iTerm2's inline image protocol (iTerm2 itself, WezTerm, ...).

Each page is rasterized once (via poppler's pdftoppm) at a resolution
matched to the terminal's actual pixel width, then scrolled by cropping
that raster in memory and redrawing the screen - the same "redraw on
each keypress" approach less(1) uses internally, since a terminal has
no way to scroll just part of an inline image.

Plain images and text files are supported directly, and (macOS only,
given a local Chrome/Chromium install) anything else this Mac's Quick
Look generators can preview - Word, Excel, PowerPoint, Keynote, Pages,
... - via qlmanage + a headless-Chrome screenshot of its HTML preview.
"""

import argparse
import base64
import concurrent.futures
import contextlib
import fcntl
import hashlib
import html
import io
import json
import os
import pathlib
import plistlib
import re
import select
import shutil
import signal
import struct
import subprocess
import sys
import tempfile
import termios
import threading
import time
import tty
import unicodedata
import webbrowser
from collections import OrderedDict

from PIL import Image, ImageChops, ImageOps

# A many-page/many-slide office document's full-height capture (see
# OfficeDocument._render_office_pages()) routinely exceeds Pillow's default "decompression
# bomb" pixel-count ceiling - that check exists for a program decoding
# untrusted images from elsewhere, which doesn't describe a CLI pager
# opening files the user themselves chose to view, so it's disabled here
# rather than raising some new, still-arbitrary limit.
Image.MAX_IMAGE_PIXELS = None

__version__ = "1.1.0"

STATUS_COLOR_ON = "\x1b[44;97m"  # white on blue - used for one-off messages
STATUS_COLOR_OFF = "\x1b[0m"

# The default status line is split into differently-colored fields so
# filename/page/loc%/zoom% each stand out, with the trailing key-hints
# text in a plainer, subdued color.
STATUS_COLOR_FILENAME = "\x1b[44;97m"  # white on blue
STATUS_COLOR_FILE_INDEX = "\x1b[46;97m"  # white on cyan
STATUS_COLOR_PAGE = "\x1b[42;97m"  # white on green
STATUS_COLOR_LOC = "\x1b[43;30m"  # black on yellow
STATUS_COLOR_ZOOM = "\x1b[45;97m"  # white on magenta
STATUS_COLOR_FOLLOW = "\x1b[41;97m"  # white on red - stands out, since it
# means pdfless is polling the disk behind your back (see -F/--follow)
STATUS_COLOR_HELP = "\x1b[100;37m"  # light grey on dark grey

# Text-mode search match: no image to draw a box marker over there, so
# the matched substring itself is highlighted with a background color.
TEXT_HIGHLIGHT_COLOR = "\x1b[43;30m"  # black on yellow
TEXT_HIGHLIGHT_RESET = "\x1b[0m"

# PDF (image) mode search match: same yellow, as a foreground color for
# the box-drawing border characters (there's no text to paint a
# background behind, just the underlying page image).
SEARCH_MARKER_COLOR = "\x1b[93m"  # bright yellow
SEARCH_MARKER_RESET = "\x1b[0m"

# Wrap mode (_draw_text_wrapped()): marks a real newline (the last
# display row of a raw line) with U+21B5 (↵), distinct from a row that's
# just a soft-wrap continuation of the same line.
NEWLINE_MARKER = "↵"
NEWLINE_MARKER_COLOR = "\x1b[34m"  # blue
NEWLINE_MARKER_RESET = "\x1b[0m"

# -N/--line-numbers: a right-aligned gutter at the start of each text-mode
# row (see Viewer._line_number_gutter_width()).
LINE_NUMBER_COLOR = "\x1b[90m"  # gray
LINE_NUMBER_RESET = "\x1b[0m"

# The scrollbar's two kinds of cell, ready to write (see
# Viewer._scrollbar_column()). The thumb is a reverse-video space
# rather than a block in some fixed color: reverse video swaps whatever
# foreground and background the terminal's theme is already using, so
# it stands out against any of them - a fixed color eventually lands on
# a theme that paints the background nearly the same shade.
SCROLLBAR_TRACK = "\x1b[90m│\x1b[0m"  # a thin gray line
SCROLLBAR_THUMB = "\x1b[7m \x1b[0m"  # a solid block
CACHE_SIZE = 6

# SGR mouse reporting (extended coordinates), only enabled while showing
# the page image - where a click can hit a PDF hyperlink or the
# scrollbar - never in text mode, where mouse tracking would swallow the
# terminal's own click-drag text selection. 1000 is buttons alone; 1002
# adds motion, but only while a button is held (unlike 1003, which
# reports every pointer move), which is all a scrollbar drag needs.
MOUSE_ON = "\x1b[?1000h\x1b[?1002h\x1b[?1006h"
MOUSE_OFF = "\x1b[?1000l\x1b[?1002l\x1b[?1006l"

# Alternate Scroll Mode: whenever the above button/motion reporting is
# NOT active (i.e. in text mode) - and only then, terminals ignore this
# while it's on - the terminal turns wheel scrolling into UP/DOWN key
# presses instead, which handle_key_text() already treats as one-line
# scrolling. Left on for the whole run: it's a no-op while MOUSE_ON is
# in effect, so it doesn't need to be toggled alongside it.
ALT_SCROLL_ON = "\x1b[?1007h"
ALT_SCROLL_OFF = "\x1b[?1007l"

# Focus reporting (xterm's FocusIn/FocusOut, CSI I / CSI O): lets a
# regained focus trigger a redraw (see FOCUS_IN handling in run_viewer()).
# This is what fixes a real bug, not just a nicety: under tmux, switching
# away from and back to the pane showing a PDF can leave it blank - its
# own screen model doesn't understand the passed-through inline image
# (see wrap_for_tmux()), so its internal redraw on a focus change repaints
# the pane from a model that never had the image in it.
#
# Only FOCUS_IN gets a redraw, not FOCUS_OUT, even though both panes
# involved in a focus change can go blank this way - confirmed by hand
# that redrawing on FOCUS_OUT actually makes things worse. OSC 1337 draws
# at "the current cursor position" with no coordinates of its own, and by
# the time a pane's process is told it just lost focus, tmux has already
# moved the terminal's one real cursor to the pane gaining focus - so
# that redraw's image lands in the *other* pane instead (as a stray,
# oddly-scaled fragment near its prompt). By the time a pane is told it
# gained focus, the cursor has already moved to it, which is why only
# that direction is safe to redraw on. A pane that just lost focus still
# goes blank in the meantime - nothing here can fix that under tmux -
# but switching back to it fixes it via its own FOCUS_IN.
#
# Left on for the whole run, on the same reasoning as ALT_SCROLL_ON
# above. Requires tmux's own "focus-events on" to reach an app running
# inside it at all - see the Caveats section in README.md.
FOCUS_ON = "\x1b[?1004h"
FOCUS_OFF = "\x1b[?1004l"


def char_width(ch):
    """Terminal column width of one character: 2 for wide/fullwidth East
    Asian characters (e.g. most Japanese/Chinese/Korean text), 1 otherwise.
    Needed because the status line is truncated/padded to fit exactly
    self.cols columns - doing that by Python string length (len()) rather
    than actual terminal column width overshoots whenever the text
    contains such characters, since each one is 1 Python character but 2
    terminal columns; that overshoot pushes the write past the last
    column of the last row, and autowrap then scrolls the whole screen up
    a line."""
    return 2 if unicodedata.east_asian_width(ch) in ("W", "F") else 1


# ECMA-48 control sequences git/man/etc. emit when pdfless is used as
# $PAGER with color enabled - must not count toward terminal width.
_ANSI_ESCAPE_RE = re.compile(
    r"\x1b\[[\?0-9;]*[ -/]*[@-~]"  # CSI (incl. SGR "...m")
    r"|\x1b\][^\x07\x1b]*(?:\x07|\x1b\\)"  # OSC
    r"|\x1b[P^_][^\x1b]*(?:\x07|\x1b\\)?"  # DCS / SOS / PM
    r"|\x1b[@-Z\\-_]"  # Fe Escape sequences
)


def _ansi_escape_at(s, i):
    if i >= len(s) or s[i] != "\x1b":
        return None
    return _ANSI_ESCAPE_RE.match(s, i)


def display_width(s):
    i = 0
    width = 0
    while i < len(s):
        m = _ansi_escape_at(s, i)
        if m:
            i = m.end()
            continue
        width += char_width(s[i])
        i += 1
    return width


def truncate_to_width(s, width):
    """Truncate `s` so its terminal column width doesn't exceed `width`."""
    out = []
    total = 0
    i = 0
    while i < len(s):
        m = _ansi_escape_at(s, i)
        if m:
            out.append(m.group(0))
            i = m.end()
            continue
        w = char_width(s[i])
        if total + w > width:
            break
        out.append(s[i])
        total += w
        i += 1
    return "".join(out)


def pad_to_width(s, width):
    return s + " " * max(0, width - display_width(s))


def slice_by_width(s, offset, width):
    """Extract the substring of `s` covering terminal columns
    [offset, offset+width) - the text-mode equivalent of cropping a
    pixel range out of the page image for horizontal pan. A wide
    character straddling either edge of that range can't be rendered
    half-visible, so it's dropped rather than included.

    Returns (substring, start_index): start_index is the character index
    into `s` the substring begins at, needed to re-base any offsets
    (e.g. a search highlight) that were computed against the original,
    unpanned line."""
    out = []
    col = 0
    taken = 0
    start_index = None
    i = 0
    while i < len(s):
        m = _ansi_escape_at(s, i)
        if m:
            if col >= offset and taken < width:
                if start_index is None:
                    start_index = i
                out.append(m.group(0))
            i = m.end()
            continue
        w = char_width(s[i])
        if col < offset:
            col += w
            i += 1
            continue
        if start_index is None:
            start_index = i
        if taken + w > width:
            break
        out.append(s[i])
        taken += w
        col += w
        i += 1
    if start_index is None:
        start_index = len(s)
    return "".join(out), start_index


MIN_ZOOM = 0.5
MAX_ZOOM = 4.0
ZOOM_STEP = 1.15
PAN_STEP_CELLS = 8
FOLLOW_INTERVAL = 3.0  # seconds between checks, under -F/--follow

KEY_TABLE = """\
Keys:
                                <MOVING>
  e ^E j ^N CR DOWN       forward  one line
  y ^Y k ^K ^P UP         backward one line
  f ^F ^V SPACE PAGEDOWN  forward  one window
  b ^B ESC-v PAGEUP       backward one window
  d ^D                    forward  half window
  u ^U                    backward half window
  h l LEFT RIGHT          pan left / right (when zoomed in)
  H L SHIFT-LEFT/RIGHT    jump to left / right edge (when zoomed in)
  K U SHIFT-UP            jump to top of the current page (same as g)
  J D SHIFT-DOWN          jump to bottom of the current page (same as G)
  g G                     jump to top / bottom of the current page
                          (text mode: type a number first to jump to
                          that line instead, e.g. 10g -> line 10)
  n p                     next / previous page (match while searching)
  < > HOME END            jump to the first / last page of the document
                          (type a number first to jump to that page
                          instead, e.g. 10< -> page 10)
                              <SEARCHING>
  /<regex> ENTER          search the whole document for <regex>,
                          landing on the first match from here on
                          (a Python regex; falls back to a literal
                          substring if it isn't valid regex syntax)
  ?<regex> ENTER          the same search, landing on the last match
                          before here instead
  / ENTER  ? ENTER        repeat the last search pattern, forward / back
  N P                     jump to next / previous search match
                            <CHANGING FILES>
  :n :p                   next / previous file, when more than one was
                          given on the command line
  x X                     jump to the first / last file in the list
  <N> x                   jump straight to file N
                               <ZOOMING>
  + -                     zoom in / out
  0                       reset zoom and pan
  m M                     fit page to terminal height / width
                           <MOUSE OPERATIONS>
  mouse click             (page image, not text mode) on the scrollbar,
                          jump to the position clicked; otherwise open
                          a PDF hyperlink under the pointer
  mouse wheel             scroll up / down
                                <LINKS>
  [ ]                     back / forward, through the positions internal
                          links have jumped from (PDF only)
                               <TOGGLES>
  t                       toggle plain-text view
  T                       toggle plain-text view already cleared for
                          copying, same as t and C together
  B                       (text mode) toggle a border around the page
  s -S                    (text mode) toggle wrapping long lines
  E                       (text mode) toggle marking an end-of-line (↵)
  # -N                    (text mode) toggle a line-number gutter
  C                       (text mode) clear the way for a select-and-
                          copy: turn off the EOL markers, the border,
                          the scrollbar and the line numbers at once,
                          and put back whatever was on before on a
                          second press
  r                       toggle the scrollbar
  F                       toggle follow mode (auto-reload on file change)
                        <MISCELLANEOUS COMMANDS>
  O v                     open the file in its own app (macOS only) and
                          switch follow mode on
  ^L                      redraw the screen
  F1 :h                   show this help (q to close it)
  q :q                    quit\
"""

FORWARD_LINE_KEYS = {"e", "\x05", "j", "\x0e", "\r", "DOWN"}
BACKWARD_LINE_KEYS = {"y", "\x19", "k", "\x0b", "\x10", "UP"}
FORWARD_WINDOW_KEYS = {"f", "\x06", "\x16", " ", "PAGEDOWN"}
BACKWARD_WINDOW_KEYS = {"b", "\x02", "ESC-v", "PAGEUP"}


def die(msg):
    print(f"pdfless: {msg}", file=sys.stderr)
    sys.exit(1)


def positive_int(s):
    n = int(s)
    if n < 1:
        raise argparse.ArgumentTypeError("must be at least 1")
    return n


def _open_in_default_app(path):
    """Hand `path` off to macOS's own default app for it, via `open` -
    the macOS-only half of "O"/"v" (see run_viewer()). Fire-and-forget:
    this only launches `open` itself and doesn't wait for or know
    anything about whatever app ends up handling the file. Returns
    True if that launch succeeded, False if this isn't macOS at all or
    `open` itself couldn't be started (there's no single equivalent
    command bundled with every Linux desktop the way `open` ships with
    every Mac, so this is deliberately macOS-only rather than guessing
    at xdg-open or similar)."""
    if sys.platform != "darwin":
        return False
    try:
        subprocess.Popen(
            ["open", path],
            stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL, start_new_session=True,
            # Detached from pdfless's own controlling terminal/session -
            # this is a real, independent program (the default app for
            # `path`), not a helper that should share pdfless's raw-
            # mode tty or die along with it.
        )
    except OSError:
        return False
    return True


POPPLER_INSTALL_HINT = (
    "install poppler (e.g. apt install poppler-utils, brew install poppler)"
)


def check_deps():
    for tool in ("pdftoppm", "pdfinfo"):
        if shutil.which(tool) is None:
            die(f"requires poppler's '{tool}' ({POPPLER_INSTALL_HINT})")

    r = subprocess.run(["pdftoppm", "-h"], capture_output=True, text=True)
    if "-png" not in r.stdout + r.stderr:
        die(f"pdftoppm is not poppler-compatible ({POPPLER_INSTALL_HINT})")


# Fallback path for anything that isn't a PDF, a plain image, or plain
# text (Word/Excel/PowerPoint/Keynote/Pages/... - whatever this Mac's
# installed Quick Look generators can handle): render it via
# `qlmanage -o DIR -p FILE`, which drops a DIR/FILE.qlpreview/ bundle
# containing Preview.html plus a PreviewProperties.plist ({Width,
# Height, ShouldNotScale, ...}), then rasterize that HTML with a local
# Chrome/Chromium (there's no Chrome-equivalent one-shot CLI screenshot
# for Safari, so this whole path is Chrome-only).
#
# Most documents (Word's CanHavePages, PowerPoint/Keynote's
# PageElementXPath - one flag per generator, and pptx sets neither)
# render as one continuously-flowing HTML block with no actual page
# breaks - "Height" from the plist is a single page/slide's height, and
# the tall render is sliced into that many page-sized PNGs, giving the
# same per-page n/p navigation as a real PDF. The one exception seen in
# practice is Excel, whose plist sets "ShouldNotScale": there "Height"
# is the exact total canvas size (just the active sheet - tab switching
# is JS-driven and invisible to a static screenshot), and it also pins
# its sheet-tab selector to the bottom of the viewport regardless of
# window height - which would defeat the "grow the capture until content
# stops reaching the bottom" trick used for the flowing case - so that
# case is instead captured at exactly the given size, no growing.
OFFICE_RENDER_SCALE = 1  # default device-pixel-ratio; --rendering-scale
# overrides this - higher gives more headroom to zoom in before it looks
# pixelated, at the cost of slower rendering (roughly linear in the
# resulting pixel count) for a large document

CHROME_CANDIDATES = (
    # (binary path, bundle id) - the bundle id lets find_chrome() move
    # whichever of these is the user's actual default browser to the
    # front, when it can tell.
    # Vivaldi is deliberately not included here: its headless mode
    # doesn't work (confirmed on 8.2.4133.52 - the UI process just
    # crashes with "--headless --screenshot", with or without
    # "--headless=old" too), so it would only make things worse for
    # anyone who has it set as their default browser.
    ("/Applications/Google Chrome.app/Contents/MacOS/Google Chrome", "com.google.chrome"),
    ("/Applications/Chromium.app/Contents/MacOS/Chromium", "org.chromium.chromium"),
    ("/Applications/Brave Browser.app/Contents/MacOS/Brave Browser", "com.brave.browser"),
)


def _default_browser_bundle_id():
    """The bundle identifier of the user's default web browser (e.g.
    "com.google.chrome"), read from Launch Services' own record of the
    "http" URL handler - or None if that can't be determined. Always
    lowercase (Launch Services itself is case-insensitive about these
    and stores them inconsistently - e.g. Chrome's own Info.plist says
    "com.google.Chrome" but the handler record says "com.google.chrome")."""
    plist_path = os.path.expanduser(
        "~/Library/Preferences/com.apple.LaunchServices/com.apple.launchservices.secure.plist"
    )
    try:
        r = subprocess.run(
            ["plutil", "-convert", "json", "-o", "-", plist_path],
            capture_output=True, text=True, timeout=5,
        )
        if r.returncode != 0:
            return None
        data = json.loads(r.stdout)
    except (OSError, subprocess.TimeoutExpired, ValueError):
        return None
    for handler in data.get("LSHandlers", []):
        if handler.get("LSHandlerURLScheme") == "http":
            role = handler.get("LSHandlerRoleAll")
            return role.lower() if role else None
    return None


class _DebugTimer:
    """Prints how long one stage of OfficeDocument._render_office_pages() took, when
    -d/--debug is on - e.g. "pdfless: [debug] slides.pptx: rendering:
    0.72s". A no-op (no timing overhead beyond one monotonic() call)
    when off."""

    def __init__(self, debug, label):
        self.debug = debug
        self.label = label

    def __enter__(self):
        if self.debug:
            self.t0 = time.monotonic()
        return self

    def __exit__(self, *exc):
        if self.debug:
            # end="\r\n", not the default "\n": this prints while the
            # terminal's in raw mode (OfficeDocument._render_office_pages() only ever
            # runs from inside the interactive viewer now - even a
            # first/only file is rendered lazily, from Viewer.__init__),
            # where a bare "\n" doesn't return the cursor to column 1
            # (that's OPOST's job, and raw mode turns it off) - every
            # line after the first would print staggered one column
            # further right than the last otherwise.
            print(
                f"pdfless: [debug] {self.label}: {time.monotonic() - self.t0:.2f}s",
                file=sys.stderr, end="\r\n",
            )


class _ProgressLine:
    """A single, self-overwriting status line on stderr - e.g.
    "pdfless: slides.pptx: rendering (1506x39796)..." - shown while
    OfficeDocument._render_office_pages() works through a Quick Look file, since that can
    take anywhere from under a second to tens of seconds and would
    otherwise look like pdfless had simply hung. Enabled only when
    stderr is a terminal (so a redirected/piped run doesn't get a stream
    of junk \\r-terminated lines) and -d/--debug isn't already printing
    its own, more detailed, per-stage timing lines."""

    def __init__(self, enabled):
        self.enabled = enabled and sys.stderr.isatty()
        self._last_len = 0
        self._lock = threading.Lock()

    def update(self, text):
        if not self.enabled:
            return
        with self._lock:
            text = f"pdfless: {text}"
            pad = max(0, self._last_len - len(text))
            sys.stderr.write("\r" + text + " " * pad)
            sys.stderr.flush()
            self._last_len = len(text)

    def clear(self):
        if not self.enabled:
            return
        with self._lock:
            if self._last_len:
                sys.stderr.write("\r" + " " * self._last_len + "\r")
                sys.stderr.flush()
            self._last_len = 0

    def spin(self, label):
        """Context manager: animates a spinner in front of `label` in a
        background thread for the duration of the `with` block - for a
        stage (e.g. the actual Chrome screenshot) that can take a while
        with no intermediate progress to report, so at least something
        visibly moves instead of the line just sitting there."""
        return _Spinner(self, label)


_SPINNER_FRAMES = "|/-\\"


class _Spinner:
    def __init__(self, progress, label):
        self.progress = progress
        self.label = label
        self._stop = threading.Event()
        self._thread = None

    def __enter__(self):
        if self.progress.enabled:
            self._thread = threading.Thread(target=self._run, daemon=True)
            self._thread.start()
        return self

    def _run(self):
        i = 0
        while not self._stop.wait(0.15 if i else 0):
            self.progress.update(f"{_SPINNER_FRAMES[i % len(_SPINNER_FRAMES)]} {self.label}")
            i += 1

    def __exit__(self, *exc):
        if self._thread:
            self._stop.set()
            self._thread.join()


class _ViewerProgress:
    """Adapts OfficeDocument._render_office_pages()'s progress reporting to the Viewer's
    own status line, for a file rendered lazily while the interactive
    session is already running (opening a file for the first time, or
    switching to one with :n/:p, now that each office-kind file is only
    ever rendered once it's actually displayed - see
    Viewer._ensure_office_pages()) - a stderr line (what _ProgressLine
    uses for the equivalent one-off startup validation in main()) would
    either corrupt or hide behind the alternate screen buffer at that
    point, so this posts into the status line instead, the same as any
    other one-off status message. Off under -d/--debug, which already
    prints its own, more detailed, per-stage timing lines to stderr."""

    def __init__(self, viewer):
        self.viewer = viewer
        self.enabled = not viewer.debug

    def update(self, text):
        if self.enabled:
            self.viewer.draw_status(text)

    def clear(self):
        # Blank the line rather than restoring the viewer's normal status
        # text (draw_status() with no argument) - that needs geometry
        # (self.scroll_max, etc.) this may run before the current file's
        # own first _load_page() has ever computed, if it's the very
        # first file opened. A real refresh() always follows moments
        # after this (from run_viewer() for the first file, or from the
        # end of go_to_file()/reload() otherwise), painting the correct
        # status right over this blank - so nothing is ever left stuck
        # looking wrong.
        if self.enabled:
            self.viewer.draw_status(" ")

    def spin(self, label):
        return _Spinner(self, label)


def find_chrome():
    """A local Chrome/Chromium-family browser binary, for headless
    screenshotting - or None if none is installed. Prefers the user's
    default browser, when it's one of these and can be determined;
    otherwise falls back to CHROME_CANDIDATES' fixed order."""
    default_id = _default_browser_bundle_id()
    candidates = CHROME_CANDIDATES
    if default_id is not None:
        candidates = sorted(candidates, key=lambda c: c[1] != default_id)
    for path, _bundle_id in candidates:
        if os.path.isfile(path) and os.access(path, os.X_OK):
            return path
    for name in (
        "google-chrome", "google-chrome-stable", "chromium", "chromium-browser",
        "vivaldi", "vivaldi-stable",
    ):
        found = shutil.which(name)
        if found:
            return found
    return None


SOFFICE_CANDIDATES = (
    "/opt/homebrew/bin/soffice",
    "/Applications/LibreOffice.app/Contents/MacOS/soffice",
    "/usr/bin/soffice",
)


def find_soffice():
    """A local LibreOffice `soffice` binary, for converting Word/RTF
    documents to a real PDF with higher fidelity than the qlmanage +
    Chrome --print-to-pdf pipeline (real page breaks, correctly
    rendered embedded pictures of any format, no reliance on Quick
    Look at all) - or None if it isn't installed. Optional: callers
    (see OfficeDocument._try_soffice_pages()) always fall back to the
    qlmanage/Chrome pipeline when this returns None."""
    for path in SOFFICE_CANDIDATES:
        if os.path.isfile(path) and os.access(path, os.X_OK):
            return path
    return shutil.which("soffice")




_IMG_SRC_RE = re.compile(r'(<img\b[^>]*\bsrc=")([^"]+)(")', re.IGNORECASE)
_IMG_TAG_RE = re.compile(r'<img\b[^>]*>', re.IGNORECASE)
_IFRAME_SRC_RE = re.compile(r'(<iframe\b[^>]*\bsrc=")([^"]+)(")', re.IGNORECASE)
_ABSOLUTE_SRC_RE = re.compile(r'^(?:[a-zA-Z][a-zA-Z0-9+.-]*:|/)')  # a URL scheme, or an absolute path
_SRC_ATTR_RE = re.compile(r'\bsrc="([^"]+)"', re.IGNORECASE)
_WIDTH_ATTR_RE = re.compile(r'\bwidth="([\d.]+)"', re.IGNORECASE)
_HEIGHT_ATTR_RE = re.compile(r'\bheight="([\d.]+)"', re.IGNORECASE)


# A hard ceiling on either dimension of a broken embedded picture
# (PDF or TIFF), once rasterized/re-encoded - regardless of what DPI
# the math below otherwise settles on for a PDF one. A Numbers/Pages/
# Keynote sheet can embed its *entire* content (a whole spreadsheet,
# potentially thousands of points on a side) as one such "picture"
# (see _rasterize_broken_img_sources()), and poppler's pdftocairo (see
# there for why it's used instead of pdftoppm) has its own ceiling on
# the cairo surface size it'll produce - past that, it fails loudly (a
# non-zero exit, caught below) rather than silently writing something
# degenerate. This cap keeps the request comfortably clear of that
# ceiling either way.
OFFICE_EMBEDDED_IMG_MAX_PX = 6000


def _pdf_page_size_pt_safe(pdf_path):
    """Like PdfDocument.page_size_pt(), but tolerant of failure (returns None
    rather than die()ing the whole program) - for sizing a picture
    embedded in a Quick Look preview, where a bad reading just means
    falling back to a default DPI rather than aborting entirely."""
    try:
        out = subprocess.run(
            ["pdfinfo", pdf_path], capture_output=True, text=True, timeout=10,
        ).stdout
    except (subprocess.TimeoutExpired, OSError):
        return None
    m = re.search(r"^Page\s*(?:\d+\s+)?size:\s+([\d.]+) x ([\d.]+)", out, re.MULTILINE)
    return (float(m.group(1)), float(m.group(2))) if m else None


def _pdf_page_count_safe(pdf_path):
    """Like PdfDocument._pdf_page_count(), but tolerant of failure
    (returns None rather than die()ing the whole program) - for reading
    back how many pages Chrome's --print-to-pdf produced (see
    FlowingText.build_pages()), where a bad reading just means falling
    back to the screenshot-based path rather than aborting entirely."""
    try:
        out = subprocess.run(
            ["pdfinfo", pdf_path], capture_output=True, text=True, timeout=10,
        ).stdout
    except (subprocess.TimeoutExpired, OSError):
        return None
    m = re.search(r"^Pages:\s+(\d+)", out, re.MULTILINE)
    return int(m.group(1)) if m else None


def _convert_via_soffice(soffice, path, tmpdir, timeout=60):
    """Convert `path` (a Word/RTF/PowerPoint document - see
    OfficeDocument._SOFFICE_EXTENSIONS) to a real PDF via LibreOffice's
    `soffice --convert-to pdf`, natively - no Quick Look/Chrome
    involved at all - returning the output PDF's path, or None on any
    failure (timeout, non-zero exit, or no output file), so callers
    (see OfficeDocument._try_soffice_pages()) can always fall back to
    the qlmanage/Chrome pipeline.

    Deliberately does NOT pass --headless: confirmed by hand that
    --headless breaks CJK (Japanese) font rendering entirely (text
    comes out blank, though the PDF's own text layer is fine - a pure
    glyph-resolution bug), while running without it renders correctly,
    including over SSH.

    -env:UserInstallation points at a profile directory scoped to this
    `tmpdir` (unique per render), so concurrent soffice invocations
    (e.g. two files opened around the same time) don't collide over a
    shared user profile lock."""
    profile_dir = os.path.join(tmpdir, "soffice-profile")
    try:
        subprocess.run(
            [
                soffice,
                f"-env:UserInstallation=file://{profile_dir}",
                "--convert-to", "pdf",
                "--outdir", tmpdir,
                path,
            ],
            capture_output=True, timeout=timeout,
        )
    except (subprocess.TimeoutExpired, OSError):
        return None
    base = os.path.splitext(os.path.basename(path))[0]
    out_pdf = os.path.join(tmpdir, f"{base}.pdf")
    return out_pdf if os.path.isfile(out_pdf) else None



def _rasterize_broken_img_sources(html_path, tmpdir, on_progress=None):
    """A Quick Look Office/iWork preview can embed a picture as
    `<img src="AttachmentN.pdf">` or `<img src="AttachmentN.tiff">` -
    formats the relevant generator apparently assumes a renderer that
    can show inline as an image, the way Safari/WebKit (Quick Look's
    own host) does; plain Chrome can't decode either one, and just
    shows a broken-image icon at whatever size the <img> tag's style
    gives it (confirmed by hand: a real Word document with a mix of
    PNG and TIFF pictures showed the PNGs fine and the TIFFs broken,
    scattered throughout - TIFF has no web-standard decode support at
    all, unlike PDF, which at least fails the same way in every
    browser other than Safari/WebKit). Across every picture in a slide
    deck, that's often enough bogus extra height to throw off later
    slides' measured positions entirely (see OfficeDocument._measure_slide_offsets()).

    iWork.qlgenerator (Numbers/Pages/Keynote) additionally splits a
    multi-sheet/page document into one `<iframe src="AttachmentN.html">`
    per sheet rather than embedding everything directly in Preview.html
    the way Office.qlgenerator does - and it's each of *those* files
    that actually embeds the broken `<img>`, not Preview.html itself.
    So this looks for that pattern recursively, through every local
    (not http/data/...) iframe target, not just in `html_path` itself.

    Rewrites each such reference found anywhere in that tree to a PNG -
    rasterized from a PDF via poppler's pdftocairo (not pdftoppm - see
    _convert() below for why), or straightforwardly re-encoded via
    Pillow for a TIFF (already a raster image; no DPI to choose, unlike
    a PDF) - and rewrites each iframe reference to point at its
    (recursively) patched target. Every patched file is written
    alongside the original it came from (same directory, different
    name) rather than elsewhere, so any *other* (unrelated) relative
    reference in it keeps resolving exactly as before, untouched.

    Returns the path to `html_path`'s own patched copy - or `html_path`
    unchanged if nothing anywhere in the tree needed patching.
    `on_progress`, if given, is called as `on_progress(done, total)`
    after each conversion finishes, `total` counting every one found
    across the whole tree."""
    # Phase 1: walk html_path plus every local HTML file it (recursively)
    # embeds via <iframe src>, collecting each file's own content and
    # its own <img src="*.pdf"/"*.tiff"/"*.tif"> references.
    file_contents = {}  # path -> content
    broken_refs_by_file = {}  # path -> [ref, ...]
    to_visit = [html_path]
    seen = set()
    while to_visit:
        path = to_visit.pop()
        real = os.path.realpath(path)
        if real in seen:
            continue
        seen.add(real)
        try:
            with open(path, "r", encoding="utf-8", errors="replace") as f:
                content = f.read()
        except OSError:
            continue
        file_contents[path] = content
        base_dir = os.path.dirname(path)
        # (ref, declared width, declared height) for every broken <img
        # src=...> - the declared size (in CSS px, i.e. ~1:1 with
        # points) is what lets _convert() below pick a sane DPI for a
        # PDF ref instead of a fixed one that can be wildly wrong for a
        # huge embedded page (moot for a TIFF ref, already a fixed-size
        # raster). Deduplicated by ref, first occurrence winning, same
        # as a plain set() would for the src-only info this replaced.
        broken_refs = {}
        for tag_m in _IMG_TAG_RE.finditer(content):
            tag = tag_m.group(0)
            src_m = _SRC_ATTR_RE.search(tag)
            if not src_m or not src_m.group(1).lower().endswith((".pdf", ".tiff", ".tif")):
                continue
            ref = src_m.group(1)
            if ref in broken_refs:
                continue
            w_m, h_m = _WIDTH_ATTR_RE.search(tag), _HEIGHT_ATTR_RE.search(tag)
            broken_refs[ref] = (
                float(w_m.group(1)) if w_m else None,
                float(h_m.group(1)) if h_m else None,
            )
        broken_refs_by_file[path] = sorted(
            (ref, w, h) for ref, (w, h) in broken_refs.items()
        )
        for m in _IFRAME_SRC_RE.finditer(content):
            src = m.group(2)
            if _ABSOLUTE_SRC_RE.match(src):
                continue  # http(s)/data/... - not a local sibling file
            candidate = os.path.join(base_dir, src)
            if src.lower().endswith((".html", ".htm")) and os.path.isfile(candidate):
                to_visit.append(candidate)

    all_refs = [
        (path, ref, w, h)
        for path, refs in broken_refs_by_file.items()
        for ref, w, h in refs
    ]
    if not all_refs:
        return html_path
    have_pdftocairo = shutil.which("pdftocairo") is not None

    def _convert(item):
        path, ref, decl_w, decl_h = item
        src_path = os.path.join(os.path.dirname(path), ref)
        if not os.path.isfile(src_path):
            return path, ref, None
        prefix = os.path.join(tmpdir, f"qlimg-{hashlib.md5(src_path.encode()).hexdigest()[:12]}")
        png_path = prefix + ".png"

        if ref.lower().endswith(".pdf"):
            if not have_pdftocairo:
                return path, ref, None
            # A fixed DPI (this used to always be 300) is wildly wrong for
            # a picture that's actually an entire spreadsheet/page flattened
            # into one PDF, sized in the thousands of points on a side - Numbers
            # in particular does this for a sheet too big to fit its normal
            # preview. Aim instead for roughly the size the <img> tag is
            # actually going to display it at (that's in CSS px, and a PDF
            # point is already ~1 CSS px at 96dpi, so this is close to
            # 1:1 - not literally 1:1 only because a page's declared point
            # size can differ slightly from its <img> tag's declared pixel
            # size), falling back to the old 300 if either the page size or
            # the declared display size isn't available - then hard-capped
            # regardless (see OFFICE_EMBEDDED_IMG_MAX_PX).
            dpi = 300.0
            page_size = _pdf_page_size_pt_safe(src_path)
            if page_size:
                page_w_pt, page_h_pt = page_size
                if decl_w and page_w_pt:
                    dpi = 72.0 * decl_w / page_w_pt
                elif decl_h and page_h_pt:
                    dpi = 72.0 * decl_h / page_h_pt
                if page_w_pt:
                    dpi = min(dpi, 72.0 * OFFICE_EMBEDDED_IMG_MAX_PX / page_w_pt)
                if page_h_pt:
                    dpi = min(dpi, 72.0 * OFFICE_EMBEDDED_IMG_MAX_PX / page_h_pt)
            dpi = max(36.0, min(300.0, dpi))

            try:
                subprocess.run(
                    # pdftocairo (not pdftoppm - it has no -transp option) so a
                    # picture with a transparent background (e.g. a PNG/GIF with
                    # alpha, flattened into this PDF by the Quick Look
                    # generator) keeps its transparency instead of getting
                    # composited onto an opaque white background here, before
                    # Chrome ever gets to draw it over the slide's real
                    # background.
                    ["pdftocairo", "-png", "-transp", "-r", str(round(dpi)), "-singlefile", src_path, prefix],
                    capture_output=True, check=True, timeout=20,
                )
            except (subprocess.CalledProcessError, subprocess.TimeoutExpired, OSError):
                return path, ref, None
        else:  # .tiff / .tif - already a raster image, just re-encoded
            # to a format Chrome can actually decode inline, downscaled
            # if it's absurdly large (see OFFICE_EMBEDDED_IMG_MAX_PX) -
            # there's no DPI to choose the way a PDF page needs.
            try:
                with Image.open(src_path) as img:
                    img.load()
                    if img.width > OFFICE_EMBEDDED_IMG_MAX_PX or img.height > OFFICE_EMBEDDED_IMG_MAX_PX:
                        img.thumbnail((OFFICE_EMBEDDED_IMG_MAX_PX, OFFICE_EMBEDDED_IMG_MAX_PX), Image.LANCZOS)
                    img.convert("RGBA" if "A" in img.getbands() else "RGB").save(png_path, "PNG")
            except Exception:
                return path, ref, None

        if not os.path.isfile(png_path):
            return path, ref, None
        # Defensive: pdftocairo failing outright over OFFICE_EMBEDDED_IMG_MAX_PX
        # is already caught above (a non-zero exit raises
        # CalledProcessError) - this instead guards a degenerate ~1px
        # output from some other cause (e.g. a wildly wrong declared
        # width/height), treating it as a failure too (leaving the
        # original broken <img src=...> in place rather than silently
        # serving a blank picture).
        try:
            with Image.open(png_path) as probe:
                if probe.width <= 2 or probe.height <= 2:
                    return path, ref, None
        except Exception:
            return path, ref, None
        return path, ref, pathlib.Path(png_path).as_uri()

    # A slide deck can embed dozens to a couple hundred of these (one
    # pdftocairo/Pillow conversion each) - running them one at a time was
    # most of this whole function's cost, and each is independent, so a
    # thread pool (subprocess.run releases the GIL while the child runs,
    # and Pillow's C decoders release it too) cuts that down by roughly
    # the number of workers.
    png_by_file_ref = {}  # (path, ref) -> uri
    done = 0
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        futures = [pool.submit(_convert, item) for item in all_refs]
        for future in concurrent.futures.as_completed(futures):
            path, ref, uri = future.result()
            if uri:
                png_by_file_ref[(path, ref)] = uri
            done += 1
            if on_progress:
                on_progress(done, len(all_refs))

    # Phase 2: write a patched copy of every file that needs one - its
    # own img srcs rasterized, and/or an iframe src repointed at its
    # child's patched copy. _patch() recurses into iframe targets first,
    # so by the time a parent rewrites its own iframe src, it already
    # knows whether (and where) that child got patched.
    patched_by_original = {}

    def _patch(path):
        if path in patched_by_original:
            return patched_by_original[path]
        content = file_contents.get(path)
        if content is None:
            return path
        base_dir = os.path.dirname(path)
        changed = False

        def _replace_img(m):
            nonlocal changed
            uri = png_by_file_ref.get((path, m.group(2)))
            if not uri:
                return m.group(0)
            changed = True
            return f"{m.group(1)}{uri}{m.group(3)}"

        def _replace_iframe(m):
            nonlocal changed
            src = m.group(2)
            candidate = os.path.join(base_dir, src)
            if candidate not in file_contents:
                return m.group(0)
            patched_child = _patch(candidate)
            if patched_child == candidate:
                return m.group(0)
            changed = True
            return f"{m.group(1)}{os.path.basename(patched_child)}{m.group(3)}"

        content = _IMG_SRC_RE.sub(_replace_img, content)
        content = _IFRAME_SRC_RE.sub(_replace_iframe, content)

        if not changed:
            patched_by_original[path] = path
            return path
        tag = hashlib.md5(path.encode("utf-8", "surrogateescape")).hexdigest()[:12]
        patched_path = os.path.join(base_dir, f"pdfless-patched-{tag}.html")
        with open(patched_path, "w", encoding="utf-8") as f:
            f.write(content)
        patched_by_original[path] = patched_path
        return patched_path

    return _patch(html_path)


def _capture_html_screenshot(chrome, html_path, width, height, out_png, render_scale):
    physical_w = width * render_scale
    physical_h = height * render_scale
    base_args = [
        chrome, "--headless", "--hide-scrollbars", "--no-sandbox",
        f"--window-size={width},{height}",
        f"--force-device-scale-factor={render_scale}",
        f"--screenshot={out_png}",
        f"file://{os.path.abspath(html_path)}",
    ]
    if max(physical_w, physical_h) < OfficeVariant.OFFICE_GPU_SAFE_PHYSICAL_PX:
        try:
            subprocess.run(base_args, capture_output=True, check=True, timeout=8)
            return
        except subprocess.TimeoutExpired:
            pass  # bigger than expected for this content; fall through
    subprocess.run(
        [base_args[0], "--disable-gpu", *base_args[1:]],
        capture_output=True, check=True, timeout=30,
    )


def _capture_html_pdf(chrome, html_path, width, height, out_pdf, timeout=20):
    """Print `html_path` to a real (vector) PDF at an exact `width` x
    `height` CSS-pixel page size, via Chrome's headless --print-to-pdf -
    unlike _capture_html_screenshot()'s fixed-resolution PNG, this keeps
    text as real PDF text (not a bitmap of it), so pdfless can
    re-rasterize it at whatever DPI the current zoom needs (see
    PdfDocument.get_page_image()) instead of upscaling one fixed
    screenshot. Confirmed by hand that Chrome's print engine happily
    paginates content taller than one `height`-tall page into further
    real PDF pages, and that a plain `<a href>` survives as a real PDF
    link annotation (see Viewer._ensure_link_index()).

    The page size is set via an injected `@page` CSS rule, in a scratch
    copy of html_path that's never written back (same idea as
    OfficeDocument._measure_slide_offsets()'s instrumented copy) - headless Chrome's
    CLI has no --paper-width/--paper-height flag of its own; this is
    the only way to reach a custom page size without going through the
    DevTools protocol (which is what a browser-automation library like
    Playwright would use instead - not worth the extra dependency just
    for this one knob).

    Returns True on success, False for anything that went wrong
    (a too-old Chrome without --print-to-pdf, a bad html_path, ...) -
    the caller falls back to the screenshot-based path either way, so
    this never raises."""
    try:
        with open(html_path, "r", encoding="utf-8", errors="replace") as f:
            content = f.read()
    except OSError:
        return False

    style = f"<style>@page {{ size: {width}px {height}px; margin: 0; }}</style>"
    idx = content.lower().find("</head>")
    injected = content[:idx] + style + content[idx:] if idx != -1 else style + content
    print_path = os.path.join(os.path.dirname(html_path), "pdfless-print.html")
    try:
        with open(print_path, "w", encoding="utf-8") as f:
            f.write(injected)
    except OSError:
        return False

    try:
        subprocess.run(
            [
                chrome, "--headless", "--disable-gpu", "--no-sandbox",
                f"--print-to-pdf={out_pdf}", "--print-to-pdf-no-header",
                f"file://{os.path.abspath(print_path)}",
            ],
            capture_output=True, check=True, timeout=timeout,
        )
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired, OSError):
        return False
    finally:
        if os.path.exists(print_path):
            os.unlink(print_path)
    return os.path.exists(out_pdf)


def _sample_background_color(img):
    """A representative "blank" background color for `img`, sampled from
    its very top-left corner - outside the actual document content for
    every Quick Look generator seen so far (page margin; or, for a slide
    deck, the grey area around the first slide). Some generators' body
    background isn't plain white (e.g. PowerPoint's is a mid-grey) and
    stretches to fill the whole browser viewport regardless of window
    height, so _trim_trailing_blank_rows() needs the actual color to
    compare against rather than assuming white."""
    return img.convert("RGB").getpixel((0, 0))


def _trim_trailing_blank_rows(img, bg_color):
    """Crop `img` to drop blank (uniformly `bg_color`) rows at the
    bottom - left over from over-provisioning the capture height in
    OfficeDocument._render_office_pages(), since the real content height isn't known
    ahead of a render. Returns (trimmed_img, might_be_cut_off) - the
    second value is True when content reaches all the way to the bottom
    of `img`, meaning the capture may have been too short to fit
    everything."""
    rgb = img.convert("RGB")
    bg = Image.new("RGB", rgb.size, bg_color)
    bbox = ImageChops.difference(rgb, bg).getbbox()
    if bbox is None:
        return img, False  # a blank page
    bottom = min(img.height, bbox[3] + 4)
    return img.crop((0, 0, img.width, bottom)), bottom >= img.height - 2


def _build_slide_measure_script(page_element_xpath):
    """The plist's own "PageElementXPath" (see OfficeDocument._generate_ql_preview()) is
    exactly what selects each page/slide's top-level element for this
    particular generator - Office.qlgenerator (Word/PowerPoint) says
    "/html/body/div", iWork.qlgenerator (Keynote) says
    "/html/body/div[starts-with(@class, 'slideStyle')]" - so use it via
    document.evaluate() rather than guessing a CSS selector (a single
    class name that happens to work for one generator, e.g. Office's
    "div.slide", silently selects nothing at all for another - which is
    indistinguishable from "no pages to measure" and falls back to
    slicing by the plist's Height instead, drifting out of alignment
    with the actual page/slide boundaries after enough of them - this
    was previously confirmed with PowerPoint, and resurfaces the same
    way with Keynote using a hardcoded selector that's specific to
    Office's own output).

    Waits for every <img> to finish loading before measuring, not just
    the page's own load event: one iWork.qlgenerator variant gives each
    page div no explicit size at all, relying entirely on its one
    full-bleed <img>'s natural (post-decode) height, so measuring before
    every image is actually decoded reads every offsetTop as 0 (each
    div still being height-0 at that point, none of them having pushed
    the next one down yet) - confirmed on a 36-slide deck where that's
    exactly what happened."""
    measure_fn = (
        "function(){"
        "document.title = JSON.stringify({"
        "total: document.body.scrollHeight,"
        "tops: (function(){"
        f"var r = document.evaluate({json.dumps(page_element_xpath)}, document, null, "
        "XPathResult.ORDERED_NODE_SNAPSHOT_TYPE, null);"
        "var out = [];"
        "for (var i = 0; i < r.snapshotLength; i++) { out.push(r.snapshotItem(i).offsetTop); }"
        "return out;"
        "})()"
        "});"
        "}"
    )
    return (
        "<script>"
        f"var _pdflessMeasure = {measure_fn};"
        "var _pdflessImgs = Array.from(document.images);"
        "var _pdflessPending = _pdflessImgs.filter(function(i){return !i.complete;}).length;"
        "if (_pdflessPending === 0) {"
        "_pdflessMeasure();"
        "} else {"
        "_pdflessImgs.forEach(function(img){"
        "if (img.complete) return;"
        "var done = function(){ _pdflessPending--; if (_pdflessPending <= 0) _pdflessMeasure(); };"
        "img.addEventListener('load', done);"
        "img.addEventListener('error', done);"
        "});"
        "}"
        "</script>"
    )


_TOP_DIV_RE = re.compile(r'<div\b.*?</div>', re.IGNORECASE | re.DOTALL)
_TOP_DIV_IMG_ONLY_RE = re.compile(r'<div\b[^>]*>\s*<img\b[^>]*>\s*</div>', re.IGNORECASE)


def _detect_fallback_page_xpath(content):
    """Some Quick Look generator output (seen from an older Keynote/
    iWork.qlgenerator variant) has no "PageElementXPath" in its plist at
    all - unlike every other case seen so far - despite still having
    one clearly-delimited element per slide: each is simply a `<div>`
    directly under `<body>` wrapping one full-bleed
    `<img src="*.pdf">`, with no distinguishing class to select by.

    Detect that specific shape - rather than assuming any document
    missing "PageElementXPath" has it, which a continuously-flowing
    Word document very much doesn't - and if (almost) every direct
    `<div>` child of `<body>` matches it, return the same
    "/html/body/div" xpath a generator that DID report one would have
    (e.g. PowerPoint's). Returns None if this doesn't look like that
    shape."""
    body_idx = content.find("<body")
    if body_idx == -1:
        return None
    top_divs = _TOP_DIV_RE.findall(content[body_idx:])
    if len(top_divs) < 2:
        return None
    matching = sum(1 for d in top_divs if _TOP_DIV_IMG_ONLY_RE.fullmatch(d.strip()))
    return "/html/body/div" if matching >= len(top_divs) * 0.9 else None


def _measure_content_height(chrome, html_path, width, timeout=30):
    """document.body.scrollHeight for `html_path` at `width` (logical
    CSS px) - the same script-injected-title / --dump-dom technique as
    OfficeDocument._measure_slide_offsets() (see there for why dump-dom rather than a
    screenshot), but for a document's total flowing height rather than
    per-slide boundaries.

    Used to size FlowingText's single continuous @page height to the
    document's real content instead of one size-fits-all oversized
    page regardless of how short the document actually is - CSS's
    `size: <width> auto` looks like the obvious way to ask a browser's
    print engine to size a page's height to its content, but confirmed
    by hand that Chromium doesn't support "auto" here at all (silently
    falls back to a default Letter page instead), so measuring first
    and passing an explicit height is the only way. Returns None on
    any failure - the caller falls back to a fixed cap
    (OfficeVariant.OFFICE_MAX_CAPTURE_HEIGHT) instead."""
    try:
        with open(html_path, "r", encoding="utf-8", errors="replace") as f:
            content = f.read()
    except OSError:
        return None
    script = "<script>document.title = String(Math.ceil(document.body.scrollHeight));</script>"
    idx = content.rfind("</body>")
    instrumented = content[:idx] + script + content[idx:] if idx != -1 else content + script
    measure_path = os.path.join(os.path.dirname(html_path), "pdfless-height-measure.html")
    try:
        with open(measure_path, "w", encoding="utf-8") as f:
            f.write(instrumented)
    except OSError:
        return None
    try:
        r = subprocess.run(
            [
                chrome, "--headless", "--no-sandbox",
                f"--window-size={width},1080",
                "--dump-dom", "--virtual-time-budget=8000",
                f"file://{os.path.abspath(measure_path)}",
            ],
            capture_output=True, text=True, timeout=timeout, check=True,
        )
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired, OSError):
        return None
    finally:
        if os.path.exists(measure_path):
            os.unlink(measure_path)
    m = re.search(r"<title>(\d+)</title>", r.stdout)
    return int(m.group(1)) if m else None


def _measure_svg_natural_size(chrome, wrapper_path, timeout=20):
    """(width, height) in CSS px that `wrapper_path`'s <img id="svg">
    (see SvgDocument._write_svg_wrapper()) naturally renders at - the
    same script-injected-title / --dump-dom technique
    _measure_content_height() uses, but reading the image's own
    naturalWidth/naturalHeight once it finishes loading (via onload,
    since decoding a local file happens asynchronously) rather than
    the document's scroll height.

    Needed because an SVG's intrinsic size varies in both dimensions
    at once - unlike FlowingText/SlideDeck's HTML, where a fixed
    Quick-Look-reported width is already known up front and only the
    height needs measuring, an SVG has no such external plist to read
    a width from; Chrome's print engine still can't size a page to its
    content on its own either way (see _measure_content_height()).

    Returns None on any failure, including an SVG Chrome couldn't
    determine a natural size for at all - the caller falls back to a
    fixed default size."""
    try:
        with open(wrapper_path, "r", encoding="utf-8", errors="replace") as f:
            content = f.read()
    except OSError:
        return None
    script = (
        '<script>document.getElementById("svg").onload = function() {'
        'document.title = this.naturalWidth + "x" + this.naturalHeight;'
        "};</script>"
    )
    idx = content.rfind("</body>")
    instrumented = content[:idx] + script + content[idx:] if idx != -1 else content + script
    measure_path = os.path.join(os.path.dirname(wrapper_path), "pdfless-svg-measure.html")
    try:
        with open(measure_path, "w", encoding="utf-8") as f:
            f.write(instrumented)
    except OSError:
        return None
    try:
        r = subprocess.run(
            [
                chrome, "--headless", "--no-sandbox",
                "--dump-dom", "--virtual-time-budget=8000",
                f"file://{os.path.abspath(measure_path)}",
            ],
            capture_output=True, text=True, timeout=timeout, check=True,
        )
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired, OSError):
        return None
    finally:
        if os.path.exists(measure_path):
            os.unlink(measure_path)
    m = re.search(r"<title>(\d+)x(\d+)</title>", r.stdout)
    if not m:
        return None
    width, height = int(m.group(1)), int(m.group(2))
    return (width, height) if width > 0 and height > 0 else None


def _slice_and_save_pages(trimmed, bounds, tmpdir, tag):
    """Crop `trimmed` at each consecutive pair in `bounds` (a list of Y
    pixel offsets, first always 0, last always trimmed.height) and save
    each slice as its own page PNG - shared by every OfficeVariant that
    captures one big image and then splits it, as opposed to
    ExcelWorkbook's multi-sheet case, which renders each page directly
    and never needs slicing at all."""
    page_paths = []
    for i in range(len(bounds) - 1):
        top, bottom = bounds[i], bounds[i + 1]
        page_path = os.path.join(tmpdir, f"office-page-{tag}-{i + 1}.png")
        trimmed.crop((0, top, trimmed.width, bottom)).save(page_path)
        page_paths.append(page_path)
    return page_paths


class OfficeVariant:
    """Base class for the different "how to turn this Quick Look
    preview into page images" strategies OfficeDocument._render_office_pages() can use -
    one of these is chosen once qlmanage's plist/HTML are known (see
    OfficeDocument._render_office_pages()), and it owns the capture strategy and the
    bounds/pagination decision for its own case. The shared preamble
    (finding Chrome, running qlmanage, deciding which variant to use)
    lives in OfficeDocument._render_office_pages() itself, since it has to run before
    any variant can even be chosen."""

    # GPU compositing has a texture-size ceiling that a multi-page/multi-
    # slide document's full-height capture (thousands of px, sometimes tens
    # of thousands) routinely exceeds, and Chrome then just hangs rather
    # than erroring out - confirmed hanging indefinitely with a physical
    # (post device-scale-factor) height anywhere from 24000px up on this
    # machine, well under Chrome's largest documented max-texture-size
    # (16384px on some GPUs) that a naive "keep the safety margin below
    # that" guess would have assumed safe. Software rasterization
    # (--disable-gpu) has no such limit but is noticeably slower, so a
    # capture kept safely under any plausible ceiling still uses the GPU;
    # anything at or beyond it skips straight to software rather than
    # wasting a mostly-guaranteed-to-time-out attempt first.
    OFFICE_GPU_SAFE_PHYSICAL_PX = 12000

    OFFICE_MAX_CAPTURE_HEIGHT = 40000  # logical px cap on how tall a single
    # document's content is allowed to be, to keep a pathological document
    # from trying to rasterize an unbounded amount of image

    def __init__(self, chrome, html_path, width, height, tag, name):
        self.chrome = chrome
        self.html_path = html_path
        self.width = width
        self.height = height
        self.tag = tag
        self.name = name

    def build_pages(self, tmpdir, debug, render_scale, progress, continuous):
        """Returns a list of page PNG paths, or None on failure (a
        Chrome screenshot subprocess failing) - or, for FlowingText
        specifically, the 3-tuple ("pdf", pdf_path, npages) when a real
        PDF was captured instead (see FlowingText._build_pdf_pages()
        and OfficeDocument._render_office_pages(), which turns that
        into a PdfDocument delegate)."""
        raise NotImplementedError

    def _save_pages(self, trimmed, bounds, tmpdir, debug, progress):
        """Wraps _slice_and_save_pages() with the same progress/debug
        reporting every variant that slices one big capture wants -
        not used by ExcelWorkbook's multi-sheet case, which has no
        single `trimmed` capture to slice at all (each sheet's capture
        already *is* its own page)."""
        npages = len(bounds) - 1
        progress.update(f"{self.name}: splitting into {npages} page(s)...")
        with _DebugTimer(debug, f"{self.name}: splitting into {npages} page(s)"):
            return _slice_and_save_pages(trimmed, bounds, tmpdir, self.tag)


class ExcelWorkbook(OfficeVariant):
    """should_not_scale (Excel's tell - see OfficeDocument._render_office_pages()).
    self.sheet_tabs, if non-empty (see _parse_sheet_tabs()), means a
    multi-sheet workbook: Office.qlgenerator renders every sheet up
    front as its own AttachmentN.html, with Preview.html itself being
    just a JS tab strip - each sheet is rendered as its own page here,
    concurrently, and never needs slicing (each capture already *is* a
    whole page). Otherwise (a single-sheet workbook, where Preview.html
    *is* the sheet) it's one capture at exactly the plist's own Width/
    Height - already sized to fit this generator's content exactly,
    unlike FlowingText's grow-and-trim approach (Excel's sheet-tab
    selector is pinned to the bottom of the viewport regardless of
    window height, which would defeat that trick)."""

    # Office.qlgenerator's tab strip for a multi-sheet spreadsheet - see
    # _parse_sheet_tabs(). One <div class="TabViewItem ..."> per sheet, each
    # with a <div class="TabHeader"> (the sheet's own name) and an <a
    # href="..."> pointing at that sheet's already-rendered AttachmentN.html.
    _TAB_VIEW_ITEM_RE = re.compile(
        r'<div\s+class="TabViewItem[^"]*">\s*'
        r'<div\s+class="TabHeader">(.*?)</div>\s*'
        r'<a\s+href="([^"]+)">',
        re.IGNORECASE | re.DOTALL,
    )
    _TAG_RE = re.compile(r'<[^>]+>')

    def __init__(self, chrome, html_path, width, height, tag, name):
        super().__init__(chrome, html_path, width, height, tag, name)
        self.sheet_tabs = self._parse_sheet_tabs(html_path)

    def _parse_sheet_tabs(self, html_path):
        """For a multi-sheet Excel-like Quick Look preview, return an
        ordered [(sheet_name, absolute_html_path), ...] - one per sheet
        - by reading the tab strip out of `html_path`'s own content
        (see _TAB_VIEW_ITEM_RE). A single-sheet workbook's Preview.html
        *is* the sheet itself (no tab strip, no <iframe>) and this
        returns []."""
        try:
            with open(html_path, "r", encoding="utf-8", errors="replace") as f:
                content = f.read()
        except OSError:
            return []
        base_dir = os.path.dirname(html_path)
        tabs = []
        for m in self._TAB_VIEW_ITEM_RE.finditer(content):
            href = m.group(2)
            if _ABSOLUTE_SRC_RE.match(href):
                continue  # http(s)/data/... - not a local sibling file
            candidate = os.path.join(base_dir, href)
            if not os.path.isfile(candidate):
                continue
            name = html.unescape(self._TAG_RE.sub("", m.group(1))).strip()
            tabs.append((name or f"Sheet {len(tabs) + 1}", candidate))
        return tabs

    def build_pages(self, tmpdir, debug, render_scale, progress, continuous):
        if self.sheet_tabs:
            return self._build_multi_sheet(tmpdir, debug, render_scale, progress)
        return self._build_single_sheet(tmpdir, debug, render_scale, progress)

    def _build_multi_sheet(self, tmpdir, debug, render_scale, progress):
        # Each sheet is an independent render (its own already-
        # rasterized HTML, its own Chrome screenshot subprocess), so -
        # like _rasterize_broken_img_sources()'s embedded-image
        # conversion - run them concurrently rather than one at a time;
        # a workbook can have dozens of sheets, and each is mostly
        # subprocess wait (releases the GIL), not CPU time here.
        sheet_tabs = self.sheet_tabs
        name = self.name

        def _render_sheet(i, sheet_name, sheet_html_path):
            with _DebugTimer(
                debug, f"{name}: sheet {i + 1} ({sheet_name}): converting embedded images"
            ):
                sheet_html_path = _rasterize_broken_img_sources(sheet_html_path, tmpdir)
            page_path = os.path.join(tmpdir, f"office-page-{self.tag}-{i + 1}.png")
            label = f"{name}: sheet {i + 1}/{len(sheet_tabs)} ({sheet_name}): rendering"
            with _DebugTimer(debug, label):
                _capture_html_screenshot(
                    self.chrome, sheet_html_path, self.width, self.height, page_path, render_scale
                )
            return page_path

        page_paths = [None] * len(sheet_tabs)
        with concurrent.futures.ThreadPoolExecutor(max_workers=min(8, len(sheet_tabs))) as pool:
            futures = {
                pool.submit(_render_sheet, i, sheet_name, sheet_html_path): i
                for i, (sheet_name, sheet_html_path) in enumerate(sheet_tabs)
            }
            done = 0
            for future in concurrent.futures.as_completed(futures):
                try:
                    page_paths[futures[future]] = future.result()
                except (subprocess.CalledProcessError, subprocess.TimeoutExpired, OSError):
                    return None
                done += 1
                progress.update(f"{name}: rendered {done}/{len(sheet_tabs)} sheet(s)...")
        return page_paths

    def _build_single_sheet(self, tmpdir, debug, render_scale, progress):
        out_png = os.path.join(tmpdir, f"office-capture-{self.tag}.png")
        label = f"{self.name}: rendering ({self.width * render_scale:.0f}x{self.height * render_scale:.0f})"
        try:
            with _DebugTimer(debug, label), progress.spin(label + "..."):
                _capture_html_screenshot(
                    self.chrome, self.html_path, self.width, self.height, out_png, render_scale
                )
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired, OSError):
            return None
        try:
            trimmed = Image.open(out_png)
            trimmed.load()
            return self._save_pages(trimmed, [0, trimmed.height], tmpdir, debug, progress)
        finally:
            if os.path.exists(out_png):
                os.unlink(out_png)


class SlideDeck(OfficeVariant):
    """A slide deck (PowerPoint/Keynote) whose page/slide boundaries
    were measured (see OfficeDocument._measure_slide_offsets()) - the exact total
    height is already known, so this is captured in one shot rather
    than guessed. `confident` (see OfficeDocument._render_office_pages()) is whether the
    boundary came from the plist's own PageElementXPath, as opposed to
    a shape-based guess (_detect_fallback_page_xpath()) - only then is
    it trusted to paginate; a guessed boundary has been observed to
    drift/overflow on some real decks, so it's rendered as a single
    continuous page instead, the same as -c/--continuous forces for
    any deck."""

    def __init__(self, chrome, html_path, width, height, tag, name, slide_offsets, confident):
        super().__init__(chrome, html_path, width, height, tag, name)
        self.slide_offsets = slide_offsets
        self.confident = confident

    def build_pages(self, tmpdir, debug, render_scale, progress, continuous):
        total_height, tops = self.slide_offsets
        capture_height = min(self.OFFICE_MAX_CAPTURE_HEIGHT, max(1, round(total_height)))
        out_png = os.path.join(tmpdir, f"office-capture-{self.tag}.png")
        label = (
            f"{self.name}: rendering "
            f"({self.width * render_scale:.0f}x{capture_height * render_scale:.0f})"
        )
        try:
            with _DebugTimer(debug, label), progress.spin(label + "..."):
                _capture_html_screenshot(
                    self.chrome, self.html_path, self.width, capture_height, out_png, render_scale
                )
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired, OSError):
            return None
        try:
            trimmed = Image.open(out_png)
            trimmed.load()
            if continuous or not self.confident:
                bounds = [0, trimmed.height]
            else:
                # Slice at each slide's own measured start, in physical
                # (scaled) pixels - exact, unlike guessing from the
                # screenshot itself (see OfficeDocument._measure_slide_offsets() for
                # why that doesn't work here).
                bounds = [
                    min(trimmed.height, round(t * render_scale)) for t in tops
                ] + [trimmed.height]
            return self._save_pages(trimmed, bounds, tmpdir, debug, progress)
        finally:
            if os.path.exists(out_png):
                os.unlink(out_png)


class FlowingText(OfficeVariant):
    """A continuously-flowing document with no slide markers (e.g.
    Word). Tries Chrome's headless --print-to-pdf first (see
    _build_pdf_pages()) - a real PDF pdfless can re-rasterize crisply at
    any zoom - and only falls back to the older screenshot-and-slice
    approach (_build_pages_via_screenshot(), see there for the
    "grow the capture height and retry" doubling loop, up to a hard
    cap) if that Chrome build doesn't support it. Renders the fallback
    at OFFICE_RENDER_SCALE_FLOWING rather than the caller's default -
    these documents are usually short and text-heavy enough that
    sharpness matters more than the render-time tradeoff the default
    otherwise makes for a large slide deck - unless the caller
    (-s/--rendering-scale) asked for a specific scale explicitly (moot
    for the PDF path, which is always re-rasterized at whatever DPI the
    current zoom needs, regardless of any render_scale)."""

    OFFICE_RENDER_SCALE_FLOWING = 2  # default device-pixel-ratio for
    # continuously-flowing text (Word and the like - no slide/page markers
    # at all, so no slide_offsets - see OfficeDocument._render_office_pages()): these are
    # text-heavy and usually short, so favor sharpness over the render-time
    # tradeoff OFFICE_RENDER_SCALE otherwise makes for a many-slide deck -
    # unless --rendering-scale was passed explicitly.

    def build_pages(self, tmpdir, debug, render_scale, progress, continuous):
        pdf_pages = self._build_pdf_pages(tmpdir, debug, progress, continuous)
        if pdf_pages is not None:
            return pdf_pages
        return self._build_pages_via_screenshot(tmpdir, debug, render_scale, progress, continuous)

    def _build_pdf_pages(self, tmpdir, debug, progress, continuous):
        """Real PDF pages via _capture_html_pdf(). Returns ("pdf",
        path, npages) for OfficeDocument._render_office_pages() to
        wire up as a PdfDocument delegate, or None to fall back to the
        screenshot path (an older Chrome without --print-to-pdf, or
        anything else going wrong).

        Not continuous (the common case): one page's own height
        (self.height, from the Quick Look preview's own plist) becomes
        the @page height, and Chrome's print engine paginates the rest
        on its own - real page breaks driven by the actual content
        flow, unlike the screenshot path's own bounds logic below,
        which can only guess at a fixed pixel height after the fact.
        That's also why this doesn't need SlideDeck's
        OfficeDocument._measure_slide_offsets() dance in the first place: a
        print-mode page break follows the content wherever it actually
        flows, so a slightly-off page height just spills part of one
        page onto the next rather than throwing off every later page's
        position too (fixed pixel-slicing's boundaries are cumulative
        - one page's error shifts every one after it; print-mode's
        aren't, each page break is independent).

        continuous=True (-c/--continuous) instead measures the
        document's real total height first (_measure_content_height())
        and requests one oversized page sized to fit it - a
        continuously-flowing document has no real page boundaries of
        its own to paginate at in the first place (see the class
        docstring), so there's nothing for the print engine to do here
        that measuring wouldn't do more precisely."""
        out_pdf = os.path.join(tmpdir, f"office-capture-{self.tag}.pdf")
        if continuous:
            measure_label = f"{self.name}: measuring content height"
            with _DebugTimer(debug, measure_label), progress.spin(measure_label + "..."):
                content_height = _measure_content_height(self.chrome, self.html_path, self.width)
            if not content_height:
                # Couldn't measure - rather than guess a one-size-fits-
                # all OfficeVariant.OFFICE_MAX_CAPTURE_HEIGHT (a real, if rare, source
                # of a giant near-blank page under load, where Chrome's
                # dump-dom measurement is more likely to time out), fall
                # back to the screenshot path, which doesn't depend on
                # this measurement at all.
                return None
            # A little headroom: print-mode layout can measure a few px
            # taller than screen-mode's scrollHeight for the same
            # content (a marginal font-metric difference between the
            # two rendering paths) - this only has to avoid spilling a
            # couple of leftover px onto a needless second page, not be
            # exact.
            page_height = min(self.OFFICE_MAX_CAPTURE_HEIGHT, content_height + 40)
        else:
            page_height = self.height
        label = f"{self.name}: rendering to PDF"
        with _DebugTimer(debug, label), progress.spin(label + "..."):
            ok = _capture_html_pdf(self.chrome, self.html_path, self.width, page_height, out_pdf)
        npages = _pdf_page_count_safe(out_pdf) if ok else None
        if not npages:
            if os.path.exists(out_pdf):
                os.unlink(out_pdf)
            return None
        return ("pdf", out_pdf, npages)

    def _build_pages_via_screenshot(self, tmpdir, debug, render_scale, progress, continuous):
        if render_scale == OFFICE_RENDER_SCALE:
            render_scale = self.OFFICE_RENDER_SCALE_FLOWING
        out_png = os.path.join(tmpdir, f"office-capture-{self.tag}.png")
        # Starting small (rather than generously large) matters for
        # speed, not just to avoid over-capturing a short document: it
        # also keeps a short document's capture(s) under
        # _capture_html_screenshot's GPU-safe size threshold, where
        # every doubling from here on is much faster than the single
        # oversized one this used to start with.
        capture_height = min(self.OFFICE_MAX_CAPTURE_HEIGHT, max(self.height * 3, 1500))
        try:
            attempt = 0
            while True:
                attempt += 1
                label = (
                    f"{self.name}: rendering attempt {attempt} "
                    f"({self.width * render_scale:.0f}x{capture_height * render_scale:.0f})"
                )
                try:
                    with _DebugTimer(debug, label), progress.spin(label + "..."):
                        _capture_html_screenshot(
                            self.chrome, self.html_path, self.width, capture_height, out_png, render_scale
                        )
                except (subprocess.CalledProcessError, subprocess.TimeoutExpired, OSError):
                    return None
                img = Image.open(out_png)
                img.load()
                trimmed, cut_off = _trim_trailing_blank_rows(img, _sample_background_color(img))
                if not cut_off or capture_height >= self.OFFICE_MAX_CAPTURE_HEIGHT:
                    break
                capture_height = min(self.OFFICE_MAX_CAPTURE_HEIGHT, capture_height * 2)
            if continuous:
                bounds = [0, trimmed.height]
            else:
                page_px = max(1, round(self.height * render_scale))
                npages = max(1, -(-trimmed.height // page_px))  # ceil division
                bounds = [min(trimmed.height, i * page_px) for i in range(npages + 1)]
            return self._save_pages(trimmed, bounds, tmpdir, debug, progress)
        finally:
            if os.path.exists(out_png):
                os.unlink(out_png)


def extract_office_text(path):
    """Plain-text extraction of a whole Word-family document (.doc,
    .docx, .rtf, .odt, ...), via macOS's own `textutil -convert txt
    -stdout` - unlike pdftotext for a PDF, this has no notion of pages,
    so it's always the entire document at once (see how kind=="office"
    is handled in Viewer._load_text_page() and around it). Returns None
    if textutil isn't available, doesn't understand this file at all
    (a spreadsheet or a slide deck: no single flowing "text" to extract,
    and textutil silently produces nothing), or the conversion otherwise
    failed."""
    if shutil.which("textutil") is None:
        return None
    try:
        out = subprocess.run(
            ["textutil", "-convert", "txt", "-stdout", path],
            capture_output=True, text=True, timeout=30,
        )
    except (subprocess.TimeoutExpired, OSError):
        return None
    if out.returncode != 0 or not out.stdout.strip():
        return None
    return out.stdout.splitlines()


def is_probably_text(path, sniff_bytes=8000):
    """The same binary/text heuristic git and file(1) use: if the first
    few KB contain a NUL byte, treat it as binary. (NUL is technically
    valid UTF-8, but genuine text essentially never contains it.)"""
    try:
        with open(path, "rb") as f:
            return b"\x00" not in f.read(sniff_bytes)
    except OSError:
        return False


_CONTROL_CHAR_RE = re.compile(r"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]")


def _caret_notation(match):
    """"^X" caret notation for one C0 control character or DEL (e.g.
    "\\x0c" (^L) or "\\x1b" (^[)) - XORing the byte with 0x40 maps the
    whole range (0x00-0x1f, plus 0x7f) to the right letter/symbol in one
    step, the same trick a terminal's own ^-echoing uses."""
    return "^" + chr(ord(match.group()) ^ 0x40)


def _sanitize_text_for_display(content):
    """Show stray control characters in caret notation, but pass ANSI
    color/style sequences through intact - git/man/etc. emit those when
    pdfless is used as $PAGER."""
    out = []
    i = 0
    while i < len(content):
        m = _ansi_escape_at(content, i)
        if m:
            out.append(m.group(0))
            i = m.end()
            continue
        ch = content[i]
        if _CONTROL_CHAR_RE.fullmatch(ch):
            out.append(_caret_notation(_CONTROL_CHAR_RE.match(ch)))
        else:
            out.append(ch)
        i += 1
    return "".join(out)


def read_plain_text_lines(path, tab_width=8):
    """A plain text file's lines, as pdftotext -layout's output is for a
    PDF page: ready to hand straight to the existing text-mode renderer.
    Tabs are expanded (there's no terminal-native tab stop handling in
    that renderer's column math) and stray control characters (e.g. a
    raw ESC, or a form feed/^L) are shown in caret notation (^[, ^L, ...)
    - see _caret_notation() - rather than passed through raw, so odd
    file content can't corrupt the terminal display the way that would.

    Always reads `path` verbatim - an RTF file's raw markup (control
    words, font/color tables, ...) rather than its document text, which
    is exactly what a plain-text sniff/decode check wants. RtfDocument
    is the one that knows to prefer extract_office_text() over this raw
    markup for actual display - see RtfDocument.extract_text()."""
    with open(path, "r", encoding="utf-8") as f:
        content = f.read()
    content = content.expandtabs(tab_width)
    content = _sanitize_text_for_display(content)
    return content.splitlines()


def compile_search_pattern(query):
    """Compile `query` as a case-insensitive regex. If it isn't valid
    regex syntax (e.g. a literal query like "C++" - "+" repeating nothing
    is a regex error), fall back to matching it literally instead of
    just failing the search."""
    try:
        return re.compile(query, re.IGNORECASE)
    except re.error:
        return re.compile(re.escape(query), re.IGNORECASE)



class UnusableFile(Exception):
    """Raised by DocumentHandler.sniff() when a file's format was
    positively identified (e.g. its PDF magic bytes matched) but it
    turned out not to be actually usable (failed to decode/parse) -
    distinct from sniff() returning None, which means "not this kind,
    try the next one instead". The caller (main()) reports this
    exception's own message and skips the file, without trying any
    further handler classes - once a format is positively identified,
    a failure to actually use it is that format's problem, not a sign
    the file might be some other kind instead."""


class DocumentHandler:
    """Base class for a file's format-specific behavior. Each subclass
    corresponds to one of main()'s "kind" strings ("pdf"/"image"/
    "text"/"office") and is tried, in a fixed priority order, via
    sniff() - see HANDLER_CLASSES."""

    kind = None  # overridden per subclass

    def __init__(self, path):
        self.path = path

    @classmethod
    def sniff(cls, path, tmpdir, debug=False):
        """Return an instance of this class if `path` looks like this
        kind, else None if it doesn't (try the next class). Raises
        UnusableFile if it does look like this kind but isn't actually
        usable. `tmpdir`/`debug` are only used by OfficeDocument
        (qlmanage needs a scratch dir; -d wants to know about a crashed
        qlmanage) - every other subclass ignores them; they're part of
        the common signature so a dispatcher can try each class
        uniformly without knowing which."""
        raise NotImplementedError

    def page_count(self):
        """Number of pages, or None if unknown until the file is
        actually rendered (only OfficeDocument - its page count isn't
        known until Quick Look + Chrome have run; see
        Viewer._ensure_office_pages())."""
        raise NotImplementedError

    def extract_text(self, page):
        """Text-mode content for `page` (1-based) - or the whole
        document, for a handler whose text isn't paginated (see
        text_mode_is_paginated()), which ignores `page` entirely. None
        means there's nothing to show (the 't' key reports that)."""
        return None

    def supports_text_mode(self):
        """Whether 't' should even try entering text mode at all - the
        actual content still comes from extract_text(), which can
        return None for a specific file even when this is True (e.g.
        OfficeDocument: textutil produces nothing for a PowerPoint/
        Excel file even though it works for Word)."""
        return False

    def supports_search(self):
        return False

    def text_mode_is_paginated(self):
        """Whether text mode's content is naturally split into pages
        the same way image mode is, so n/p/g/G page navigation should
        apply to it too. False means text mode shows one flowing blob
        regardless of the current image-mode page (e.g. TextDocument/
        RtfDocument's whole file, OfficeDocument's whole document via
        textutil)."""
        return False

    def search_resets_on_text_mode_toggle(self):
        """Whether an active search should be cleared when `t` crosses
        between image mode and text mode. False for handlers where both
        views search the same extracted text (e.g. PDF); True when the
        two modes search different things (MarkdownDocument)."""
        return False

    def starts_in_text_mode(self):
        """Whether this handler has no image view at all - permanently
        "in text mode" from the moment the file opens (a plain text
        file - see TextDocument, and so by inheritance RtfDocument) -
        as opposed to starting in image mode and only switching to text
        mode via 't' (a PDF, or a Quick Look preview file)."""
        return False

    def default_text_border(self, border_default):
        """Whether text mode's border should be on by default for this
        handler - see Viewer._default_text_border(). `border_default` is
        whatever --no-border requested; overridden by TextDocument (and
        so, by inheritance, RtfDocument), which have no real "page"
        boundary worth bordering at all, regardless of --no-border."""
        return border_default

    def default_text_wrap(self, wrap_default):
        """Whether text mode should default to soft-wrapping long lines
        (off means panning across them instead, with h/l/H/L) - see
        Viewer._default_text_wrap(). Off here regardless of
        `wrap_default` (whatever -S/--chop-long-lines requested): a
        PDF's per-page text or an Office document's whole-document text
        (via textutil) is derived from something else, not the actual
        file being paged through, so panning (the pre-existing behavior)
        stays the default - overridden by TextDocument (and so, by
        inheritance, RtfDocument), which default to `wrap_default`
        itself, i.e. wrapped unless -S said otherwise."""
        return False

    def get_page_image(self, cache, page, target_px, fit):
        """Return `page`'s image (a PIL.Image), scaled so it's
        `target_px` wide (fit="width") or tall (fit="height") - used by
        PageCache.get(), which only ever calls this for the kinds it's
        used for at all (pdf/image/office - never text). `cache` (a
        PageCache) owns the shared LRU eviction bookkeeping (see
        cache._cached()/cache._store()) while each handler owns the
        format-specific way to actually produce/scale the page.

        This default implementation - used by ImageDocument and
        OfficeDocument via _source_for_page() - treats the page as a
        single native image, loaded once (see _native_page_image()) and
        resized by pixel ratio; PdfDocument overrides this entirely,
        rasterizing on demand at whatever DPI the target size implies
        instead, since a PDF has no fixed native pixel size at all."""
        native = self._native_page_image(cache, page)
        native_dim = native.width if fit == "width" else native.height
        key = (page, round(target_px))
        cached = cache._cached(key)
        if cached is not None:
            return cached
        scale = target_px / native_dim
        new_size = (
            max(1, round(native.width * scale)),
            max(1, round(native.height * scale)),
        )
        img = native.resize(new_size, Image.Resampling.LANCZOS)
        cache._store(key, img)
        return img

    def _native_page_image(self, cache, page):
        """Load (once per page, cached in `cache`) and normalize
        _source_for_page()'s file - shared by every get_page_image()
        that treats a page as a single native image (see there)."""
        native = cache._native_images.get(page)
        if native is not None:
            return native
        source = self._source_for_page(cache, page)
        try:
            img = Image.open(source)
            img = ImageOps.exif_transpose(img)  # also .load()s it
            if img.mode in ("RGBA", "LA") or (
                img.mode == "P" and "transparency" in img.info
            ):
                img = img.convert("RGBA")
            else:
                img = img.convert("RGB")
        except Exception as e:
            # Reached from -F/--follow noticing the file changed into
            # something that fails to decode - main() already checks
            # this once up front, but the file can always go bad again
            # later. Re-raised as a plain RuntimeError so callers
            # (reload()'s caller in run_viewer) don't need to know
            # anything PIL-specific to catch it.
            raise RuntimeError(f"cannot load {source}: {e}") from e
        cache._native_images[page] = img
        return img

    def _source_for_page(self, cache, page):
        """The file to load for `page`, for the default get_page_image()
        - overridden by ImageDocument (always its own path) and
        OfficeDocument (one pre-rendered PNG per page, from `cache`)."""
        raise NotImplementedError


class PdfDocument(DocumentHandler):
    kind = "pdf"

    _BBOX_PAGE_RE = re.compile(
        r'<page width="([\d.]+)" height="([\d.]+)">(.*?)</page>', re.S
    )
    _BBOX_WORD_RE = re.compile(
        r'<word xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)">(.*?)</word>'
    )

    @staticmethod
    def is_pdf_file(path):
        """Sniff the file's own content rather than trusting its
        extension - a PDF always starts with "%PDF-", regardless of
        what it's named. A staticmethod (not reading self.path) since
        main() also calls this directly, on a candidate path, before
        any classification (and so any PdfDocument instance) exists -
        to decide up front whether poppler is required at all."""
        try:
            with open(path, "rb") as f:
                return f.read(5) == b"%PDF-"
        except OSError:
            return False

    @staticmethod
    def _pdf_page_count(path):
        out = subprocess.run(
            ["pdfinfo", path], capture_output=True, text=True, check=True
        ).stdout
        m = re.search(r"^Pages:\s+(\d+)", out, re.MULTILINE)
        if not m:
            die("could not determine page count")
        return int(m.group(1))

    @classmethod
    def sniff(cls, path, tmpdir, debug=False):
        if not cls.is_pdf_file(path):
            return None
        try:
            cls._pdf_page_count(path)
        except Exception as e:
            raise UnusableFile(f"not a usable PDF ({e})") from e
        return cls(path)

    def page_count(self):
        return self._pdf_page_count(self.path)

    def page_size_pt(self, page):
        """(width_pt, height_pt) for `page`."""
        out = subprocess.run(
            ["pdfinfo", "-f", str(page), "-l", str(page), self.path],
            capture_output=True,
            text=True,
            check=True,
        ).stdout
        m = re.search(r"^Page\s*(?:\d+\s+)?size:\s+([\d.]+) x ([\d.]+)", out, re.MULTILINE)
        if not m:
            die(f"could not determine page size for page {page}")
        return float(m.group(1)), float(m.group(2))

    def extract_text(self, page):
        """Plain-text rendering of one page, via poppler's pdftotext
        -layout (which tries to preserve the page's visual line/column
        layout, unlike the flat word-run text used for search)."""
        out = subprocess.run(
            ["pdftotext", "-f", str(page), "-l", str(page), "-layout", self.path, "-"],
            capture_output=True,
            text=True,
            check=True,
        ).stdout
        return out.splitlines()

    def build_search_index(self):
        """Extract per-page text and word positions (via poppler's pdftotext
        -bbox) for searching. Returns a list, one entry per page, each
        {"width_pt": float, "height_pt": float, "text": str,
        "words": [(start, end, xMin, yMin, xMax, yMax), ...]} (all in points)
        where (start, end) are offsets into "text" for that word."""
        out = subprocess.run(
            ["pdftotext", "-bbox", self.path, "-"],
            capture_output=True,
            text=True,
            check=True,
        ).stdout

        pages = []
        for width, height, body in self._BBOX_PAGE_RE.findall(out):
            words = []
            parts = []
            offset = 0
            for xmin, ymin, xmax, ymax, word_html in self._BBOX_WORD_RE.findall(body):
                word_text = html.unescape(word_html)
                if not word_text:
                    continue
                start = offset
                parts.append(word_text)
                offset += len(word_text)
                words.append(
                    (start, offset, float(xmin), float(ymin), float(xmax), float(ymax))
                )
                parts.append(" ")
                offset += 1
            pages.append(
                {
                    "width_pt": float(width),
                    "height_pt": float(height),
                    "text": "".join(parts),
                    "words": words,
                }
            )
        return pages

    @staticmethod
    def _resolve_link_dest(reader, page_num_by_ref, dest):
        """A /Dest or action /D value - either an explicit destination array,
        or a name/bytestring to look up among the document's named
        destinations. Returns (page_num, top_pt) - top_pt is the target's y
        position in PDF points (bottom-up, i.e. still in the PDF's own
        coordinate system - the caller converts it), or None if it isn't
        specified by this destination type. Returns None outright if the
        destination can't be resolved at all (e.g. it points outside this
        document, or the PDF is malformed)."""
        from pypdf.generic import IndirectObject

        if isinstance(dest, (str, bytes)):
            name = dest if isinstance(dest, str) else dest.decode("utf-8", "replace")
            named = reader.named_destinations.get(name)
            if named is None:
                return None
            dest = getattr(named, "dest_array", named)
        if not dest:
            return None

        target = dest[0]
        ref = target if isinstance(target, IndirectObject) else getattr(
            target, "indirect_reference", None
        )
        if ref is None:
            return None
        page_num = page_num_by_ref.get((ref.idnum, ref.generation))
        if page_num is None:
            return None

        top_pt = None
        fit_type = str(dest[1]) if len(dest) > 1 else None
        try:
            if fit_type == "/XYZ" and len(dest) > 3 and dest[3] is not None:
                top_pt = float(dest[3])
            elif fit_type in ("/FitH", "/FitBH") and len(dest) > 2 and dest[2] is not None:
                top_pt = float(dest[2])
        except (TypeError, ValueError):
            top_pt = None
        return page_num, top_pt

    def build_link_index(self, npages):
        """Extract clickable link annotations for every page, via pypdf.
        Returns a list of `npages` dicts, one per page in order, each
        {"width_pt": float, "height_pt": float, "links": [...]}, where each
        link is {"xmin", "ymin", "xmax", "ymax"} (points, top-down - flipped
        from the PDF's own bottom-up rects to match this file's coordinate
        system elsewhere, e.g. build_search_index()) plus either
        {"kind": "uri", "uri": str} for an external link or
        {"kind": "page", "page": int, "top_pt": float | None} for a jump to
        another page in the same document."""
        empty = [{"width_pt": 0.0, "height_pt": 0.0, "links": []} for _ in range(npages)]
        try:
            from pypdf import PdfReader
        except ImportError:
            return empty

        try:
            reader = PdfReader(self.path)
        except Exception:
            return empty

        page_num_by_ref = {}
        for i, p in enumerate(reader.pages):
            ref = p.indirect_reference
            if ref is not None:
                page_num_by_ref[(ref.idnum, ref.generation)] = i + 1

        result = []
        for i in range(npages):
            links = []
            width_pt = height_pt = 0.0
            try:
                page = reader.pages[i]
                box = page.mediabox
                width_pt, height_pt = float(box.width), float(box.height)
                for annot_ref in page.get("/Annots") or []:
                    try:
                        annot = annot_ref.get_object()
                        if annot.get("/Subtype") != "/Link":
                            continue
                        rect = annot.get("/Rect")
                        if rect is None or len(rect) != 4:
                            continue
                        x0, y0, x1, y1 = (float(v) for v in rect)
                        xmin, xmax = min(x0, x1), max(x0, x1)
                        ymin_bu, ymax_bu = min(y0, y1), max(y0, y1)
                        # Flip the PDF's bottom-up rect into the top-down
                        # system used everywhere else here.
                        ymin, ymax = height_pt - ymax_bu, height_pt - ymin_bu

                        action = annot.get("/A")
                        if action is not None and action.get("/S") == "/URI":
                            uri = action.get("/URI")
                            if uri:
                                links.append({
                                    "xmin": xmin, "ymin": ymin,
                                    "xmax": xmax, "ymax": ymax,
                                    "kind": "uri", "uri": str(uri),
                                })
                            continue

                        dest = annot.get("/Dest")
                        if dest is None and action is not None and action.get("/S") == "/GoTo":
                            dest = action.get("/D")
                        if dest is None:
                            continue
                        resolved = self._resolve_link_dest(reader, page_num_by_ref, dest)
                        if resolved is None:
                            continue
                        page_num, top_pt = resolved
                        links.append({
                            "xmin": xmin, "ymin": ymin, "xmax": xmax, "ymax": ymax,
                            "kind": "page", "page": page_num, "top_pt": top_pt,
                        })
                    except Exception:
                        continue  # one malformed annotation shouldn't lose the rest
            except Exception:
                pass
            result.append({"width_pt": width_pt, "height_pt": height_pt, "links": links})
        return result

    @staticmethod
    def find_search_matches(index, query):
        """Return every match of `query` (a case-insensitive regex, or a
        literal substring if it isn't valid regex syntax) across the whole
        document, as a list of (page_number, xMin, yMin, xMax, yMax) bounding
        boxes (in points, the union of every word the match touches), in
        reading order."""
        pattern = compile_search_pattern(query)
        matches = []
        for page_num, page in enumerate(index, start=1):
            for m in pattern.finditer(page["text"]):
                pos, match_end = m.start(), m.end()
                if pos == match_end:
                    continue  # skip zero-width matches (e.g. a pattern like "x*")
                box = None
                for word_start, word_end, xmin, ymin, xmax, ymax in page["words"]:
                    if word_start < match_end and word_end > pos:
                        # poppler often lumps a whole run of CJK text (with no
                        # spaces to split on) into a single <word>, sometimes
                        # spanning most of a line. Highlighting that whole word
                        # would hugely overstate the match, so narrow the box
                        # to just the matched characters' share of it, assuming
                        # roughly uniform character width left-to-right.
                        word_len = word_end - word_start
                        local_start = max(pos, word_start) - word_start
                        local_end = min(match_end, word_end) - word_start
                        frac_start = local_start / word_len if word_len else 0.0
                        frac_end = local_end / word_len if word_len else 1.0
                        sub_xmin = xmin + frac_start * (xmax - xmin)
                        sub_xmax = xmin + frac_end * (xmax - xmin)
                        if box is None:
                            box = [sub_xmin, ymin, sub_xmax, ymax]
                        else:
                            box[0] = min(box[0], sub_xmin)
                            box[1] = min(box[1], ymin)
                            box[2] = max(box[2], sub_xmax)
                            box[3] = max(box[3], ymax)
                if box is not None:
                    matches.append((page_num, box[0], box[1], box[2], box[3]))
        return matches

    def supports_text_mode(self):
        return True

    def supports_search(self):
        return True

    def text_mode_is_paginated(self):
        return True

    def get_page_image(self, cache, page, target_px, fit):
        """Rasterize `page` at whatever DPI makes it `target_px` wide
        (fit="width") or tall (fit="height") - a PDF page has no fixed
        native pixel size, unlike a plain image or an office-preview
        PNG (see DocumentHandler.get_page_image()'s default)."""
        width_pt, height_pt = self.page_size_pt(page)
        page_pt = width_pt if fit == "width" else height_pt
        dpi = 72.0 * target_px / page_pt
        key = (page, round(dpi))

        cached = cache._cached(key)
        if cached is not None:
            return cached

        prefix = os.path.join(cache.tmpdir, f"page-{page}-{round(dpi)}")
        subprocess.run(
            [
                "pdftoppm", "-png", "-r", str(dpi),
                "-f", str(page), "-l", str(page),
                "-singlefile", self.path, prefix,
            ],
            check=True,
        )
        img = Image.open(prefix + ".png")
        img.load()
        os.unlink(prefix + ".png")

        cache._store(key, img)
        return img


class ImageDocument(DocumentHandler):
    kind = "image"

    @classmethod
    def sniff(cls, path, tmpdir, debug=False):
        try:
            # .load() rather than the lighter .verify(): some formats
            # (e.g. WMF without a system loader available) pass
            # verify() - which only sanity-checks the file structure -
            # but still fail to actually decode.
            with Image.open(path) as probe:
                probe.load()
        except Exception:
            return None
        return cls(path)

    def page_count(self):
        return 1

    def _source_for_page(self, cache, page):
        return self.path  # always page 1 - see page_count()


class TextDocument(DocumentHandler):
    kind = "text"

    @classmethod
    def sniff(cls, path, tmpdir, debug=False):
        if not is_probably_text(path):
            return None
        try:
            read_plain_text_lines(path)  # just to validate it decodes
        except Exception as e:
            raise UnusableFile(f"not valid UTF-8 text ({e})") from e
        return cls(path)

    def page_count(self):
        return 1

    def extract_text(self, page):
        return read_plain_text_lines(self.path)

    def supports_text_mode(self):
        return True

    def supports_search(self):
        return True

    def starts_in_text_mode(self):
        return True

    def default_text_border(self, border_default):
        # No real "page" boundary in a plain text file worth bordering,
        # regardless of --no-border.
        return False

    def default_text_wrap(self, wrap_default):
        # This *is* the actual file content being paged through (unlike
        # a PDF's extracted text or an Office document's textutil
        # dump), so it defaults to wrapping like less(1) itself does -
        # unless -S/--chop-long-lines said otherwise.
        return wrap_default


class RtfDocument(TextDocument):
    """An RTF file is - deliberately - plain ASCII text, so it also
    matches TextDocument's own signature; tried first (see
    HANDLER_CLASSES) so its more specific one wins. Everything else is
    inherited from TextDocument - only extract_text() differs: showing
    an RTF file's "plain text" verbatim would mean showing its raw
    markup (control words, font/color tables, ...), not the document's
    actual content - see is_rtf_file()."""

    @staticmethod
    def is_rtf_file(path):
        """Sniff for RTF's own signature ("{\\rtf1" right at the start),
        the same way PdfDocument.is_pdf_file() sniffs "%PDF-" rather
        than trusting the extension. RTF is - deliberately - plain
        ASCII text, so is_probably_text()'s NUL-byte heuristic happily
        calls it plain text too; sniff() uses this to tell the two
        apart. A staticmethod (not reading self.path) since
        RtfOfficeDocument.sniff() also calls this directly, on a
        candidate path, before any RtfDocument instance exists."""
        try:
            with open(path, "rb") as f:
                return f.read(6) == b"{\\rtf1"
        except OSError:
            return False

    @classmethod
    def sniff(cls, path, tmpdir, debug=False):
        if not cls.is_rtf_file(path):
            return None
        if not is_probably_text(path):
            # Vanishingly unlikely for genuine RTF (it's pure ASCII by
            # spec) - but keep the same NUL-byte safety net
            # TextDocument itself applies, rather than trusting the RTF
            # signature alone.
            return None
        try:
            read_plain_text_lines(path)  # just to validate it decodes
        except Exception as e:
            raise UnusableFile(f"not valid UTF-8 text ({e})") from e
        return cls(path)

    def extract_text(self, page):
        return extract_office_text(self.path) or super().extract_text(page)


class OfficeDocument(DocumentHandler):
    """Anything this Mac's Quick Look generators can preview (Word,
    Excel, PowerPoint, Keynote, Pages, ...) via qlmanage + a local
    Chrome. page_count() is deliberately None - unknown until
    build_pages() actually renders it (see
    Viewer._ensure_office_pages()). The actual rendering
    (_render_office_pages()) picks one of the ExcelWorkbook/SlideDeck/
    FlowingText OfficeVariant strategies and delegates to it."""

    kind = "office"

    # Extensions where soffice's own --convert-to pdf pagination lands
    # on the same "page" boundary the qlmanage/Chrome pipeline already
    # uses - a real Word/RTF page break, or one slide per PowerPoint
    # page (confirmed by hand: soffice's page count matches the
    # existing qlmanage/Chrome one exactly, both for a small fixture
    # and for a real 55-slide deck with hidden slides). .docm/.pptm
    # (macro-enabled Word/PowerPoint) already classify as
    # OfficeDocument via the same Office.qlgenerator that handles
    # .docx/.pptx (confirmed by hand), so they get the same treatment.
    # Deliberately excludes Excel (.xls/.xlsx/.xlsm): soffice
    # paginates a spreadsheet by its print area/page setup, which for
    # a workbook never tuned for printing fragments one sheet across
    # several oddly-cut pages (confirmed by hand on a real 2-sheet
    # workbook: 9 soffice pages, split mid-column with no header row)
    # - nothing like qlmanage's "one full sheet per page". See
    # _soffice_pages_if_eligible().
    _SOFFICE_EXTENSIONS = (".doc", ".docx", ".docm", ".ppt", ".pptx", ".pptm", ".rtf")

    OFFICE_DEFAULT_WIDTH = 816  # 8.5in at 96dpi, if the plist has no Width
    OFFICE_DEFAULT_HEIGHT = 1056  # 11in at 96dpi, if the plist has no Height

    def __init__(self, path):
        super().__init__(path)
        self.pages = None  # [png_path, ...] once rendered - see
        # build_pages()/ensure_pages(); None until the first render.
        self._pdf_delegate = None  # a PdfDocument wrapping a real,
        # print-to-pdf-rendered PDF, when FlowingText managed one (see
        # _render_office_pages()) - get_page_image() forwards to it
        # instead of treating self.pages as a list of PNGs, so these
        # pages stay crisp at any zoom the same way a real PDF does.
        # self.pages is still set (to a same-length placeholder list)
        # in that case, purely so len(self.pages) keeps working for
        # Viewer._ensure_office_pages()/reload().

    @classmethod
    def sniff(cls, path, tmpdir, debug=False):
        return cls(path) if cls._probe_preview(path, tmpdir, debug=debug) else None

    @staticmethod
    def _generate_ql_preview(path, tmpdir, debug=False):
        """Ask Quick Look for an HTML preview of `path` via
        `qlmanage -p`. Returns (html_path, width, height,
        should_not_scale, page_element_xpath) - width/height are None
        if the plist didn't have them, page_element_xpath is None if it
        has no "PageElementXPath" (meaning this document has no
        distinct page/slide elements to speak of - e.g. Word's
        continuously-flowing text) - or None if qlmanage isn't
        available, has no generator for this file, or produced
        nothing. `path` isn't necessarily self.path (see
        RtfOfficeDocument, which previews a converted .docx instead),
        so this is a staticmethod rather than reading self.path.

        With debug=True (-d/--debug), a `qlmanage` that crashed or
        exited non-zero is reported to stderr - this isn't rare: buggy
        third-party (or even Apple's own) Quick Look generators can
        crash qlmanage outright (e.g. an uncaught NSException, seen in
        the wild for some .odt files) rather than just fail to produce
        a preview, and without this it's indistinguishable from "no
        generator for this file at all", which looks identical from
        here (no Preview.html either way)."""
        if shutil.which("qlmanage") is None:
            return None
        outdir = tempfile.mkdtemp(dir=tmpdir, prefix="qlpreview-")
        name = os.path.basename(path)
        try:
            result = subprocess.run(
                ["qlmanage", "-o", outdir, "-p", path],
                capture_output=True, timeout=30,
            )
        except (subprocess.TimeoutExpired, OSError) as e:
            if debug:
                print(
                    f"pdfless: [debug] {name}: qlmanage failed to run: {e}",
                    file=sys.stderr, end="\r\n",
                )
            return None
        bundle = os.path.join(outdir, f"{os.path.basename(path)}.qlpreview")
        html_path = os.path.join(bundle, "Preview.html")
        if not os.path.isfile(html_path):
            if debug and result.returncode != 0:
                # A negative code means killed by that signal (e.g.
                # -6/SIGABRT for an uncaught Objective-C exception) -
                # qlmanage itself crashed, not just "no generator for
                # this file".
                how = (
                    f"crashed (signal {-result.returncode})"
                    if result.returncode < 0
                    else f"exited with status {result.returncode}"
                )
                stderr_lines = result.stderr.decode("utf-8", "replace").strip().splitlines()
                detail = f" - {stderr_lines[0]}" if stderr_lines else ""
                print(
                    f"pdfless: [debug] {name}: qlmanage {how}{detail}",
                    file=sys.stderr, end="\r\n",
                )
            return None

        width = height = page_element_xpath = None
        should_not_scale = False
        plist_path = os.path.join(bundle, "PreviewProperties.plist")
        try:
            with open(plist_path, "rb") as f:
                props = plistlib.load(f)
            raw_width, raw_height = props.get("Width"), props.get("Height")
            # Chrome's --window-size silently falls back to a default
            # size if given a float (e.g. "637.0,792.0") rather than
            # plain integers - the plist's numbers are often floats, so
            # round them here.
            width = round(raw_width) if raw_width else None
            height = round(raw_height) if raw_height else None
            should_not_scale = bool(props.get("ShouldNotScale"))
            page_element_xpath = props.get("PageElementXPath") or None
        except (OSError, ValueError):
            pass
        return html_path, width, height, should_not_scale, page_element_xpath

    @staticmethod
    def _probe_preview(path, tmpdir, debug=False):
        """Cheaply check whether `path` is something this Mac's Quick
        Look generators can preview at all (Word, Excel, PowerPoint,
        Keynote, Pages, ...) - i.e. whether _render_office_pages() has
        any chance of working - without doing that method's expensive
        part (the actual Chrome rendering). Used by sniff() (main()'s
        classification, so a file that will never be looked at doesn't
        pay for a render - see Viewer._ensure_office_pages()) - `path`
        isn't necessarily what self.path will end up being (see
        RtfOfficeDocument.sniff(), which probes a converted .docx), so
        this can't be a normal instance method.

        debug=True (-d/--debug) reports a crashed/failing qlmanage -
        see _generate_ql_preview()."""
        # soffice alone is enough, without ever touching qlmanage/
        # Chrome - both macOS-only, so on Linux (no Quick Look at all)
        # this is the only way Word/PowerPoint/RTF get previewed. Safe
        # even on macOS: _render_office_pages()/build_pages() already
        # try soffice before qlmanage for these extensions (see
        # _soffice_pages_if_eligible()), so this just matches what
        # rendering would do anyway instead of paying for a redundant
        # qlmanage dry run.
        if path.lower().endswith(OfficeDocument._SOFFICE_EXTENSIONS) and find_soffice() is not None:
            return True
        if find_chrome() is None:
            return False
        return OfficeDocument._generate_ql_preview(path, tmpdir, debug=debug) is not None

    def _render_error_placeholder(self, tmpdir, message):
        """A single-page fallback for when _render_office_pages()
        succeeds at sniff()/_probe_preview() time (qlmanage has a
        generator for this file) but then fails for real later (e.g.
        Chrome crashes or times out on this particular render) -
        rendering happening lazily, on first display rather than
        upfront, means a failure here can't just fall back to skipping
        the file the way main() does for one that never looked
        previewable in the first place. Returns a one-item list of PNG
        paths, the same shape _render_office_pages() itself returns on
        success, so callers don't need to special-case this."""
        from PIL import ImageDraw

        img = Image.new("RGB", (900, 200), "white")
        draw = ImageDraw.Draw(img)
        draw.text((20, 20), f"could not render {os.path.basename(self.path)}", fill="black")
        draw.text((20, 50), message, fill="black")
        out_path = os.path.join(
            tmpdir,
            f"office-error-{hashlib.md5(self.path.encode('utf-8', 'surrogateescape')).hexdigest()[:12]}.png",
        )
        img.save(out_path)
        return [out_path]

    def page_count(self):
        return None

    def build_pages(
        self, tmpdir, debug=False, render_scale=OFFICE_RENDER_SCALE,
        progress=None, continuous=False,
    ):
        """Render fresh - always, regardless of self.pages - remembering
        the result for _source_for_page() and any later ensure_pages()
        call. Used directly by Viewer.reload() (which always wants a
        fresh render, since the file changed on disk); see
        ensure_pages() for the memoized entry point everything else
        wants instead."""
        return self._render_and_remember(
            self.path, tmpdir, debug=debug, render_scale=render_scale,
            progress=progress, continuous=continuous,
        )

    def _render_and_remember(self, source_path, tmpdir, **kwargs):
        pages = self._render_office_pages(source_path, tmpdir, **kwargs)
        return self._remember_pages(pages)

    def _remember_pages(self, pages):
        """Normalize and remember whatever build_pages()'s underlying
        rendering produced - either a ("pdf", pdf_path, npages) tuple
        (FlowingText's own PDF path, or soffice - see
        _try_soffice_pages()) or a plain list of per-page PNG paths -
        into self.pages/self._pdf_delegate, and return the same
        same-length list of paths every caller of build_pages()/
        ensure_pages() (which only ever does len(pages)) already
        expects."""
        if pages:
            if isinstance(pages, tuple) and pages[0] == "pdf":
                # A real PDF (Chrome's --print-to-pdf or soffice) -
                # wrap it as a PdfDocument delegate (see
                # get_page_image()) and normalize back to a
                # same-length list of paths.
                _, pdf_path, npages = pages
                self._pdf_delegate = PdfDocument(pdf_path)
                pages = [pdf_path] * npages
            else:
                self._pdf_delegate = None
            self.pages = pages
        return pages

    def _soffice_pages_if_eligible(self, path, tmpdir, debug, progress, continuous):
        """The one place that decides whether _try_soffice_pages() is
        even worth attempting for `path` - both call sites
        (_render_office_pages(), for Word/PowerPoint, and
        RtfOfficeDocument.build_pages(), for RTF) delegate here instead
        of repeating the same two checks:

        - continuous=True is never eligible: soffice always paginates
          for real (one PDF page per real page/slide), and unlike the
          qlmanage/Chrome screenshot path, there's no way to collapse
          that back into a single continuously-scrollable page.
        - the extension must be one of _SOFFICE_EXTENSIONS - see its
          comment for why Excel is deliberately excluded.

        Returns the ("pdf", pdf_path, npages) tuple _try_soffice_pages()
        produces, or None - either because it wasn't eligible to try at
        all, or because the attempt itself failed - so callers always
        fall through to their own qlmanage/Chrome-based rendering."""
        if continuous or not path.lower().endswith(self._SOFFICE_EXTENSIONS):
            return None
        return self._try_soffice_pages(path, tmpdir, debug, progress)

    def _try_soffice_pages(self, path, tmpdir, debug, progress):
        """Render `path` to a real PDF via LibreOffice's `soffice
        --convert-to pdf` (see _convert_via_soffice() for why
        --headless is never used) - the mechanism _soffice_pages_if_eligible()
        decides whether to even attempt. Preferred over the qlmanage/
        Chrome pipeline when available - soffice paginates natively
        (real page breaks/slide boundaries matching the original
        document) and needs no embedded-picture workaround (see
        _rasterize_broken_img_sources()) at all.

        Returns the same ("pdf", pdf_path, npages) tuple shape
        FlowingText._build_pdf_pages() already produces, or None if
        soffice isn't installed or the conversion/page-count reading
        failed for any reason - callers always fall back to the
        existing qlmanage/Chrome pipeline in that case."""
        name = os.path.basename(path)
        progress.update(f"{name}: looking for LibreOffice...")
        soffice = find_soffice()
        if soffice is None:
            return None
        if debug:
            print(f"pdfless: [debug] {name}: using soffice: {soffice}", file=sys.stderr, end="\r\n")
        label = f"{name}: converting via LibreOffice"
        with _DebugTimer(debug, label), progress.spin(label + "..."):
            out_pdf = _convert_via_soffice(soffice, path, tmpdir)
        if out_pdf is None:
            return None
        npages = _pdf_page_count_safe(out_pdf)
        if not npages:
            os.unlink(out_pdf)
            return None
        return ("pdf", out_pdf, npages)

    def _measure_slide_offsets(self, chrome, html_path, page_element_xpath, width):
        """For a document whose Quick Look preview has distinct page/slide
        elements (see _generate_ql_preview()'s page_element_xpath - Word's
        continuously-flowing text has none, so this is never called for
        that), ask Chrome for the exact pixel boundary between each one, via
        a small script injected into a scratch copy of the HTML and read
        back with `--dump-dom` - real computed layout (offsetTop) rather
        than a guess. This matters because they can butt right up against
        each other with no clean gap to detect in a screenshot (e.g. a
        PowerPoint slide's drop shadow bleeding into the margin before the
        next one), so slicing by the plist's Height (one page/slide's own
        height, not counting that margin) drifts out of alignment with the
        actual boundaries after enough of them.

        Returns (total_height, [offset, ...]) in logical (unscaled) CSS
        pixels - one offset per page/slide, in document order - or None if
        page_element_xpath matched nothing, or Chrome/parsing failed.

        Note this still can't guarantee a slide's content never bleeds onto
        the next one: PowerPoint/Keynote auto-shrink text at display time so
        it fits its placeholder, but this static HTML preview doesn't
        reproduce that, so a slide relying on it can render past its box's
        bottom edge despite the box's own overflow:hidden - that's a
        limitation of the generator's HTML output itself (also visible in
        Quick Look proper), not something fixable from here.

        `width` must match the logical width the real screenshot is later
        taken at (_render_office_pages()'s own `width`): layout - and so each
        element's offsetTop - can depend on the viewport's width (e.g. a
        slide whose content is one `<img width="100%">`, scaling with the
        container), so measuring at any other width (Chrome's own headless
        default, if not given explicitly) can silently disagree with the
        boundaries the real capture ends up with, throwing off every slice
        from that point on."""
        try:
            with open(html_path, "r", encoding="utf-8", errors="replace") as f:
                content = f.read()
        except OSError:
            return None

        if not page_element_xpath:
            page_element_xpath = _detect_fallback_page_xpath(content)
            if not page_element_xpath:
                return None

        idx = content.rfind("</body>")
        script = _build_slide_measure_script(page_element_xpath)
        instrumented = content[:idx] + script + content[idx:] if idx != -1 else content + script
        measure_path = os.path.join(os.path.dirname(html_path), "pdfless-slide-measure.html")
        with open(measure_path, "w", encoding="utf-8") as f:
            f.write(instrumented)
        try:
            r = subprocess.run(
                [
                    chrome, "--headless", "--no-sandbox",
                    # Must match the real capture's width (see the
                    # docstring): a tall, arbitrary height is fine since
                    # dump-dom doesn't render/screenshot anything, just
                    # loads and serializes the DOM at that viewport size.
                    f"--window-size={width},1080",
                    # 8s, not 2s: an upper bound on how long the injected
                    # script (see _build_slide_measure_script()) is allowed
                    # to wait for every <img> to finish decoding before
                    # giving up and dumping whatever it's got - it resolves
                    # as soon as they're all ready, so this only matters as
                    # a cap for a deck with many/large embedded images.
                    "--dump-dom", "--virtual-time-budget=8000",
                    f"file://{os.path.abspath(measure_path)}",
                ],
                capture_output=True, text=True, timeout=30, check=True,
            )
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired, OSError):
            return None
        finally:
            os.unlink(measure_path)

        m = re.search(r"<title>(.*?)</title>", r.stdout, re.S)
        if not m:
            return None
        try:
            data = json.loads(html.unescape(m.group(1)))
            tops = [float(t) for t in data["tops"]]
            if not tops:
                return None
            # Sanity check: a real stack of pages/slides lays out top to
            # bottom, so each offsetTop should be strictly greater than the
            # last. Seen in the wild for one Keynote/iWork.qlgenerator
            # variant: the same shape _detect_fallback_page_xpath() looks
            # for (a <div> wrapping one full-bleed <img> per slide), but
            # with every single one reporting offsetTop 0 and a tiny total
            # scrollHeight - i.e. this generator overlaps them (probably
            # meant to be shown one at a time via some JS this static
            # capture doesn't run), not stacked in document flow at all. If
            # so, slicing by these numbers would compute zero- or negative-
            # height "pages" - return None and let the caller fall back to
            # the plain grow-and-trim path instead of acting on bogus data.
            if any(tops[i + 1] <= tops[i] for i in range(len(tops) - 1)):
                return None
            return float(data["total"]), tops
        except (ValueError, KeyError, TypeError):
            return None

    def _render_office_pages(
        self, path, tmpdir, debug=False, render_scale=OFFICE_RENDER_SCALE,
        progress=None, continuous=False,
    ):
        """Try to render `path` - any file this Mac's Quick Look
        generators can preview (Word, Excel, PowerPoint, Keynote,
        Pages, ...) - into one or more page PNGs, via qlmanage + a
        local Chrome/Chromium. `path` isn't necessarily self.path -
        RtfOfficeDocument renders a converted .docx instead (see its
        build_pages()). Returns a list of PNG file paths (one per page,
        in reading order), or None if qlmanage has no generator for
        this file or no Chrome is installed. With debug=True
        (-d/--debug), prints each stage's wall-clock time (and which
        browser got used) to stderr, plus a total at the end.
        `render_scale` is the device-pixel-ratio to rasterize at
        (--rendering-scale) - higher is sharper when zoomed in but
        slower for a large document; left at its default
        (OFFICE_RENDER_SCALE), continuously-flowing text (Word and the
        like) renders at FlowingText.OFFICE_RENDER_SCALE_FLOWING instead, favoring
        sharpness since these documents are usually short. `progress`,
        if given, is a _ProgressLine to post a one-line "what's
        happening right now" status to, since this whole method can
        take anywhere from under a second to tens of seconds and would
        otherwise look like pdfless had simply hung.

        Pagination for a screenshot-sliced variant (splitting into
        distinct page/slide images, so `n`/`p`/`g`/`G` and jumping
        straight to page N work) is only used when the slide
        boundaries are known with confidence - i.e. the Quick Look
        generator's own plist named a PageElementXPath (currently true
        for PowerPoint and some Keynote decks), and measuring it
        produced sane (strictly increasing) offsets. Anything else -
        spreadsheets, and Keynote/Pages variants where the boundary can
        only be guessed via a content-shape heuristic (see
        _detect_fallback_page_xpath()) - is rendered as a single,
        continuously-scrollable "page" instead (the same as a plain
        image file), since a guessed boundary has been observed to
        drift/overflow on some real decks. FlowingText is the one
        exception to all of this: its own PDF path
        (_build_pdf_pages()) paginates for real when not continuous,
        driven by Chrome's print engine rather than any measured/
        guessed boundary - though RtfOfficeDocument's own qlmanage/
        Chrome fallback always asks for continuous=True regardless
        (see its build_pages()), since a converted RTF's page-height
        metadata doesn't correspond to anything in the original file
        either way. Word and PowerPoint (see _SOFFICE_EXTENSIONS) try
        LibreOffice's soffice before any of this (see
        _soffice_pages_if_eligible(), called at the very top of this
        method) when it's installed, since it paginates natively and
        renders with higher fidelity than either of the above; RTF
        does the same, but from its own build_pages(), against the
        original .rtf rather than a converted .docx - so it isn't
        limited to always-continuous the way the qlmanage/Chrome
        fallback is.

        continuous=True (-c/--continuous) forces the single-continuous-
        page behavior even for a document that would otherwise paginate
        confidently."""
        if progress is None:
            progress = _ProgressLine(enabled=False)
        name = os.path.basename(path)
        t_start = time.monotonic()
        try:
            soffice_pages = self._soffice_pages_if_eligible(path, tmpdir, debug, progress, continuous)
            if soffice_pages is not None:
                return soffice_pages

            progress.update(f"{name}: looking for a local Chrome...")
            chrome = find_chrome()
            if chrome is None:
                return None
            if debug:
                print(f"pdfless: [debug] {name}: using browser: {chrome}", file=sys.stderr, end="\r\n")

            progress.update(f"{name}: reading Quick Look preview...")
            with _DebugTimer(debug, f"{name}: qlmanage preview"):
                preview = self._generate_ql_preview(path, tmpdir, debug=debug)
            if preview is None:
                return None
            html_path, width, height, should_not_scale, page_element_xpath = preview
            width = width or self.OFFICE_DEFAULT_WIDTH
            height = height or self.OFFICE_DEFAULT_HEIGHT

            # A short, stable-per-path tag so this file's capture/page
            # PNGs don't collide with another file's (or its own
            # previous ones, e.g. across a -F/--follow reload) - unlike
            # id(path), collision odds are negligible even if a path
            # string gets reused after being freed.
            tag = hashlib.md5(path.encode("utf-8", "surrogateescape")).hexdigest()[:12]

            # Pick which OfficeVariant strategy applies - see their own
            # docstrings for what distinguishes each. should_not_scale
            # (a plist flag) is Excel's tell and is cheap to check up
            # front; the rest can only be told apart by actually
            # attempting to measure the slide/page layout.
            if should_not_scale:
                # A spreadsheet with more than one sheet:
                # Office.qlgenerator renders every sheet up front as its
                # own AttachmentN.html, with Preview.html itself being
                # just a JS tab strip that swaps an <iframe> between
                # them - ExcelWorkbook._parse_sheet_tabs() reads that
                # strip back out; empty for a single-sheet workbook,
                # where Preview.html *is* the sheet.
                variant = ExcelWorkbook(chrome, html_path, width, height, tag, name)
            else:
                progress.update(f"{name}: converting embedded images...")
                on_img_progress = lambda done, total: progress.update(
                    f"{name}: converting embedded images ({done}/{total})..."
                )
                with _DebugTimer(debug, f"{name}: converting embedded images"):
                    html_path = _rasterize_broken_img_sources(html_path, tmpdir, on_progress=on_img_progress)

                # Confident means the Quick Look generator itself named
                # the page/slide element (page_element_xpath came from
                # the plist, not guessed by _detect_fallback_page_xpath
                # inside _measure_slide_offsets) - only then is
                # pagination trusted; see SlideDeck's docstring for why
                # a guessed boundary defaults to continuous instead.
                confident = bool(page_element_xpath)
                slide_offsets = None
                if not continuous:
                    # _measure_slide_offsets() still tries a
                    # content-shape-based fallback before giving up even
                    # when page_element_xpath is None, purely so
                    # FlowingText's "attempt 1/2/3..." growth loop can be
                    # skipped when it happens to work out - but a result
                    # obtained that way isn't "confident" (see above)
                    # and won't be used to paginate. Skipped entirely in
                    # continuous mode - nothing needs a per-page/slide
                    # boundary if there's only ever going to be one
                    # "page".
                    progress.update(f"{name}: measuring page/slide layout...")
                    with _DebugTimer(debug, f"{name}: measure slide/page offsets"):
                        slide_offsets = self._measure_slide_offsets(chrome, html_path, page_element_xpath, width)

                if slide_offsets is not None:
                    variant = SlideDeck(chrome, html_path, width, height, tag, name, slide_offsets, confident)
                else:
                    variant = FlowingText(chrome, html_path, width, height, tag, name)

            page_paths = variant.build_pages(tmpdir, debug, render_scale, progress, continuous)
            if page_paths is None:
                return None
            if debug:
                print(
                    f"pdfless: [debug] {name}: total: {time.monotonic() - t_start:.2f}s",
                    file=sys.stderr, end="\r\n",
                )
            return page_paths
        finally:
            progress.clear()

    def ensure_pages(self, tmpdir, **kwargs):
        """Render once and reuse afterward - a no-op on every call after
        the first (see Viewer._ensure_office_pages(), which only needs
        this once per file no matter how many times it's revisited)."""
        if self.pages is None:
            self.build_pages(tmpdir, **kwargs)
        return self.pages

    def extract_text(self, page):
        if self._pdf_delegate is not None:
            # A real PDF page (soffice or Chrome's --print-to-pdf) -
            # use its own per-page text (pdftotext -layout), so page
            # breaks - lost once extract_office_text()'s textutil
            # flattens the whole document into one blob - come through
            # correctly (see also text_mode_is_paginated()).
            return self._pdf_delegate.extract_text(page)
        # textutil (see extract_office_text()) has no notion of pages -
        # the whole document, or None for a format it can't handle at
        # all (a spreadsheet or slide deck).
        return extract_office_text(self.path)

    def supports_text_mode(self):
        return True

    def supports_search(self):
        # Real per-page/bbox search (build_search_index()/
        # find_search_matches() below) only works against a real PDF -
        # a screenshot-based OfficeVariant (always true for Excel/
        # Keynote/Pages/Numbers; for Word/RTF/PowerPoint, only when
        # neither soffice nor Chrome's --print-to-pdf could be used)
        # has no such index to search.
        return self._pdf_delegate is not None

    def text_mode_is_paginated(self):
        return self._pdf_delegate is not None

    def build_search_index(self):
        if self._pdf_delegate is not None:
            return self._pdf_delegate.build_search_index()
        return None

    def find_search_matches(self, index, query):
        if self._pdf_delegate is not None:
            return self._pdf_delegate.find_search_matches(index, query)
        return []

    def _source_for_page(self, cache, page):
        # One pre-rendered PNG per page (see OfficeDocument._render_office_pages()) -
        # unlike ImageDocument, there's no single fixed path, so this
        # reads self.pages (kept in sync by build_pages()/
        # ensure_pages()) rather than a path fixed at construction time.
        # Only reached when self._pdf_delegate is None - get_page_image()
        # (below) forwards to it directly otherwise, without ever
        # calling this (self.pages holds a same-length placeholder list
        # in that case, not real per-page paths - see
        # _render_and_remember()).
        return self.pages[page - 1]

    def get_page_image(self, cache, page, target_px, fit):
        # A FlowingText document rendered to a real PDF instead of PNGs
        # (see _render_and_remember()) - re-rasterize it the same way a
        # real PdfDocument would, at whatever DPI the current zoom
        # needs, instead of resizing one fixed-resolution screenshot
        # (the DocumentHandler default this falls back to otherwise).
        if self._pdf_delegate is not None:
            return self._pdf_delegate.get_page_image(cache, page, target_px, fit)
        return super().get_page_image(cache, page, target_px, fit)


class RtfOfficeDocument(OfficeDocument):
    """An RTF file, rendered as an image. Preferably via soffice
    reading the original .rtf natively (see build_pages()'s
    _soffice_pages_if_eligible() call against self.path, not a
    converted .docx) - the only path available on Linux, where
    textutil doesn't exist. Falls back to converting it to .docx via
    macOS's own textutil (_rtf_to_docx()) when soffice isn't
    installed, since RTF's own Quick Look preview is just a redirect
    back to the original file (a Preview.url), not an HTML bundle
    qlmanage/Chrome could render directly (see
    RtfDocument.is_rtf_file()). Once converted, it's handled through
    the exact same OfficeDocument._render_office_pages() pipeline as
    any other Word document (most often as a FlowingText
    OfficeVariant).

    Tried before the plain-text-only RtfDocument fallback (see
    HANDLER_CLASSES) - falls through to it if neither soffice nor
    textutil is available, or qlmanage can't preview the converted
    .docx for some reason."""

    @staticmethod
    def _rtf_to_docx(path, tmpdir):
        """Convert an RTF file to .docx via macOS's own `textutil`, so
        it can be handled through the same Office/Quick Look + Chrome
        pipeline as a native Word document (formatting - bold/italic/
        color/fonts, verified by hand - survives the round trip
        reasonably well; a table degrades to plain concatenated text, a
        known limitation left as-is). `path` isn't necessarily
        self.path (sniff() converts before an instance even exists), so
        this is a staticmethod.

        Returns the converted file's path, or None if textutil isn't
        available or the conversion failed. Always reconverts (rather
        than reusing a previous run's output) so a changed source file
        (e.g. -F/--follow) can't leave a stale docx behind."""
        if shutil.which("textutil") is None:
            return None
        tag = hashlib.md5(path.encode("utf-8", "surrogateescape")).hexdigest()[:12]
        out_path = os.path.join(tmpdir, f"rtf-as-docx-{tag}.docx")
        try:
            subprocess.run(
                ["textutil", "-convert", "docx", "-output", out_path, path],
                capture_output=True, check=True, timeout=20,
            )
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired, OSError):
            return None
        return out_path if os.path.isfile(out_path) else None

    @classmethod
    def sniff(cls, path, tmpdir, debug=False):
        if not RtfDocument.is_rtf_file(path):
            return None
        if find_soffice() is not None:
            # build_pages() will try soffice against the original
            # .rtf first anyway (see _soffice_pages_if_eligible()) -
            # no need to pay for a textutil conversion just to probe
            # that here, and textutil doesn't even exist on Linux.
            return cls(path)
        docx_path = cls._rtf_to_docx(path, tmpdir)
        if docx_path is None:
            return None
        if not cls._probe_preview(docx_path, tmpdir, debug=debug):
            return None
        return cls(path)

    def build_pages(
        self, tmpdir, debug=False, render_scale=OFFICE_RENDER_SCALE,
        progress=None, continuous=False,
    ):
        if progress is None:
            progress = _ProgressLine(enabled=False)
        # Unlike the textutil-converted-docx path below, soffice reads
        # the original .rtf natively, so its page breaks correspond to
        # the real document - no need to force continuous=True just to
        # dodge untrustworthy converted-page-height metadata (see the
        # comment below).
        soffice_pages = self._soffice_pages_if_eligible(self.path, tmpdir, debug, progress, continuous)
        if soffice_pages is not None:
            return self._remember_pages(soffice_pages)

        docx_path = self._rtf_to_docx(self.path, tmpdir)
        if docx_path is None:
            return None
        # Always continuous, regardless of the caller's -c/--continuous
        # setting - a converted RTF's page-height pagination (the plist
        # Width/Height textutil's own docx conversion reports) doesn't
        # correspond to anything in the original RTF, so it's not worth
        # trusting as a page boundary the way a native Word document's
        # is.
        return self._render_and_remember(
            docx_path, tmpdir, debug=debug, render_scale=render_scale,
            progress=progress, continuous=True,
        )

    def extract_text(self, page):
        if self._pdf_delegate is not None:
            # soffice rendered the original .rtf natively to a real
            # PDF (see build_pages()) - use its own per-page text, the
            # same as OfficeDocument.extract_text() does for Word.
            return self._pdf_delegate.extract_text(page)
        # textutil already handles RTF directly for plain-text
        # extraction (see extract_office_text()) - no need to go via
        # the .docx conversion just for this.
        return extract_office_text(self.path)


class SofficeOnlyDocument(OfficeDocument):
    """Formats macOS Quick Look has no generator for at all - an ODF
    document, a Visio drawing, or a WMF vector metafile (confirmed by
    hand: qlmanage crashes outright on a real .odt, and produces no
    preview whatsoever - not even a Preview.url - for a real .ods/
    .odp/.odg/.vsd). Previewable only when soffice is installed, with
    no qlmanage/Chrome fallback to speak of - unlike Word/RTF/
    PowerPoint (see OfficeDocument._SOFFICE_EXTENSIONS), there's
    nothing to fall back TO here; these formats were entirely
    unsupported before this class existed, so requiring soffice isn't
    a regression for anyone.

    sniff() deliberately never touches qlmanage (unlike
    OfficeDocument._probe_preview()) - both because it's known not to
    work for any of these extensions, and because it would risk
    reproducing the .odt crash above just to classify a file.

    -c/--continuous has no effect here: soffice always paginates for
    real, and - unlike OfficeDocument._render_office_pages()'s
    qlmanage-based variants - there's no screenshot-based single-page
    rendering to fall back to instead.

    .ods (Calc) carries the same print-area/page-setup pagination
    caveat as Excel (see _SOFFICE_EXTENSIONS's docstring - confirmed
    by hand: a real 4-sheet workbook came out as 8 soffice pages, with
    a chart split across two of them) - but unlike Excel, there's no
    working qlmanage fallback to prefer instead, so it's included here
    anyway rather than left entirely unsupported.

    .vsdx hasn't been verified by hand (no local sample was
    available) - LibreOffice's Visio import filter (libvisio) handles
    both .vsd and .vsdx through the same code, so the same behavior is
    expected, but only .vsd has actually been confirmed to render
    correctly."""

    _SOFFICE_ONLY_EXTENSIONS = (".odt", ".odp", ".odg", ".ods", ".vsd", ".vsdx", ".wmf")

    @classmethod
    def sniff(cls, path, tmpdir, debug=False):
        if not path.lower().endswith(cls._SOFFICE_ONLY_EXTENSIONS):
            return None
        if find_soffice() is None:
            return None
        return cls(path)

    def build_pages(
        self, tmpdir, debug=False, render_scale=OFFICE_RENDER_SCALE,
        progress=None, continuous=False,
    ):
        if progress is None:
            progress = _ProgressLine(enabled=False)
        soffice_pages = self._try_soffice_pages(self.path, tmpdir, debug, progress)
        if soffice_pages is None:
            return None
        return self._remember_pages(soffice_pages)


class SvgDocument(OfficeDocument):
    """A standalone SVG file, rendered to a real PDF via headless
    Chrome directly - no Quick Look or LibreOffice involved at all.
    Quick Look's own preview for an SVG is just a Preview.url redirect
    back to the file (confirmed by hand - the same dead end WMF hits;
    see SofficeOnlyDocument), not a proper HTML bundle to build on, so
    there's nothing to reuse from the qlmanage/Chrome pipeline here.
    Chrome was chosen over soffice's Draw import (both were compared
    by hand on a complex real SVG - embedded raster photos plus vector
    line art - and came out visually equivalent) since Chrome is
    already a hard requirement for every other Office kind, so this
    doesn't add a new soffice dependency just to view an SVG.

    The SVG is embedded via a plain <img>, which is what lets
    _capture_html_pdf()'s existing @page-injection machinery work
    unmodified (an SVG file has no <head>/<body> of its own for that
    to target safely) - confirmed by hand that the vector parts of a
    complex SVG survive print-to-pdf as real vector PDF content, not
    a flattened bitmap (checked via pdfimages -list: only the source
    SVG's own embedded raster images showed up there, nothing for the
    vector line art). The one real cost of this approach: <img> always
    strips interactivity, so a hyperlink inside the SVG itself can't
    be clickable here the way one in a Word document is."""

    @classmethod
    def sniff(cls, path, tmpdir, debug=False):
        if not path.lower().endswith(".svg"):
            return None
        if find_chrome() is None:
            return None
        return cls(path)

    def build_pages(
        self, tmpdir, debug=False, render_scale=OFFICE_RENDER_SCALE,
        progress=None, continuous=False,
    ):
        if progress is None:
            progress = _ProgressLine(enabled=False)
        name = os.path.basename(self.path)
        chrome = find_chrome()
        if chrome is None:
            return None
        if debug:
            print(f"pdfless: [debug] {name}: using browser: {chrome}", file=sys.stderr, end="\r\n")
        tag = hashlib.md5(self.path.encode("utf-8", "surrogateescape")).hexdigest()[:12]
        wrapper_path = os.path.join(tmpdir, f"svg-wrap-{tag}.html")

        # There's no plist (unlike a Quick Look preview) to read a
        # width from up front, and an SVG's own intrinsic size varies
        # in both dimensions - so the natural size has to be measured
        # first, the same "auto" page sizing isn't supported reasoning
        # as _measure_content_height() (see _measure_svg_natural_size()).
        progress.update(f"{name}: measuring size...")
        self._write_svg_wrapper(wrapper_path, self.path, None, None)
        with _DebugTimer(debug, f"{name}: measure SVG size"):
            size = _measure_svg_natural_size(chrome, wrapper_path)
        width, height = size if size else (self.OFFICE_DEFAULT_WIDTH, self.OFFICE_DEFAULT_HEIGHT)
        self._write_svg_wrapper(wrapper_path, self.path, width, height)

        out_pdf = os.path.join(tmpdir, f"svg-capture-{tag}.pdf")
        label = f"{name}: rendering to PDF"
        with _DebugTimer(debug, label), progress.spin(label + "..."):
            ok = _capture_html_pdf(chrome, wrapper_path, width, height, out_pdf)
        npages = _pdf_page_count_safe(out_pdf) if ok else None
        if not npages:
            if os.path.exists(out_pdf):
                os.unlink(out_pdf)
            return None
        return self._remember_pages(("pdf", out_pdf, npages))

    @staticmethod
    def _write_svg_wrapper(wrapper_path, svg_path, width, height):
        """A minimal HTML page embedding `svg_path` as a plain <img> -
        see this class's docstring for why <img> rather than
        navigating to the SVG directly. `width`/`height` (CSS px), if
        given, are set explicitly so the rendered page size matches
        exactly what _capture_html_pdf()'s own @page injection expects
        - left unset (None) for the first, size-finding pass (see
        build_pages()), which needs the image at its own natural size
        instead."""
        style = f"width:{width}px;height:{height}px;" if width and height else ""
        html = (
            "<!DOCTYPE html><html><head></head><body style=\"margin:0\">"
            f'<img id="svg" style="display:block;{style}" '
            f'src="file://{os.path.abspath(svg_path)}"></body></html>'
        )
        with open(wrapper_path, "w", encoding="utf-8") as f:
            f.write(html)


class MarkdownDocument(OfficeDocument):
    """A Markdown file, rendered to a real PDF via the `markdown` +
    `weasyprint` Python libraries (see _render_markdown_pdf() below) - no
    Quick Look, Chrome, or LibreOffice involved at all, and
    dramatically faster than either (confirmed by hand: well under a
    second, against Chrome's own ~1-2s process startup alone), since
    WeasyPrint paginates for real on its own rather than needing a
    measured/injected @page size the way FlowingText/SvgDocument do.

    Falls back to plain text (TextDocument, showing the raw Markdown
    source) if `markdown`/`weasyprint` - or the system libraries
    WeasyPrint itself needs (Cairo/Pango/GLib, not something pip can
    install on its own) - aren't available; see sniff().

    Text mode (`t`) always shows the raw Markdown source from disk -
    not text extracted from the rendered PDF - so you can read or
    search the `#`/`*` markup while keeping the WeasyPrint preview in
    image mode. text_mode_is_paginated() is False because that source
    is one continuous blob in text mode; image-mode / search still
    uses the PDF delegate's own per-page bbox index (see
    Viewer._search_uses_text_lines()).

    -c/--continuous has no effect here, the same as SofficeOnlyDocument
    and for the same reason: WeasyPrint's real pagination can't be
    collapsed back into a single page."""

    _MARKDOWN_EXTENSIONS = (".md", ".markdown")

    # Minimal styling for the rendered pages - just enough that
    # headings/code/quotes are visually distinct, deliberately not
    # trying to imitate any particular Markdown renderer's house style.
    # No @font-face/font-family override: left to whatever WeasyPrint
    # picks as the system default, so CJK text (which needs a real CJK
    # font) renders using whatever's actually installed rather than a
    # Latin-only font silently dropping every Japanese glyph.
    MARKDOWN_CSS = """
body { line-height: 1.5; padding: 2em; }
h1, h2, h3, h4, h5, h6 { line-height: 1.2; margin-top: 1em; }
pre, code { font-family: monospace; background: #f0f0f0; }
pre { padding: 0.6em; white-space: pre-wrap; }
code { padding: 0.1em 0.3em; }
pre code { padding: 0; background: none; }
blockquote { border-left: 4px solid #ccc; margin-left: 0; padding-left: 1em; color: #555; }
table { border-collapse: collapse; max-width: 100%; }
th, td { border: 1px solid #ccc; padding: 0.3em 0.6em; }
img { max-width: 100%; height: auto; }
"""

    @staticmethod
    def _ensure_homebrew_lib_path_for_weasyprint():
        """WeasyPrint (via cffi) dlopen()s Cairo/Pango/GLib by their bare
        library names, relying on the dynamic linker's own default search
        to find them. Confirmed by hand: that default search does NOT
        include Homebrew's own lib directory when running under a
        uv-managed standalone Python build (e.g. a free-threaded 3.14
        install) - even with those exact libraries installed via Homebrew
        - while the same import succeeds unmodified under a
        Homebrew-installed Python on the same machine. Rather than
        requiring every user hitting this to discover and set
        DYLD_LIBRARY_PATH by hand (WeasyPrint's own macOS troubleshooting
        docs suggest exactly that), add Homebrew's lib directory to
        DYLD_FALLBACK_LIBRARY_PATH before the first import attempt -
        confirmed by hand this alone is enough to fix the failing case.
        A *fallback* path (rather than DYLD_LIBRARY_PATH, which is
        consulted first) can't ever shadow a library some other search
        step already finds correctly, so this is safe to always do.
        macOS-only; a no-op everywhere else."""
        if sys.platform != "darwin":
            return
        existing = os.environ.get("DYLD_FALLBACK_LIBRARY_PATH", "")
        parts = existing.split(":") if existing else []
        for lib_dir in ("/opt/homebrew/lib", "/usr/local/lib"):
            if os.path.isdir(lib_dir) and lib_dir not in parts:
                parts.append(lib_dir)
        if parts:
            os.environ["DYLD_FALLBACK_LIBRARY_PATH"] = ":".join(parts)

    @staticmethod
    def _markdown_rendering_available():
        """Whether MarkdownDocument can even attempt to render at all -
        both the `markdown` and `weasyprint` libraries import cleanly.
        Cheap to call more than once: a successful import is cached by
        Python itself (sys.modules), so only the first call actually pays
        for it. See _render_markdown_pdf() for why this has to be a
        runtime check rather than something assumed from the PEP723
        dependency list.

        Deliberately catches more than just ImportError: weasyprint's own
        import chain reaches into cffi to dlopen() the actual Cairo/Pango/
        GLib shared libraries, and a missing one there raises a plain
        OSError, not an ImportError (confirmed by hand: "cannot load
        library 'libgobject-2.0-0'" on a machine without those system
        libraries installed) - anything going wrong at import time means
        the same thing here (rendering isn't available), so it's all
        caught the same way rather than letting a fairly common
        installation gap crash the whole program on startup.

        Also deliberately swallows whatever weasyprint prints along the
        way: on that same missing-libraries path, it print()s its own
        multi-line "could not import some external libraries" notice
        before the OSError above even reaches here (confirmed by hand).
        Since this whole function's job is to fail silently and let the
        caller fall back to plain text, letting that notice through would
        defeat the point - and pdfless spends most of its life with the
        terminal in raw mode showing an alternate screen, where a stray
        print from a library is a corrupted-looking screen, not just
        unwanted noise."""
        MarkdownDocument._ensure_homebrew_lib_path_for_weasyprint()
        try:
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                import markdown  # noqa: F401
                import weasyprint  # noqa: F401
        except Exception:
            return False
        return True

    def _render_markdown_pdf(self, out_pdf):
        """Convert self.path (a Markdown file) to a real PDF via the
        `markdown` (Markdown -> HTML) and `weasyprint` (HTML+CSS -> PDF)
        libraries - no headless Chrome or LibreOffice involved at all, and
        dramatically faster than either (confirmed by hand: a whole
        conversion takes well under a second, against Chrome's own ~1-2s
        process startup alone), since WeasyPrint has a real CSS
        pagination engine of its own - no need for FlowingText/
        SvgDocument's own "measure the content first, then set an exact
        @page size" dance; a long document just comes out as however many
        pages it naturally takes.

        Both libraries are declared PEP723 dependencies (so `uv run`
        always installs the pip packages), but weasyprint also needs
        system-level Cairo/Pango/GLib libraries pip can't install by
        itself - so the import happens lazily, here (via
        _markdown_rendering_available()), rather than at module load time,
        and any failure is treated the same as "not installed": returns
        False, and the caller falls back to plain-text rendering, the
        same graceful degradation soffice/Chrome already get when they're
        missing.

        Returns False on any failure (including a missing library) - never
        raises, so this is always safe for a caller to attempt speculatively."""
        if not self._markdown_rendering_available():
            return False
        import markdown
        from weasyprint import HTML

        try:
            with open(self.path, "r", encoding="utf-8", errors="replace") as f:
                source = f.read()
        except OSError:
            return False
        body = markdown.markdown(source, extensions=["extra", "sane_lists"])
        html = f'<!DOCTYPE html><html><head><meta charset="utf-8"><style>{self.MARKDOWN_CSS}</style></head><body>{body}</body></html>'
        # base_url lets a relative-path image reference in the source
        # (e.g. "![alt](./diagram.png)") resolve against the Markdown
        # file's own directory, the same as a browser would for a page
        # loaded from there.
        base_url = os.path.dirname(os.path.abspath(self.path)) + "/"
        try:
            HTML(string=html, base_url=base_url).write_pdf(out_pdf)
        except Exception:
            # WeasyPrint can raise a variety of its own exception types for
            # a malformed document/CSS - none of them worth the whole
            # program aborting over; the caller's error-placeholder
            # fallback handles it the same as any other rendering failure.
            return False
        return os.path.exists(out_pdf)

    @classmethod
    def sniff(cls, path, tmpdir, debug=False):
        if not path.lower().endswith(cls._MARKDOWN_EXTENSIONS):
            return None
        if not cls._markdown_rendering_available():
            return None
        return cls(path)

    def build_pages(
        self, tmpdir, debug=False, render_scale=OFFICE_RENDER_SCALE,
        progress=None, continuous=False,
    ):
        if progress is None:
            progress = _ProgressLine(enabled=False)
        name = os.path.basename(self.path)
        tag = hashlib.md5(self.path.encode("utf-8", "surrogateescape")).hexdigest()[:12]
        out_pdf = os.path.join(tmpdir, f"markdown-capture-{tag}.pdf")
        label = f"{name}: rendering to PDF"
        with _DebugTimer(debug, label), progress.spin(label + "..."):
            ok = self._render_markdown_pdf(out_pdf)
        npages = _pdf_page_count_safe(out_pdf) if ok else None
        if not npages:
            if os.path.exists(out_pdf):
                os.unlink(out_pdf)
            return None
        return self._remember_pages(("pdf", out_pdf, npages))

    def extract_text(self, page):
        return read_plain_text_lines(self.path)

    def text_mode_is_paginated(self):
        return False

    def default_text_border(self, border_default):
        return False

    def default_text_wrap(self, wrap_default):
        return wrap_default

    def search_resets_on_text_mode_toggle(self):
        return True


# The order main()'s classification loop tries these in - RtfOfficeDocument
# and RtfDocument (both RTF - the former tried first, see their own
# docstrings), SvgDocument, and MarkdownDocument before the generic
# TextDocument, since all would otherwise match the same file (RTF,
# SVG, and Markdown are all plain text - SvgDocument/MarkdownDocument
# fall through to TextDocument's raw-source rendering when their own
# dependency isn't installed, the same way RtfOfficeDocument falls
# through to RtfDocument without textutil); SofficeOnlyDocument before
# OfficeDocument since it covers formats OfficeDocument's own qlmanage
# probe can't handle at all; OfficeDocument last since it's the most
# expensive check (shells out to qlmanage).
HANDLER_CLASSES = [
    PdfDocument, ImageDocument, RtfOfficeDocument, RtfDocument, SvgDocument,
    MarkdownDocument, TextDocument, SofficeOnlyDocument, OfficeDocument,
]


class RawTerminal:
    """Puts the tty into raw (cbreak-ish) mode for the duration of the block."""

    def __init__(self, fd):
        self.fd = fd
        self.old = None

    def __enter__(self):
        self.old = termios.tcgetattr(self.fd)
        tty.setraw(self.fd)
        return self

    def __exit__(self, *exc):
        termios.tcsetattr(self.fd, termios.TCSADRAIN, self.old)


def read_utf8_char(fd, timeout=0.1):
    """Read one full UTF-8 character (1-4 bytes) from fd, returning it
    decoded as a str, or None on EOF. A single-byte os.read() at a time
    would mangle multi-byte characters (e.g. Japanese search queries),
    since each individual byte of a multi-byte sequence is not valid
    ASCII/UTF-8 on its own."""
    first = os.read(fd, 1)
    if not first:
        return None
    lead = first[0]
    if lead & 0x80 == 0:
        length = 1
    elif lead & 0xE0 == 0xC0:
        length = 2
    elif lead & 0xF0 == 0xE0:
        length = 3
    elif lead & 0xF8 == 0xF0:
        length = 4
    else:
        length = 1  # a stray continuation byte; decode it on its own below

    buf = first
    while len(buf) < length:
        r, _, _ = select.select([fd], [], [], timeout)
        if not r:
            break
        more = os.read(fd, 1)
        if not more:
            break
        buf += more
    return buf.decode("utf-8", errors="replace")


CSI_FINAL_LETTERS = {"A": "UP", "B": "DOWN", "C": "RIGHT", "D": "LEFT", "H": "HOME", "F": "END"}
CSI_TILDE_CODES = {
    "1": "HOME", "7": "HOME",
    "4": "END", "8": "END",
    "5": "PAGEUP",
    "6": "PAGEDOWN",
    "11": "F1",  # terminals that send F1 as a CSI; see SS3_FINAL_LETTERS
    # for the ESC O P form most of them use instead
}
SS3_FINAL_LETTERS = {"P": "F1"}


def read_csi_sequence(fd, timeout=0.15):
    """Read the rest of a CSI sequence (after ESC [) up to and including its
    final byte (0x40-0x7E). Returns the sequence as a string, or None on
    timeout/EOF."""
    buf = b""
    deadline = time.monotonic() + timeout
    while True:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            return None
        r, _, _ = select.select([fd], [], [], remaining)
        if not r:
            return None
        b = os.read(fd, 1)
        if not b:
            return None
        buf += b
        if 0x40 <= b[0] <= 0x7E:
            return buf.decode("ascii", errors="ignore")


def read_ss3_key(fd, timeout=0.15):
    """Read the single byte following ESC O (SS3) and turn it into a
    symbolic key name - F1 is the only one pdfless has any use for, and
    most terminals send it as ESC O P. Returns None on timeout/EOF, or
    for anything not in SS3_FINAL_LETTERS (the other function keys, and
    the arrows as a terminal in application-cursor mode sends them -
    pdfless never turns that mode on, so its arrows arrive as CSI)."""
    r, _, _ = select.select([fd], [], [], timeout)
    if not r:
        return None
    b = os.read(fd, 1)
    if not b:
        return None
    return SS3_FINAL_LETTERS.get(b.decode("ascii", errors="ignore"))


def decode_csi_key(seq):
    """Turn a CSI sequence body like "A", "1;2A" or "5~" into a symbolic
    key name such as "UP" or "SHIFT-LEFT", or None if unrecognized."""
    if not seq:
        return None
    if seq == "I":
        return "FOCUS_IN"
    if seq == "O":
        return "FOCUS_OUT"
    final = seq[-1]
    params = seq[:-1].split(";") if seq[:-1] else [""]
    modifier = params[1] if len(params) > 1 else "1"

    if final == "~":
        name = CSI_TILDE_CODES.get(params[0])
    else:
        name = CSI_FINAL_LETTERS.get(final)

    if name is None:
        return None
    return f"SHIFT-{name}" if modifier == "2" else name


def decode_sgr_mouse(seq):
    """Parse an SGR mouse-reporting sequence body (after ESC [), e.g.
    "<0;42;17M" - a left-button press at column 42, row 17 (both
    1-based, in terminal cells). Returns (kind, col, row) where kind is
    "MOUSE_CLICK", "MOUSE_DRAG"/"MOUSE_RELEASE" (left button held and
    moved, then let go - see MOUSE_ON's 1002),
    "MOUSE_WHEEL_UP"/"MOUSE_WHEEL_DOWN", or "MOUSE_BACK"/"MOUSE_FORWARD"
    (a mouse's side buttons, where it has them - button 8/9 in the xterm
    protocol). Returns None for anything else (a button other than the
    left one, a malformed sequence) - not a recognized action here, so
    ignored."""
    if not seq.startswith("<") or seq[-1] not in "Mm":
        return None
    body, final = seq[1:-1], seq[-1]
    parts = body.split(";")
    if len(parts) != 3:
        return None
    try:
        cb, cx, cy = (int(p) for p in parts)
    except ValueError:
        return None
    if cb & 0x80:
        # Side buttons 8-11: bit 7 (0x80) marks the group, low 2 bits
        # pick which one - button 8 (back) and 9 (forward) are the
        # common "browser navigation" buttons; 10/11 aren't mapped to
        # anything here. Reported as a press/release pair like the
        # ordinary buttons, so only act on the press.
        if final != "M":
            return None
        offset = cb & 0x03
        if offset == 0:
            return "MOUSE_BACK", cx, cy
        if offset == 1:
            return "MOUSE_FORWARD", cx, cy
        return None
    if cb & 0x40:
        # The scroll wheel: bit 6 (0x40) marks it, and bit 0 then tells
        # up from down. Always reported as a "press" (final "M"), never
        # a release.
        if final != "M":
            return None
        return ("MOUSE_WHEEL_DOWN" if cb & 1 else "MOUSE_WHEEL_UP"), cx, cy
    if (cb & 3) != 0:
        return None  # a button other than the left one
    if final == "m":
        # A release ends a drag (see Viewer.end_scrollbar_drag()); the
        # motion bit may or may not still be set on it, so don't look.
        return "MOUSE_RELEASE", cx, cy
    if cb & 0x20:
        return "MOUSE_DRAG", cx, cy  # bit 5 (0x20) is drag/motion
    return "MOUSE_CLICK", cx, cy


def get_term_cells(fd):
    packed = fcntl.ioctl(fd, termios.TIOCGWINSZ, struct.pack("HHHH", 0, 0, 0, 0))
    rows, cols, xpix, ypix = struct.unpack("HHHH", packed)
    return rows, cols, xpix, ypix


def query_pixel_size_osc(fd, timeout=0.5):
    """Ask the terminal for its text-area size in pixels via CSI 14t
    (an iTerm2/xterm extension). Returns (width_px, height_px) or None."""
    os.write(fd, b"\x1b[14t")
    pattern = re.compile(rb"\x1b\[4;(\d+);(\d+)t")
    buf = b""
    deadline = time.monotonic() + timeout
    while True:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            return None
        r, _, _ = select.select([fd], [], [], remaining)
        if not r:
            return None
        chunk = os.read(fd, 64)
        if not chunk:
            return None
        buf += chunk
        m = pattern.search(buf)
        if m:
            height, width = int(m.group(1)), int(m.group(2))
            return width, height


_warned_fallback = False


def get_pixel_size(fd):
    """Best-effort terminal text-area size in pixels: (width_px, height_px)."""
    global _warned_fallback
    rows, cols, xpix, ypix = get_term_cells(fd)
    if xpix and ypix:
        return xpix, ypix

    got = query_pixel_size_osc(fd)
    if got is not None:
        return got

    if not _warned_fallback:
        # end="\r\n": this can print from inside the viewer's raw-mode
        # terminal (get_pixel_size() is called on every resize), where a
        # bare "\n" wouldn't return the cursor to column 1.
        print(
            "pdfless: could not determine terminal pixel size; falling back "
            "to a rough estimate (image sharpness/fit may be off)",
            file=sys.stderr, end="\r\n",
        )
        _warned_fallback = True

    # Last resort: guess a plausible cell size.
    guess_w, guess_h = 8, 17
    return cols * guess_w, rows * guess_h


def wrap_for_tmux(osc):
    if not os.environ.get("TMUX"):
        return osc
    escaped = osc.replace("\x1b", "\x1b\x1b")
    return f"\x1bPtmux;{escaped}\x1b\\"


def iterm2_like():
    """True when running under iTerm2, WezTerm, or a close OSC-1337
    clone - terminals that support the OSC 1337 inline image protocol
    well enough to accept a JPEG-encoded payload, not just PNG."""
    if os.environ.get("TERM_PROGRAM") in ("iTerm.app", "WezTerm"):
        return True
    if os.environ.get("ITERM_SESSION_ID") or os.environ.get("WEZTERM_PANE"):
        return True
    return "iterm" in os.environ.get("LC_TERMINAL", "").lower()


def _format_ech_clear(char_w, char_h):
    """Erase `char_w` x `char_h` cells at the home position (ECH/CUU)."""
    out = ["\x1b[H"]
    for i in range(char_h):
        out.append(f"\x1b[{char_w}X")
        if i < char_h - 1:
            out.append("\x1b[1B")
    if char_h > 0:
        out.append(f"\x1b[{char_h}A")
    return "".join(out)


def _strip_leading_home(s):
    home = "\x1b[H"
    if s.startswith(home):
        return s[len(home):]
    return s


class PageCache:
    """Caches rasterized/resized page images, keyed by (page, size) -
    the actual per-kind work (rasterize a PDF page at some DPI, resize
    a pre-rendered image/office PNG) is delegated to `handler` (the
    same DocumentHandler instance Viewer itself uses - see
    Viewer._set_current_file() - which for an OfficeDocument owns its
    own rendered page list, self.pages), which reaches back into this
    cache's own bookkeeping (_cached()/_store(), and tmpdir) since that
    bookkeeping - LRU eviction, the "loaded once natively" table - is
    shared machinery rather than any one kind's own concern."""

    def __init__(self, doc_path, tmpdir, handler, size=CACHE_SIZE):
        self.doc_path = doc_path
        self.tmpdir = tmpdir
        self.kind = handler.kind  # "pdf", "image", or "office"
        self.size = size
        self._cache = OrderedDict()  # (page, dpi_or_px_rounded) -> PIL.Image
        self._native_images = {}  # page -> PIL.Image, loaded once each - see
        # DocumentHandler._native_page_image(): for kind == "image"
        # there's only ever page 1, but kind == "office" has one source
        # file per pre-rendered page (handler.pages).
        self.handler = handler

    def clear(self):
        self._cache.clear()
        self._native_images.clear()  # re-read the file(s), e.g. for -F/--follow

    def get(self, page, target_px, fit="width"):
        """The PDF page, or a pre-rendered page (a plain image file for
        kind=="image", or one of the pre-sliced Quick Look preview PNGs
        for kind=="office"), scaled so it's `target_px` wide (fit="width")
        or tall (fit="height")."""
        return self.handler.get_page_image(self, page, target_px, fit)

    def _cached(self, key):
        """A previously-computed page image for `key`, or None - shared
        LRU bookkeeping used by every DocumentHandler.get_page_image()."""
        if key in self._cache:
            self._cache.move_to_end(key)
            return self._cache[key]
        return None

    def _store(self, key, img):
        self._cache[key] = img
        if len(self._cache) > self.size:
            self._cache.popitem(last=False)


class EncodeCache:
    """Cache JPEG/PNG payloads keyed by viewport position."""

    def __init__(self, size=CACHE_SIZE * 4):
        self.size = size
        self._cache = OrderedDict()  # encode_key -> bytes

    def clear(self):
        self._cache.clear()

    def get(self, key):
        if key not in self._cache:
            return None
        self._cache.move_to_end(key)
        return self._cache[key]

    def put(self, key, data):
        self._cache[key] = data
        if len(self._cache) > self.size:
            self._cache.popitem(last=False)


class Viewer:
    def __init__(
        self, files, file_index, page, tmpdir, fd, fit="width",
        border=True, wrap=True, eol_mark=True, line_numbers=False,
        scrollbar=True, wheel_scroll_step=2, incremental_scroll=True,
        debug=False, office_render_scale=OFFICE_RENDER_SCALE,
        office_continuous=False, follow=False,
    ):
        self.files = files  # [DocumentHandler, ...] - one per CLI argument
        self.file_index = file_index
        self.tmpdir = tmpdir
        self.follow = follow  # -F/--follow, or toggled at runtime with F -
        # purely a display flag for status_segments(); the actual mtime-
        # polling/reload logic lives in run_viewer()'s own loop, which
        # keeps this in sync when the F key toggles it
        self.debug = debug  # -d/--debug: print office-preview stage timing
        self.office_render_scale = office_render_scale  # --rendering-scale
        self.office_continuous = office_continuous  # -c/--continuous
        self.fd = fd
        self.fit = fit
        self.eol_mark = eol_mark  # --no-eol-mark: mark a real end-of-line
        # (NEWLINE_MARKER) in text mode - independent of text_wrap/-S, on
        # by default either way (see _draw_text_wrapped()/_unwrapped())
        self.wheel_scroll_step = wheel_scroll_step
        self.incremental_scroll = incremental_scroll  # --no-incremental-
        # scroll: force every redraw through _draw()'s full-viewport
        # path, skipping the _scroll_shift_rows()/_draw_shifted()
        # shortcut - an escape hatch for a terminal where that shortcut
        # (confirmed by hand on iTerm2 - see _scroll_shift_rows()) turns
        # out not to hold
        # A real (not just placeholder-0) self.rows/cols before
        # _set_current_file() below is what lets its lazy office-preview
        # render (if the first file needs one) show live status-line
        # progress the same as any later one (e.g. a :n/:p switch) does -
        # draw_status() needs both to lay out that line. The rest of the
        # geometry (avail_height_px, cell sizes, ...) still isn't known
        # this early - that needs self.cache, set up moments from now -
        # but the status line alone doesn't touch any of that.
        self.rows, self.cols, _, _ = get_term_cells(fd)
        self.page = page
        self._set_current_file()  # sets path/name/kind/npages/cache
        # For an office-kind first file, self.npages was just determined
        # above (by _ensure_office_pages(), lazily) rather than known
        # ahead of time the way main() clamps a PDF/image/text file's
        # start page against - so clamp it here instead, now that it's
        # known.
        self.page = max(1, min(self.npages, self.page))
        self.encode_cache = EncodeCache()
        self.scroll = 0
        self.zoom = 1.0
        self.resized = True
        self.img = None
        self.avail_height_px = 0
        self.cell_h_px = 1
        self.cell_w_px = 1
        # self.rows/self.cols are already set, above - see the comment there
        self.crop_width = 0
        self.x_offset = 0
        self.help_active = False
        self.help_scroll = 0
        self._search_index = None  # lazily built, via PdfDocument.build_search_index()
        self._link_index = None  # lazily built, via PdfDocument.build_link_index()
        self._history_back = []  # [(page, scroll, x_offset), ...]
        self._history_forward = []
        self.search_query = None
        self.search_matches = []
        self.search_pos = None
        # A plain text file has no image view at all - it's permanently
        # "in text mode", the same rendering PDF's `t` key switches to.
        self.text_mode = self.doc_handler.starts_in_text_mode()
        self.text_lines = []
        self.text_scroll = 0
        self.text_scroll_min = 0
        self.text_scroll_max = 0
        self.text_x_offset = 0
        self.text_x_offset_min = 0
        self.text_x_offset_max = 0
        self.text_max_line_width = 0
        self.border_default = border  # --no-border, as given on the command line
        self.text_border = self._default_text_border()  # border around the
        # page's edges, in text mode; can be swept up along with the text
        # if you select-and-copy it, so it's toggled off with --no-border
        # (or on/off any time with the B key) - see _default_text_border()
        self.wrap_default = wrap  # -S/--chop-long-lines, as given on the
        # command line (inverted - this is "should it wrap", not "should
        # it chop")
        self.text_wrap = self._default_text_wrap()  # soft-wrap long lines
        # instead of panning across them (h/l/H/L) - see
        # _default_text_wrap(); no border while wrapped (see
        # _draw_text_wrapped()), regardless of text_border
        self._display_rows = None  # lazily built by _ensure_display_rows(),
        # only while text_wrap is on - [(line_idx, start, end), ...], one
        # entry per on-screen row
        self.line_numbers = line_numbers  # -N/--line-numbers: right-
        # aligned gutter at the start of each row - see
        # _line_number_gutter_width(); no per-kind default (unlike
        # border/wrap/eol_mark) since there's no kind numbering wouldn't
        # make sense for
        self._copy_mode_saved = None  # while "C" has the decorations
        # off, what to put back on the next press - see toggle_copy_mode()
        self._scrollbar_drag = False  # a press landed on the scrollbar
        # and the button hasn't come back up yet - see handle_drag()
        self._scrollbar_drag_row = None  # its latest position, not acted
        # on until flush_scrollbar_drag()
        self.scrollbar = scrollbar  # --no-scrollbar: a column on the
        # terminal's right edge showing scroll position - in both image
        # mode (_draw()) and text mode (_draw_text_wrapped()/
        # _draw_text_unwrapped()); "r" toggles it either way (see
        # toggle_scrollbar()), applying uniformly to both since it's
        # handled at run_viewer()'s top level rather than per-mode
        self._last_viewport_w = 0
        self._last_viewport_h = 0
        self._last_viewport_set = False
        self._last_char_h = 0
        self._last_marker_bounds = None  # (row0, col0, row1, col1) or None
        # What _draw() last actually put on screen, for _scroll_shift_rows()
        # to compare against - only trusted while _last_viewport_set is
        # True, which every place that overwrites the screen with
        # something else (help, text mode, a resize, ...) already turns
        # off, so these never need resetting anywhere but here.
        self._last_page = None
        self._last_x_offset = None
        self._last_zoom_key = None
        self._last_scroll = None

    def request_resize(self):
        self.resized = True
        # The help box's size/position and the underlying page raster are
        # both stale after a resize; simplest is to just drop back to the
        # normal view, which always does a full redraw at the new size.
        self.help_active = False

    def _set_current_file(self):
        """Point path/name/kind/npages/doc_handler/cache at
        self.files[self.file_index] - just the file's identity, not the
        page/zoom/search/etc. state, which __init__ sets up once and
        go_to_file() resets explicitly on every later switch."""
        handler = self.files[self.file_index]
        self.path = handler.path
        self.name = os.path.basename(handler.path)
        self.doc_handler = handler
        self.kind = handler.kind  # "pdf", "image", "text", or "office"
        self.npages = handler.page_count()  # None for an OfficeDocument
        # until _ensure_office_pages() below actually renders it
        self._ensure_office_pages()  # a no-op unless doc_handler is an
        # OfficeDocument, and sets self.npages for real in that case
        # (memoized on the handler itself - see OfficeDocument.pages -
        # so a revisit to an already-rendered file is still cheap)
        self.cache = PageCache(handler.path, self.tmpdir, handler)

    def _ensure_office_pages(self):
        """With multiple files on the command line, an office-kind one
        (Word/Excel/PowerPoint/etc. via Quick Look) is only actually
        rendered the moment it's about to be displayed - not upfront for
        every such file regardless of whether it's ever looked at - so
        this is where that render happens, the first time doc_handler is
        an OfficeDocument. A no-op every time after that (doc_handler.
        ensure_pages() remembers its own result on the handler itself,
        the same as a file that's always been rendered up front would
        be) other than resetting self.npages, which is cheap."""
        if not isinstance(self.doc_handler, OfficeDocument):
            return
        pages = self.doc_handler.ensure_pages(
            self.tmpdir, debug=self.debug,
            render_scale=self.office_render_scale, progress=_ViewerProgress(self),
            continuous=self.office_continuous,
        )
        if not pages:
            pages = self.doc_handler._render_error_placeholder(
                self.tmpdir, "Quick Look rendering failed - see -d/--debug for details",
            )
            self.doc_handler.pages = pages  # remember the placeholder too - don't retry every revisit
        self.npages = len(pages)

    @property
    def is_pdf(self):
        return isinstance(self.doc_handler, PdfDocument)

    def next_file(self):
        self.go_to_file(self.file_index + 1, "no next file")

    def previous_file(self):
        self.go_to_file(self.file_index - 1, "no previous file")

    def go_to_file(self, index, boundary_message="no such file"):
        """Switch to files[index], starting fresh at its first page -
        zoom, search, link history, and text mode all reset, the same
        as if pdfless had been started fresh on that file. A no-op
        (with a status message) if index is out of range."""
        if index < 0 or index >= len(self.files):
            self.draw_status(boundary_message)
            return
        self.file_index = index
        self._set_current_file()
        self.encode_cache.clear()
        self._search_index = None
        self.clear_search()
        self._link_index = None
        self._history_back = []
        self._history_forward = []
        self.text_mode = self.doc_handler.starts_in_text_mode()
        self.text_border = self._default_text_border()
        self.text_wrap = self._default_text_wrap()
        self._display_rows = None
        # Mouse reporting is only useful in the page image (clicking
        # hyperlinks, wheel scroll); off in any kind of text view, the
        # same as enter_text_mode()/exit_text_mode() do for a PDF's `t`
        # toggle - needed here too since a text-kind file goes straight
        # into text_mode without ever calling those.
        sys.stdout.write(MOUSE_OFF if self.text_mode else MOUSE_ON)
        self.zoom = 1.0
        self.page = 1
        self.scroll = 0
        self.x_offset = 0
        self._last_viewport_set = False
        self._last_marker_bounds = None
        if self.text_mode:
            self._load_text_page()
        else:
            self._load_page()
        self.refresh()  # its normal status line already includes "file i/N"

    def _recompute_geometry(self):
        rows, cols, _, _ = get_term_cells(self.fd)
        width_px, height_px = get_pixel_size(self.fd)
        cell_h = max(1, height_px // max(1, rows))
        cell_w = max(1, width_px // max(1, cols))
        self.rows = rows
        self.cols = cols
        # One cell's width held back for the scrollbar (see _draw()),
        # while it's on - crop_width/x_offset/pan bounds/click hit-
        # testing are all derived from base_width_px (see _load_page()),
        # so reserving it here is enough to keep the image itself out
        # of that column everywhere else.
        self.base_width_px = width_px - (cell_w if self.scrollbar else 0)
        self.cell_h_px = cell_h
        self.cell_w_px = cell_w
        self.avail_height_px = cell_h * max(1, rows - 1)
        self.cache.clear()
        self.encode_cache.clear()
        self._last_viewport_set = False
        self._last_char_h = 0
        self._last_marker_bounds = None
        self._display_rows = None  # stale - self.cols may have changed,
        # which is what wrapping is measured against

    def _load_page(self):
        self.encode_cache.clear()
        if self.fit == "height":
            target_height = max(1, round(self.avail_height_px * self.zoom))
            self.img = self.cache.get(self.page, target_height, fit="height")
        else:
            target_width = max(1, round(self.base_width_px * self.zoom))
            self.img = self.cache.get(self.page, target_width, fit="width")
        self.crop_width = min(self.img.width, self.base_width_px)
        # Keep whatever horizontal position you panned to (h/l/H/L),
        # only clamping it to the image that just got loaded. Turning a
        # page mustn't move the view sideways: with -h on a wide
        # document (a slide deck, say) every page is wider than the
        # terminal, so re-centering here would undo an "H" the moment
        # you pressed j - and j is a page turn there, since a
        # height-fitted page has nothing left to scroll. Zoom anchors
        # itself deliberately instead; see set_zoom().
        self.x_offset = max(0, min(self.x_offset, self.img.width - self.crop_width))
        self.scroll_max = max(0, self.img.height - self.avail_height_px)
        self.scroll = min(self.scroll, self.scroll_max)

    def set_zoom(self, new_zoom):
        new_zoom = max(MIN_ZOOM, min(MAX_ZOOM, new_zoom))
        if new_zoom == self.zoom:
            return
        # Zoom around the middle of what's on screen, rather than around
        # the image's left edge: remember where the viewport's center
        # sits as a fraction of the page's width, then put it back there
        # once the resized image is in. _load_page() only clamps
        # x_offset now, so this is what decides where a zoom lands.
        center_frac = (self.x_offset + self.crop_width / 2) / max(1, self.img.width)
        self.zoom = new_zoom
        self._load_page()
        self.x_offset = max(0, min(
            self.img.width - self.crop_width,
            round(center_frac * self.img.width - self.crop_width / 2),
        ))

    def reset_view(self):
        """"0": back to the untouched view of this page - zoom 1 and the
        left edge. The pan has to be put back by hand: _load_page() only
        clamps x_offset these days, and at zoom 1 a -h page can still be
        wider than the terminal, so there'd be nothing to clamp it to."""
        self.zoom = 1.0
        self._load_page()
        self.x_offset = 0

    def set_fit(self, fit):
        self.fit = fit
        self.zoom = 1.0
        self.scroll = 0
        self._load_page()
        self.x_offset = 0

    def pan(self, dx):
        max_offset = max(0, self.img.width - self.crop_width)
        self.x_offset = max(0, min(max_offset, self.x_offset + dx))

    def _relayout(self):
        """Redo the layout after something on screen changed how much
        room is left for the content itself (the scrollbar's column,
        copy mode's four decorations) - everything a terminal resize
        recomputes, except that it keeps you where you were reading.
        refresh()'s resize path can't be reused for this: for a file
        that starts in text mode it re-reads the whole file, which
        starts you over at the top - fine when the terminal really did
        change size, but not for a keystroke that just hid a column."""
        # Read before the recompute, put back after it: a narrower or
        # wider content area re-splits every wrapped line, so the row
        # number text_scroll holds stops meaning the same place.
        top_line = self._top_text_line() if self.text_mode else None
        self._recompute_geometry()
        self.resized = False
        if self.text_mode:
            self._scroll_to_text_line(top_line)
        else:
            self._load_page()

    def _top_text_line(self):
        """The raw text_lines index showing at the top of the screen:
        text_scroll itself when text is unwrapped, and the line the top
        display row belongs to when it's wrapped (text_scroll counts
        display rows then - see _ensure_display_rows())."""
        if not self.text_wrap:
            return max(0, self.text_scroll)  # -1 is the border's own row
        self._ensure_display_rows()
        if not self._display_rows:
            return 0
        row = max(0, min(self.text_scroll, len(self._display_rows) - 1))
        return self._display_rows[row][0]

    def _scroll_to_text_line(self, line_idx):
        """Put raw line `line_idx` back at the top of the screen, in
        whichever unit the current mode scrolls in - the inverse of
        _top_text_line(), so the pair of them carry a reading position
        across anything that changes the layout underneath it."""
        self.text_scroll = self._row_for_line(line_idx) if self.text_wrap else line_idx
        self._clamp_text_scroll()

    def refresh(self):
        if self.resized:
            self._recompute_geometry()
            self.resized = False
            if self.doc_handler.starts_in_text_mode():
                self._load_text_page()  # (re)read the file - it's always "page 1"
            elif self.text_mode:
                self._clamp_text_scroll()
            else:
                self._load_page()
        if self.help_active:
            self._draw_help()
        elif self.text_mode:
            self._draw_text()
        else:
            self._draw()

    def show_help(self):
        self.help_active = True
        self.help_scroll = 0
        self._draw_help()

    def scroll_help(self, delta):
        """Scroll the help box by `delta` lines (negative = up), for when
        KEY_TABLE has grown taller than the box can show at once."""
        lines = KEY_TABLE.splitlines()
        available_rows = max(1, self.rows - 1)
        content_h = min(max(1, available_rows - 2), len(lines))
        max_scroll = max(0, len(lines) - content_h)
        new_scroll = max(0, min(max_scroll, self.help_scroll + delta))
        if new_scroll != self.help_scroll:
            self.help_scroll = new_scroll
            self._draw_help()

    def hide_help(self):
        self.help_active = False
        self._last_viewport_set = False  # help chars overlay the page
        self._last_marker_bounds = None
        self.refresh()

    def enter_text_mode(self):
        """Switch to text mode - False (no-op) if there's no text to
        show at all, which for an OfficeDocument means textutil
        couldn't extract anything from this particular file (e.g. a
        spreadsheet or slide deck - see extract_office_text())."""
        if not self.doc_handler.supports_text_mode():
            return False
        if self.doc_handler.extract_text(self.page) is None:
            return False
        self.text_mode = True
        # Mouse reporting is only useful (and only turned on) for
        # clicking hyperlinks in the page image; leave it off here so
        # the terminal's own click-drag text selection works normally.
        sys.stdout.write(MOUSE_OFF)
        self._last_viewport_set = False
        self._last_marker_bounds = None
        reindex_search = (
            self.search_query and self.doc_handler.search_resets_on_text_mode_toggle()
        )
        self._load_text_page()
        if reindex_search:
            # image mode and text mode search different extractions here
            # (see search_resets_on_text_mode_toggle()) - the match object
            # itself can't carry over, so re-run the same query against
            # this mode's own text instead, landing on the nearest hit.
            self.start_search(self.search_query)
        else:
            # If there's a search match highlighted/boxed on this same
            # page, follow it across into text mode too, scrolled into
            # view.
            match = self._active_search_page_match()
            if match:
                self._scroll_text_to_match(match)
        self.refresh()
        return True

    def exit_text_mode(self):
        if self._copy_mode_saved is not None:
            # Copy mode (however it was turned on - "C" inside text
            # mode, or "T"'s own combined enter) only makes sense while
            # in text mode - restore it here, on every way out,
            # regardless of which key got us into text mode in the
            # first place. Skipping this would leak the decorations it
            # hid (most importantly the scrollbar, which also applies
            # in image mode - see toggle_scrollbar()) into the image
            # view and leave them stuck off on a later re-entry too,
            # since _copy_mode_saved would still be holding the
            # original values from however long ago copy mode was
            # first turned on.
            self.toggle_copy_mode()
        self.text_mode = False
        sys.stdout.write(MOUSE_ON)
        self._last_viewport_set = False
        self._last_marker_bounds = None
        # self.page may have moved while browsing in text mode (n/p, g/G,
        # <N>g all update it), but self.img was never touched during that
        # - refresh() only reloads it on a resize - so without this it'd
        # redraw whatever page/scroll was last loaded before entering text
        # mode instead of following you back to where you navigated to.
        reindex_search = (
            self.search_query and self.doc_handler.search_resets_on_text_mode_toggle()
        )
        self.scroll = 0
        self._load_page()
        if reindex_search:
            # Symmetric with enter_text_mode(): the two modes search
            # different extractions here, so re-run the same query
            # against image mode's own (bbox) index instead of trying to
            # carry the match object across.
            self.start_search(self.search_query)
        else:
            # Symmetric with enter_text_mode(): carry a highlighted match
            # back into the box marker on the rendered page.
            match = self._active_search_page_match()
            if match:
                self._scroll_image_to_match(match)
        self.refresh()

    def toggle_text_mode(self):
        """Returns False if switching (specifically *into* text mode)
        failed for lack of any text to show - see enter_text_mode()."""
        if self.text_mode:
            self.exit_text_mode()
            return True
        return self.enter_text_mode()

    def toggle_clean_text_mode(self):
        """T: t and C in one press - enter text mode with the copy-mode
        decorations (border/EOL marks/scrollbar/line numbers) already
        cleared, and undo both together on a second press, back to a
        plain image view (exit_text_mode() itself restores copy mode
        before leaving, however it was turned on - see there). Returns
        False if there was no text to switch to (same as
        toggle_text_mode()) - copy mode is left untouched in that
        case."""
        if self.text_mode:
            self.exit_text_mode()  # restores copy mode, then refreshes
            return True
        if not self.enter_text_mode():  # refreshes into "undecorated" text mode
            return False
        if self._copy_mode_saved is None:
            self.toggle_copy_mode()  # relayout only - no redraw of its own
            self.refresh()  # so draw the now-decoration-free view here
        return True

    def _load_text_page(self):
        # For a handler whose text isn't paginated (office/text/rtf),
        # extract_text() ignores `page` and returns the whole document
        # every time - simplest to just always ask fresh here rather
        # than trying to cache it, since nothing else calls this often
        # enough for that to matter (see enter_text_mode()/reload(),
        # the only other places that ask for this same text).
        self.text_lines = self.doc_handler.extract_text(self.page)
        self._display_rows = None  # stale - built fresh from the new text_lines
        self.text_scroll = 0
        self.text_x_offset = 0
        self._clamp_text_scroll()
        if self.text_border and not self.text_wrap:
            # Default to showing the new page's top-left corner - and so
            # its border, since that's otherwise off past the default
            # (0, 0) position. go_to_page_text() below still overrides
            # this for scroll=None (continuous backward scroll wants the
            # bottom of the page instead). No border to reveal at all
            # while wrapped - see _draw_text_wrapped().
            self.text_scroll = self.text_scroll_min
            self.text_x_offset = self.text_x_offset_min

    def _text_avail_rows(self):
        return max(1, self.rows - 1)  # bottom row is the status bar

    def _text_avail_cols(self):
        # One column held back for the scrollbar (see
        # _scrollbar_column()) while it's on - regardless of whether the
        # current file actually needs scrolling, so every other column
        # reservation built on top of this (border, EOL marker, line
        # numbers) never has to special-case it.
        return max(1, self.cols - (1 if self.scrollbar else 0))

    def toggle_text_border(self):
        self.text_border = not self.text_border
        self._clamp_text_scroll()

    def _default_text_border(self):
        """Whether text mode's border should be on by default for the
        current file - delegated to doc_handler.default_text_border()
        (e.g. always off for a plain text file, regardless of
        --no-border, since there's usually no real "page" boundary in
        one worth bordering; otherwise whatever --no-border asked for).
        The B key can still toggle either way, on top of this default."""
        return self.doc_handler.default_text_border(self.border_default)

    def toggle_text_wrap(self):
        """Switches between soft-wrapping long lines and panning across
        them (h/l/H/L) - "s", or the less(1)-style "-S" (see
        run_viewer()'s dash_pending handling). Keeps your place across
        the switch: the two modes scroll in different units (a display
        row, once wrapping has split a line across several, vs. the raw
        text_lines index), so what carries over is the line currently at
        the top of the screen, translated into the other mode's terms.
        Horizontal pan doesn't carry over - there's nothing to pan while
        wrapped, so unwrapping starts back at the left edge."""
        top_line = self._top_text_line()  # read in the mode being left...
        self.text_wrap = not self.text_wrap
        self._display_rows = None  # rebuilt against the new mode's layout
        self.text_x_offset = 0
        self._scroll_to_text_line(top_line)  # ...written in the one entered

    def toggle_eol_mark(self):
        """Switches NEWLINE_MARKER on/off - bound to "E" (see
        handle_key_text()). text_max_line_width/_display_rows both
        reserve a column for the marker only while it's on, so both
        need recomputing here - and, since that re-splits every wrapped
        line, so does the scroll position (_top_text_line())."""
        top_line = self._top_text_line()
        self.eol_mark = not self.eol_mark
        self._display_rows = None
        self._scroll_to_text_line(top_line)

    def toggle_line_numbers(self):
        """Switches the -N/--line-numbers gutter on/off - "#" (see
        handle_key_text()), or "-N"/"-n" (less(1)-style, see
        run_viewer()'s dash_pending). Its width changes what's left for
        content, so the wrapped segments (_display_rows), the scroll
        bounds and the scroll position itself (_top_text_line()) all
        need recomputing."""
        top_line = self._top_text_line()
        self.line_numbers = not self.line_numbers
        self._display_rows = None
        self._scroll_to_text_line(top_line)

    def toggle_copy_mode(self):
        """Clear the way for a terminal select-and-copy, and put things
        back on a second press - "C" (see handle_key_text()). Text mode
        exists largely to copy text out of a document, and the EOL
        markers, the border, the scrollbar and the line-number gutter
        all sit in the way of that: a drag across the text sweeps them
        up along with it. Rather than hunting down E/B/r/# one at a
        time and remembering which of them were on to begin with, this
        turns off all four at once and remembers that for you."""
        if self._copy_mode_saved is not None:
            (
                self.eol_mark, self.text_border, self.scrollbar, self.line_numbers
            ) = self._copy_mode_saved
            self._copy_mode_saved = None
        else:
            self._copy_mode_saved = (
                self.eol_mark, self.text_border, self.scrollbar, self.line_numbers
            )
            self.eol_mark = self.text_border = False
            self.scrollbar = self.line_numbers = False
        # Each of the four frees up (or takes back) room of its own -
        # let _relayout() work out what that means rather than spelling
        # out which widths moved here.
        self._relayout()

    def _line_number_gutter_width(self):
        """Columns reserved for the -N gutter - 0 when it's off. Right-
        aligned digits sized to the largest line number currently in
        self.text_lines (a PDF's per-page text, or the whole document
        for anything else - see _load_text_page()), plus one separator
        column."""
        if not self.line_numbers or not self.text_lines:
            return 0
        return len(str(len(self.text_lines))) + 1

    def toggle_scrollbar(self):
        """Switches the scrollbar on/off - "r" (see run_viewer(), which
        handles it at the top level since it applies in both image mode
        (_draw()) and text mode). Its column is reserved from
        base_width_px (image mode - see _recompute_geometry()) or
        _text_avail_cols() (text mode), so the whole layout has to be
        redone around it - see _relayout()."""
        self.scrollbar = not self.scrollbar
        self._relayout()

    def _scrollbar_fractions(self, start, avail_extent, total_extent, page, npages):
        """(start_frac, visible_frac), both in [0, 1]: where the visible
        window starts, and how much of it is visible, as a fraction of
        the WHOLE document (all `npages` pages) - not just the current
        page/screen. `start`/`avail_extent`/`total_extent` share any one
        consistent unit (pixels in image mode, rows in text mode):
        `start` is how far into the current page the window's top edge
        sits, `total_extent` the page's own full size, `avail_extent`
        how much of it fits on screen at once. A 10-page PDF, showing
        the top half of page 1, is start_frac=0, visible_frac=0.5/10 -
        the thumb sits in the top 5% of the track, not top-50%, which
        was this method's whole reason for existing (see toggle_scrollbar()'s
        callers) - a single-page view (page=npages=1) reduces exactly to
        "this page/screen's own fraction", unaffected."""
        total_extent = max(1, total_extent)
        page_start_frac = max(0.0, min(1.0, start / total_extent))
        page_visible_frac = max(0.0, min(1.0, avail_extent / total_extent))
        npages = max(1, npages)
        return (page - 1 + page_start_frac) / npages, page_visible_frac / npages

    def _text_scrollbar_fractions(self, avail_rows):
        """(start_frac, visible_frac) for the text-mode scrollbar - see
        _scrollbar_fractions(). Only a PDF's text mode pages separately
        (doc_handler.text_mode_is_paginated()) - anything else shows
        the whole document in one continuous text_scroll range
        already, so page/npages are fixed at 1/1 there (self.page/
        self.npages might otherwise still reflect an unrelated slide/
        page count from image mode - e.g. a multi-slide OfficeDocument
        - that text mode's own single flowing view doesn't split on)."""
        total_extent = avail_rows + (self.text_scroll_max - self.text_scroll_min)
        start = self.text_scroll - self.text_scroll_min
        if self.doc_handler.text_mode_is_paginated():
            page, npages = self.page, self.npages
        else:
            page, npages = 1, 1
        return self._scrollbar_fractions(start, avail_rows, total_extent, page, npages)

    def _scrollbar_column(self, avail_rows, start_frac, visible_frac):
        """One rendered cell (color + char) per screen row, top to
        bottom, for the scrollbar column - the terminal's last column,
        reserved (while self.scrollbar is on) from base_width_px in
        image mode (see _draw()) or _text_avail_cols() in text mode
        (see _draw_text_wrapped()/_draw_text_unwrapped()). `start_frac`/
        `visible_frac` (see _scrollbar_fractions()) are already
        normalized to the whole document, so this is just laying them
        out over avail_rows screen cells. A file that fits on screen
        entirely (visible_frac >= 1) shows a thumb spanning the whole
        track, rather than an arbitrary track/thumb split that would
        suggest otherwise."""
        visible_frac = max(0.0, min(1.0, visible_frac))
        if visible_frac >= 1.0:
            return [SCROLLBAR_THUMB] * avail_rows
        thumb_size = max(1, min(avail_rows, round(visible_frac * avail_rows)))
        thumb_start = max(0, min(avail_rows - thumb_size, round(start_frac * avail_rows)))
        return [
            SCROLLBAR_THUMB if thumb_start <= i < thumb_start + thumb_size
            else SCROLLBAR_TRACK
            for i in range(avail_rows)
        ]

    def _default_text_wrap(self):
        """Whether text mode should default to wrapping long lines for
        the current file - delegated to doc_handler.default_text_wrap()
        (on for a plain text file, unless -S/--chop-long-lines said
        otherwise; off for a PDF/Office's own derived text view, which
        pans instead, regardless of -S). The -S key sequence can still
        toggle either way, on top of this default."""
        return self.doc_handler.default_text_wrap(self.wrap_default)

    def _clamp_text_scroll(self):
        # The border sits at the page's actual edges - one row above the
        # first line, one below the last; one column left of column 0,
        # one right of the widest line - which is usually off-screen at
        # the default scroll/pan position. It only comes into view by
        # scrolling/panning one step past the content itself, so with the
        # border on, the scroll/pan range is widened by exactly that much;
        # with it off, the range is exactly what it was before this
        # feature existed.
        avail_rows = self._text_avail_rows()
        if self.text_wrap:
            # No border while wrapped (see _draw_text_wrapped()) - the
            # scroll range is over display rows (self._display_rows,
            # built fresh here since content_width may have changed),
            # not raw text_lines, and there's no pan to speak of.
            self._ensure_display_rows()
            self.text_scroll_min = 0
            self.text_scroll_max = max(0, len(self._display_rows) - avail_rows)
            self.text_scroll = max(
                self.text_scroll_min, min(self.text_scroll, self.text_scroll_max)
            )
            self.text_x_offset_min = 0
            self.text_x_offset_max = 0
            self.text_x_offset = 0
            return

        # The border sits at the page's actual edges - one row above the
        # first line, one below the last; one column left of column 0,
        # one right of the widest line - which is usually off-screen at
        # the default scroll/pan position. It only comes into view by
        # scrolling/panning one step past the content itself, so with the
        # border on, the scroll/pan range is widened by exactly that much;
        # with it off, the range is exactly what it was before this
        # feature existed.
        if self.text_border:
            self.text_scroll_min = -1
            self.text_scroll_max = max(-1, len(self.text_lines) - avail_rows + 1)
        else:
            self.text_scroll_min = 0
            self.text_scroll_max = max(0, len(self.text_lines) - avail_rows)
        self.text_scroll = max(
            self.text_scroll_min, min(self.text_scroll, self.text_scroll_max)
        )

        # The -N gutter (if on) lives outside this space entirely - see
        # _draw_text_unwrapped() - so the "page" is narrower by that much.
        avail_cols = max(1, self._text_avail_cols() - self._line_number_gutter_width())
        self.text_max_line_width = max(
            (display_width(l) for l in self.text_lines), default=0
        )
        if self.eol_mark:
            # Otherwise the widest line's own marker (see
            # _draw_text_unwrapped()) would have nowhere to go without
            # overflowing past the border - this pretends the page is 1
            # column wider than its content actually is, the same way
            # _ensure_display_rows() reserves a column when wrapped.
            self.text_max_line_width += 1
        if self.text_border:
            self.text_x_offset_min = -1
            self.text_x_offset_max = max(-1, self.text_max_line_width - avail_cols + 1)
        else:
            self.text_x_offset_min = 0
            self.text_x_offset_max = max(0, self.text_max_line_width - avail_cols)
        self.text_x_offset = max(
            self.text_x_offset_min, min(self.text_x_offset, self.text_x_offset_max)
        )

    def _active_search_page_match(self):
        """The currently-selected search match (self.search_pos), but
        only if it's on the page being displayed right now - this is
        what lets the box marker (image mode) and highlight (text mode)
        follow each other across a `t` toggle: both are derived from this
        same bit of state, recomputed fresh on every draw, rather than
        each mode tracking its own separate "is a match showing" flag."""
        if self.search_pos is None:
            return None
        match = self.search_matches[self.search_pos]
        return match if match[0] == self.page else None

    def _active_search_occurrence_index(self):
        """How many other matches with the same page precede
        self.search_matches[self.search_pos] (0-indexed) - i.e. this is
        the Nth occurrence of the query on that page, in reading order.
        Used to correlate the same occurrence between the bbox-based
        document search index and the independently pdftotext -layout
        -extracted text-mode lines: when a page has the query more than
        once, matching by *position* between the two isn't reliable
        (their coordinate systems and line-splitting differ), but
        reading order should still agree between them."""
        if self.search_pos is None:
            return None
        page = self.search_matches[self.search_pos][0]
        if page != self.page:
            return None
        return sum(1 for m in self.search_matches[: self.search_pos] if m[0] == page)

    def _match_bbox_px(self, match):
        """Pixel bounding box (in the current page image) of a
        (page, xMin, yMin, xMax, yMax) search match, in points."""
        _, xmin_pt, ymin_pt, xmax_pt, ymax_pt = match
        page_info = self._search_index[self.page - 1]
        scale_x = self.img.width / page_info["width_pt"]
        scale_y = self.img.height / page_info["height_pt"]
        return (
            xmin_pt * scale_x,
            ymin_pt * scale_y,
            xmax_pt * scale_x,
            ymax_pt * scale_y,
        )

    def _find_all_text_matches(self):
        """Every occurrence of self.search_query within self.text_lines
        (the current page's pdftotext -layout text), as a list of
        (line_idx, start, end), in reading order."""
        if not self.search_query:
            return []
        pattern = compile_search_pattern(self.search_query)
        results = []
        for i, line in enumerate(self.text_lines):
            for m in pattern.finditer(line):
                if m.start() != m.end():
                    results.append((i, m.start(), m.end()))
        return results

    def _text_search_highlight(self):
        """(line_idx, start, end) to highlight while drawing text mode,
        or None. Never returns a PDF bbox tuple."""
        if self.search_pos is None or not self.search_matches:
            return None
        match = self.search_matches[self.search_pos]
        if self._search_uses_text_lines():
            if len(match) == 3:
                return match
            return self._text_highlight_for_match(match)
        return self._text_highlight_for_match(self._active_search_page_match())

    def _text_highlight_for_match(self, match):
        """(line_idx, start, end) of `match` within self.text_lines, or
        None if the query doesn't appear there at all (a real
        possibility, given the two extractions can differ)."""
        if match is None:
            return None
        all_matches = self._find_all_text_matches()
        if not all_matches:
            return None

        occurrence_index = self._active_search_occurrence_index()
        if occurrence_index is not None and occurrence_index < len(all_matches):
            return all_matches[occurrence_index]

        # Fall back to a proportional-position guess, for the rare case
        # where the two extractions disagree on how many times the query
        # appears on this page.
        _, _xmin_pt, ymin_pt, _xmax_pt, _ymax_pt = match
        page_info = self._search_index[self.page - 1]
        height_pt = page_info["height_pt"]
        approx_line = (
            round((ymin_pt / height_pt) * len(self.text_lines)) if height_pt else 0
        )
        return min(all_matches, key=lambda c: abs(c[0] - approx_line))

    def _scroll_image_to_match(self, match):
        """Scroll/pan the image view so `match` is visible, landing it a
        little below the top-left rather than jammed against the edge."""
        px_left, px_top, px_right, px_bottom = self._match_bbox_px(match)
        margin = self.avail_height_px // 4
        self.scroll = max(0, min(self.scroll_max, round(px_top) - margin))
        max_x_offset = max(0, self.img.width - self.crop_width)
        if px_left < self.x_offset or px_right > self.x_offset + self.crop_width:
            self.x_offset = max(
                0,
                min(max_x_offset, round((px_left + px_right) / 2 - self.crop_width / 2)),
            )

    def _scroll_text_to_match(self, match):
        """Scroll/pan the text view so `match` is visible, landing it a
        little below the top rather than jammed against the top edge -
        panning horizontally into view too, in case the terminal is too
        narrow for the line and it's off to the side of the truncated
        view (the text-mode equivalent of _scroll_image_to_match()).
        Wrapped text has no pan to speak of - _row_for_line() converts
        the raw line position into a display-row scroll target instead."""
        avail_cols = max(1, self._text_avail_cols() - self._line_number_gutter_width())
        highlight = self._text_highlight_for_match(match)
        if highlight:
            line_idx, start, end = highlight
            if self.text_wrap:
                target_row = self._row_for_line(line_idx)
            else:
                line = self.text_lines[line_idx]
                col_start = display_width(line[:start])
                col_end = display_width(line[:end])
                if col_start < self.text_x_offset or col_end > self.text_x_offset + avail_cols:
                    self.text_x_offset = max(
                        self.text_x_offset_min,
                        min(
                            self.text_x_offset_max,
                            round((col_start + col_end) / 2 - avail_cols / 2),
                        ),
                    )
                target_row = line_idx
        else:
            _, _xmin_pt, ymin_pt, _xmax_pt, _ymax_pt = match
            height_pt = self._search_index[self.page - 1]["height_pt"]
            line_idx = (
                round((ymin_pt / height_pt) * len(self.text_lines)) if height_pt else 0
            )
            target_row = self._row_for_line(line_idx) if self.text_wrap else line_idx
        avail_rows = self._text_avail_rows()
        margin = avail_rows // 4
        self.text_scroll = max(
            self.text_scroll_min, min(self.text_scroll_max, target_row - margin)
        )

    def go_to_page_text(self, page, scroll):
        self.page = max(1, min(self.npages, page))
        self._load_text_page()  # already leaves text_scroll at text_scroll_min
        if scroll is None:
            self.text_scroll = self.text_scroll_max  # continuous scroll-up wants the bottom
        elif scroll != 0:
            # 0 means "top of page", which _load_text_page() already set
            # up (text_scroll_min, revealing the border if there is one);
            # anything else is a specific line to land on (e.g. <N>g).
            self.text_scroll = max(
                self.text_scroll_min, min(self.text_scroll_max, scroll)
            )

    def go_to_text_line(self, n):
        """Jump to line `n` (1-based) within the current page's text -
        <N>g/<N>G in text mode. Lands it at the very top of the screen,
        same as less(1)'s own <N>g, even if that leaves blank space
        below near the end of the page - unlike normal scrolling, which
        never scrolls past showing a full screen of content, in order
        to guarantee the requested line is the one that ends up on top.
        While wrapped, "line n" still means the same raw line - it just
        lands on whichever display row that line's wrapping starts at."""
        target_line = max(0, min(len(self.text_lines) - 1, n - 1))
        row = self._row_for_line(target_line) if self.text_wrap else target_line
        self.text_scroll = max(self.text_scroll_min, row)

    def text_scroll_down(self, n):
        if self.text_scroll < self.text_scroll_max:
            self.text_scroll = min(self.text_scroll_max, self.text_scroll + n)
        elif self.page < self.npages:
            self.go_to_page_text(self.page + 1, 0)

    def text_scroll_up(self, n):
        if self.text_scroll > self.text_scroll_min:
            self.text_scroll = max(self.text_scroll_min, self.text_scroll - n)
        elif self.page > 1:
            self.go_to_page_text(self.page - 1, None)

    def _row_for_line(self, line_idx):
        """The first display-row index (into self._display_rows, see
        _ensure_display_rows()) covering raw line `line_idx` - lets
        anything that thinks in terms of a raw text_lines index (search
        highlighting, <N>g) target the right scroll position once
        wrapping has split that line across one or more screen rows."""
        self._ensure_display_rows()
        for row, (li, _start, _end) in enumerate(self._display_rows):
            if li == line_idx:
                return row
        return max(0, len(self._display_rows) - 1)

    @staticmethod
    def _wrap_line_segments(line, width):
        """Split `line` into consecutive (start, end) character-index
        segments, each at most `width` display columns wide - the
        wrap-mode equivalent of slice_by_width()'s single pan window,
        but covering the whole line instead of just one panned slice of
        it. An empty line still yields exactly one (empty) segment, so
        it still occupies one display row, same as an unwrapped blank
        line does."""
        width = max(1, width)
        if not line:
            return [(0, 0)]
        segments = []
        start = 0
        n = len(line)
        while start < n:
            piece = truncate_to_width(line[start:], width)
            if not piece:
                # a single character wider than the whole available
                # width - it still has to go somewhere
                piece = line[start:start + 1]
            end = start + len(piece)
            segments.append((start, end))
            start = end
        return segments

    def _ensure_display_rows(self):
        """Build self._display_rows - one (line_idx, start, end) entry
        per on-screen row while wrapped - lazily, since it's invalidated
        (set to None) whenever self.text_lines, text_wrap, or the
        terminal width changes, and rebuilding it is O(total document
        length)."""
        if self._display_rows is not None:
            return
        # One column held back for the real-newline marker (see
        # _draw_text_wrapped()), if it's on - reserved on every row, not
        # just one that ends up actually drawing it, so the marker never
        # has to compete with content for the same column. The -N gutter
        # (if on) is held back the same way, drawn outside this width.
        width = (
            self._text_avail_cols()
            - (1 if self.eol_mark else 0)
            - self._line_number_gutter_width()
        )
        width = max(1, width)
        rows = []
        for i, line in enumerate(self.text_lines):
            for start, end in self._wrap_line_segments(line, width):
                rows.append((i, start, end))
        self._display_rows = rows

    def _draw_text(self):
        if self.text_wrap:
            self._draw_text_wrapped()
        else:
            self._draw_text_unwrapped()

    def _draw_text_wrapped(self):
        """Wrap-mode rendering: self._display_rows (built by
        _ensure_display_rows()) already breaks the document into
        on-screen rows, each guaranteed to fit the terminal width - so,
        unlike _draw_text_unwrapped(), there's no pan position to
        account for. The border (text_border) isn't drawn here either,
        regardless of its own on/off state: a border only makes sense
        around a fixed page shape, and wrapped text has no edges of its
        own to border - it just keeps flowing to fill the width."""
        self._ensure_display_rows()
        avail_rows = self._text_avail_rows()
        highlight = self._text_search_highlight()

        out = [STATUS_COLOR_OFF, "\x1b[H\x1b[2J"]
        n_rows = len(self._display_rows)
        gutter_width = self._line_number_gutter_width()

        for i in range(avail_rows):
            virtual_row = self.text_scroll + i
            screen_row = i + 1
            if not (0 <= virtual_row < n_rows):
                continue  # above/below the document entirely

            line_idx, start, end = self._display_rows[virtual_row]
            rendered = self.text_lines[line_idx][start:end]

            if gutter_width:
                # Only the line's first display row gets a number - a
                # wrapped continuation row (start != 0) stays blank.
                if start == 0:
                    num = str(line_idx + 1).rjust(gutter_width - 1)
                    gutter_text = LINE_NUMBER_COLOR + num + " " + LINE_NUMBER_RESET
                else:
                    gutter_text = " " * gutter_width
                out.append(f"\x1b[{screen_row};1H{gutter_text}")

            if highlight and highlight[0] == line_idx:
                # start/end are character offsets into the raw line;
                # clip them to this segment, then shift into the
                # segment's own (rendered-relative) coordinates.
                _, h_start, h_end = highlight
                h_start, h_end = max(h_start, start) - start, min(h_end, end) - start
                if h_start < len(rendered) and h_end > h_start:
                    rendered = (
                        rendered[:h_start]
                        + TEXT_HIGHLIGHT_COLOR
                        + rendered[h_start:h_end]
                        + TEXT_HIGHLIGHT_RESET
                        + rendered[h_end:]
                    )

            if self.eol_mark and end == len(self.text_lines[line_idx]):
                # This segment reaches the actual end of the raw line -
                # a real newline, not just where this row's wrapping
                # happened to cut it - see NEWLINE_MARKER.
                rendered += NEWLINE_MARKER_COLOR + NEWLINE_MARKER + NEWLINE_MARKER_RESET

            out.append(f"\x1b[{screen_row};{gutter_width + 1}H{rendered}")

        if self.scrollbar:
            start_frac, visible_frac = self._text_scrollbar_fractions(avail_rows)
            cells = self._scrollbar_column(avail_rows, start_frac, visible_frac)
            for i, cell in enumerate(cells):
                out.append(f"\x1b[{i + 1};{self.cols}H{cell}")

        out.append(self.format_status())
        sys.stdout.write("".join(out))
        sys.stdout.flush()

    def _draw_text_unwrapped(self):
        # The border sits at the page's own edges in this same scrollable/
        # pannable space the text lines live in - virtual row -1 (top)
        # and row len(text_lines) (bottom), virtual column -1 (left) and
        # column text_max_line_width (right) - rather than around
        # whatever happens to be on screen. So depending on text_scroll/
        # text_x_offset, any side of it may be scrolled out of view; each
        # row below independently figures out which of border/content/
        # nothing falls at its current position.
        avail_rows = self._text_avail_rows()
        # The -N gutter (if on) lives outside this whole border/pan
        # space, in columns of its own - the "page" here is simply
        # narrower by that much, same as the border/content geometry
        # below never needs to know it exists.
        gutter_width = self._line_number_gutter_width()
        avail_cols = max(1, self._text_avail_cols() - gutter_width)
        highlight = self._text_search_highlight()
        # Reset text attributes *before* clearing, not after: a
        # still-active SGR state (e.g. a background color left on by
        # draw_search_prompt(), which doesn't reset it since it's
        # mid-edit) is what \x1b[2J fills the newly-blanked cells with -
        # resetting only afterwards colors future writes but leaves
        # every cell the clear itself touched stuck in that stale color.
        out = [STATUS_COLOR_OFF, "\x1b[H\x1b[2J"]

        left_col = -1 - self.text_x_offset
        right_col = self.text_max_line_width - self.text_x_offset
        left_visible = self.text_border and 0 <= left_col < avail_cols
        right_visible = self.text_border and 0 <= right_col < avail_cols

        for i in range(avail_rows):
            virtual_row = self.text_scroll + i
            screen_row = i + 1

            if gutter_width:
                if 0 <= virtual_row < len(self.text_lines):
                    num = str(virtual_row + 1).rjust(gutter_width - 1)
                    gutter_text = LINE_NUMBER_COLOR + num + " " + LINE_NUMBER_RESET
                else:
                    gutter_text = " " * gutter_width  # border row, or off the page
                out.append(f"\x1b[{screen_row};1H{gutter_text}")

            if self.text_border and virtual_row in (-1, len(self.text_lines)):
                line_start = max(0, left_col)
                line_end = min(avail_cols - 1, right_col)
                if line_end < line_start:
                    continue  # this border edge is panned out of view
                chars = ["─"] * (line_end - line_start + 1)
                if left_visible:
                    chars[0] = "┌" if virtual_row == -1 else "└"
                if right_visible:
                    chars[-1] = "┐" if virtual_row == -1 else "┘"
                out.append(f"\x1b[{screen_row};{line_start + 1 + gutter_width}H{''.join(chars)}")
                continue

            if not (0 <= virtual_row < len(self.text_lines)):
                continue  # above/below the border entirely - nothing there

            line = self.text_lines[virtual_row]
            content_start = (left_col + 1) if left_visible else 0
            content_end = right_col if right_visible else avail_cols
            content_width = max(0, content_end - content_start)
            rendered, base = slice_by_width(
                line, max(0, self.text_x_offset), content_width
            )
            reaches_end = base + len(rendered) == len(line)
            # Measured before any color codes (highlight, marker) are
            # spliced in below - display_width() would miscount those
            # escape bytes as visible columns otherwise. When bordered,
            # text_max_line_width's own +1 (above) already guarantees
            # room for the marker on every row (the widest line just
            # uses all of it, up against the border); unbordered, there's
            # no such guarantee, so only draw it if there's room to spare.
            shown_width = display_width(rendered)
            show_marker = self.eol_mark and reaches_end and shown_width < content_width

            if highlight and highlight[0] == virtual_row:
                # start/end are character offsets into the original,
                # unpanned `line`; `rendered` starts partway through it
                # (at character index `base`, i.e. wherever text_x_offset
                # columns in falls) once panned, so shift them into
                # rendered's own coordinates before slicing it up to
                # splice in color codes.
                _, start, end = highlight
                start, end = start - base, end - base
                start, end = max(start, 0), min(end, len(rendered))
                if start < len(rendered) and end > start:
                    rendered = (
                        rendered[:start]
                        + TEXT_HIGHLIGHT_COLOR
                        + rendered[start:end]
                        + TEXT_HIGHLIGHT_RESET
                        + rendered[end:]
                    )

            if show_marker:
                # Right after the real content - i.e. at the actual
                # newline position - not padded out to the border (see
                # below), which would misleadingly suggest the line
                # itself reaches all the way to the page edge.
                rendered += NEWLINE_MARKER_COLOR + NEWLINE_MARKER + NEWLINE_MARKER_RESET
                shown_width += 1

            if right_visible:
                # Pad with plain spaces (not pad_to_width(), which would
                # re-measure `rendered` and miscount the escape codes
                # just spliced in) so the border still lines up straight
                # at the page's actual right edge, same as before.
                rendered += " " * max(0, content_width - shown_width)

            parts = []
            if left_visible:
                parts.append("│")
            parts.append(rendered)
            if right_visible:
                parts.append("│")
            start_col = (left_col if left_visible else content_start) + 1 + gutter_width
            out.append(f"\x1b[{screen_row};{start_col}H{''.join(parts)}")

        if self.scrollbar:
            start_frac, visible_frac = self._text_scrollbar_fractions(avail_rows)
            cells = self._scrollbar_column(avail_rows, start_frac, visible_frac)
            for i, cell in enumerate(cells):
                out.append(f"\x1b[{i + 1};{self.cols}H{cell}")

        out.append(self.format_status())
        sys.stdout.write("".join(out))
        sys.stdout.flush()

    def _draw_help(self):
        # Overlay the help as a boxed panel centered over the page, instead
        # of clearing the screen: we only ever move the cursor and rewrite
        # the exact cells the box covers, so the PDF still showing in the
        # rest of the terminal is left untouched.
        available_rows = max(1, self.rows - 1)  # bottom row is the status bar
        all_lines = KEY_TABLE.splitlines()

        content_w = min(max(20, self.cols - 4), max(len(l) for l in all_lines))
        all_lines = [l[:content_w] for l in all_lines]
        content_h = min(max(1, available_rows - 2), len(all_lines))
        # KEY_TABLE may be taller than the box can show at once; clamp the
        # scroll position (e.g. after a resize shrank the box) and slice
        # out just the window of lines currently in view.
        max_scroll = max(0, len(all_lines) - content_h)
        self.help_scroll = max(0, min(max_scroll, self.help_scroll))
        lines = all_lines[self.help_scroll:self.help_scroll + content_h]

        box_w = content_w + 4  # border (2) + padding (2)
        box_h = content_h + 2  # top/bottom border
        row0 = max(1, (available_rows - box_h) // 2 + 1)
        col0 = max(1, (self.cols - box_w) // 2 + 1)

        out = [STATUS_COLOR_OFF, f"\x1b[{row0};{col0}H┌{'─' * (box_w - 2)}┐"]
        for i, line in enumerate(lines):
            out.append(f"\x1b[{row0 + 1 + i};{col0}H│ {line.ljust(content_w)} │")
        out.append(f"\x1b[{row0 + box_h - 1};{col0}H└{'─' * (box_w - 2)}┘")
        sys.stdout.write("".join(out))
        sys.stdout.flush()
        if max_scroll:
            pct = round(100 * self.help_scroll / max_scroll)
            self.draw_status(f"q to close help - j/k or wheel to scroll ({pct}%)")
        else:
            self.draw_status("q to close help")

    def _encode_crop(self, crop):
        buf = io.BytesIO()
        if iterm2_like():
            # JPEG encodes much faster than PNG; iTerm2 accepts it inline.
            crop.convert("RGB").save(buf, format="JPEG", quality=90)
        else:
            crop.save(buf, format="PNG", compress_level=1)
        return buf.getvalue()

    def _format_viewport_clear(self, crop_w, crop_h, full_clear):
        char_w = max(1, -(-crop_w // self.cell_w_px))
        char_h = max(1, -(-crop_h // self.cell_h_px))
        prev_char_h = self._last_char_h or char_h

        if full_clear:
            self._last_char_h = char_h
            return "\x1b[H\x1b[2J"

        out = ["\x1b[H"]
        if self._last_viewport_set and crop_h > self._last_viewport_h:
            out.append(_strip_leading_home(_format_ech_clear(char_w, char_h)))
        if prev_char_h > char_h:
            for row in range(char_h, min(prev_char_h, self.rows - 1)):
                out.append(f"\x1b[{row + 1};1H\x1b[2K")
        total_rows = max(1, -(-self.avail_height_px // self.cell_h_px))
        blank_from = char_h
        if prev_char_h > char_h:
            blank_from = max(char_h, prev_char_h)
        for row in range(blank_from, min(self.rows - 1, total_rows)):
            out.append(f"\x1b[{row + 1};1H\x1b[2K")
        self._last_char_h = char_h
        return "".join(out)

    def _needs_full_clear(self, crop_w, crop_h):
        if not self._last_viewport_set:
            return True
        if self._last_viewport_w != crop_w:
            return True
        if crop_h > self._last_viewport_h:
            return True
        return False

    def _draw(self):
        crop_bottom = min(self.scroll + self.avail_height_px, self.img.height)
        crop_h = crop_bottom - self.scroll

        shift = self._scroll_shift_rows(self.crop_width, crop_h)
        if shift is not None:
            self._draw_shifted(shift, crop_bottom)
            return

        crop = self.img.crop(
            (self.x_offset, self.scroll, self.x_offset + self.crop_width, crop_bottom)
        )
        crop_w, crop_h = crop.width, crop.height

        encode_key = (
            self.page, self.scroll, self.x_offset, crop_w, crop_h,
            round(self.zoom * 100),
        )
        data = self.encode_cache.get(encode_key)
        if data is None:
            data = self._encode_crop(crop)
            self.encode_cache.put(encode_key, data)

        b64 = base64.b64encode(data).decode("ascii")
        osc = (
            f"\x1b]1337;File=inline=1;doNotMoveCursor=1;size={len(data)};"
            f"width={crop_w}px;height={crop_h}px;"
            f"preserveAspectRatio=0:{b64}\x07"
        )

        full_clear = self._needs_full_clear(crop_w, crop_h)
        self._last_viewport_w = crop_w
        self._last_viewport_h = crop_h
        self._last_viewport_set = True
        self._remember_drawn_position()

        match = self._active_search_page_match()
        new_bounds = (
            self._match_marker_bounds(*self._match_bbox_px(match))
            if match else None
        )

        # Reset *before* any clearing/erasing below, not after: a
        # still-active SGR state (e.g. a background color left on by
        # draw_search_prompt(), which doesn't reset it since it's
        # mid-edit) is what a \x1b[2J/ECH fills the newly-blanked cells
        # with - see _draw_text()'s longer version of this comment.
        out = [STATUS_COLOR_OFF, self._format_viewport_clear(crop_w, crop_h, full_clear)]
        # Erase the previous marker before the new image lands; otherwise
        # box-drawing chars linger on iTerm2 inline-image cells (especially
        # when search is cleared or n/p jumps to another match).
        if self._last_marker_bounds and self._last_marker_bounds != new_bounds:
            out.append(self._format_marker_erase(*self._last_marker_bounds))
        out.extend([
            "\x1b[H",  # erase leaves the cursor elsewhere; doNotMoveCursor=1
            # draws the inline image at the current cell, not home.
            wrap_for_tmux(osc),
        ])
        if new_bounds:
            out.append(self._format_marker_at_bounds(*new_bounds))
        self._last_marker_bounds = new_bounds

        out.extend(self._scrollbar_column_escapes())
        out.append(self.format_status())
        sys.stdout.write("".join(out))
        sys.stdout.flush()

    def _remember_drawn_position(self):
        """Bookkeeping shared by _draw()'s full redraw and _draw_shifted()'s
        incremental one - what _scroll_shift_rows() compares the *next*
        draw's position against, to tell a plain scroll apart from a page
        turn, a zoom, or a pan (see there)."""
        self._last_page = self.page
        self._last_x_offset = self.x_offset
        self._last_zoom_key = round(self.zoom * 100)
        self._last_scroll = self.scroll

    def _scroll_shift_rows(self, crop_w, crop_h):
        """Whole character-rows the viewport shifted since the last
        _draw(), or None if a full redraw is required.

        A vertical-only scroll within the same page/zoom/pan can reuse
        what's already on screen: the terminal's own scroll-region
        primitive (DECSTBM + CSI S/T) shifts an already-placed iTerm2
        inline image right along with plain text (confirmed by hand -
        see scroll_spike.py in this repo's history), so _draw_shifted()
        only has to transmit the newly-exposed strip instead of
        re-encoding and re-sending the whole viewport. This is what
        decides whether that shortcut applies; every condition here
        falls back to the always-correct full redraw when in doubt:

        - _last_viewport_set is the same "do we know anything about the
          previous frame" flag _needs_full_clear() uses - every place
          that overwrites the screen with something else (help, text
          mode, a resize, ...) already clears it, so relying on it here
          for free means _last_page/_last_x_offset/etc. never need
          resetting anywhere but _remember_drawn_position().
        - TMUX / not iterm2_like(): the shortcut depends on inline-image
          placements riding along with a scroll-region shift, which is
          unverified (and, for tmux, actively suspect - tmux owns the
          pane's own scrolling and may not replay image content the way
          a real terminal's internal grid does).
        - page/x_offset/zoom/crop size all matching: anything else means
          self.img itself or the crop rectangle changed shape, so there
          may be nothing valid left on screen to shift.
        - no active search marker: its box-drawing overlay would need
          shifting (or erasing) too, and matches are rare enough that
          it's simplest to just fall back when one's showing.
        - self.incremental_scroll: --no-incremental-scroll's escape
          hatch, for a terminal where the above turns out not to hold.
        """
        if (not self.incremental_scroll
                or not self._last_viewport_set
                or os.environ.get("TMUX")
                or not iterm2_like()
                or crop_w != self._last_viewport_w
                or crop_h != self._last_viewport_h
                or self._last_page != self.page
                or self._last_x_offset != self.x_offset
                or self._last_zoom_key != round(self.zoom * 100)
                or self._last_marker_bounds is not None
                or self._active_search_page_match() is not None):
            return None
        delta = self.scroll - self._last_scroll
        if delta == 0 or delta % self.cell_h_px != 0:
            return None
        shift = delta // self.cell_h_px
        avail_rows = max(1, self.rows - 1)
        if abs(shift) >= avail_rows:
            return None  # no overlap left - a full redraw is just as cheap
        return shift

    def _draw_shifted(self, shift, crop_bottom):
        """The incremental path _draw() takes for a plain vertical
        scroll (see _scroll_shift_rows()): shift whatever's already
        displayed with the terminal's own scroll region instead of
        redrawing it, and transmit only the strip of pixels that just
        became visible."""
        avail_rows = max(1, self.rows - 1)
        strip_rows = abs(shift)
        strip_h = strip_rows * self.cell_h_px
        if shift > 0:
            # Scrolled forward: content moves UP, revealing new rows at
            # the BOTTOM.
            strip_top = crop_bottom - strip_h
            screen_row = avail_rows - strip_rows + 1
        else:
            # Scrolled backward: content moves DOWN, revealing new rows
            # at the TOP.
            strip_top = self.scroll
            screen_row = 1
        strip = self.img.crop((
            self.x_offset, strip_top,
            self.x_offset + self.crop_width, strip_top + strip_h,
        ))

        encode_key = (
            self.page, strip_top, self.x_offset, strip.width, strip.height,
            round(self.zoom * 100),
        )
        data = self.encode_cache.get(encode_key)
        if data is None:
            data = self._encode_crop(strip)
            self.encode_cache.put(encode_key, data)

        b64 = base64.b64encode(data).decode("ascii")
        osc = (
            f"\x1b]1337;File=inline=1;doNotMoveCursor=1;size={len(data)};"
            f"width={strip.width}px;height={strip.height}px;"
            f"preserveAspectRatio=0:{b64}\x07"
        )

        self._remember_drawn_position()

        out = [
            STATUS_COLOR_OFF,
            f"\x1b[1;{avail_rows}r",
            f"\x1b[{shift}S" if shift > 0 else f"\x1b[{strip_rows}T",
            "\x1b[r",  # back to a full-screen scroll region right away -
            # nothing past this point should be confined by it.
            f"\x1b[{screen_row};1H",
            wrap_for_tmux(osc),
        ]
        out.extend(self._scrollbar_column_escapes())
        out.append(self.format_status())
        sys.stdout.write("".join(out))
        sys.stdout.flush()

    def _scrollbar_column_escapes(self):
        """The scrollbar column's cells, as a list of positioned escape
        strings - shared by _draw()'s full redraw and _draw_shifted()'s
        incremental one, both of which repaint it every frame regardless
        (it's cheap plain text, not part of what differential drawing
        is meant to optimize)."""
        if not self.scrollbar:
            return []
        # Same row count avail_height_px was computed from (see
        # _recompute_geometry()) - the column itself was already
        # held back from base_width_px, so the image never reaches
        # into it regardless of zoom/pan. self.page/self.npages fold
        # this page's own (self.scroll, avail_height_px, img.height)
        # fraction into a whole-document position - see
        # _scrollbar_fractions() - rather than just this page's own.
        avail_rows = max(1, self.rows - 1)
        start_frac, visible_frac = self._scrollbar_fractions(
            self.scroll, self.avail_height_px, self.img.height, self.page, self.npages
        )
        cells = self._scrollbar_column(avail_rows, start_frac, visible_frac)
        return [f"\x1b[{i + 1};{self.cols}H{cell}" for i, cell in enumerate(cells)]

    def status_segments(self):
        """The default status line, as (text, color) fields in order."""
        if self.text_mode:
            pct = (
                100
                if self.text_scroll_max == 0
                else int(100 * self.text_scroll / self.text_scroll_max)
            )
            mode_field = " text "
        else:
            pct = (
                100
                if self.scroll_max == 0
                else int(100 * self.scroll / self.scroll_max)
            )
            # self.zoom alone isn't comparable across m/M (fit height/
            # width): it's always "1.0" right after switching fit mode
            # (see set_fit()), which would show "100%" for either one
            # even though a fit-height page is rarely the same actual
            # size as its fit-width rendering. Comparing the page's
            # current pixel width (self.img.width - fit="height" still
            # yields a real width, just one implied by the page's
            # aspect ratio rather than target_px directly - see
            # get_page_image()) against self.base_width_px (M's own
            # 100% reference) instead makes the percentage mean the
            # same thing - "size relative to fit-to-width" - no matter
            # which fit mode or zoom level produced it.
            zoom_pct = round(100 * self.img.width / max(1, self.base_width_px))
            mode_field = f" zoom {zoom_pct}% "
        segments = [(f" {self.name} ", STATUS_COLOR_FILENAME)]
        if len(self.files) > 1:
            segments.append((
                f" file {self.file_index + 1}/{len(self.files)} ",
                STATUS_COLOR_FILE_INDEX,
            ))
        segments += [
            (f" page {self.page:>{len(str(self.npages))}}/{self.npages} ", STATUS_COLOR_PAGE),
            (f" {pct:>3}% ", STATUS_COLOR_LOC),
            (mode_field, STATUS_COLOR_ZOOM),
        ]
        if self.follow:
            segments.append((" follow ", STATUS_COLOR_FOLLOW))
        segments.append((" F1 or :h for help ", STATUS_COLOR_HELP))
        return segments

    def format_status(self, text=None):
        """Return escape sequence for the status line (no write)."""
        if text is not None:
            status = pad_to_width(truncate_to_width(f" {text} ", self.cols), self.cols)
            return (
                f"\x1b[{self.rows};1H{STATUS_COLOR_ON}\x1b[2K"
                f"{status}{STATUS_COLOR_OFF}"
            )

        # Truncate/pad by terminal column width, not Python string length:
        # search queries or the filename can contain wide (e.g. Japanese)
        # characters that are 1 Python character but 2 terminal columns,
        # and undercounting that would write past the last column of the
        # last row, which triggers autowrap and scrolls the whole screen
        # up a line.
        out = []
        width_used = 0
        for text_seg, color in self.status_segments():
            if width_used >= self.cols:
                break
            chunk = truncate_to_width(text_seg, self.cols - width_used)
            if not chunk:
                continue
            out.append(f"{color}{chunk}")
            width_used += display_width(chunk)
        if width_used < self.cols:
            out.append(f"{STATUS_COLOR_OFF}{' ' * (self.cols - width_used)}")

        return f"\x1b[{self.rows};1H\x1b[2K{''.join(out)}{STATUS_COLOR_OFF}"

    def draw_status(self, text=None):
        # \x1b[?25l re-hides the real terminal cursor draw_search_prompt()
        # shows while a "/"/"?" query is being typed - every other status
        # line (including the "isn't available"/no-match ones shown right
        # after a search prompt closes) goes back to the normal paging
        # UI, which never shows a cursor of its own.
        sys.stdout.write(self.format_status(text) + "\x1b[?25l")
        sys.stdout.flush()

    def draw_search_prompt(self, buf, cursor, backward=False):
        """The search pattern being typed, echoed on the status line
        behind the prompt character it was opened with - "/" forward,
        "?" backward, the same as less(1) shows them. `cursor` is the
        index into `buf` (in Python characters, not columns) the next
        inserted/deleted character applies at - not necessarily
        len(buf), since ^B/^F/LEFT/RIGHT can move it back into the
        middle of an already-typed query."""
        # Unlike draw_status(), this doesn't pad the line out to the full
        # terminal width: padding leaves the cursor sitting at the far
        # right edge (in autowrap's "pending wrap" state), which is past
        # where the typed text actually is. That confuses things like the
        # terminal's IME composition popup, which anchors on the cursor -
        # it ends up rendered a line below instead of right after "/query".
        # Leaving the cursor immediately after the last character keeps it
        # where it visually belongs. The line is still cleared (and thus
        # filled) with the status color first, via \x1b[2K, and the color
        # is left active (not reset) so text typed via IME composition
        # picks it up too; draw_status() resets it on the next full redraw.
        prefix = "?" if backward else "/"
        text = truncate_to_width(f"{prefix}{buf}", self.cols)
        # The terminal cursor's column, not buf's: it sits after the
        # prompt character plus every column `buf[:cursor]` occupies -
        # using display_width() (not len()) since a wide character (e.g.
        # Japanese) covers 2 columns, same reasoning as
        # format_status()'s own width accounting.
        col = min(self.cols, 1 + display_width(prefix) + display_width(buf[:cursor]))
        # \x1b[?25h shows the real terminal cursor - normally hidden the
        # whole time pdfless owns the screen (see the entry-screen write
        # in main()) - positioned at `col` so it tracks mid-string edits
        # too (draw_status() hides it again once the prompt closes).
        sys.stdout.write(
            f"\x1b[{self.rows};1H{STATUS_COLOR_ON}\x1b[2K{text}"
            f"\x1b[{self.rows};{col}H\x1b[?25h"
        )
        sys.stdout.flush()

    def go_page(self, page, scroll):
        self.page = max(1, min(self.npages, page))
        self._load_page()
        self.scroll = scroll

    def _pdf_source(self):
        """The PdfDocument to defer to for anything that only makes
        sense against a real PDF (page_size_pt(), build_link_index()) -
        either self.doc_handler itself, or the PdfDocument an
        OfficeDocument rendered to under the hood (see
        OfficeDocument.get_page_image()'s _pdf_delegate - a plain
        <a href> in the original Word/RTF document survives
        Chrome's --print-to-pdf as a real PDF link annotation, so this
        lets it be treated exactly like a real PDF's hyperlinks
        wherever this is used), or None if neither applies."""
        if self.is_pdf:
            return self.doc_handler
        return getattr(self.doc_handler, "_pdf_delegate", None)

    def _ensure_link_index(self):
        if self._link_index is None:
            pdf_source = self._pdf_source()
            if pdf_source is not None:
                self._link_index = pdf_source.build_link_index(self.npages)
            else:
                # No hyperlinks outside a PDF, but a multi-page "office"
                # preview (or, in principle, a multi-page "image") still
                # needs one empty entry per page - handle_click() indexes
                # this by self.page, which can be > 1 for those kinds.
                self._link_index = [
                    {"width_pt": 0.0, "height_pt": 0.0, "links": []}
                    for _ in range(self.npages)
                ]

    def handle_click(self, col, row):
        """A left-click at 1-based terminal cell (col, row): on the
        scrollbar, jump to the position it points at; otherwise, if it
        landed on a PDF hyperlink in the currently displayed crop,
        follow it - open a URL in the system browser, or jump to an
        internal link's target page/position."""
        if self.text_mode or self.help_active or row >= self.rows:
            return  # row == self.rows is the status bar
        # Any press starts a fresh gesture: one that lands on the
        # scrollbar keeps following the pointer until the button comes
        # back up (see handle_drag()), one anywhere else doesn't.
        self._scrollbar_drag = bool(self.scrollbar and col == self.cols)
        if self._scrollbar_drag:
            self._jump_to_scrollbar_row(row)
            return
        self._ensure_link_index()
        page_info = self._link_index[self.page - 1]
        if not page_info["links"] or not page_info["width_pt"] or not page_info["height_pt"]:
            return

        # The clicked cell -> the pixel rectangle it covers on the full
        # page raster (undoing the current pan/scroll) -> a PDF-point
        # rectangle, in the same coordinate system build_link_index()
        # stored link rects in. A whole-cell rectangle, not just its
        # center point, matters here: a citation-style link (e.g. just
        # "5.7" in "figure 5.7") is often tightly boxed around the
        # digits by whatever generated the PDF, so its rect can be
        # thinner than one terminal row is tall - a single sampled point
        # would frequently land just outside it and miss the click.
        scale_x = page_info["width_pt"] / self.img.width
        scale_y = page_info["height_pt"] / self.img.height
        cell_xmin = (self.x_offset + (col - 1) * self.cell_w_px) * scale_x
        cell_xmax = cell_xmin + self.cell_w_px * scale_x
        cell_ymin = (self.scroll + (row - 1) * self.cell_h_px) * scale_y
        cell_ymax = cell_ymin + self.cell_h_px * scale_y

        best = None
        best_area = None
        for link in page_info["links"]:
            if (
                link["xmax"] < cell_xmin or link["xmin"] > cell_xmax
                or link["ymax"] < cell_ymin or link["ymin"] > cell_ymax
            ):
                continue  # no overlap between the link and the clicked cell
            area = (link["xmax"] - link["xmin"]) * (link["ymax"] - link["ymin"])
            if best is None or area < best_area:
                best, best_area = link, area
        if best is not None:
            self._activate_link(best)

    def handle_drag(self, row):
        """Left-button motion, while a scrollbar drag is in progress -
        i.e. the press that started it landed on the scrollbar (see
        handle_click()); dragging anywhere else is left alone, so a
        stray drag across the page image doesn't send it jumping.

        Only records where the pointer is: acting on it costs a page
        rasterize, and a drag arrives as a burst of motion events, so
        flush_scrollbar_drag() applies the last one once the burst lets
        up rather than walking every page in between. Returns whether
        the drag was taken."""
        if not self._scrollbar_drag or self.text_mode or self.help_active:
            return False
        self._scrollbar_drag_row = row
        return True

    def flush_scrollbar_drag(self):
        """Act on the position handle_drag() last recorded, if any."""
        if self._scrollbar_drag_row is None:
            return
        row = self._scrollbar_drag_row
        self._scrollbar_drag_row = None
        self._jump_to_scrollbar_row(row)

    def end_scrollbar_drag(self):
        """The button came back up - act on wherever it was let go."""
        self.flush_scrollbar_drag()
        self._scrollbar_drag = False

    def _jump_to_scrollbar_row(self, row):
        """Jump to wherever a click at `row` points on the scrollbar -
        the clicked cell's own place in the track is read as where the
        visible window should start, undoing what _scrollbar_fractions()
        did to put the thumb there. Image mode only: mouse reporting
        stays off in text mode so the terminal's own click-drag text
        selection keeps working (see enter_text_mode())."""
        avail_rows = max(1, self.rows - 1)
        start_frac = max(0.0, min(1.0, (row - 1) / avail_rows))
        # In "page units" - e.g. 3.5 is halfway down page 4 - so the
        # page and the position within it fall out of the same number.
        doc_pos = start_frac * max(1, self.npages)
        page = max(1, min(self.npages, int(doc_pos) + 1))
        within_frac = max(0.0, min(1.0, doc_pos - (page - 1)))
        if page != self.page:
            # Skipped when it's the page already showing, so a click
            # that only scrolls within it doesn't reload and rescale
            # the very same image for nothing.
            self.go_page(page, 0)
        self.scroll = max(0, min(self.scroll_max, round(within_frac * self.img.height)))
        self.refresh()

    def handle_wheel(self, direction):
        """A scroll-wheel step: direction -1 (up) or +1 (down),
        self.wheel_scroll_step lines each (--wheel-scroll-step) - the
        same page-boundary roll-over as e/y. Only meaningful in the page
        image (mouse reporting is off in text mode, so this shouldn't
        normally fire there, but the guard is cheap insurance)."""
        if self.text_mode or self.help_active:
            return
        step = self.cell_h_px * self.wheel_scroll_step
        if direction < 0:
            self.scroll_up(step)
        else:
            self.scroll_down(step)
        self.refresh()

    def _activate_link(self, link):
        if link["kind"] == "uri":
            try:
                opened = webbrowser.open(link["uri"])
            except webbrowser.Error:
                opened = False
            self.draw_status(
                f"opened {link['uri']}" if opened else f"couldn't open {link['uri']}"
            )
        else:
            self._push_history()
            self.go_to_link_target(link["page"], link["top_pt"])
            self.refresh()

    def _push_history(self):
        """Record the position an internal-link jump is about to leave,
        so `[`/`]` (or a mouse back/forward button) can return to it -
        the same "back stack, forward stack, a fresh jump clears
        forward" model a web browser uses."""
        self._history_back.append((self.page, self.scroll, self.x_offset))
        self._history_forward.clear()

    def go_back(self):
        self._go_history(self._history_back, self._history_forward, "earlier")

    def go_forward(self):
        self._go_history(self._history_forward, self._history_back, "later")

    def _go_history(self, from_stack, to_stack, label):
        if self.text_mode or self.help_active:
            return
        if not from_stack:
            self.draw_status(f"no {label} position")
            return
        to_stack.append((self.page, self.scroll, self.x_offset))
        page, scroll, x_offset = from_stack.pop()
        self._restore_position(page, scroll, x_offset)
        self.refresh()

    def _restore_position(self, page, scroll, x_offset):
        self.page = max(1, min(self.npages, page))
        self._load_page()  # loads the image and recomputes scroll_max
        self.scroll = max(0, min(self.scroll_max, scroll))
        max_x_offset = max(0, self.img.width - self.crop_width)
        self.x_offset = max(0, min(max_x_offset, x_offset))

    def go_to_link_target(self, page, top_pt):
        """Jump to `page`, scrolled so the link's target y-position
        (`top_pt`, in PDF points, bottom-up - or None if the link didn't
        specify one) lands a little below the top of the window, the
        same placement _scroll_image_to_match() uses for search matches."""
        self.page = max(1, min(self.npages, page))
        self._load_page()
        if top_pt is None:
            self.scroll = 0
            return
        pdf_source = self._pdf_source()
        height_pt = pdf_source.page_size_pt(self.page)[1] if pdf_source else None
        if not height_pt:
            self.scroll = 0
            return
        scale_y = self.img.height / height_pt
        px_top = (height_pt - top_pt) * scale_y  # bottom-up -> top-down
        margin = self.avail_height_px // 4
        self.scroll = max(0, min(self.scroll_max, round(px_top) - margin))

    def reload(self):
        """Re-read the PDF from disk (e.g. -F/--follow noticed it changed
        underneath us) and redraw, staying on the same page number and
        in the same mode. The rasterized-page cache and search index are
        both keyed off content that's now stale, so both get dropped;
        any in-progress search is cleared too, since its match list may
        no longer correspond to anything in the new file."""
        if self.is_pdf:
            self.npages = self.doc_handler.page_count()
            self.page = max(1, min(self.npages, self.page))
        elif isinstance(self.doc_handler, OfficeDocument):
            # Unlike a PDF, an office-preview's pages are pre-rendered
            # PNGs on disk (see OfficeDocument._render_office_pages()) rather than
            # generated on demand - those need regenerating too, not
            # just dropping from the cache, or a changed file would just
            # redisplay the same stale pages.
            pages = self.doc_handler.build_pages(
                self.tmpdir,
                debug=self.debug, render_scale=self.office_render_scale,
                progress=_ViewerProgress(self), continuous=self.office_continuous,
            )
            if pages:
                # build_pages() already updated self.doc_handler.pages
                # (see OfficeDocument._render_and_remember()) - just
                # self.cache.clear() below is needed to drop any now-stale
                # resized/cached images.
                self.npages = len(pages)
                self.page = max(1, min(self.npages, self.page))
        self.cache.clear()
        self._search_index = None
        self.clear_search()
        if self.text_mode:
            self._load_text_page()
        else:
            self._load_page()
        self.refresh()
        self.draw_status(f"reloaded (file changed) - page {self.page}/{self.npages}")

    def clear_search(self):
        self.search_query = None
        self.search_matches = []
        self.search_pos = None

    @staticmethod
    def _match_index_from(positions, here, backward):
        """Which of the matches a search should land on, given where it
        started from. `positions` is every match's position in ascending
        order, in whatever unit `here` is in (a page number, or a raw
        text_lines index); the answer is an index into it.

        Forward ("/"), that's the first match at or after `here`;
        backward ("?"), the last one strictly before it - so "?" can
        never move you forward, while "/" can leave you where you are if
        a match is already on screen. Either way it wraps around the
        ends of the document less(1)-style: a backward search from
        before the first match lands on the last one, a forward search
        from past the last one lands on the first."""
        if backward:
            for i in range(len(positions) - 1, -1, -1):
                if positions[i] < here:
                    return i
            return len(positions) - 1
        for i, pos in enumerate(positions):
            if pos >= here:
                return i
        return 0

    def _search_uses_text_lines(self):
        """Whether / search should walk self.text_lines as one blob
        (line_idx, start, end) matches rather than a PDF page/bbox
        index. True for plain text files (always in text mode) and for
        handlers like MarkdownDocument whose text mode shows the whole
        raw source at once - but False in image mode even for those,
        where a real PDF delegate's bbox index should still be used."""
        return self.text_mode and not self.doc_handler.text_mode_is_paginated()

    def start_search(self, query, backward=False):
        """Search the whole document for `query` and jump to one match -
        which one depends on where you are now and on `backward`, i.e.
        on whether the prompt was opened with "?" rather than "/" (see
        _match_index_from()). N/P walk every match from there on,
        regardless of the direction this started in."""
        if not query:
            return
        self.search_query = query
        if self._search_uses_text_lines():
            # No page/bbox structure for a non-paginated document
            # (plain text/RTF, or Markdown currently in text mode) -
            # matches are just (line_idx, start, end) straight out of
            # text_lines, the whole document's text.
            self.search_matches = self._find_all_text_matches()
            if not self.search_matches:
                self.search_pos = None
                self.draw_status(f'"{query}" not found')
                return
            # Positions are raw line indices, so "here" has to be one
            # too - text_scroll itself counts display rows while the
            # text is wrapped (see _top_text_line()).
            self._goto_search_match(self._match_index_from(
                [m[0] for m in self.search_matches], self._top_text_line(), backward,
            ))
            return

        if self._search_index is None:
            self.draw_status("building search index...")
            self._search_index = self.doc_handler.build_search_index()
        self.search_matches = self.doc_handler.find_search_matches(self._search_index, query)
        if not self.search_matches:
            self.search_pos = None
            self.draw_status(f'"{query}" not found')
            return
        # A paginated document's matches are only ordered down to the
        # page they're on, so that's the unit the starting point is
        # measured in too.
        self._goto_search_match(self._match_index_from(
            [m[0] for m in self.search_matches], self.page, backward,
        ))

    def repeat_search(self, forward):
        if not self.search_matches:
            msg = (
                f'"{self.search_query}" not found'
                if self.search_query
                else "no previous search pattern"
            )
            self.draw_status(msg)
            return
        if self.search_pos is None:
            self.search_pos = 0
        else:
            step = 1 if forward else -1
            next_pos = self.search_pos + step
            if not (0 <= next_pos < len(self.search_matches)):
                # No wraparound - N past the last match / P before the
                # first one just reports there's nowhere further to go,
                # the way less(1)'s own (non-wrapping) search does.
                self.draw_status(
                    f'"{self.search_query}" no more matches '
                    + ("forward" if forward else "backward")
                )
                return
            self.search_pos = next_pos
        self._goto_search_match(self.search_pos)

    def _goto_search_match(self, idx):
        self.search_pos = idx

        if self._search_uses_text_lines():
            line_idx, start, end = self.search_matches[idx]
            if self.text_wrap:
                # No pan to speak of while wrapped - _row_for_line()
                # converts the raw line position into a display-row
                # scroll target instead (same as _scroll_text_to_match()).
                target_row = self._row_for_line(line_idx)
            else:
                avail_cols = max(1, self._text_avail_cols() - self._line_number_gutter_width())
                line = self.text_lines[line_idx]
                col_start = display_width(line[:start])
                col_end = display_width(line[:end])
                if col_start < self.text_x_offset or col_end > self.text_x_offset + avail_cols:
                    self.text_x_offset = max(
                        self.text_x_offset_min,
                        min(
                            self.text_x_offset_max,
                            round((col_start + col_end) / 2 - avail_cols / 2),
                        ),
                    )
                target_row = line_idx
            avail_rows = self._text_avail_rows()
            margin = avail_rows // 4
            self.text_scroll = max(
                self.text_scroll_min, min(self.text_scroll_max, target_row - margin)
            )
            self.refresh()
            self.draw_status(
                f'"{self.search_query}" match {idx + 1}/{len(self.search_matches)}'
            )
            return

        page = self.search_matches[idx][0]

        if self.text_mode:
            self.go_to_page_text(page, 0)
        else:
            self.go_page(page, 0)

        # self.page == page now, so this is the match we just landed on;
        # _draw()/_draw_text() will independently rediscover and render
        # it (marker box or text highlight) on every redraw from here on,
        # including a later `t` mode toggle - see _active_search_page_match().
        match = self._active_search_page_match()
        if self.text_mode:
            self._scroll_text_to_match(match)
        else:
            self._scroll_image_to_match(match)

        self.refresh()
        self.draw_status(
            f'"{self.search_query}" match {idx + 1}/{len(self.search_matches)} '
            f"(page {self.page})"
        )

    def _match_marker_bounds(self, px_left, px_top, px_right, px_bottom):
        """Screen-cell bounds for a search-match box, or None if off-screen."""
        available_rows = max(1, self.rows - 1)  # bottom row is the status bar

        col0 = (px_left - self.x_offset) // self.cell_w_px
        col1 = -(-(px_right - self.x_offset) // self.cell_w_px) - 1  # ceil - 1
        row0 = (px_top - self.scroll) // self.cell_h_px
        row1 = -(-(px_bottom - self.scroll) // self.cell_h_px) - 1

        col0, col1 = col0 - 1, col1 + 1  # border sits one cell outside the text
        row0, row1 = row0 - 1, row1 + 1

        col0, col1 = max(0, int(col0)), min(self.cols - 1, int(col1))
        row0, row1 = max(0, int(row0)), min(available_rows - 1, int(row1))
        if col0 > col1 or row0 > row1:
            return None
        return row0, col0, row1, col1

    def _format_marker_erase(self, row0, col0, row1, col1):
        """Wipe a previously drawn search-match box without clearing the screen."""
        width = col1 - col0 + 1
        out = [SEARCH_MARKER_RESET]
        for row in range(row0, row1 + 1):
            out.append(f"\x1b[{row + 1};{col0 + 1}H\x1b[{width}X")
        return "".join(out)

    def _format_marker_at_bounds(self, row0, col0, row1, col1):
        """Return escape sequence for a search-match box overlay."""
        width = col1 - col0 + 1
        out = [SEARCH_MARKER_COLOR, f"\x1b[{row0 + 1};{col0 + 1}H┏{'━' * (width - 2)}┓"]
        for row in range(row0 + 1, row1):
            out.append(f"\x1b[{row + 1};{col0 + 1}H┃")
            out.append(f"\x1b[{row + 1};{col1 + 1}H┃")
        if row1 > row0:
            out.append(f"\x1b[{row1 + 1};{col0 + 1}H┗{'━' * (width - 2)}┛")
        out.append(SEARCH_MARKER_RESET)
        return "".join(out)

    def _half_page_step(self):
        """"d"/"u"'s step size: half a screenful, rounded to a whole
        number of terminal rows rather than avail_height_px // 2 (which
        can land mid-row when the row count is odd). Keeping it a clean
        multiple of cell_h_px is also what lets _scroll_shift_rows()
        treat a "d"/"u" press the same as any other scroll - otherwise
        it'd fall back to a full redraw exactly on terminals with an
        odd number of rows, for no reason a user could see."""
        half_rows = max(1, (self.rows - 1) // 2)
        return self.cell_h_px * half_rows

    def scroll_down(self, step):
        if self.scroll < self.scroll_max:
            self.scroll = min(self.scroll_max, self.scroll + step)
        elif self.page < self.npages:
            self.go_page(self.page + 1, 0)

    def scroll_up(self, step):
        if self.scroll > 0:
            self.scroll = max(0, self.scroll - step)
        elif self.page > 1:
            self.go_page(self.page - 1, None)
            self.scroll = self.scroll_max

    def handle_key_text(self, key):
        """Key handling while in text mode: page/line navigation plus
        horizontal pan (for lines too wide for the terminal) - no
        zoom/fit, since there's no image here to resize."""
        avail_rows = self._text_avail_rows()
        if key == "B":
            # The border is opt-in precisely because its border
            # characters would get swept up in a terminal select-and-
            # copy, so it needs its own key - uppercase since lowercase
            # "b" is already BACKWARD_WINDOW_KEYS.
            self.toggle_text_border()
        elif key == "E":
            # Same idea as "B" above - uppercase, since lowercase "e"
            # is already FORWARD_LINE_KEYS (and stays that way here).
            self.toggle_eol_mark()
        elif key == "s":
            # The primary way to toggle wrap - "-S" (see run_viewer()'s
            # dash_pending) is kept only for less(1) compatibility.
            self.toggle_text_wrap()
        elif key == "C":
            self.toggle_copy_mode()
        elif key == "#":
            # "N"/"n" are both already taken (next search match, next
            # page) - "-N"/"-n" (see run_viewer()'s dash_pending, kept
            # for less(1) compatibility) still work, but "#" is the
            # primary key for this one.
            self.toggle_line_numbers()
        elif key in FORWARD_WINDOW_KEYS:
            self.text_scroll_down(avail_rows)
        elif key in BACKWARD_WINDOW_KEYS:
            self.text_scroll_up(avail_rows)
        elif key in ("d", "\x04"):
            self.text_scroll_down(avail_rows // 2)
        elif key in ("u", "\x15"):
            self.text_scroll_up(avail_rows // 2)
        elif key in FORWARD_LINE_KEYS:
            self.text_scroll_down(1)
        elif key in BACKWARD_LINE_KEYS:
            self.text_scroll_up(1)
        elif key in ("h", "LEFT"):
            self.text_x_offset = max(
                self.text_x_offset_min, self.text_x_offset - PAN_STEP_CELLS
            )
        elif key in ("l", "RIGHT"):
            self.text_x_offset = min(
                self.text_x_offset_max, self.text_x_offset + PAN_STEP_CELLS
            )
        elif key in ("H", "SHIFT-LEFT"):
            self.text_x_offset = self.text_x_offset_min
        elif key in ("L", "SHIFT-RIGHT"):
            self.text_x_offset = self.text_x_offset_max
        elif key in ("K", "U", "SHIFT-UP", "g"):
            self.text_scroll = self.text_scroll_min
        elif key in ("J", "D", "SHIFT-DOWN", "G"):
            self.text_scroll = self.text_scroll_max
        elif key == "n":
            # A handler whose text isn't paginated (office/text/rtf -
            # see _load_text_page()) shows the whole document at once,
            # not one page/slide at a time - nothing for "next" to do.
            if self.doc_handler.text_mode_is_paginated() and self.page < self.npages:
                self.go_to_page_text(self.page + 1, 0)
        elif key == "p":
            if self.doc_handler.text_mode_is_paginated() and self.page > 1:
                self.go_to_page_text(self.page - 1, 0)
        elif key == "q":
            return False
        return True

    def handle_key(self, key):
        if self.text_mode:
            return self.handle_key_text(key)
        if key in FORWARD_WINDOW_KEYS:
            self.scroll_down(self.avail_height_px)
        elif key in BACKWARD_WINDOW_KEYS:
            self.scroll_up(self.avail_height_px)
        elif key in ("d", "\x04"):
            self.scroll_down(self._half_page_step())
        elif key in ("u", "\x15"):
            self.scroll_up(self._half_page_step())
        elif key in FORWARD_LINE_KEYS:
            self.scroll_down(self.cell_h_px)
        elif key in BACKWARD_LINE_KEYS:
            self.scroll_up(self.cell_h_px)
        elif key in ("+", "="):
            self.set_zoom(self.zoom * ZOOM_STEP)
        elif key == "-":
            self.set_zoom(self.zoom / ZOOM_STEP)
        elif key == "0":
            self.reset_view()
        elif key == "m":
            self.set_fit("height")
        elif key == "M":
            self.set_fit("width")
        elif key in ("h", "LEFT"):
            self.pan(-max(1, self.cell_w_px * PAN_STEP_CELLS))
        elif key in ("l", "RIGHT"):
            self.pan(max(1, self.cell_w_px * PAN_STEP_CELLS))
        elif key in ("H", "SHIFT-LEFT"):
            self.x_offset = 0
        elif key in ("L", "SHIFT-RIGHT"):
            self.x_offset = max(0, self.img.width - self.crop_width)
        elif key in ("K", "U", "SHIFT-UP", "g"):
            self.scroll = 0
        elif key in ("J", "D", "SHIFT-DOWN", "G"):
            self.scroll = self.scroll_max
        elif key == "n":
            if self.page < self.npages:
                self.go_page(self.page + 1, 0)
        elif key == "p":
            if self.page > 1:
                self.go_page(self.page - 1, 0)
        elif key == "[":
            self.go_back()
        elif key == "]":
            self.go_forward()
        elif key == "q":
            return False
        return True


def run_viewer(
    files, start_file_index, start_page, tmpdir, fd, old_termios, fit="width",
    border=True, wrap=True, eol_mark=True, line_numbers=False, scrollbar=True,
    follow=False, wheel_scroll_step=2, keep=False, incremental_scroll=True,
    debug=False, office_render_scale=OFFICE_RENDER_SCALE,
    office_continuous=False,
):
    """Run the interactive viewer loop. Returns the Viewer instance so the
    caller can inspect its final geometry (e.g. to tidy up the screen)."""
    viewer = Viewer(
        files, start_file_index, start_page, tmpdir, fd, fit=fit,
        border=border, wrap=wrap, eol_mark=eol_mark, line_numbers=line_numbers,
        scrollbar=scrollbar, wheel_scroll_step=wheel_scroll_step,
        incremental_scroll=incremental_scroll,
        debug=debug,
        office_render_scale=office_render_scale, office_continuous=office_continuous,
        follow=follow,
    )

    def on_winch(signum, frame):
        viewer.request_resize()

    signal.signal(signal.SIGWINCH, on_winch)

    num_buf = ""
    search_buf = None  # None: not typing; otherwise the query in progress
    search_cursor = 0  # index into search_buf the next inserted/deleted
    # character applies at - only meaningful while search_buf is not None
    search_backward = False  # whether that query was opened with "?" (not "/")
    last_search_query = None  # remembered across searches, for a bare "/"/"?"
    colon_pending = False  # True right after ":", awaiting n/p/h
    dash_pending = False  # True right after "-" in text mode, awaiting "S"

    last_follow_path = viewer.path
    try:
        last_mtime = os.path.getmtime(last_follow_path) if follow else None
    except OSError:
        last_mtime = None
    last_follow_check = time.monotonic()

    def start_following():
        """(Re)start follow's mtime tracking from the current file/time -
        shared by "F" turning follow on and "O"/"v" doing the same as a
        side effect of handing the file to an external app. Otherwise a
        change that happened while follow was off (a stale last_mtime)
        would trigger an immediate reload the moment it's turned on."""
        nonlocal last_follow_path, last_mtime, last_follow_check
        last_follow_path = viewer.path
        try:
            last_mtime = os.path.getmtime(last_follow_path)
        except OSError:
            last_mtime = None
        last_follow_check = time.monotonic()

    viewer.refresh()
    while True:
        r, _, _ = select.select([fd], [], [], 0.3)

        if follow and viewer.path != last_follow_path:
            # :n/:p switched to a different file - start tracking that
            # one instead, rather than comparing its mtime against
            # whatever the previous file's was.
            last_follow_path = viewer.path
            try:
                last_mtime = os.path.getmtime(last_follow_path)
            except OSError:
                last_mtime = None
            last_follow_check = time.monotonic()
        elif follow and time.monotonic() - last_follow_check >= FOLLOW_INTERVAL:
            last_follow_check = time.monotonic()
            try:
                mtime = os.path.getmtime(last_follow_path)
            except OSError:
                mtime = None  # e.g. mid save-as-replace; try again next tick
            if mtime is not None and mtime != last_mtime:
                last_mtime = mtime
                try:
                    viewer.reload()
                except Exception:
                    # The file may have been mid-write when we noticed the
                    # mtime change (e.g. pdftoppm/pdfinfo saw a truncated
                    # file); keep showing the last good render and pick
                    # up the change on a later, now-complete write.
                    pass

        if viewer.resized:
            viewer.refresh()
            continue
        if not r:
            # Nothing waiting - a good moment to act on a scrollbar drag
            # whose motion events stopped without a release arriving
            # (see the MOUSE_DRAG handling below); a no-op otherwise.
            viewer.flush_scrollbar_drag()
            continue
        key = read_utf8_char(fd)
        if key is None:
            break
        if key == "\x1b":
            # Possibly ESC-v (Meta-v, "backward one window"), an SS3
            # sequence (F1), or a CSI one (arrow/Home/End/PageUp/
            # PageDown, plain or Shift-ed; F1 on some terminals).
            r2, _, _ = select.select([fd], [], [], 0.1)
            if r2:
                nxt = os.read(fd, 1)
                if nxt == b"v":
                    key = "ESC-v"
                elif nxt == b"O":
                    key = read_ss3_key(fd) or ""
                elif nxt == b"[":
                    seq = read_csi_sequence(fd)
                    mouse = decode_sgr_mouse(seq) if seq else None
                    if mouse:
                        kind, mcol, mrow = mouse
                        if search_buf is None:
                            if viewer.help_active:
                                if kind == "MOUSE_WHEEL_UP":
                                    viewer.scroll_help(-1)
                                elif kind == "MOUSE_WHEEL_DOWN":
                                    viewer.scroll_help(1)
                            elif kind == "MOUSE_CLICK":
                                viewer.handle_click(mcol, mrow)
                            elif kind == "MOUSE_DRAG":
                                if viewer.handle_drag(mrow):
                                    # A drag arrives as a burst of motion
                                    # events, and acting on one costs a
                                    # page rasterize - so let the burst
                                    # drain first and only act on where
                                    # the pointer actually ended up.
                                    ready, _, _ = select.select([fd], [], [], 0)
                                    if not ready:
                                        viewer.flush_scrollbar_drag()
                            elif kind == "MOUSE_RELEASE":
                                viewer.end_scrollbar_drag()
                            elif kind == "MOUSE_WHEEL_UP":
                                viewer.handle_wheel(-1)
                            elif kind == "MOUSE_WHEEL_DOWN":
                                viewer.handle_wheel(1)
                            elif kind == "MOUSE_BACK":
                                viewer.go_back()
                            elif kind == "MOUSE_FORWARD":
                                viewer.go_forward()
                        continue
                    key = decode_csi_key(seq) or ""

        if key == "\x1a":
            # ^Z: suspend, like a normal shell job-control app would -
            # raw mode disables the tty's own ^Z-to-SIGTSTP translation
            # (see RawTerminal), so this does it by hand: leave the
            # mouse modes and cooked-mode the tty before actually
            # stopping, then reverse all of that once `fg` resumes us.
            # Takes priority over everything else (even typing a search
            # query), same as a real terminal's ^Z would.
            #
            # --keep leaves the alternate screen buffer alone (no
            # \x1b[?1049l) so the page stays on screen while suspended,
            # the same trick main() uses to leave it up after quitting;
            # otherwise leave the alternate screen like normal, so the
            # shell prompt lands on the real scrollback instead.
            leave_screen = "" if keep else "\x1b[?1049l"
            sys.stdout.write(MOUSE_OFF + ALT_SCROLL_OFF + FOCUS_OFF + "\x1b[?25h" + leave_screen)
            sys.stdout.flush()
            termios.tcsetattr(fd, termios.TCSADRAIN, old_termios)
            # SIGSTOP rather than SIGTSTP: the cleanup above already does
            # everything SIGTSTP's catchability would be for, so there's
            # no downside to using the one stop signal that's guaranteed
            # to actually stop the process - it can't be caught, blocked,
            # or ignored, unlike SIGTSTP (which, at least on some
            # setups, can silently fail to stop it on the first try).
            # Sent to the whole process group (pid 0), not just our own
            # pid: when launched via `uv run --script` (its shebang),
            # this process is a *child* of uv, which is what the shell
            # actually sees as the foreground job - stopping only
            # ourselves would leave uv running and still attached to the
            # tty, so the shell would never notice anything stopped.
            os.kill(0, signal.SIGSTOP)
            # ... stopped here until `fg` sends SIGCONT ...
            tty.setraw(fd)
            enter_screen = "" if keep else "\x1b[?1049h"
            sys.stdout.write(
                enter_screen + "\x1b[?25l" + ALT_SCROLL_ON + FOCUS_ON
                + ("" if viewer.text_mode else MOUSE_ON)
            )
            sys.stdout.flush()
            viewer.request_resize()  # the terminal may have been resized
            # while stopped, and its contents are gone either way
            continue

        if search_buf is not None:
            # Typing a search pattern after "/" or "?": collect
            # characters until Enter confirms it, Esc/^C cancels,
            # backspace edits it (or also cancels, if the pattern is
            # already empty), ^B/^F/LEFT/RIGHT move search_cursor within
            # it, ^A/^E/HOME/END jump it to the start/end, ^D deletes the
            # character under search_cursor, and ^U/^K kill from
            # search_cursor to the start/end - readline's own bindings
            # for these. Every other key is swallowed so it can't leak
            # through as a page command while the prompt is up.
            if key in ("\r", "\n"):
                query = search_buf or last_search_query
                search_buf = None
                if query:
                    last_search_query = query
                    viewer.start_search(query, backward=search_backward)
                else:
                    viewer.draw_status()
            elif key in ("\x1b", "\x03"):
                search_buf = None
                viewer.draw_status()
            elif key in ("\x7f", "\x08"):
                if search_cursor > 0:
                    search_buf = search_buf[:search_cursor - 1] + search_buf[search_cursor:]
                    search_cursor -= 1
                    viewer.draw_search_prompt(search_buf, search_cursor, backward=search_backward)
                elif not search_buf:
                    search_buf = None
                    viewer.draw_status()
            elif key in ("\x02", "LEFT"):  # ^B
                if search_cursor > 0:
                    search_cursor -= 1
                    viewer.draw_search_prompt(search_buf, search_cursor, backward=search_backward)
            elif key in ("\x06", "RIGHT"):  # ^F
                if search_cursor < len(search_buf):
                    search_cursor += 1
                    viewer.draw_search_prompt(search_buf, search_cursor, backward=search_backward)
            elif key in ("\x01", "HOME"):  # ^A: jump to the start
                if search_cursor > 0:
                    search_cursor = 0
                    viewer.draw_search_prompt(search_buf, search_cursor, backward=search_backward)
            elif key in ("\x05", "END"):  # ^E: jump to the end
                if search_cursor < len(search_buf):
                    search_cursor = len(search_buf)
                    viewer.draw_search_prompt(search_buf, search_cursor, backward=search_backward)
            elif key == "\x04":  # ^D: delete the character under search_cursor
                if search_cursor < len(search_buf):
                    search_buf = search_buf[:search_cursor] + search_buf[search_cursor + 1:]
                    viewer.draw_search_prompt(search_buf, search_cursor, backward=search_backward)
            elif key == "\x15":  # ^U: kill from search_cursor to the start
                if search_cursor > 0:
                    search_buf = search_buf[search_cursor:]
                    search_cursor = 0
                    viewer.draw_search_prompt(search_buf, search_cursor, backward=search_backward)
            elif key == "\x0b":  # ^K: kill from search_cursor to the end
                if search_cursor < len(search_buf):
                    search_buf = search_buf[:search_cursor]
                    viewer.draw_search_prompt(search_buf, search_cursor, backward=search_backward)
            elif len(key) == 1 and key.isprintable():
                search_buf = search_buf[:search_cursor] + key + search_buf[search_cursor:]
                search_cursor += 1
                viewer.draw_search_prompt(search_buf, search_cursor, backward=search_backward)
            continue

        if colon_pending:
            # ":" was just pressed - less(1)'s :n/:p, next/previous file
            # (only meaningful with more than one file on the command
            # line; harmless otherwise, since go_to_file() just reports
            # there's nowhere to go), :q to quit, plus pdfless's own ":h"
            # for the help screen. Any other key cancels quietly.
            colon_pending = False
            if key == "n":
                viewer.next_file()
            elif key == "p":
                viewer.previous_file()
            elif key == "h":
                viewer.show_help()  # the spelt-out way in; F1 is primary
            elif key == "q":
                break  # less(1)'s ":q" - same as the plain "q" quit key
            else:
                viewer.draw_status()
            continue

        if dash_pending:
            # "-" was just pressed in text mode - less(1)'s own runtime
            # "-<option-letter>" toggle syntax, kept only for
            # -S/--chop-long-lines and -N/--line-numbers compatibility
            # with less(1); "s"/"#" alone (see handle_key_text()) are the
            # primary ways to toggle wrap/line-numbers. eol-mark and the
            # border have no dash-toggle of their own - just "E"/"B".
            # Any other key cancels quietly.
            dash_pending = False
            if key in ("S", "s"):
                viewer.toggle_text_wrap()
                viewer.refresh()
            elif key in ("N", "n"):
                viewer.toggle_line_numbers()
                viewer.refresh()
            else:
                viewer.draw_status()
            continue

        if key == "\x03":
            break

        if viewer.help_active:
            # While the help screen is up, only "q"/F1 and the scroll
            # keys (for when KEY_TABLE is taller than the box) do
            # anything. Everything else is swallowed so page keys can't
            # leak through underneath it.
            if key in ("q", "F1"):
                viewer.hide_help()
            elif key in FORWARD_LINE_KEYS:
                viewer.scroll_help(1)
            elif key in BACKWARD_LINE_KEYS:
                viewer.scroll_help(-1)
            elif key in FORWARD_WINDOW_KEYS:
                viewer.scroll_help(max(1, viewer.rows - 3))
            elif key in BACKWARD_WINDOW_KEYS:
                viewer.scroll_help(-max(1, viewer.rows - 3))
            continue

        if key == "\x0c":  # ^L: repaint the screen (e.g. after other
            # output has garbled it), without otherwise changing anything
            viewer.refresh()
            continue

        if key == "FOCUS_IN":
            # Same fix as ^L, triggered automatically: see FOCUS_ON's
            # comment for why a focus change (under tmux, especially)
            # can otherwise leave this pane blank - and for why only
            # this direction, not FOCUS_OUT, is safe to redraw on.
            viewer.refresh()
            continue
        if key == "FOCUS_OUT":
            continue

        if key == "r":
            # Applies in both image and text mode (see
            # Viewer.toggle_scrollbar()), so handled here at the top
            # level rather than inside handle_key()/handle_key_text().
            viewer.toggle_scrollbar()
            viewer.refresh()
            continue

        if key == "F":
            # Same -F/--follow behavior as the command-line flag, toggled
            # at runtime; applies in both image and text mode, so handled
            # here rather than inside handle_key()/handle_key_text().
            follow = not follow
            viewer.follow = follow
            if follow:
                start_following()
            viewer.refresh()
            continue

        if key in ("O", "v"):
            # Hand the current file off to macOS's own default app for
            # it (Preview/Word/Excel/...), and switch follow mode on (if
            # it wasn't already) so an edit made there comes back
            # automatically - the same reload path -F/--follow and "F"
            # already use. viewer.path is always the original file (see
            # DocumentHandler.__init__/Viewer.path), never a temporary
            # rendered PDF, so this opens the same thing the user
            # pointed pdfless at in the first place, even for a
            # soffice/Chrome-rendered format.
            if not _open_in_default_app(viewer.path):
                viewer.draw_status(
                    "opening the file in its own app needs macOS"
                    if sys.platform != "darwin" else f"couldn't open {viewer.path}"
                )
                continue
            if not follow:
                follow = True
                viewer.follow = True
                start_following()
            viewer.refresh()
            continue

        if key == "F1":
            # less(1) puts its help on "h"/"H", which pdfless can't -
            # both are panning keys here (less has nothing to pan). "?"
            # isn't free either, being less's backward search, so help
            # lives on F1, with ":h" as a second way in for terminals
            # that send something unexpected for F1.
            viewer.show_help()
            continue

        if key == ":":
            colon_pending = True
            viewer.draw_status(":")
            continue

        if key == "-" and viewer.text_mode:
            # In image mode, "-" already means zoom out (see
            # Viewer.handle_key()) - only text mode gets the
            # less(1)-style "-S" toggle.
            dash_pending = True
            viewer.draw_status("-")
            continue

        if key == "t":
            if viewer.doc_handler.starts_in_text_mode():
                # Always-on text mode already - toggling would try to
                # switch to an image view this kind doesn't have.
                viewer.draw_status("this is already a plain text file")
            elif viewer.doc_handler.supports_text_mode():
                if not viewer.toggle_text_mode():
                    viewer.draw_status("no text could be extracted from this file")
            else:
                viewer.draw_status("text mode isn't available for this file type")
            continue

        if key == "T":
            # t and C combined into one press/undo - see
            # Viewer.toggle_clean_text_mode(). Same eligibility checks
            # as "t" above; there's no separate image view to enter for
            # a kind that's always in text mode, so this is a no-op
            # there too.
            if viewer.doc_handler.starts_in_text_mode():
                viewer.draw_status("this is already a plain text file")
            elif viewer.doc_handler.supports_text_mode():
                if not viewer.toggle_clean_text_mode():
                    viewer.draw_status("no text could be extracted from this file")
            else:
                viewer.draw_status("text mode isn't available for this file type")
            continue

        if key in ("/", "?"):
            # less(1)'s pair: "/" searches forward from here, "?"
            # backward. Either way the whole document is searched and
            # N/P then walk every match - the direction only decides
            # which match this search lands on first (see
            # Viewer._match_index_from()).
            #
            # Search always works in text mode (there's always a flat
            # list of lines to search, self.text_lines) regardless of
            # what the underlying file kind otherwise supports in image
            # mode (doc_handler.supports_search() - currently PDF only,
            # via its own page/bbox index).
            if viewer.text_mode or viewer.doc_handler.supports_search():
                search_buf = ""
                search_cursor = 0
                search_backward = key == "?"
                viewer.draw_search_prompt(search_buf, search_cursor, backward=search_backward)
            else:
                viewer.draw_status("search isn't available for this file type")
            continue

        if viewer.search_query is not None:
            if key in ("n", "N"):
                viewer.repeat_search(forward=True)
                continue
            if key in ("p", "P"):
                viewer.repeat_search(forward=False)
                continue

        if key in ("q", "\x1b") and viewer.search_query is not None:
            # With a search active, "q"/Esc dismiss it (removing the
            # match box/highlight and its status line) rather than
            # quitting pdfless outright - quit still works normally on
            # a second press, once there's no longer a search to clear.
            viewer.clear_search()
            viewer.refresh()
            continue

        # A lone "0" (no pending page number) resets the zoom/pan instead
        # of starting a number entry.
        if key.isdigit() and not (key == "0" and not num_buf):
            num_buf += key
            viewer.draw_status(f"number: {num_buf}")
            continue

        if key in ("g", "G") and num_buf:
            # "<number>g"/"<number>G": in text mode, jump straight to
            # that line of the current page's text (a new capability -
            # there's no page-image equivalent of "line", so the count
            # is simply ignored there and this falls through to plain
            # g/G below: jump to the top/bottom of the current page).
            if viewer.text_mode:
                viewer.go_to_text_line(int(num_buf))
                num_buf = ""
                viewer.refresh()
                continue
            num_buf = ""

        if key in ("<", ">", "HOME", "END"):
            # "<"/">" (HOME/END are aliases): jump to the first/last
            # page of the whole document - "<number><" or "<number>>"
            # jumps straight to that page instead, in either mode.
            first = key in ("<", "HOME")
            if num_buf:
                target = int(num_buf)
                num_buf = ""
                if viewer.text_mode:
                    viewer.go_to_page_text(target, 0)
                else:
                    viewer.go_page(target, 0)
            elif viewer.text_mode:
                if first:
                    viewer.go_to_page_text(1, 0)
                else:
                    viewer.go_to_page_text(viewer.npages, None)
            else:
                if first:
                    viewer.go_page(1, 0)
                else:
                    viewer.go_page(viewer.npages, None)
                    viewer.scroll = viewer.scroll_max
            viewer.refresh()
            continue

        if key == "x":
            # "x" jumps to the first file in the list; "<number>x" jumps
            # straight to that file (1-based, matching "<number><"'s
            # page numbering) - meaningful only with more than one file,
            # but harmless otherwise (go_to_file() just reports there's
            # nowhere to go).
            target = int(num_buf) - 1 if num_buf else 0
            num_buf = ""
            viewer.go_to_file(target, "no such file")
            continue

        if key == "X":
            # "X" jumps to the last file in the list, mirroring "x" for
            # the first.
            num_buf = ""
            viewer.go_to_file(len(viewer.files) - 1, "no such file")
            continue

        if num_buf:
            # Any other key cancels a pending page number.
            num_buf = ""
            viewer.draw_status()

        border_before = viewer.text_border
        before = (
            viewer.page, viewer.scroll, viewer.zoom, viewer.x_offset, viewer.fit,
            viewer.text_mode, viewer.text_scroll, viewer.text_x_offset, viewer.text_border,
            viewer.text_wrap, viewer.eol_mark, viewer.line_numbers, viewer.scrollbar,
        )
        if not viewer.handle_key(key):
            break
        after = (
            viewer.page, viewer.scroll, viewer.zoom, viewer.x_offset, viewer.fit,
            viewer.text_mode, viewer.text_scroll, viewer.text_x_offset, viewer.text_border,
            viewer.text_wrap, viewer.eol_mark, viewer.line_numbers, viewer.scrollbar,
        )
        if after != before:
            viewer.refresh()
            if viewer.text_border != border_before and viewer.text_wrap:
                # "B" toggled text_border, but _draw_text_wrapped() never
                # draws a border regardless of it - without this, B looks
                # like it does nothing at all while wrapped.
                viewer.draw_status("no border while wrapped - see -S/-s")

    return viewer


def main():
    parser = argparse.ArgumentParser(
        prog="pdfless",
        description=(
            "Display a PDF, image, text, or (macOS only, needs a local "
            "Chrome) Quick-Look-previewable file (Word, Excel, "
            "PowerPoint, ...) in iTerm2 or WezTerm, less(1)-style."
        ),
        epilog=KEY_TABLE,
        formatter_class=argparse.RawDescriptionHelpFormatter,
        add_help=False,
    )
    parser.add_argument(
        "--help", action="help", help="show this help message and exit"
    )
    parser.add_argument(
        "-v", "--version", action="version", version=f"%(prog)s {__version__}"
    )
    parser.add_argument(
        "files", nargs="*", metavar="file",
        help="path to one or more PDF, image, text, or Quick-Look-"
             "previewable files - reads from stdin instead if none are "
             "given (or if \"-\" is given in their place), so pdfless "
             "can also be used as $PAGER",
    )
    parser.add_argument(
        "-p", "--page", type=int, default=1,
        help="page to start on, in the first file (default: 1)",
    )
    parser.add_argument(
        "-d", "--debug",
        action="store_true",
        help="print timing for each stage of Quick Look preview "
             "rendering (qlmanage, pdftocairo, measuring, rendering, "
             "splitting into pages) to stderr",
    )
    parser.add_argument(
        "-s", "--rendering-scale", type=float, default=OFFICE_RENDER_SCALE, metavar="N",
        help="device-pixel-ratio to render Quick Look preview files "
             "(Excel/PowerPoint/Keynote/Pages/etc., macOS only) at - higher "
             "looks sharper when zoomed in but is slower to render (default: "
             "%(default)s). No effect on Word/RTF, which render to a "
             "real PDF instead and are always sharp regardless of zoom",
    )
    parser.add_argument(
        "-c", "--continuous",
        action="store_true",
        help="for a Quick Look preview file (macOS only), force continuous "
             "scrolling instead of paginating",
    )
    parser.add_argument(
        "-k", "--keep",
        action="store_true",
        help="leave the last page on screen when quitting (q or ^C) "
             "instead of restoring the terminal screen",
    )
    parser.add_argument(
        "-h", "--fit-height",
        action="store_true",
        help="fit each page to the terminal's full height instead of its "
             "full width (default: fit width)",
    )
    parser.add_argument(
        "-B", "--no-border",
        action="store_false",
        dest="border",
        default=True,
        help="don't draw a border around the page's edges in text mode "
             "(t); on by default (except for a plain text file, where "
             "it's off by default regardless of this), toggle any time "
             "with B",
    )
    parser.add_argument(
        "-S", "--chop-long-lines",
        action="store_true",
        help="in text mode, don't wrap long lines - pan across them "
             "instead with h/l/H/L, less(1)-style. Already the default "
             "for anything but a plain text file, which normally wraps; "
             "toggle any time by typing -S",
    )
    parser.add_argument(
        "-E", "--no-eol-mark",
        action="store_false",
        dest="eol_mark",
        default=True,
        help="don't mark a real end-of-line (↵) in text mode - shown "
             "by default (regardless of -S/--chop-long-lines) to tell a "
             "genuine line ending apart from where wrapping/panning "
             "simply ran out of room",
    )
    parser.add_argument(
        "-N", "--line-numbers",
        action="store_true",
        help="show line numbers in text mode, less(1)-style - off by "
             "default; toggle any time with # (or -N, kept for less(1) "
             "compatibility)",
    )
    parser.add_argument(
        "--no-scrollbar",
        action="store_false",
        dest="scrollbar",
        default=True,
        help="don't show the scrollbar (a column on the terminal's "
             "right edge marking your position) - shown by default, in "
             "both image and text mode; toggle any time with r",
    )
    parser.add_argument(
        "--no-incremental-scroll",
        action="store_false",
        dest="incremental_scroll",
        default=True,
        help="always redraw the full page image on scroll, instead of "
             "shifting the terminal's existing content and transmitting "
             "only the newly-exposed strip - a fallback for a terminal "
             "where that shortcut (iTerm2/WezTerm-only, and already off "
             "under tmux) doesn't render correctly",
    )
    parser.add_argument(
        "-F", "--follow",
        action="store_true",
        help="watch the file and reload it if it changes on disk "
             f"(checked every {FOLLOW_INTERVAL:.0f}s), staying on the "
             "same page and in the same mode; toggle any time with F",
    )
    parser.add_argument(
        "--wheel-scroll-step", type=positive_int, default=2, metavar="N",
        help="scroll N lines per mouse wheel step, in the page image "
             "(default: %(default)s)",
    )
    args = parser.parse_args()

    # Reading from stdin - no file given at all, or "-" given in its
    # place - lets pdfless work as $PAGER: git/man/etc. invoke $PAGER
    # with nothing but the piped content on stdin. Every
    # DocumentHandler.sniff() reads from a real path, not a stream, so
    # the whole pipe has to be drained into a file of its own first -
    # before stdin's fd gets reused for keyboard/mouse input, further
    # down (see "reading_stdin" again below).
    reading_stdin = not args.files or "-" in args.files
    if reading_stdin and sys.stdin.isatty():
        die("no file given, and stdin is a terminal - pipe something "
            "into pdfless, or name a file")

    tmpdir = tempfile.mkdtemp(prefix="pdfless.")
    tty_fd = None  # set below if reading_stdin - ours to close on the way out
    try:
        if reading_stdin:
            stdin_path = os.path.join(tmpdir, "stdin")
            with open(stdin_path, "wb") as f:
                shutil.copyfileobj(sys.stdin.buffer, f)
            # "-" (if given) stands for this same captured file; bare
            # `pdfless.py` with no file arguments at all means just it.
            args.files = [stdin_path if a == "-" else a for a in args.files] or [stdin_path]

        # Validate every file up front - each one is checked (existence,
        # type, and that it actually decodes) before the terminal ever goes
        # into raw/alternate-screen mode. An invalid file is skipped (with a
        # warning) rather than aborting the whole thing, so one bad path in
        # a big batch doesn't stop you from seeing the rest.
        candidates = []  # [abs_path, ...] - files that at least exist
        for arg in args.files:
            if not os.path.isfile(arg):
                print(f"pdfless: no such file, skipping: {arg}", file=sys.stderr)
                continue
            candidates.append(os.path.abspath(arg))
        if any(PdfDocument.is_pdf_file(path) for path in candidates):
            check_deps()

        files = []  # [DocumentHandler, ...], in the given order (each knows its own .path)
        for path in candidates:
            # Try each DocumentHandler subclass, in priority order, for
            # the first one whose sniff() claims this file - see
            # HANDLER_CLASSES. A raised UnusableFile means one of them
            # positively identified the format but couldn't actually use
            # it (e.g. corrupt PDF) - that's specific enough to report
            # and skip outright, rather than falling through to try
            # treating it as some other kind.
            handler = None
            try:
                for handler_cls in HANDLER_CLASSES:
                    handler = handler_cls.sniff(path, tmpdir, debug=args.debug)
                    if handler is not None:
                        break
            except UnusableFile as e:
                print(f"pdfless: {e}, skipping: {path}", file=sys.stderr)
                continue

            if handler is None:
                print(
                    f"pdfless: not a PDF, image, text, or Quick-Look-previewable "
                    f"file, skipping: {path}",
                    file=sys.stderr,
                )
                continue

            files.append(handler)

        if not files:
            die("no valid PDF, image, text, or Quick-Look-previewable files given")
        # A None page_count() (an office-kind first file) means its real
        # page count isn't known until Viewer.__init__ actually renders
        # it, which also clamps self.page against it then; here just
        # keep whatever page number was asked for (>= 1).
        first_npages = files[0].page_count()
        start_page = args.page if first_npages is None else min(first_npages, args.page)
        start_page = max(1, start_page)

        if not sys.stdout.isatty():
            die("stdout must be a terminal")
        if reading_stdin:
            # stdin's own fd was just drained above (or was never going
            # to be read again, for bare `pdfless.py`) - /dev/tty is the
            # real keyboard now, the same trick less(1)/most(1) use to
            # double as $PAGER.
            try:
                fd = tty_fd = os.open("/dev/tty", os.O_RDWR)
            except OSError as e:
                die(f"can't open /dev/tty for keyboard input: {e}")
        else:
            if not sys.stdin.isatty():
                die("stdin must be a terminal (or pipe something into "
                    "pdfless, or pass \"-\", to page it)")
            fd = sys.stdin.fileno()

        with RawTerminal(fd) as rt:
            # A text-kind first file starts straight in text mode (see
            # Viewer.__init__), where mouse reporting should be off, the
            # same as it would be for a PDF's `t` toggle.
            initial_mouse = MOUSE_OFF if files[0].starts_in_text_mode() else MOUSE_ON
            sys.stdout.write("\x1b[?1049h\x1b[?25l" + initial_mouse + ALT_SCROLL_ON + FOCUS_ON)
            sys.stdout.flush()
            viewer = None
            try:
                fit = "height" if args.fit_height else "width"
                viewer = run_viewer(
                    files, 0, start_page, tmpdir, fd, rt.old,
                    fit=fit, border=args.border, wrap=not args.chop_long_lines,
                    eol_mark=args.eol_mark, line_numbers=args.line_numbers,
                    scrollbar=args.scrollbar, follow=args.follow,
                    wheel_scroll_step=args.wheel_scroll_step, keep=args.keep,
                    incremental_scroll=args.incremental_scroll,
                    debug=args.debug,
                    office_render_scale=args.rendering_scale,
                    office_continuous=args.continuous,
                )
            finally:
                if args.keep and viewer is not None:
                    # Stay in the alternate screen buffer so the last
                    # rendered page remains visible; just clear the status
                    # line and bring the cursor back so the shell prompt
                    # lands cleanly below the image.
                    sys.stdout.write(
                        MOUSE_OFF + ALT_SCROLL_OFF + FOCUS_OFF
                        + f"\x1b[{viewer.rows};1H\x1b[2K\x1b[?25h"
                    )
                else:
                    sys.stdout.write(
                        MOUSE_OFF + ALT_SCROLL_OFF + FOCUS_OFF + "\x1b[?25h\x1b[?1049l"
                    )
                sys.stdout.flush()
    finally:
        if tty_fd is not None:
            os.close(tty_fd)
        shutil.rmtree(tmpdir, ignore_errors=True)


if __name__ == "__main__":
    main()
