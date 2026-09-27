import os
import struct
import fcntl
import termios
import shutil
import signal
import sys
import time
import pty

import pytest

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PDFLESS_PY = os.path.join(REPO_ROOT, "pdfless.py")
FIXTURES_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fixtures")

sys.path.insert(0, REPO_ROOT)
import pdfless  # noqa: E402  (import after sys.path tweak, deliberately)


@pytest.fixture(autouse=True)
def _isolated_office_cache(tmp_path, monkeypatch):
    """Every test gets its own throwaway LibreOffice-PDF cache directory
    (see pdfless._office_cache_root()) instead of ever touching the
    real persistent one on the machine running the suite - via an env
    var rather than a plain monkeypatch of the function, since a
    PtySession-driven test spawns a real, separate `pdfless.py`
    subprocess (see PtySession) that only an inherited env var (not an
    attribute patched on this process's own imported pdfless module)
    can actually reach."""
    monkeypatch.setenv("PDFLESS_OFFICE_CACHE_DIR", str(tmp_path / "office-cache"))


# All of these are static files checked into tests/fixtures/ rather
# than generated on the fly - faster (no per-run PIL/textutil work),
# easy to inspect/open by hand, and (sample.docx in particular) works
# the same regardless of whether textutil happens to be available at
# test time; only the actual Quick Look/Chrome rendering of it is
# gated on macOS (see requires_office_support).
@pytest.fixture
def sample_pdf():
    """A real, small PDF already checked into the repo root (used for
    screenshots/manual testing too) - avoids depending on any PDF-
    writing library just to get a valid multi-page-capable sample."""
    return os.path.join(REPO_ROOT, "lorem_ipsum.pdf")


@pytest.fixture
def sample_encrypted_pdf():
    """Same content as sample_pdf (lorem_ipsum.pdf), password-protected
    (user password "secret123") via `qpdf --encrypt secret123 secret123
    256 -- lorem_ipsum.pdf sample_encrypted.pdf` - for exercising
    PdfDocument's password-prompt handling (see _ensure_unlocked())."""
    return os.path.join(FIXTURES_DIR, "sample_encrypted.pdf")


@pytest.fixture
def sample_image():
    return os.path.join(FIXTURES_DIR, "sample.png")


@pytest.fixture
def sample_text():
    return os.path.join(FIXTURES_DIR, "sample.txt")


@pytest.fixture
def sample_rtf():
    return os.path.join(FIXTURES_DIR, "sample.rtf")


@pytest.fixture
def sample_docx():
    return os.path.join(FIXTURES_DIR, "sample.docx")


@pytest.fixture
def sample_twopage_rtf():
    """A 2-page RTF file (an explicit \\page break between two
    paragraphs) - unlike sample_rtf, real enough to confirm soffice's
    native RTF pagination (see OfficeDocument._try_soffice_pages())
    lands on the real page count, the same way sample_twopage_docx
    does for Word."""
    return os.path.join(FIXTURES_DIR, "sample_twopage.rtf")


@pytest.fixture
def sample_multisheet_xlsx():
    """A 3-sheet workbook (Alpha/Beta/Gamma), each with distinct
    content in A1 - built via openpyxl (see the fixture-generation
    notes below)."""
    return os.path.join(FIXTURES_DIR, "sample_multisheet.xlsx")


@pytest.fixture
def sample_multisheet_xls():
    """Same workbook as sample_multisheet_xlsx, converted to the
    legacy binary format via `soffice --headless --convert-to xls`."""
    return os.path.join(FIXTURES_DIR, "sample_multisheet.xls")


@pytest.fixture
def sample_multisheet_numbers():
    """Same 3-sheet structure, but built with the real Numbers app
    (via AppleScript) rather than openpyxl - Numbers' own Quick Look
    generator (iWork.qlgenerator) marks up its sheet-tab strip
    differently from Excel's (Office.qlgenerator), which is why this
    is a separate fixture rather than just another Excel conversion."""
    return os.path.join(FIXTURES_DIR, "sample_multisheet.numbers")


@pytest.fixture
def sample_twopage_docx():
    """A 2-page Word document (an explicit page break between two
    paragraphs of body text) - built via python-docx."""
    return os.path.join(FIXTURES_DIR, "sample_twopage.docx")


@pytest.fixture
def sample_docx_with_link():
    """A Word document with one real external hyperlink ("click me" ->
    https://example.com/hello) - built via python-docx (its w:hyperlink
    XML written by hand, since python-docx has no built-in helper for
    it). Used to confirm a Word document's own hyperlinks survive
    Chrome's --print-to-pdf as real, clickable PDF link annotations
    (see OfficeDocument.get_page_image()'s PdfDocument delegate)."""
    return os.path.join(FIXTURES_DIR, "sample_with_link.docx")


@pytest.fixture
def sample_docx_with_internal_link():
    """A Word document with an internal hyperlink ("jump to target") to
    a w:bookmark ~80 filler paragraphs further down - built via
    python-docx (bookmarkStart/bookmarkEnd and an anchor-based
    w:hyperlink, both written by hand). Since FlowingText always
    renders as a single continuous page (see its class docstring), a
    genuine same-document jump like this resolves to the *same* page
    with a different scroll target, not a different page - confirmed
    by hand that it survives Chrome's --print-to-pdf as a real PDF
    /GoTo link annotation pypdf resolves to {"kind": "page", "page": 1,
    "top_pt": ...}, the same as a real PDF's own internal links."""
    return os.path.join(FIXTURES_DIR, "sample_with_internal_link.docx")


@pytest.fixture
def sample_twopage_doc():
    """Same document as sample_twopage_docx, converted to the legacy
    binary format via `soffice --headless --convert-to doc`."""
    return os.path.join(FIXTURES_DIR, "sample_twopage.doc")


@pytest.fixture
def sample_twopage_pages():
    """A 2-page Pages document (body text long enough to overflow one
    page) - built with the real Pages app via AppleScript."""
    return os.path.join(FIXTURES_DIR, "sample_twopage.pages")


@pytest.fixture
def sample_twoslide_pptx():
    """A 2-slide PowerPoint deck (a title plus lorem-ipsum/Japanese
    bullet text on each slide) - built via python-pptx."""
    return os.path.join(FIXTURES_DIR, "sample_twoslide.pptx")


@pytest.fixture
def sample_twoslide_ppt():
    """Same deck as sample_twoslide_pptx, converted to the legacy
    binary format via `soffice --headless --convert-to ppt`."""
    return os.path.join(FIXTURES_DIR, "sample_twoslide.ppt")


@pytest.fixture
def sample_twoslide_key():
    """A 2-slide Keynote deck ("Slide one/two content" titles) - built
    with the real Keynote app via AppleScript."""
    return os.path.join(FIXTURES_DIR, "sample_twoslide.key")


@pytest.fixture
def sample_twopage_docm():
    """Same 2-page content as sample_twopage_docx (2 paragraphs of
    mixed Japanese/English body text, an explicit page break between
    them) but built via python-docx into a plain .docx first, then
    converted to the macro-enabled format with `soffice --convert-to
    docm` - confirmed by hand that macOS's Office.qlgenerator already
    classifies a .docm the same way it does a .docx (Preview.html and
    all), so this only needs OfficeDocument._SOFFICE_EXTENSIONS to
    also include it."""
    return os.path.join(FIXTURES_DIR, "sample_twopage.docm")


@pytest.fixture
def sample_twopage_odt():
    """Same source content as sample_twopage_docm, converted to
    OpenDocument Text instead (`soffice --convert-to odt`) - unlike
    .docm, macOS Quick Look has no generator for .odt at all (confirmed
    by hand: qlmanage crashes outright), so this only classifies at
    all via SofficeOnlyDocument, not OfficeDocument."""
    return os.path.join(FIXTURES_DIR, "sample_twopage.odt")


@pytest.fixture
def sample_twoslide_pptm():
    """Same 2-slide content as sample_twoslide_pptx (a title + a couple
    of mixed Japanese/English bullet lines per slide) but converted to
    the macro-enabled format with `soffice --convert-to pptm` -
    confirmed by hand that Quick Look already classifies a .pptm the
    same way it does a .pptx."""
    return os.path.join(FIXTURES_DIR, "sample_twoslide.pptm")


@pytest.fixture
def sample_twoslide_odp():
    """Same source content as sample_twoslide_pptm, converted to
    OpenDocument Presentation instead (`soffice --convert-to odp`) -
    like .odt, Quick Look has no generator for .odp at all, so this
    only classifies via SofficeOnlyDocument."""
    return os.path.join(FIXTURES_DIR, "sample_twoslide.odp")


@pytest.fixture
def sample_multisheet_ods():
    """Same 3-sheet structure as sample_multisheet_xlsx (each sheet
    has a Japanese header row plus a few rows of mixed Japanese/English
    data) but converted to OpenDocument Spreadsheet (`soffice
    --convert-to ods`) - confirmed by hand this simple workbook still
    comes out as exactly 3 soffice PDF pages (one per sheet); a
    real-world spreadsheet with print areas/page breaks configured can
    fragment a single sheet across several pages instead (see
    SofficeOnlyDocument's docstring), which this fixture is
    deliberately too simple to exercise."""
    return os.path.join(FIXTURES_DIR, "sample_multisheet.ods")


@pytest.fixture
def sample_odg():
    """A small OpenDocument Drawing (a rectangle and a circle, each
    with a Japanese text label, plus two lines of standalone text) -
    built as an SVG first and converted with `soffice --convert-to
    odg`, since ODG has no convenient Python-library writer the way
    docx/pptx/xlsx do."""
    return os.path.join(FIXTURES_DIR, "sample.odg")


@pytest.fixture
def sample_wmf():
    """Same shapes/labels as sample_odg, converted to a WMF vector
    metafile instead (`soffice --convert-to wmf`) - confirmed by hand
    that Quick Look only ever produces a Preview.url dead end for WMF
    (see SvgDocument's docstring for the same issue with SVG), so this
    only renders at all via SofficeOnlyDocument."""
    return os.path.join(FIXTURES_DIR, "sample.wmf")


@pytest.fixture
def sample_svg():
    """The hand-written source SVG sample_odg/sample_wmf were both
    converted from - a rectangle and a circle with Japanese text
    labels, plus two standalone lines of mixed Japanese/English text -
    used directly (not converted) to test SvgDocument's own
    Chrome-based rendering."""
    return os.path.join(FIXTURES_DIR, "sample.svg")


def office_support_available():
    return (
        shutil.which("qlmanage") is not None
        and pdfless.find_chrome() is not None
    )


requires_office_support = pytest.mark.skipif(
    not office_support_available(),
    reason="needs macOS Quick Look (qlmanage) + a local Chrome/Chromium",
)


requires_soffice = pytest.mark.skipif(
    pdfless.find_soffice() is None,
    reason="needs a local LibreOffice (soffice) install",
)


requires_markdown_rendering = pytest.mark.skipif(
    not pdfless.MarkdownDocument._markdown_rendering_available(),
    reason="needs the markdown and weasyprint Python libraries (and weasyprint's own Cairo/Pango system libraries)",
)


requires_macos = pytest.mark.skipif(
    sys.platform != "darwin",
    reason="needs macOS (e.g. for the \"O\"/\"v\" open-in-default-app feature)",
)


@pytest.fixture
def sample_md():
    """A Markdown file with a title, lorem-ipsum/Japanese body text,
    a bulleted list, a fenced code block, a blockquote, and a link -
    long enough (see the "追加セクション" padding sections) to span 2
    real WeasyPrint-paginated pages, so MarkdownDocument's pagination
    (not just single-page rendering) gets exercised."""
    return os.path.join(FIXTURES_DIR, "sample.md")


class PtySession:
    """Drives a real `pdfless.py <files...>` subprocess through a
    pseudo-terminal - the only way to exercise Viewer end-to-end (it
    needs a real tty for ioctl-based terminal-size queries), the same
    way this was done by hand throughout development."""

    def __init__(self, args, rows=40, cols=120, stdin_data=None):
        """`stdin_data`, if given, is piped in on fd 0 instead of the pty
        itself - simulating `cat file | pdfless.py`, the shape pdfless
        needs to work as $PAGER (see main()'s "reading_stdin"). The pty
        is still stdout/stderr/the controlling terminal either way -
        pdfless falls back to /dev/tty for keyboard input once its own
        stdin is a plain pipe rather than a tty."""
        if stdin_data is not None:
            stdin_r, stdin_w = os.pipe()
        self.pid, self.fd = pty.fork()
        if self.pid == 0:
            if stdin_data is not None:
                os.dup2(stdin_r, 0)
                os.close(stdin_r)
                os.close(stdin_w)
            # Every test here assumes real image-mode output (an
            # OSC 1337 inline image), which iterm2_like() only turns on
            # given the right env vars - present when the suite happens
            # to run inside a real iTerm2 window, but not guaranteed
            # anywhere else (CI, a plain xterm, ...). Forcing it here
            # (only in this forked child, not the pytest process
            # itself) keeps every test deterministic regardless of
            # where the suite is actually run from.
            os.environ["TERM_PROGRAM"] = "iTerm.app"
            os.execvp(sys.executable, [sys.executable, PDFLESS_PY, *args])
        else:
            fcntl.ioctl(
                self.fd, termios.TIOCSWINSZ,
                struct.pack("HHHH", rows, cols, cols * 8, rows * 16),
            )
            if stdin_data is not None:
                os.close(stdin_r)
                os.write(stdin_w, stdin_data)
                os.close(stdin_w)  # EOF - the whole point being paged

    def send(self, data, wait=0.5):
        os.write(self.fd, data)
        time.sleep(wait)

    def read_all(self, timeout=2.0):
        """Drain whatever output is currently available, waiting up to
        `timeout` seconds for more between reads - bounded by design,
        unlike reading until EOF (which would block forever if the
        child is still alive and simply idle, e.g. stuck waiting on a
        keypress it never got)."""
        import select

        buf = b""
        while True:
            ready, _, _ = select.select([self.fd], [], [], timeout)
            if not ready:
                break
            try:
                chunk = os.read(self.fd, 65536)
            except OSError:
                break
            if not chunk:
                break
            buf += chunk
        return buf

    def close(self, timeout=5):
        """Never blocks indefinitely: SIGTERM first, then poll with
        WNOHANG so a test that leaves pdfless wedged (e.g. stuck
        waiting for a keypress it never got) can't hang the whole
        suite - SIGKILL once `timeout` elapses without it exiting."""
        try:
            os.kill(self.pid, signal.SIGTERM)
        except OSError:
            pass
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            try:
                pid, _status = os.waitpid(self.pid, os.WNOHANG)
            except OSError:
                return
            if pid != 0:
                return
            time.sleep(0.1)
        try:
            os.kill(self.pid, signal.SIGKILL)
        except OSError:
            pass
        try:
            os.waitpid(self.pid, 0)
        except OSError:
            pass


@pytest.fixture
def pty_session():
    sessions = []

    def _make(args, rows=40, cols=120, stdin_data=None):
        s = PtySession(args, rows=rows, cols=cols, stdin_data=stdin_data)
        sessions.append(s)
        return s

    yield _make
    for s in sessions:
        s.close()
