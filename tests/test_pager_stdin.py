"""Reading from stdin (main()'s "reading_stdin") - no file argument at
all, or "-" in its place - lets pdfless work as $PAGER: git, man, and
friends invoke $PAGER with nothing but the piped content on stdin and
expect it to still take keyboard input from the terminal. pdfless
drains the pipe into a real file up front (every DocumentHandler.sniff()
needs a path, not a stream) and falls back to /dev/tty for the
keyboard/mouse side once its own stdin is a plain pipe rather than a
tty - the same trick less(1)/most(1) use."""

import time

from conftest import PtySession


def assert_no_crash(session, keys, wait=0.5, initial_wait=3):
    time.sleep(initial_wait)
    for k in keys:
        session.send(k, wait=wait)
    out = session.read_all().decode(errors="replace")
    assert "Traceback" not in out, out


def test_no_file_argument_pages_piped_stdin(pty_session):
    content = "".join(f"piped line {i}\n" for i in range(30)).encode()
    session = pty_session([], stdin_data=content)
    time.sleep(3)
    out = session.read_all(1.0).decode(errors="replace")
    assert "piped line 0" in out
    assert "piped line 1" in out
    assert_no_crash(session, [b"q"], initial_wait=0)


def test_dash_argument_also_means_stdin(pty_session):
    """"-" is the explicit spelling of the same thing, e.g. for `cmd |
    pdfless.py - notes.pdf` alongside a real file."""
    content = b"content via dash\n"
    session = pty_session(["-"], stdin_data=content)
    time.sleep(3)
    out = session.read_all(1.0).decode(errors="replace")
    assert "content via dash" in out
    assert_no_crash(session, [b"q"], initial_wait=0)


def test_stdin_pager_passes_through_ansi_color_sequences(pty_session):
    """When used as $PAGER (e.g. for `git diff`), colored output must
    not treat SGR escapes as visible text - otherwise headers show up
    as literal ^[[1mdiff --git..."""
    import pdfless

    line = "\x1b[1mdiff --git a/README.md b/README.md\x1b[m\n"
    assert pdfless.display_width(line.rstrip("\n")) == len("diff --git a/README.md b/README.md")

    content = (line + "plain line\n").encode()
    session = pty_session([], rows=20, cols=80, stdin_data=content)
    time.sleep(3)
    out = session.read_all(1.0).decode(errors="replace")
    assert "diff --git a/README.md b/README.md" in out
    assert "plain line" in out
    assert "^[[1m" not in out  # ESC must not become caret notation
    assert_no_crash(session, [b"q"], initial_wait=0)


def test_stdin_pager_scrolls_and_quits_cleanly(pty_session):
    """Not just a static dump - the usual line/page navigation and a
    clean "q" exit work the same as paging a real file."""
    content = "".join(f"line {i}\n" for i in range(200)).encode()
    session = pty_session([], rows=20, cols=60, stdin_data=content)
    time.sleep(3)
    session.read_all(0.5)

    session.send(b"G")  # jump to the end
    out = session.read_all(0.5).decode(errors="replace")
    assert "line 199" in out

    assert_no_crash(session, [b"q"], initial_wait=0)


def test_no_file_and_no_piped_stdin_reports_an_error(pty_session):
    """With nothing piped in, pdfless's own stdin is the pty - a real
    tty - so there's nothing to read and no file to fall back to. This
    dies almost instantly (no raw/alt-screen mode is ever entered), so
    read promptly - once the child has exited, an already-closed pty's
    still-unread output isn't guaranteed to survive on every platform,
    unlike the other tests here where the process stays alive and
    waiting."""
    session = pty_session([])  # no stdin_data: stdin stays the pty itself
    out = session.read_all(1.0).decode(errors="replace")
    assert "no file given" in out
    session.close()
