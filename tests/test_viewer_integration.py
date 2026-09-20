"""End-to-end tests driving a real `pdfless.py` subprocess through a
pty - the only way to exercise Viewer at all (it needs a real terminal
for ioctl-based size queries). These are slower than the unit tests in
the other modules, but they're what actually catches a crash in the
Viewer/DocumentHandler wiring - e.g. the regression this module is
named for, where opening a plain text file crashed with
`TypeError: object of type 'NoneType' has no len()` because
_load_text_page() assumed a cache that's only populated by
enter_text_mode()/reload(), neither of which ever runs for a
kind=="text" file (it starts permanently in text mode)."""

import os
import signal
import time

from conftest import requires_office_support, requires_macos


def assert_no_crash(session, keys, wait=0.5, initial_wait=3):
    time.sleep(initial_wait)
    for k in keys:
        session.send(k, wait=wait)
    out = session.read_all().decode(errors="replace")
    assert "Traceback" not in out, out


def test_plain_text_file_opens_without_crashing(pty_session, sample_text):
    session = pty_session([sample_text])
    assert_no_crash(session, [b"q"])


def test_rtf_file_opens_without_crashing(pty_session, sample_rtf):
    session = pty_session([sample_rtf])
    assert_no_crash(session, [b"q"])


def test_plain_text_file_survives_a_resize(pty_session, sample_text):
    """A kind=="text" file's _load_text_page() runs again on every
    resize (refresh()'s SIGWINCH path) - make sure that doesn't crash
    either, not just the very first load."""
    session = pty_session([sample_text])
    time.sleep(3)
    os.kill(session.pid, signal.SIGWINCH)
    time.sleep(0.5)
    session.send(b"q")
    out = session.read_all().decode(errors="replace")
    assert "Traceback" not in out


def test_pdf_text_mode_toggle_and_search(pty_session, sample_pdf):
    session = pty_session([sample_pdf])
    assert_no_crash(session, [b"t", b"/", b"Lorem\r", b"n", b"t", b"q"])


def test_image_file_refuses_text_mode_and_search(pty_session, sample_image):
    session = pty_session([sample_image])
    assert_no_crash(session, [b"t", b"/", b"q"])


@requires_office_support
def test_docx_office_text_mode_toggle(pty_session, sample_docx):
    session = pty_session([sample_docx])
    assert_no_crash(session, [b"t", b"t", b"q"], wait=1.0, initial_wait=6)


@requires_office_support
def test_rtf_office_text_mode_toggle(pty_session, sample_rtf):
    """An RTF file now renders as an image via RtfOfficeDocument (a
    textutil-to-docx conversion feeding the same pipeline as a native
    Word document) - make sure both the image view and 't' toggling
    into/out of text mode work end-to-end, not just the plain-text
    fallback path."""
    session = pty_session([sample_rtf])
    assert_no_crash(session, [b"t", b"t", b"q"], wait=1.0, initial_wait=6)


def test_f_key_toggles_follow_mode_and_its_status_indicator(pty_session, sample_pdf):
    """F is a runtime toggle for the same follow behavior -F/--follow
    turns on at startup (see run_viewer()'s "F" handling) - and the
    status line shows a " follow " segment (status_segments()) only
    while it's active, regardless of how it got turned on."""
    session = pty_session([sample_pdf])
    time.sleep(3)
    assert b" follow " not in session.read_all(0.5)  # off by default (startup paint)

    session.send(b"F")
    assert b" follow " in session.read_all(0.5)

    session.send(b"F")
    assert b" follow " not in session.read_all(0.5)
    session.send(b"q")


@requires_macos
def test_o_or_v_opens_the_file_externally_and_turns_on_follow_mode(
    pty_session, sample_pdf, tmp_path, monkeypatch,
):
    """"O"/"v" (see run_viewer(), pdfless._open_in_default_app()) hand
    the file off to macOS's own `open` command and switch follow mode
    on. A real `open` would launch a real GUI app, so this puts a fake
    one on PATH instead - a script that just records the path it was
    given - for the pdfless subprocess's own subprocess.Popen(["open",
    ...]) call to find via PATH lookup instead of the genuine
    /usr/bin/open. monkeypatching os.environ here (before pty.fork(),
    inside the pty_session fixture) is inherited by the forked child,
    since it duplicates the parent's memory before exec()ing."""
    marker = tmp_path / "opened.txt"
    fake_bin = tmp_path / "bin"
    fake_bin.mkdir()
    fake_open = fake_bin / "open"
    fake_open.write_text(f'#!/bin/sh\necho "$1" >> {marker}\n')
    fake_open.chmod(0o755)
    monkeypatch.setenv("PATH", f"{fake_bin}:{os.environ['PATH']}")

    session = pty_session([sample_pdf])
    time.sleep(3)
    assert b" follow " not in session.read_all(0.5)  # off by default (startup paint)

    session.send(b"O", wait=1.0)
    assert b" follow " in session.read_all(0.5)
    assert marker.read_text().strip() == sample_pdf
    session.send(b"q")


def test_f1_and_colon_h_both_open_the_help(pty_session, sample_text):
    """less(1)'s "?" is a backward search, so help moved to F1 - sent
    as ESC O P by most terminals and ESC [ 1 1 ~ by the rest - with
    ":h" as a second way in."""
    session = pty_session([sample_text])
    time.sleep(3)
    session.read_all(0.5)  # drop the startup paint

    for keys in (b"\x1bOP", b"\x1b[11~", b":h"):
        session.send(keys)
        out = session.read_all(0.5).decode(errors="replace")
        assert "q to close help" in out, keys  # the help box's own status line
        session.send(b"q")  # close it again
    session.send(b"q")
    assert "Traceback" not in session.read_all().decode(errors="replace")


def test_question_mark_opens_a_backward_search_prompt(pty_session, sample_text):
    session = pty_session([sample_text])
    time.sleep(3)
    session.read_all(0.5)

    session.send(b"?")
    out = session.read_all(0.5).decode(errors="replace")
    assert "q to close help" not in out  # no longer the help key
    assert out.rstrip().endswith("?")  # the prompt, echoed with its own "?"

    session.send(b"line\r")
    assert_no_crash(session, [b"q"], initial_wait=0)


def test_colon_q_quits(pty_session, sample_text):
    """less(1) users reach for ":q" out of habit - it should quit just
    like the plain "q" key, not just cancel the colon-command prompt."""
    session = pty_session([sample_text])
    time.sleep(3)
    session.read_all(0.5)

    session.send(b":q", wait=0)
    deadline = time.monotonic() + 5
    exited = False
    while time.monotonic() < deadline:
        # Keep draining the pty's master side while polling - otherwise
        # the terminal-reset escapes pdfless writes on its way out can
        # fill the pty buffer and block the child inside write(),
        # keeping it from ever reaching the exit() that follows (and
        # hanging this check regardless of whether ":q" itself worked).
        session.read_all(0.2)
        pid, _status = os.waitpid(session.pid, os.WNOHANG)
        if pid != 0:
            exited = True
            break
    assert exited, "pdfless did not exit after \":q\""


def test_empty_search_pattern_repeats_the_last_one(pty_session, sample_text):
    """A bare "/"/"?" Enter should re-run the previous search pattern,
    less(1)-style - the prompt is pre-filled with it when opened."""
    session = pty_session([sample_text])
    time.sleep(3)
    session.read_all(0.5)

    session.send(b"/line\r")
    session.read_all(0.5)

    session.send(b"/")
    out = session.read_all(0.5).decode(errors="replace")
    assert "/line" in out  # previous pattern pre-filled in the prompt

    session.send(b"\r")
    out = session.read_all(0.5).decode(errors="replace")
    assert "no previous search pattern" not in out
    assert '"line" not found' not in out
    assert "Traceback" not in out

    session.send(b"?")
    out = session.read_all(0.5).decode(errors="replace")
    assert "?line" in out

    session.send(b"\r")
    out = session.read_all(0.5).decode(errors="replace")
    assert "no previous search pattern" not in out
    assert '"line" not found' not in out
    assert "Traceback" not in out

    assert_no_crash(session, [b"q"], initial_wait=0)
