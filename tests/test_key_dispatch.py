"""The pieces run_viewer()'s input loop is built from, tested without a
pty-driven subprocess: read_key() (escape-sequence decoding),
_LineEditor (the search prompt's line editing), _PREFIX_BINDINGS (":"
and "-" prefixes), and the Viewer's own key/count handlers."""

import fcntl
import os
import pty
import struct
import tempfile
import termios

import pdfless


def keys_from(data: bytes):
    """Every read_key() result for `data`, fed through a pipe."""
    r, w = os.pipe()
    os.write(w, data)
    os.close(w)
    out = []
    try:
        while True:
            key = pdfless.read_key(r)
            if key is None:
                return out
            out.append(key)
    finally:
        os.close(r)


def test_read_key_decodes_plain_named_and_mouse_input():
    assert keys_from(b"j") == ["j"]
    assert keys_from(b"\x1b[A") == ["UP"]
    assert keys_from(b"\x1bv") == ["ESC-v"]
    assert keys_from(b"\x1b[<0;40;7M") == [("MOUSE", "MOUSE_CLICK", 40, 7)]
    assert keys_from("é".encode()) == ["é"]


def type_into(editor, keys):
    return [editor.handle(k) for k in keys]


def test_line_editor_inserts_moves_and_deletes_like_readline():
    ed = pdfless._LineEditor()
    type_into(ed, "held")
    assert (ed.text, ed.cursor) == ("held", 4)
    type_into(ed, ["LEFT", "LEFT"])
    assert ed.handle("l") == "changed"
    assert (ed.text, ed.cursor) == ("helld", 3)
    ed.handle("\x01")  # ^A
    assert ed.cursor == 0
    assert ed.handle("\x08") is None  # backspace at the start of a non-empty line
    ed.handle("\x04")  # ^D deletes under the cursor
    assert ed.text == "elld"
    ed.handle("\x05")  # ^E
    ed.handle("\x7f")
    assert (ed.text, ed.cursor) == ("ell", 3)
    ed.handle("LEFT")
    ed.handle("\x0b")  # ^K
    assert ed.text == "el"
    ed.handle("\x15")  # ^U
    assert (ed.text, ed.cursor) == ("", 0)
    assert ed.handle("\x7f") == "cancel"  # backspace on an empty line
    assert ed.handle("\r") == "submit"
    assert ed.handle("\x1b") == "cancel"
    assert ed.handle("\x03") == "cancel"
    assert ed.handle("F1") is None  # swallowed, never leaks through


def make_viewer(handler, rows=30, cols=100):
    _master, slave = pty.openpty()
    fcntl.ioctl(slave, termios.TIOCSWINSZ, struct.pack("HHHH", rows, cols, cols * 8, rows * 16))
    viewer = pdfless.Viewer([handler], 0, 1, tempfile.mkdtemp(), slave, "width")
    viewer.refresh()
    return viewer


def test_prefix_bindings(sample_pdf, sample_text):
    assert pdfless._PREFIX_BINDINGS[":"]["q"](None) is False  # :q quits
    viewer = make_viewer(pdfless.TextDocument(sample_text))
    wrap = viewer.text_wrap
    assert pdfless._PREFIX_BINDINGS["-"]["S"](viewer) is not False
    assert viewer.text_wrap is not wrap
    assert "x" not in pdfless._PREFIX_BINDINGS["-"]  # anything else cancels


def test_count_keys_jump_to_the_numbered_page(sample_pdf):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf))
    assert viewer.handle_count_key(">", None)
    assert viewer.page == viewer.npages
    assert viewer.handle_count_key("<", 3)
    assert viewer.page == 3
    assert viewer.handle_count_key("HOME", None)
    assert viewer.page == 1
    assert not viewer.handle_count_key("j", None)  # not a count key


def test_global_keys_are_handled_in_either_mode(sample_pdf, sample_text):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf))
    assert viewer.handle_global_key("r")
    assert viewer.scrollbar is False
    assert viewer.handle_global_key("t")
    assert viewer.text_mode
    assert not viewer.handle_global_key("j")

    text_viewer = make_viewer(pdfless.TextDocument(sample_text))
    assert text_viewer.text_toggle_refusal() == "this is already a plain text file"


def test_follow_reloads_when_the_file_changes(sample_pdf, tmp_path, monkeypatch):
    import shutil
    path = tmp_path / "doc.pdf"
    shutil.copy(sample_pdf, path)
    viewer = make_viewer(pdfless.PdfDocument(str(path)))
    reloads = []
    monkeypatch.setattr(viewer, "reload", lambda: reloads.append(1))
    viewer.toggle_follow()
    assert viewer.follow and viewer._follow_path == str(path)
    viewer.poll_follow()
    assert reloads == []  # unchanged, and not due for a check yet anyway
    os.utime(path, (1, 1))
    viewer._follow_checked -= pdfless.FOLLOW_INTERVAL
    viewer.poll_follow()
    assert reloads == [1]


def test_turning_follow_on_catches_up_with_a_change_at_once(sample_pdf, tmp_path, monkeypatch):
    """A change made while follow was off is reloaded the moment F turns
    it on - not FOLLOW_INTERVAL seconds later, and not ignored - while
    turning it on for an unchanged file reloads nothing."""
    import shutil
    path = tmp_path / "doc.pdf"
    shutil.copy(sample_pdf, path)
    viewer = make_viewer(pdfless.PdfDocument(str(path)))
    reloads = []
    monkeypatch.setattr(viewer, "reload", lambda: reloads.append(1))

    viewer.toggle_follow()  # on - nothing changed yet
    assert reloads == []
    viewer.toggle_follow()  # off again

    os.utime(path, (1, 1))  # changed while follow is off
    viewer.poll_follow()
    assert reloads == []  # off: not watched
    viewer.toggle_follow()  # on: caught up at once
    assert reloads == [1]
    viewer.poll_follow()  # and not reloaded again for the same change
    viewer._follow_checked -= pdfless.FOLLOW_INTERVAL
    viewer.poll_follow()
    assert reloads == [1]


def test_follow_blanks_the_screen_while_the_file_is_gone(sample_pdf, tmp_path, monkeypatch, capsys):
    """Follow mode's check finding the file deleted blanks the screen,
    with a status line saying why, instead of leaving the old content up
    - and reloads it once it's back."""
    import shutil
    path = tmp_path / "doc.pdf"
    shutil.copy(sample_pdf, path)
    viewer = make_viewer(pdfless.PdfDocument(str(path)))
    viewer.toggle_follow()
    reloads = []
    monkeypatch.setattr(viewer, "reload", lambda: reloads.append(1))
    capsys.readouterr()

    os.unlink(path)
    viewer._follow_checked -= pdfless.FOLLOW_INTERVAL
    viewer.poll_follow()
    assert viewer.file_missing
    out = capsys.readouterr().out
    assert "\x1b[2J" in out and "deleted or moved" in out
    assert "1337;File" not in out  # no page image, old or new
    viewer.refresh()  # any redraw meanwhile stays blank
    assert "1337;File" not in capsys.readouterr().out

    shutil.copy(sample_pdf, path)
    viewer._follow_checked -= pdfless.FOLLOW_INTERVAL
    viewer.poll_follow()
    assert not viewer.file_missing
    assert reloads == [1]


def test_a_failed_read_of_a_deleted_file_blanks_the_screen(sample_pdf, tmp_path, monkeypatch):
    """Without follow mode, a read that fails because the file is gone
    (what run_viewer()'s loop hands to _report_unreadable_file()) blanks
    the screen the same way; the next redraw after the file is back
    reloads it."""
    import shutil
    path = tmp_path / "doc.pdf"
    shutil.copy(sample_pdf, path)
    viewer = make_viewer(pdfless.PdfDocument(str(path)))
    os.unlink(path)
    try:
        viewer.go_page(5, 0)  # never rendered before - needs the file
    except (OSError, pdfless.subprocess.CalledProcessError):
        pdfless._report_unreadable_file(viewer)
    else:
        raise AssertionError("rendering a new page should need the file")
    assert viewer.file_missing

    reloads = []
    monkeypatch.setattr(viewer, "reload", lambda: reloads.append(1))
    viewer.refresh()
    assert reloads == []  # still gone
    shutil.copy(sample_pdf, path)
    viewer.refresh()
    assert not viewer.file_missing
    assert reloads == [1]


def test_report_unreadable_file_reraises_if_the_file_is_still_there(sample_pdf):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf))
    try:
        try:
            raise OSError("some other failure")
        except OSError:
            pdfless._report_unreadable_file(viewer)
    except OSError as e:
        assert str(e) == "some other failure"
    else:
        raise AssertionError("should have re-raised")
