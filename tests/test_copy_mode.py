""""C" (see Viewer.toggle_copy_mode()): clears the decorations that a
terminal select-and-copy would otherwise sweep up along with the text -
the EOL markers, the border, the scrollbar and the line-number gutter -
and puts back exactly what was on before on a second press."""

import fcntl
import pty
import struct
import termios
import tempfile

import pdfless


def make_viewer(handler, border=True, eol_mark=True, scrollbar=True,
                line_numbers=False):
    _master, slave = pty.openpty()
    fcntl.ioctl(slave, termios.TIOCSWINSZ, struct.pack("HHHH", 20, 40, 320, 360))
    tmpdir = tempfile.mkdtemp()
    viewer = pdfless.Viewer(
        [handler], 0, 1, tmpdir, slave, None,
        border=border, eol_mark=eol_mark, scrollbar=scrollbar,
        line_numbers=line_numbers,
    )
    viewer._load_page = lambda: None
    viewer._draw = lambda: None
    viewer._draw_text = lambda: None
    viewer.refresh()
    return viewer


def decorations(viewer):
    return (
        viewer.eol_mark, viewer.text_border, viewer.scrollbar, viewer.line_numbers,
    )


def test_copy_mode_clears_every_decoration(sample_pdf):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), line_numbers=True)
    assert viewer.enter_text_mode() is True
    assert decorations(viewer) == (True, True, True, True)

    viewer.toggle_copy_mode()
    assert decorations(viewer) == (False, False, False, False)


def test_copy_mode_puts_back_what_was_on_before(sample_pdf):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), line_numbers=True)
    viewer.enter_text_mode()
    viewer.toggle_copy_mode()
    viewer.toggle_copy_mode()
    assert decorations(viewer) == (True, True, True, True)


def test_copy_mode_leaves_what_was_already_off_alone(sample_text):
    """Restoring means "back to how it was", not "everything on" - a
    plain text file starts without a border, and anything switched off
    by hand beforehand stays off."""
    viewer = make_viewer(pdfless.TextDocument(sample_text))
    assert viewer.text_border is False  # a plain text file's own default
    viewer.toggle_eol_mark()
    assert decorations(viewer) == (False, False, True, False)

    viewer.toggle_copy_mode()
    assert decorations(viewer) == (False, False, False, False)
    viewer.toggle_copy_mode()
    assert decorations(viewer) == (False, False, True, False)


def test_copy_mode_does_the_recompute_its_widths_need(sample_text):
    """The scrollbar's column and the border's own space come back to
    the text when they go - the same geometry a resize redoes."""
    viewer = make_viewer(pdfless.TextDocument(sample_text))
    assert viewer._text_avail_cols() == 39  # 40 less the scrollbar's column
    viewer.toggle_copy_mode()
    assert viewer._text_avail_cols() == 40  # the column is back in play


def test_clean_text_mode_enters_text_mode_with_decorations_off(sample_pdf):
    """T (Viewer.toggle_clean_text_mode()): t and C in one press - image
    mode straight into text mode, already cleared for copying."""
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), line_numbers=True)
    assert viewer.text_mode is False

    assert viewer.toggle_clean_text_mode() is True
    assert viewer.text_mode is True
    assert decorations(viewer) == (False, False, False, False)


def test_clean_text_mode_second_press_restores_decorations_and_image_mode(sample_pdf):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), line_numbers=True)
    viewer.toggle_clean_text_mode()

    assert viewer.toggle_clean_text_mode() is True
    assert viewer.text_mode is False
    assert decorations(viewer) == (True, True, True, True)


class _NoTextModeDocument(pdfless.ImageDocument):
    """Stands in for a kind with no text mode at all - ImageDocument
    itself has one now (format/EXIF info - see its extract_text())."""

    def supports_text_mode(self):
        return False


def test_clean_text_mode_returns_false_without_touching_copy_mode(sample_image):
    """Same failure case as toggle_text_mode() - a kind with no text
    mode at all shouldn't have side effects on the decorations either."""
    viewer = make_viewer(_NoTextModeDocument(sample_image))
    before = decorations(viewer)

    assert viewer.toggle_clean_text_mode() is False
    assert viewer.text_mode is False
    assert decorations(viewer) == before


def test_leaving_text_mode_via_plain_t_still_restores_copy_mode(sample_pdf):
    """Regression: T (toggle_clean_text_mode()) turns copy mode on, but
    "t" (toggle_text_mode()) - not "T" - was used to leave text mode
    again. exit_text_mode() itself has to restore copy mode no matter
    which key got you out, or the decorations it hid (most importantly
    the scrollbar, which also applies in image mode) leak into the
    image view and then stay stuck off on the next entry too, since
    _copy_mode_saved would still be holding stale values - reported by
    hand as "T -> t -> t makes the line numbers and EOL mark disappear"."""
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), line_numbers=True)
    original = decorations(viewer)
    assert original == (True, True, True, True)

    viewer.toggle_clean_text_mode()  # T: in, decorations off
    assert decorations(viewer) == (False, False, False, False)

    viewer.toggle_text_mode()  # t: out - must restore, not just leave
    assert viewer.text_mode is False
    assert decorations(viewer) == original
    assert viewer._copy_mode_saved is None

    viewer.toggle_text_mode()  # t: back in - must show the real decorations
    assert viewer.text_mode is True
    assert decorations(viewer) == original


def test_leaving_text_mode_via_t_after_c_also_restores_copy_mode(sample_pdf):
    """Same bug, reachable without T at all: "C" turns copy mode on
    inside text mode, and "t" (not a second "C") leaves without
    restoring it first."""
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), line_numbers=True)
    viewer.enter_text_mode()
    original = decorations(viewer)

    viewer.toggle_copy_mode()  # C
    assert decorations(viewer) == (False, False, False, False)

    viewer.toggle_text_mode()  # t: out - must restore first
    assert decorations(viewer) == original
    assert viewer._copy_mode_saved is None


def test_copy_mode_stays_where_you_were_reading(tmp_path):
    """Toggling it is not a resize: the file isn't re-read, so the
    scroll position survives both presses. Needs a file taller than
    the 20-row terminal make_viewer() sets up, to have somewhere to
    scroll to in the first place."""
    path = tmp_path / "long.txt"
    path.write_text("".join(f"line {i}\n" for i in range(100)))
    viewer = make_viewer(pdfless.TextDocument(str(path)))
    viewer.text_scroll = 42
    assert viewer.text_scroll_max >= 42

    viewer.toggle_copy_mode()
    assert viewer.text_scroll == 42
    viewer.toggle_copy_mode()
    assert viewer.text_scroll == 42
