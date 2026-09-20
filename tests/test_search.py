"""Search-while-in-text-mode: search now works whenever text_mode is
on, regardless of whether the underlying kind's image view has its own
page/bbox search index (currently PDF only, via build_search_index()).
These construct a real Viewer directly (needs a real pty for
get_term_cells()'s ioctl) rather than going through a full pdfless.py
subprocess, since asserting on search results/highlighting from a pty's
raw escape-sequence output is unreliable to parse - see
test_viewer_integration.py for the subprocess-level smoke tests."""

import fcntl
import pty
import struct
import termios
import tempfile

import pdfless
from conftest import requires_markdown_rendering, requires_office_support
from test_markdown import classify


def make_viewer(handler):
    """A real Viewer, with page/match-scroll rendering stubbed out -
    this synthetic pty has no real terminal pixel size
    (get_pixel_size()), which _load_page()/the image-mode match-scroll
    helpers need but text-mode search doesn't. viewer.refresh() (which
    a real run_viewer() calls right after construction - see there) is
    what actually populates text_lines for kind=="text"/"office" via
    _load_text_page(), so tests must call this instead of
    Viewer.__init__ alone."""
    _master, slave = pty.openpty()
    fcntl.ioctl(slave, termios.TIOCSWINSZ, struct.pack("HHHH", 40, 120, 960, 720))
    tmpdir = tempfile.mkdtemp()
    viewer = pdfless.Viewer([handler], 0, 1, tmpdir, slave, None)
    viewer._load_page = lambda: None
    viewer._scroll_image_to_match = lambda match: None
    viewer._scroll_text_to_match = lambda match: None
    viewer._draw = lambda: None
    viewer._draw_text = lambda: None
    viewer.refresh()
    return viewer


@requires_office_support
def test_docx_search_uses_pdf_bbox_index_in_both_modes(sample_docx):
    """Word now renders via a real PDF (soffice, or Chrome's
    --print-to-pdf as a fallback - see OfficeDocument._pdf_delegate,
    _try_soffice_pages()), so - like a native PdfDocument (see
    test_pdf_search_uses_bbox_index_in_both_modes below) -
    doc_handler.supports_search() is already True before ever entering
    text mode, and search uses the real per-page/bbox index
    (build_search_index()/find_search_matches()) in both image and
    text mode, rather than the line-based text_lines search a
    non-PDF-backed Office variant (Excel/PowerPoint/etc.) falls back
    to (see test_image_document_never_supports_search for that
    gating condition's other branch)."""
    viewer = make_viewer(pdfless.OfficeDocument(sample_docx))
    assert isinstance(viewer.doc_handler, pdfless.OfficeDocument)
    assert viewer.doc_handler._pdf_delegate is not None
    assert viewer.doc_handler.supports_search() is True

    viewer.start_search("Hello")
    assert viewer.search_matches
    assert len(viewer.search_matches[0]) == 5  # (page, xmin, ymin, xmax, ymax)

    viewer.start_search("ThisTextDoesNotAppearAnywhere")
    assert viewer.search_matches == []

    assert viewer.enter_text_mode() is True
    assert viewer.text_mode is True

    viewer.start_search("Hello")
    assert viewer.search_matches
    assert len(viewer.search_matches[0]) == 5


@requires_markdown_rendering
def test_markdown_image_search_uses_pdf_bbox_index(sample_md, tmp_path):
    """Regression: MarkdownDocument.text_mode_is_paginated() is False
    (text mode shows the whole raw source), but image-mode / search
    must still use the PDF delegate's bbox index - not
    self.text_lines, which isn't even loaded yet."""
    handler = classify(sample_md, tmp_path)
    handler.build_pages(str(tmp_path))
    viewer = make_viewer(handler)
    assert viewer.text_mode is False
    assert viewer.doc_handler.text_mode_is_paginated() is False

    viewer.start_search("追加セクション2")
    assert viewer.search_matches
    assert len(viewer.search_matches[0]) == 5  # (page, xmin, ymin, xmax, ymax)

    assert viewer.enter_text_mode() is True
    viewer.start_search("## リスト")
    assert viewer.search_matches
    assert len(viewer.search_matches[0]) == 3  # (line_idx, start, end)


def test_plain_text_file_search_works(sample_text):
    viewer = make_viewer(pdfless.TextDocument(sample_text))
    assert viewer.text_mode is True  # permanently, for kind=="text"
    assert viewer.text_lines == ["line one", "line two", "line three"]

    viewer.start_search("line two")
    assert viewer.search_matches == [(1, 0, 8)]


def test_pdf_search_uses_bbox_index_in_both_modes(sample_pdf):
    """Regression check: PdfDocument.text_mode_is_paginated() is True,
    so PDF search must keep using the page/bbox index (5-tuple matches)
    rather than the line-based search text/rtf/office use - in image
    mode (already worked before this change) and in text mode (must
    keep working the same way after it)."""
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf))

    viewer.start_search("Lorem")
    assert viewer.search_matches
    assert len(viewer.search_matches[0]) == 5  # (page, xmin, ymin, xmax, ymax)

    viewer.text_mode = True
    viewer.start_search("Lorem")
    assert viewer.search_matches
    assert len(viewer.search_matches[0]) == 5


def test_image_document_never_supports_search(sample_image):
    viewer = make_viewer(pdfless.ImageDocument(sample_image))
    assert viewer.doc_handler.supports_search() is False
    assert viewer.doc_handler.supports_text_mode() is False
    assert viewer.text_mode is False
    # Mirrors the '/' key handler's gating condition directly, since an
    # ImageDocument can never reach text_mode at all.
    assert not (viewer.text_mode or viewer.doc_handler.supports_search())

def test_match_index_from_picks_the_nearest_one_in_each_direction():
    """"/" takes the first match from here on, "?" the last one before
    here - the whole difference between the two prompts (see
    Viewer.start_search())."""
    positions = [2, 5, 5, 9]  # e.g. page numbers, two matches on page 5
    pick = pdfless.Viewer._match_index_from

    assert pick(positions, 5, False) == 1  # first match on page 5...
    assert pick(positions, 5, True) == 0  # ...vs. the last one before it
    assert pick(positions, 6, False) == 3
    assert pick(positions, 6, True) == 2


def test_match_index_from_uses_viewport_position_within_a_page():
    """Forward/backward search on a paginated PDF should start from
    the top of the current viewport, not just the page number."""
    positions = [(2, 100.0), (2, 500.0), (2, 900.0), (3, 50.0)]
    pick = pdfless.Viewer._match_index_from

    assert pick(positions, (2, 450.0), False) == 1
    assert pick(positions, (2, 450.0), True) == 0
    assert pick(positions, (2, 950.0), False) == 3


def test_match_index_from_wraps_around_the_ends():
    positions = [2, 5, 9]
    pick = pdfless.Viewer._match_index_from

    assert pick(positions, 10, False) == 0  # past the last match -> the first
    assert pick(positions, 1, True) == 2  # before the first -> the last


def test_forward_search_starts_from_the_top_visible_line(tmp_path):
    path = tmp_path / "hits.txt"
    path.write_text("".join(
        ("hit\n" if i in (3, 17, 40) else f"line {i}\n") for i in range(60)
    ))
    viewer = make_viewer(pdfless.TextDocument(str(path)))
    viewer.text_scroll = 10

    viewer.start_search("hit")
    assert viewer.search_matches[viewer.search_pos][0] == 17
    assert viewer._top_text_line() == 17


def test_backward_search_lands_on_the_match_above_you(tmp_path):
    path = tmp_path / "hits.txt"
    path.write_text("".join(
        ("hit\n" if i in (3, 17, 40) else f"line {i}\n") for i in range(60)
    ))
    viewer = make_viewer(pdfless.TextDocument(str(path)))
    viewer.text_scroll = 30

    viewer.start_search("hit", backward=True)
    assert viewer.search_matches[viewer.search_pos][0] == 17
    assert viewer._top_text_line() == 17
    # ...where a forward search from the same spot goes the other way
    # (that first search scrolled us, so put us back first).
    viewer.text_scroll = 30
    viewer.start_search("hit")
    assert viewer.search_matches[viewer.search_pos][0] == 40


def test_n_repeats_in_same_direction_as_search(sample_text):
    """less(1)-style: after ? search, n walks backward; after /, forward."""
    viewer = make_viewer(pdfless.TextDocument(sample_text))
    viewer.start_search("line", backward=True)
    assert viewer.search_pos == 2  # last match before the top

    viewer.repeat_search_for_key("n")
    assert viewer.search_pos == 1
    viewer.repeat_search_for_key("n")
    assert viewer.search_pos == 0

    viewer.start_search("line", backward=False)
    assert viewer.search_pos == 0
    viewer.repeat_search_for_key("n")
    assert viewer.search_pos == 1

    viewer.repeat_search_for_key("N")
    assert viewer.search_pos == 0


def test_repeat_search_does_not_wrap_around(sample_text):
    """N past the last match, or P before the first one, should just
    stay put and report there's nothing further - unlike the initial
    "/"/"?" jump (_match_index_from()), which does wrap."""
    viewer = make_viewer(pdfless.TextDocument(sample_text))
    viewer.start_search("line")
    assert len(viewer.search_matches) == 3

    viewer.repeat_search(forward=True)
    assert viewer.search_pos == 1
    viewer.repeat_search(forward=True)
    assert viewer.search_pos == 2

    viewer.repeat_search(forward=True)  # past the last match - no wrap
    assert viewer.search_pos == 2

    viewer.repeat_search(forward=False)
    assert viewer.search_pos == 1
    viewer.repeat_search(forward=False)
    assert viewer.search_pos == 0

    viewer.repeat_search(forward=False)  # before the first match - no wrap
    assert viewer.search_pos == 0


def test_backward_search_in_a_pdf_works_by_page(sample_pdf):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf))
    viewer.start_search("Lorem")  # from page 1: the first match forward
    first = viewer.search_pos
    pages = [m[0] for m in viewer.search_matches]
    assert len(set(pages)) > 1  # matches on more than one page, or this
    # says nothing

    viewer.page = pages[-1]
    viewer.start_search("Lorem", backward=True)
    assert viewer.search_pos != first
    assert pages[viewer.search_pos] < viewer.npages
