"""-c/--continuous (or c at runtime): consecutive pages scroll one after
another - in image mode stacked with a gray gap between them (see
Viewer._normalize_continuous()/_view_crop()), in a paginated text mode
as one run of every page's text with a separator row between each page
and the next (see Viewer._text_continuous()) - instead of one page at a
time. These construct a real Viewer directly on a pty with a known
pixel size, the same as test_incremental_scroll.py."""

import fcntl
import pty
import struct
import termios
import tempfile

import pdfless


def make_viewer(handler, monkeypatch, continuous=True, fit="width", rows=30, cols=100,
                text=False, border=True, line_numbers=False):
    """8x16-pixel cells; fit-to-width then makes an A4 page of
    lorem_ipsum.pdf far taller than the 29-row viewport, so there's
    real scrolling within a page as well as across pages. iTerm2-like
    so _scroll_shift_rows()'s incremental path is eligible at all."""
    monkeypatch.setenv("TERM_PROGRAM", "iTerm.app")
    monkeypatch.delenv("TMUX", raising=False)
    _master, slave = pty.openpty()
    fcntl.ioctl(slave, termios.TIOCSWINSZ, struct.pack("HHHH", rows, cols, cols * 8, rows * 16))
    viewer = pdfless.Viewer(
        [handler], 0, 1, tempfile.mkdtemp(), slave, fit,
        border=border, wrap=False, line_numbers=line_numbers, continuous=continuous,
    )
    viewer.refresh()
    if text:
        assert viewer.enter_text_mode()
    return viewer


def gap(viewer):
    return viewer._continuous_gap_px()


# --- image mode -------------------------------------------------------


def test_scrolling_past_a_page_carries_on_into_the_next(sample_pdf, monkeypatch):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), monkeypatch)
    page1_height = viewer.img.height
    step = viewer.cell_h_px
    steps = 0
    # On past page 1's own scroll_max (its bottom at the bottom of the
    # screen), where a paginated view would have turned the page.
    while viewer.page == 1:
        viewer.scroll_down(step)
        steps += 1
    assert viewer.page == 2
    # The position carried over exactly - no jump to page 2's top: the
    # total distance scrolled is page 1 plus the gap plus how far into
    # page 2 it now is.
    assert steps * step == page1_height + gap(viewer) + viewer.scroll


def test_page_bottom_and_next_page_top_share_the_screen(sample_pdf, monkeypatch):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), monkeypatch)
    viewer.scroll = viewer.img.height - viewer.avail_height_px // 2
    viewer.refresh()
    assert viewer.page == 1
    assert [p for p, _top, _img in viewer._layout] == [1, 2]
    _, top2, _ = viewer._layout[1]
    crop = viewer._view_crop(0, viewer._view_height)
    assert crop.height == viewer.avail_height_px
    # The gap between the pages is drawn in CONTINUOUS_GAP_COLOR...
    assert crop.getpixel((crop.width // 2, top2 - 1)) == pdfless.CONTINUOUS_GAP_COLOR
    # ...and page 2 itself starts right after it (white page margin).
    assert crop.getpixel((2, top2 + 1)) == (255, 255, 255)


def test_scrolling_up_from_a_page_top_lands_in_the_previous_page(sample_pdf, monkeypatch):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), monkeypatch)
    viewer.go_page(3, 0)
    viewer.refresh()
    viewer.scroll_up(viewer.cell_h_px)
    assert viewer.page == 2
    assert viewer.scroll == viewer.img.height + gap(viewer) - viewer.cell_h_px


def test_the_end_of_the_document_stops_at_the_bottom_of_the_screen(sample_pdf, monkeypatch):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), monkeypatch)
    viewer.go_page(viewer.npages, None)
    viewer.scroll = viewer.scroll_max
    viewer.refresh()
    at_end = (viewer.page, viewer.scroll)
    assert at_end == (viewer.npages, viewer.scroll_max)
    viewer.scroll_down(viewer.avail_height_px)  # nowhere further to go
    viewer.refresh()
    assert (viewer.page, viewer.scroll) == at_end


def test_a_short_last_page_pulls_the_previous_one_into_view(sample_pdf, monkeypatch):
    """Fit-to-height makes every page exactly one screen tall, so
    zooming out leaves the last page shorter than the screen - the
    view must end with it at the bottom, earlier pages above it,
    rather than the last page alone at the top of an empty screen."""
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), monkeypatch, fit="height")
    viewer.set_zoom(0.5)
    viewer.go_page(viewer.npages, 0)
    viewer.refresh()
    assert viewer.page < viewer.npages
    _, last_top, last_img = viewer._layout[-1]
    assert viewer._layout[-1][0] == viewer.npages
    assert last_top + last_img.height == viewer.avail_height_px


def test_crossing_a_page_boundary_still_scrolls_incrementally(sample_pdf, monkeypatch):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), monkeypatch)
    step = viewer.cell_h_px
    # One step short of page 2 starting at the top of the screen, so
    # the next step crosses into it.
    viewer.scroll = viewer.img.height + gap(viewer) - step // 2
    viewer.refresh()
    assert viewer.page == 1
    viewer.scroll_down(step)
    assert viewer.page == 2
    assert viewer._scroll_shift_rows(viewer.crop_width, viewer._view_height) == 1


def test_g_and_G_stay_on_the_current_page(sample_pdf, monkeypatch):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), monkeypatch)
    viewer.go_page(3, 0)
    viewer.handle_key("G")
    viewer.refresh()
    assert (viewer.page, viewer.scroll) == (3, viewer.scroll_max)
    viewer.handle_key("G")  # pressing it again doesn't walk anywhere
    viewer.refresh()
    assert (viewer.page, viewer.scroll) == (3, viewer.scroll_max)
    viewer.handle_key("g")
    viewer.refresh()
    assert (viewer.page, viewer.scroll) == (3, 0)


def test_turning_continuous_off_clamps_back_into_the_page(sample_pdf, monkeypatch):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), monkeypatch)
    viewer.scroll = viewer.img.height - 10  # page 2 is on screen too
    viewer.refresh()
    viewer.toggle_continuous()
    assert viewer.continuous is False
    assert viewer.page == 1
    assert viewer.scroll == viewer.scroll_max
    viewer.toggle_continuous()
    assert viewer.continuous is True


def test_search_marker_on_a_lower_page_on_screen(sample_pdf, monkeypatch):
    """A match on page 2 is boxed while page 2 is on screen below page
    1's bottom - positioned relative to page 2's own top in the layout."""
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), monkeypatch)
    viewer._search_index = viewer.doc_handler.build_search_index()
    matches = viewer.doc_handler.find_search_matches(viewer._search_index, "Chapter")
    page2_match = next(i for i, m in enumerate(matches) if m[0] == 2)
    viewer.search_query = "Chapter"
    viewer.search_matches = matches
    viewer.search_pos = page2_match
    viewer.scroll = viewer.img.height - viewer.avail_height_px // 2
    viewer.refresh()
    assert viewer.page == 1
    match = viewer._visible_search_match()
    assert match is not None and match[0] == 2
    assert viewer._active_search_page_match() is None  # not the top page
    _, px_top, _, _ = viewer._match_bbox_px(match)
    bounds = viewer._match_marker_bounds(
        *viewer._match_bbox_px(match), page_top=viewer._visible_page_top(2)
    )
    top2 = viewer._visible_page_top(2)
    assert bounds is not None
    assert bounds[0] == (px_top + top2) // viewer.cell_h_px - 1


def test_a_click_maps_to_the_page_under_it(sample_pdf, monkeypatch):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), monkeypatch)
    viewer.scroll = viewer.img.height - viewer.avail_height_px // 2
    viewer.refresh()
    seen = []
    viewer._link_index = [
        {"width_pt": 595.0, "height_pt": 842.0, "links": []} for _ in range(viewer.npages)
    ]
    # Give page 2 one link covering its whole page, so any click landing
    # on page 2 (and only there) activates it.
    viewer._link_index[1]["links"] = [{
        "kind": "uri", "uri": "x", "xmin": 0, "ymin": 0, "xmax": 595, "ymax": 842,
    }]
    viewer._activate_link = seen.append
    _, top2, _ = viewer._layout[1]
    viewer.handle_click(5, top2 // viewer.cell_h_px - 1)  # still page 1
    assert seen == []
    viewer.handle_click(5, top2 // viewer.cell_h_px + 3)  # page 2
    assert len(seen) == 1


# --- text mode --------------------------------------------------------


def test_extract_text_pages_agrees_with_extract_text(sample_pdf):
    doc = pdfless.PdfDocument(sample_pdf)
    n = doc.page_count()
    assert doc.extract_text_pages(n) == [doc.extract_text(p) for p in range(1, n + 1)]


def test_text_mode_shows_every_page_with_separators(sample_pdf, monkeypatch):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), monkeypatch, text=True)
    assert viewer._text_continuous()
    assert len(viewer._text_page_starts) == viewer.npages
    # One heading row per page, page 1 included.
    assert len(viewer._text_separator_lines) == viewer.npages
    assert 0 in viewer._text_separator_lines
    for page in range(1, viewer.npages + 1):
        start, _end = viewer._text_page_range(page)
        assert start - 1 in viewer._text_separator_lines
        assert viewer._text_page_of_line(start - 1) == page
    rule = viewer._text_separator_rule(viewer._text_page_starts[1], 30)
    assert pdfless.PAGE_NUMBER_COLOR + f" 2/{viewer.npages} " + pdfless.SGR_RESET in rule
    assert pdfless.PAGE_NUMBER_COLOR + f" 1/{viewer.npages} " in viewer._text_separator_rule(0, 30)
    # Page 1's heading stands in for the border's top edge: nothing to
    # scroll up to above it.
    assert viewer.text_scroll_min == 0
    assert viewer.text_scroll == 0


def test_text_scrolling_crosses_pages_and_tracks_the_page(sample_pdf, monkeypatch):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), monkeypatch, text=True)
    sep = viewer._text_page_starts[1]
    # Scroll line by line until the separator is on screen: page 1's
    # last lines and page 2's first are then visible together.
    while viewer.text_scroll + viewer._text_avail_rows() <= sep + 1:
        viewer.text_scroll_down(1)
    viewer.refresh()
    assert viewer.page == 1
    viewer.text_scroll = sep
    viewer.refresh()
    assert viewer.page == 2


def test_text_n_p_and_line_numbers_are_per_page(sample_pdf, monkeypatch):
    viewer = make_viewer(
        pdfless.PdfDocument(sample_pdf), monkeypatch, text=True, line_numbers=True,
    )
    viewer.handle_key_text("n")
    viewer.refresh()
    assert viewer.page == 2
    assert viewer.text_scroll == viewer._text_page_starts[1]  # separator on top
    start, _end = viewer._text_page_range(2)
    assert viewer._text_line_number(start) == 1
    assert viewer._text_line_number(start - 1) is None  # the separator
    viewer.go_to_text_line(5)
    assert viewer.text_scroll == start + 4
    viewer.handle_key_text("p")
    viewer.refresh()
    assert viewer.page == 1


def test_text_G_stays_on_the_current_page(sample_pdf, monkeypatch):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), monkeypatch, text=True)
    viewer.go_to_page_text(3, 0)
    viewer.handle_key_text("G")
    viewer.refresh()
    assert viewer.page == 3
    viewer.handle_key_text("G")
    viewer.refresh()
    assert viewer.page == 3


def test_text_highlight_for_a_match_on_another_page(sample_pdf, monkeypatch):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), monkeypatch, text=True)
    viewer.start_search("Chapter")
    assert viewer.search_matches
    target = next(i for i, m in enumerate(viewer.search_matches) if m[0] == 3)
    viewer._goto_search_match(target)
    highlight = viewer._text_search_highlight()
    assert highlight is not None
    start, end = viewer._text_page_range(3)
    assert start <= highlight[0] < end
    assert "Chapter" in viewer.text_lines[highlight[0]]


def test_text_toggle_keeps_the_page_and_line(sample_pdf, monkeypatch):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), monkeypatch, text=True)
    viewer.go_to_page_text(3, 7)
    viewer.refresh()
    start, _end = viewer._text_page_range(3)
    assert viewer._top_text_line() == start + 7
    viewer.toggle_continuous()
    assert viewer._text_page_starts is None
    assert viewer.page == 3
    assert viewer._top_text_line() == 7
    viewer.toggle_continuous()
    start, _end = viewer._text_page_range(3)
    assert viewer.page == 3
    assert viewer._top_text_line() == start + 7


def test_text_view_is_paginated_without_continuous(sample_pdf, monkeypatch):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), monkeypatch, continuous=False, text=True)
    assert viewer._text_page_starts is None
    assert viewer.text_lines == viewer.doc_handler.extract_text(1)


class _FlowingTextPdf(pdfless.PdfDocument):
    """A multi-page image view whose text mode is one flowing blob -
    what MarkdownDocument (its raw source) is, without needing
    WeasyPrint just to get a multi-page render of one."""

    def text_mode_is_paginated(self):
        return False

    def extract_text(self, page):
        return [f"source line {i}" for i in range(100)]


def test_unpaginated_text_mode_is_a_single_page(sample_pdf, monkeypatch):
    """Scrolling past the end of it, or <, >, N<, must not "turn" to
    image page 2..N - each of which would just reload the whole text
    again, showing the same content once per image page."""
    for continuous in (True, False):
        viewer = make_viewer(_FlowingTextPdf(sample_pdf), monkeypatch,
                             continuous=continuous, text=True)
        assert viewer.npages > 1  # the image view is paginated
        assert viewer._text_page_starts is None
        for _ in range(20):
            viewer.text_scroll_down(viewer._text_avail_rows())
        assert viewer.page == 1
        assert viewer.text_scroll == viewer.text_scroll_max
        assert len(viewer.text_lines) == 100
        viewer.go_to_page_text(viewer.npages, None)  # ">"
        assert viewer.page == 1
        assert viewer.text_scroll == viewer.text_scroll_max
        viewer.go_to_page_text(3, 0)  # "3<"
        assert viewer.page == 1
        assert viewer.text_scroll == viewer.text_scroll_min
        page_field = next(t for t, _c in viewer.status_segments() if t.startswith(" page"))
        assert page_field == " page 1/1 "


def test_scrolling_reads_each_page_size_only_once(sample_pdf, monkeypatch):
    """page_size_pt() is needed on every get_page_image() call, and the
    continuous layout asks for every page on screen on every draw - each
    page's size must come from pdfinfo just once, not once per scroll."""
    reads = []
    real_read = pdfless.PdfDocument._read_page_size_pt

    def counting_read(self, page):
        reads.append(page)
        return real_read(self, page)

    monkeypatch.setattr(pdfless.PdfDocument, "_read_page_size_pt", counting_read)
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), monkeypatch)
    for _ in range(3 * viewer.img.height // viewer.cell_h_px):
        viewer.scroll_down(viewer.cell_h_px)
        viewer.refresh()
    assert viewer.page >= 3
    assert sorted(reads) == sorted(set(reads))  # no page read twice

    viewer.doc_handler.forget_page_sizes()  # what reload() does
    viewer.refresh()
    assert len(reads) > len(set(reads))  # re-read after the file changed


def test_go_page_none_means_the_bottom_of_the_page(sample_pdf, monkeypatch):
    """go_page(page, None) lands on the page's bottom by itself - never
    leaving self.scroll as None for the caller to patch up."""
    for continuous in (False, True):
        viewer = make_viewer(pdfless.PdfDocument(sample_pdf), monkeypatch, continuous=continuous)
        viewer.go_page(2, None)
        assert viewer.page == 2
        assert viewer.scroll == viewer.scroll_max > 0
