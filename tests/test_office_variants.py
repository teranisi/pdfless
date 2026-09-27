"""Real-world Office/iWork format coverage: multi-sheet spreadsheets,
multi-page word-processor documents, and multi-slide presentations,
across both the modern (OOXML) and legacy binary formats, plus the
native iWork formats - see conftest.py for how each fixture was built.

requires_office_support (qlmanage + a local Chrome) since these all
go through OfficeDocument._render_office_pages() for real - there is
no way to test ExcelWorkbook/SlideDeck/FlowingText selection without
actually rendering.
"""

import fcntl
import pty
import struct
import termios
import tempfile

import pdfless
from PIL import Image
from conftest import requires_office_support, requires_soffice


def classify(path, tmp_path, debug=False):
    for cls in pdfless.HANDLER_CLASSES:
        handler = cls.sniff(path, str(tmp_path), debug=debug)
        if handler is not None:
            return handler
    return None


@requires_office_support
def test_xlsx_multisheet_renders_one_page_per_sheet(sample_multisheet_xlsx, tmp_path, monkeypatch):
    """Without soffice: Quick Look's preview, one screenshot per sheet
    (see ExcelWorkbook)."""
    monkeypatch.setattr(pdfless, "find_soffice", lambda: None)
    handler = classify(sample_multisheet_xlsx, tmp_path)
    assert isinstance(handler, pdfless.OfficeDocument)
    pages = handler.build_pages(str(tmp_path))
    assert len(pages) == 3


@requires_office_support
def test_xls_legacy_multisheet_renders_one_page_per_sheet(sample_multisheet_xls, tmp_path, monkeypatch):
    """The legacy binary format (soffice --headless --convert-to xls)
    must classify and paginate the same way as its .xlsx source -
    ShouldNotScale and the TabViewItem tab strip are both properties
    of qlmanage's own generated preview, not of the file format
    itself."""
    monkeypatch.setattr(pdfless, "find_soffice", lambda: None)
    handler = classify(sample_multisheet_xls, tmp_path)
    assert isinstance(handler, pdfless.OfficeDocument)
    pages = handler.build_pages(str(tmp_path))
    assert len(pages) == 3


@requires_soffice
def test_excel_renders_via_soffice_one_whole_sheet_per_page(
    sample_multisheet_xlsx, sample_multisheet_xls, tmp_path, monkeypatch,
):
    """With soffice, Excel is exported to a real PDF with Calc's
    SinglePageSheets option (see _SOFFICE_SPREADSHEET_PDF_FILTER) - one
    page per sheet, never paginated by print area - so it's searchable
    and has per-sheet text, like Word."""
    commands = []
    real = pdfless.run_subprocess

    def spy(cmd, *args, **kwargs):
        commands.append(cmd)
        return real(cmd, *args, **kwargs)
    monkeypatch.setattr(pdfless, "run_subprocess", spy)
    for i, path in enumerate((sample_multisheet_xlsx, sample_multisheet_xls)):
        tmpdir = tmp_path / str(i)
        tmpdir.mkdir()
        handler = classify(path, tmpdir)
        assert isinstance(handler, pdfless.OfficeDocument)
        pages = handler.build_pages(str(tmpdir))
        assert len(pages) == 3
        assert handler._pdf_delegate is not None
        assert handler.supports_search() is True
        assert handler.text_mode_is_paginated() is True
        assert "サンプルB" in "\n".join(handler.extract_text(3))
    soffice_runs = [c for c in commands if "--convert-to" in c]
    assert len(soffice_runs) == 2
    assert all(c[c.index("--convert-to") + 1] == pdfless._SOFFICE_SPREADSHEET_PDF_FILTER for c in soffice_runs)
    assert not any(c[0] == "qlmanage" for c in commands)  # classified without a Quick Look dry run


@requires_office_support
def test_numbers_multisheet_renders_one_page_per_sheet(sample_multisheet_numbers, tmp_path):
    """Numbers' own Quick Look generator (iWork.qlgenerator) marks up
    its multi-sheet tab strip differently from Excel's (see
    ExcelWorkbook._NAVPANE_SHEET_RE), but it's still one page per
    sheet, the same as the equivalent .xlsx/.xls."""
    handler = classify(sample_multisheet_numbers, tmp_path)
    assert isinstance(handler, pdfless.OfficeDocument)
    pages = handler.build_pages(str(tmp_path))
    assert len(pages) == 3


@requires_office_support
def test_numbers_sheets_have_no_broken_image(sample_multisheet_numbers, tmp_path):
    """Each Numbers sheet embeds its content as <img src="AttachmentN.pdf">,
    which Chrome can't display - it has to be converted first (see
    _rasterize_broken_img_sources()), or all that's left is Chrome's
    broken-image icon on an otherwise blank sheet. The sheet's own cell
    grid is drawn in gray, so a converted sheet has plenty of non-white
    pixels; a broken one has almost none."""
    handler = classify(sample_multisheet_numbers, tmp_path)
    pages = handler.build_pages(str(tmp_path))
    for page in pages:
        img = Image.open(page).convert("L")
        dark = sum(img.histogram()[:200])  # pixels darker than 200/255
        assert dark > img.width * img.height // 100


@requires_office_support
def test_docx_twopage_paginates_via_print_to_pdf(sample_twopage_docx, tmp_path):
    """Word has no per-page markup Quick Look exposes (no
    PageElementXPath, unlike PowerPoint), but FlowingText's PDF path
    (see _build_pdf_pages()) doesn't need any - printing at one page's
    own height and letting Chrome's print engine paginate the rest
    lands on the document's real page count on its own."""
    handler = classify(sample_twopage_docx, tmp_path)
    assert isinstance(handler, pdfless.OfficeDocument)
    pages = handler.build_pages(str(tmp_path))
    assert len(pages) == 2
    assert handler._pdf_delegate is not None

    # extract_text() delegates to the real PDF per page (see
    # OfficeDocument.extract_text()), so each page's text comes back
    # separately rather than textutil's single whole-document blob.
    assert "日本語のサンプル段落" in "\n".join(handler.extract_text(1))
    assert "本文の続きです" in "\n".join(handler.extract_text(2))


@requires_office_support
@requires_soffice
def test_rtf_uses_soffice_when_available_and_paginates_really(sample_twopage_rtf, tmp_path):
    """Unlike the textutil-converted-docx fallback (see
    RtfOfficeDocument.build_pages()'s "Always continuous" branch),
    soffice reads the original .rtf natively, so its real \\page break
    is trusted and produces 2 real pages."""
    handler = classify(sample_twopage_rtf, tmp_path)
    assert isinstance(handler, pdfless.RtfOfficeDocument)
    pages = handler.build_pages(str(tmp_path))
    assert len(pages) == 2
    assert handler._pdf_delegate is not None


@requires_office_support
def test_docx_falls_back_to_qlmanage_when_soffice_missing(sample_twopage_docx, tmp_path, monkeypatch):
    """Regression test: with soffice unavailable (simulated here rather
    than relying on this machine's actual install state), Word must
    still render via the pre-existing qlmanage/Chrome + Chrome
    --print-to-pdf pipeline exactly as before soffice support existed
    - the same 2-page, PDF-delegate-backed result."""
    monkeypatch.setattr(pdfless, "find_soffice", lambda: None)
    handler = classify(sample_twopage_docx, tmp_path)
    assert isinstance(handler, pdfless.OfficeDocument)
    pages = handler.build_pages(str(tmp_path))
    assert len(pages) == 2
    assert handler._pdf_delegate is not None


@requires_office_support
def test_docx_becomes_searchable_via_its_pdf_delegate(sample_twopage_docx, tmp_path):
    """Word now renders via a real PDF (soffice or Chrome's
    --print-to-pdf - see OfficeDocument._pdf_delegate), so it should
    be searchable with a real per-page/bbox index
    (build_search_index()/find_search_matches()), not just via text
    mode's flat text-line search - and text mode should page along
    with image mode (text_mode_is_paginated()), since each page's text
    (extract_text()) now comes from the real PDF page rather than one
    whole-document textutil blob with no page boundaries."""
    handler = classify(sample_twopage_docx, tmp_path)
    assert isinstance(handler, pdfless.OfficeDocument)
    handler.build_pages(str(tmp_path))
    assert handler._pdf_delegate is not None

    assert handler.supports_search() is True
    assert handler.text_mode_is_paginated() is True

    index = handler.build_search_index()
    assert len(index) == 2
    matches = handler.find_search_matches(index, "続きです")
    assert any(page == 2 for page, *_ in matches)


@requires_office_support
def test_xlsx_has_no_pdf_delegate_so_search_is_unavailable(sample_multisheet_xlsx, tmp_path, monkeypatch):
    """Without soffice, Excel never renders via a real PDF (see
    ExcelWorkbook) - its OfficeDocument._pdf_delegate stays None, so
    there's no per-page/bbox index to search against, unlike Word (see
    test_docx_becomes_searchable_via_its_pdf_delegate)."""
    monkeypatch.setattr(pdfless, "find_soffice", lambda: None)
    handler = classify(sample_multisheet_xlsx, tmp_path)
    assert isinstance(handler, pdfless.OfficeDocument)
    handler.build_pages(str(tmp_path))
    assert handler._pdf_delegate is None
    assert handler.supports_search() is False
    assert handler.text_mode_is_paginated() is False


@requires_office_support
def test_docx_renders_via_a_pdf_delegate_for_crisp_zoom(sample_twopage_docx, tmp_path):
    """Word renders via a real PDF - soffice when installed (see
    OfficeDocument._try_soffice_pages()), else Chrome's --print-to-pdf
    (see FlowingText._build_pdf_pages()) - re-rasterized at whatever
    DPI the current zoom needs (see OfficeDocument.get_page_image()),
    instead of resizing one fixed-resolution screenshot. Confirmed
    here by asking for the same page at two different target widths
    and checking the returned image's actual pixel width tracks each
    one - a fixed screenshot resized by Pillow would still report the
    target width after an upscale (Pillow's resize() always returns
    exactly the requested size), so this alone doesn't distinguish the
    two paths; what does is handler._pdf_delegate itself being set at
    all - only a real-PDF path ever creates one, the screenshot
    fallback never does."""
    handler = classify(sample_twopage_docx, tmp_path)
    assert isinstance(handler, pdfless.OfficeDocument)
    handler.build_pages(str(tmp_path))
    assert handler._pdf_delegate is not None

    cache = pdfless.PageCache(str(tmp_path), handler)
    small = handler.get_page_image(cache, 1, 300, "width")
    big = handler.get_page_image(cache, 1, 1200, "width")
    assert small.width == 300
    assert big.width == 1200
    # Re-rasterized independently at each width, not the same bitmap
    # twice over - the aspect ratio (and so the height) should match,
    # within the few pixels two independently-rounded DPIs can differ
    # by (a bit more slack than a single fixed page size would need,
    # since soffice and Chrome pick slightly different page
    # dimensions for the same document).
    assert abs(big.height - round(small.height * 1200 / 300)) <= 3


@requires_office_support
def test_docx_hyperlink_survives_as_a_real_pdf_link(sample_docx_with_link, tmp_path):
    """A plain <a href> in the original Word document, run through
    Quick Look -> Chrome's --print-to-pdf, comes out as a real PDF
    /Link annotation (confirmed by hand with pypdf) - so it's clickable
    exactly like a native PDF's hyperlink, via the exact same
    PdfDocument.build_link_index() a real PDF's links go through (see
    Viewer._ensure_link_index()'s pdf_source fallback to
    doc_handler._pdf_delegate)."""
    handler = classify(sample_docx_with_link, tmp_path)
    assert isinstance(handler, pdfless.OfficeDocument)
    pages = handler.build_pages(str(tmp_path))
    assert handler._pdf_delegate is not None

    link_index = handler._pdf_delegate.build_link_index(len(pages))
    links = link_index[0]["links"]
    assert any(link.get("uri") == "https://example.com/hello" for link in links)


def _find_goto_links(link_index):
    """Every "kind": "page" link across a whole build_link_index()
    result, as (found_on_page, link) pairs - the internal-link fixture
    now spans several real PDF pages (see
    test_docx_twopage_paginates_via_print_to_pdf), so a fixed page
    index can't be assumed the way it could when FlowingText always
    forced a single page."""
    return [
        (page_num, link)
        for page_num, page in enumerate(link_index, start=1)
        for link in page["links"]
        if link.get("kind") == "page"
    ]


@requires_office_support
def test_docx_internal_link_survives_as_a_real_pdf_goto(sample_docx_with_internal_link, tmp_path):
    """An internal (bookmark-anchored) hyperlink survives as a real PDF
    /GoTo link, resolved the same way a real PDF's internal links are
    (build_link_index()'s "kind": "page" case). With FlowingText now
    paginating normally (see test_docx_twopage_paginates_via_print_to_pdf),
    the ~80 filler paragraphs between the link and its target bookmark
    span several real pages, so this is a genuine cross-page jump, not
    just a different scroll position on the same page."""
    handler = classify(sample_docx_with_internal_link, tmp_path)
    assert isinstance(handler, pdfless.OfficeDocument)
    pages = handler.build_pages(str(tmp_path))
    assert len(pages) > 1
    assert handler._pdf_delegate is not None

    link_index = handler._pdf_delegate.build_link_index(len(pages))
    goto_links = _find_goto_links(link_index)
    assert len(goto_links) == 1
    found_on_page, link = goto_links[0]
    assert link["top_pt"] is not None
    # The target bookmark is ~80 filler paragraphs below the link
    # itself - a real forward jump, not a same-spot no-op.
    assert link["page"] > found_on_page


@requires_office_support
def test_docx_internal_link_click_scrolls_without_crashing(sample_docx_with_internal_link, tmp_path):
    """Regression test: Viewer.go_to_link_target() used to call
    self.doc_handler.page_size_pt() unconditionally, assuming
    doc_handler is a real PdfDocument - AttributeError for an
    OfficeDocument (even one with a _pdf_delegate, since that's the
    delegate's method, not doc_handler's own). Exercises the exact
    path a mouse click on this link takes (handle_click() ->
    _activate_link() -> go_to_link_target()) via a real Viewer,
    checking the click actually jumps to the target page and scrolls
    there instead of crashing or silently doing nothing."""
    _master, slave = pty.openpty()
    fcntl.ioctl(slave, termios.TIOCSWINSZ, struct.pack("HHHH", 40, 120, 960, 720))
    handler = classify(sample_docx_with_internal_link, tmp_path)
    viewer = pdfless.Viewer([handler], 0, 1, str(tmp_path), slave, None)
    viewer.refresh()

    viewer._ensure_link_index()
    found_on_page, link = _find_goto_links(viewer._link_index)[0]

    viewer.page = found_on_page
    viewer._load_page()
    viewer.scroll = 0
    viewer._activate_link(link)
    assert viewer.page == link["page"]
    assert viewer.scroll > 0


@requires_office_support
def test_doc_legacy_twopage_paginates_via_print_to_pdf(sample_twopage_doc, tmp_path):
    handler = classify(sample_twopage_doc, tmp_path)
    assert isinstance(handler, pdfless.OfficeDocument)
    pages = handler.build_pages(str(tmp_path))
    assert len(pages) == 2

    assert "日本語のサンプル段落" in "\n".join(handler.extract_text(1))
    assert "本文の続きです" in "\n".join(handler.extract_text(2))


@requires_office_support
def test_pages_twopage_renders_as_single_continuous_page(sample_twopage_pages, tmp_path):
    """Pages' Quick Look preview (iWork.qlgenerator) has the same
    shape as Word's here - no PageElementXPath - so it gets the same
    always-continuous FlowingText treatment as Word, even though the
    source document genuinely spans 2 physical pages."""
    handler = classify(sample_twopage_pages, tmp_path)
    assert isinstance(handler, pdfless.OfficeDocument)
    pages = handler.build_pages(str(tmp_path))
    assert len(pages) == 1


@requires_office_support
def test_pptx_twoslide_paginates_confidently(sample_twoslide_pptx, tmp_path):
    """PowerPoint's Quick Look generator names the slide boundary via
    PageElementXPath, so (unlike Word) this is trusted to paginate by
    default with no -c/--continuous involved - true regardless of
    whether soffice (see OfficeDocument._SOFFICE_EXTENSIONS) or the
    qlmanage/Chrome fallback ends up rendering it, since one soffice
    PDF page per slide was confirmed (by hand, against both this
    fixture and a real 55-slide deck) to land on the same page count
    either way."""
    handler = classify(sample_twoslide_pptx, tmp_path)
    assert isinstance(handler, pdfless.OfficeDocument)
    pages = handler.build_pages(str(tmp_path))
    assert len(pages) == 2


@requires_office_support
def test_ppt_legacy_twoslide_paginates_confidently(sample_twoslide_ppt, tmp_path):
    handler = classify(sample_twoslide_ppt, tmp_path)
    assert isinstance(handler, pdfless.OfficeDocument)
    pages = handler.build_pages(str(tmp_path))
    assert len(pages) == 2


@requires_office_support
def test_pptx_falls_back_to_qlmanage_when_soffice_missing(sample_twoslide_pptx, tmp_path, monkeypatch):
    """Regression test: with soffice unavailable (simulated here rather
    than relying on this machine's actual install state), PowerPoint
    must still render via the pre-existing qlmanage/Chrome + SlideDeck
    pipeline exactly as before soffice support existed - the same
    2-page result, just without a PDF delegate."""
    monkeypatch.setattr(pdfless, "find_soffice", lambda: None)
    handler = classify(sample_twoslide_pptx, tmp_path)
    assert isinstance(handler, pdfless.OfficeDocument)
    pages = handler.build_pages(str(tmp_path))
    assert len(pages) == 2
    assert handler._pdf_delegate is None


@requires_office_support
@requires_soffice
def test_pptx_becomes_searchable_and_gains_text_mode_via_its_pdf_delegate(sample_twoslide_pptx, tmp_path):
    """PowerPoint gains the same benefits Word already got from a real
    PDF delegate (see OfficeDocument.supports_search()/extract_text()):
    real per-page/bbox search, and - newly, since textutil (see
    extract_office_text()) has never been able to extract anything at
    all from a .pptx - working text mode with each slide's own text."""
    handler = classify(sample_twoslide_pptx, tmp_path)
    assert isinstance(handler, pdfless.OfficeDocument)
    handler.build_pages(str(tmp_path))
    assert handler._pdf_delegate is not None

    assert handler.supports_search() is True
    assert handler.text_mode_is_paginated() is True
    assert "サンプルスライド" in "\n".join(handler.extract_text(2))


@requires_office_support
def test_key_twoslide_renders_as_single_continuous_page(sample_twoslide_key, tmp_path):
    """Known gap (not a regression to fix here): unlike PowerPoint,
    Keynote's own Quick Look generator doesn't emit PageElementXPath
    at all, so a 2-slide .key deck isn't paginated confidently and
    falls back to a single continuously-scrollable page, the same as
    Word/Pages."""
    handler = classify(sample_twoslide_key, tmp_path)
    assert isinstance(handler, pdfless.OfficeDocument)
    pages = handler.build_pages(str(tmp_path))
    assert len(pages) == 1


@requires_office_support
@requires_soffice
def test_docm_uses_soffice_and_paginates_like_docx(sample_twopage_docm, tmp_path):
    """A macro-enabled Word document (.docm) already classifies as
    OfficeDocument via the same Office.qlgenerator that handles .docx
    (confirmed by hand), so adding it to _SOFFICE_EXTENSIONS is all
    that's needed for it to prefer soffice - real page breaks and a
    PDF delegate, the same as sample_twopage_docx."""
    handler = classify(sample_twopage_docm, tmp_path)
    assert isinstance(handler, pdfless.OfficeDocument)
    pages = handler.build_pages(str(tmp_path))
    assert len(pages) == 2
    assert handler._pdf_delegate is not None

    assert "日本語のサンプル段落" in "\n".join(handler.extract_text(1))
    assert "本文の続きです" in "\n".join(handler.extract_text(2))


@requires_office_support
@requires_soffice
def test_pptm_uses_soffice_and_paginates_like_pptx(sample_twoslide_pptm, tmp_path):
    """A macro-enabled PowerPoint deck (.pptm) already classifies as
    OfficeDocument via the same Office.qlgenerator that handles .pptx
    (confirmed by hand) - adding it to _SOFFICE_EXTENSIONS upgrades it
    from a PNG screenshot (the old SlideDeck path) to a real PDF, the
    same as sample_twoslide_pptx."""
    handler = classify(sample_twoslide_pptm, tmp_path)
    assert isinstance(handler, pdfless.OfficeDocument)
    pages = handler.build_pages(str(tmp_path))
    assert len(pages) == 2
    assert handler._pdf_delegate is not None

    assert "日本語の箇条書きサンプル" in "\n".join(handler.extract_text(1))
    assert "サンプルスライド" in "\n".join(handler.extract_text(2))


@requires_soffice
def test_odt_renders_via_soffice_with_real_page_breaks(sample_twopage_odt, tmp_path):
    """Quick Look has no generator at all for .odt (confirmed by hand:
    qlmanage crashes outright), so this only classifies via
    SofficeOnlyDocument, not OfficeDocument - and needs only soffice,
    not qlmanage/Chrome, to render (no requires_office_support here)."""
    handler = classify(sample_twopage_odt, tmp_path)
    assert isinstance(handler, pdfless.SofficeOnlyDocument)
    pages = handler.build_pages(str(tmp_path))
    assert len(pages) == 2
    assert handler._pdf_delegate is not None

    assert "日本語のサンプル段落" in "\n".join(handler.extract_text(1))
    assert "本文の続きです" in "\n".join(handler.extract_text(2))


@requires_soffice
def test_odp_renders_via_soffice_one_page_per_slide(sample_twoslide_odp, tmp_path):
    handler = classify(sample_twoslide_odp, tmp_path)
    assert isinstance(handler, pdfless.SofficeOnlyDocument)
    pages = handler.build_pages(str(tmp_path))
    assert len(pages) == 2
    assert handler._pdf_delegate is not None

    assert "日本語の箇条書きサンプル" in "\n".join(handler.extract_text(1))
    assert "サンプルスライド" in "\n".join(handler.extract_text(2))


@requires_soffice
def test_ods_renders_via_soffice_one_page_per_sheet_for_a_simple_workbook(sample_multisheet_ods, tmp_path):
    """One soffice PDF page per sheet (see
    _SOFFICE_SPREADSHEET_PDF_FILTER). This fixture is too simple to
    fragment even without that option (a real-world spreadsheet with
    its own print layout does - see SofficeOnlyDocument's docstring),
    since there's no reliable way to construct a reproducible
    fragmentation case as a small checked-in fixture."""
    handler = classify(sample_multisheet_ods, tmp_path)
    assert isinstance(handler, pdfless.SofficeOnlyDocument)
    pages = handler.build_pages(str(tmp_path))
    assert len(pages) == 3
    assert handler._pdf_delegate is not None

    assert "サンプルB" in "\n".join(handler.extract_text(3))


@requires_soffice
def test_odg_renders_via_soffice_one_page_per_draw_page(sample_odg, tmp_path):
    """Confirmed by hand on a real multi-page Draw file that soffice's
    PDF page count matches the source's own draw:page count exactly -
    this fixture only has one Draw page, so that's all this can check
    directly, but the extracted text still confirms the Japanese
    labels survive the conversion."""
    handler = classify(sample_odg, tmp_path)
    assert isinstance(handler, pdfless.SofficeOnlyDocument)
    pages = handler.build_pages(str(tmp_path))
    assert len(pages) == 1
    assert handler._pdf_delegate is not None

    assert "サンプル図形" in "\n".join(handler.extract_text(1))


@requires_soffice
def test_wmf_renders_via_soffice(sample_wmf, tmp_path):
    """Quick Look only ever produces a Preview.url dead end for WMF
    (confirmed by hand - the same issue SvgDocument's docstring
    describes for SVG), so soffice is the only way this renders at
    all."""
    handler = classify(sample_wmf, tmp_path)
    assert isinstance(handler, pdfless.SofficeOnlyDocument)
    pages = handler.build_pages(str(tmp_path))
    assert len(pages) == 1
    assert handler._pdf_delegate is not None

    assert "サンプル図形" in "\n".join(handler.extract_text(1))


def test_soffice_only_document_unavailable_without_soffice(sample_twopage_odt, tmp_path, monkeypatch):
    """Unlike Word/RTF/PowerPoint, there's nothing to fall back to for
    an ODF/Visio/WMF file when soffice isn't installed - it was
    entirely unsupported before SofficeOnlyDocument existed, so
    sniff() must return None (not raise, not half-render) and the file
    ends up unclassified by every HANDLER_CLASSES entry. Runs
    regardless of whether this machine actually has soffice, since
    find_soffice() is monkeypatched either way."""
    monkeypatch.setattr(pdfless, "find_soffice", lambda: None)
    assert pdfless.SofficeOnlyDocument.sniff(sample_twopage_odt, str(tmp_path)) is None
    assert classify(sample_twopage_odt, tmp_path) is None


@requires_office_support
def test_svg_renders_via_chrome_directly(sample_svg, tmp_path):
    """SvgDocument renders via a real PDF (Chrome's --print-to-pdf on
    an <img>-wrapped copy - see its docstring for why, and why not
    soffice), so - like Word's own crisp-zoom test - it should
    re-rasterize independently at whatever width is asked for, rather
    than resizing one fixed screenshot."""
    handler = classify(sample_svg, tmp_path)
    assert isinstance(handler, pdfless.SvgDocument)
    pages = handler.build_pages(str(tmp_path))
    assert len(pages) == 1
    assert handler._pdf_delegate is not None

    cache = pdfless.PageCache(str(tmp_path), handler)
    small = handler.get_page_image(cache, 1, 300, "width")
    big = handler.get_page_image(cache, 1, 900, "width")
    assert small.width == 300
    assert big.width == 900


def test_svg_falls_back_to_plain_text_without_chrome(sample_svg, tmp_path, monkeypatch):
    """With no Chrome available, SvgDocument.sniff() must return None
    so classification falls through to TextDocument (the pre-existing
    behavior - showing the SVG's own raw XML source) rather than the
    file going unclassified entirely, the same way RtfOfficeDocument
    falls through to RtfDocument without textutil."""
    monkeypatch.setattr(pdfless, "find_chrome", lambda: None)
    handler = classify(sample_svg, tmp_path)
    assert isinstance(handler, pdfless.TextDocument)
    assert not isinstance(handler, pdfless.SvgDocument)


def test_find_chrome_never_picks_vivaldi_from_path(monkeypatch):
    """Vivaldi's headless mode doesn't work, so it's excluded from
    CHROME_CANDIDATES - and must not sneak back in via the PATH fallback
    either, on a machine where it's the only Chromium-family browser."""
    monkeypatch.setattr(pdfless, "CHROME_CANDIDATES", ())
    monkeypatch.setattr(pdfless, "_default_browser_bundle_id", lambda: None)
    monkeypatch.setattr(
        pdfless.shutil, "which",
        lambda name: "/usr/bin/" + name if name.startswith("vivaldi") else None,
    )
    assert pdfless.find_chrome() is None
