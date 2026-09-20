"""Markdown support: rendered to a real PDF via the `markdown` +
`weasyprint` Python libraries (MarkdownDocument), not Quick Look,
Chrome, or LibreOffice - see pdfless.py's _render_markdown_pdf() for
why. requires_markdown_rendering gates on both libraries (and
weasyprint's own Cairo/Pango system libraries) actually being usable;
see conftest.py.
"""

import pdfless
from conftest import requires_markdown_rendering


def classify(path, tmp_path, debug=False):
    for cls in pdfless.HANDLER_CLASSES:
        handler = cls.sniff(path, str(tmp_path), debug=debug)
        if handler is not None:
            return handler
    return None


def test_markdown_css_constrains_images_to_the_page_width():
    """Regression test: a screenshot embedded in a Markdown file (e.g.
    README.md's own screenshots) is usually much wider than a rendered
    page, and with no img rule at all it renders at its native pixel
    width and spills off the right edge of the page (confirmed by
    hand opening README.md itself) rather than being scaled down to
    fit, the way a browser or any other Markdown renderer would."""
    assert "img" in pdfless.MARKDOWN_CSS
    assert "max-width: 100%" in pdfless.MARKDOWN_CSS


@requires_markdown_rendering
def test_markdown_renders_via_weasyprint_with_real_pagination(sample_md, tmp_path):
    """WeasyPrint has a real CSS pagination engine of its own, so a
    long-enough Markdown file (see conftest.py's sample_md fixture)
    naturally lands on more than one page - no measured/injected
    @page size needed the way FlowingText/SvgDocument require."""
    handler = classify(sample_md, tmp_path)
    assert isinstance(handler, pdfless.MarkdownDocument)
    pages = handler.build_pages(str(tmp_path))
    assert len(pages) == 2
    assert handler._pdf_delegate is not None


@requires_markdown_rendering
def test_markdown_text_mode_shows_raw_source(sample_md, tmp_path):
    """Text mode (`t`) shows the raw Markdown source from disk - not
    text extracted from the rendered PDF - so markup like `#` headings
    is still visible."""
    handler = classify(sample_md, tmp_path)
    assert isinstance(handler, pdfless.MarkdownDocument)
    handler.build_pages(str(tmp_path))
    assert handler.text_mode_is_paginated() is False

    source = handler.extract_text(1)
    assert source == handler.extract_text(2)
    joined = "\n".join(source)
    assert joined.startswith("# Lorem Ipsum Sample")
    assert "## リストの例" in joined
    assert "追加セクション2" in joined


@requires_markdown_rendering
def test_markdown_text_mode_toggle_reindexes_active_search(sample_md, tmp_path):
    """Markdown image mode searches the rendered PDF; text mode searches
    the raw source - different extractions, so `t` re-runs the same query
    in the new mode instead of carrying the match object across."""
    from test_search import make_viewer

    handler = classify(sample_md, tmp_path)
    handler.build_pages(str(tmp_path))
    viewer = make_viewer(handler)
    viewer.start_search("追加セクション2")
    assert viewer.search_query == "追加セクション2"
    assert viewer.search_matches
    assert len(viewer.search_matches[0]) == 5  # PDF bbox tuple

    assert viewer.enter_text_mode() is True
    assert viewer.text_mode is True
    assert viewer.search_query == "追加セクション2"
    assert viewer.search_matches
    assert len(viewer.search_matches[0]) == 3  # (line_idx, start, end)
    viewer._draw_text_unwrapped()  # must not raise

    assert viewer.toggle_text_mode() is True
    assert viewer.text_mode is False
    assert viewer.search_query == "追加セクション2"
    assert viewer.search_matches
    assert len(viewer.search_matches[0]) == 5  # PDF bbox again
    viewer.refresh()  # must not raise

    # A query that only exists in the raw source: reindex keeps the
    # query but finds no PDF bbox matches.
    assert viewer.enter_text_mode() is True
    viewer.start_search("## リスト")
    assert viewer.search_matches
    assert viewer.toggle_text_mode() is True
    assert viewer.search_query == "## リスト"
    assert viewer.search_matches == []
    assert viewer.search_pos is None
    viewer.refresh()  # must not raise


@requires_markdown_rendering
def test_markdown_image_mode_search_uses_pdf_delegate(sample_md, tmp_path):
    """Image-mode search still comes from the real PDF delegate's own
    per-page/bbox index - separate from text mode's whole-file source
    search."""
    handler = classify(sample_md, tmp_path)
    assert isinstance(handler, pdfless.MarkdownDocument)
    handler.build_pages(str(tmp_path))
    assert handler.supports_search() is True

    index = handler.build_search_index()
    assert len(index) == 2
    matches = handler.find_search_matches(index, "追加セクション2")
    assert any(page == 2 for page, *_ in matches)


@requires_markdown_rendering
def test_markdown_link_survives_as_a_real_pdf_link(sample_md, tmp_path):
    """A plain [text](url) link in the source survives WeasyPrint's
    HTML->PDF conversion as a real PDF /Link annotation (confirmed by
    hand with pypdf) - clickable exactly like a native PDF's
    hyperlink, via the same PdfDocument.build_link_index() a real
    PDF's links go through."""
    handler = classify(sample_md, tmp_path)
    assert isinstance(handler, pdfless.MarkdownDocument)
    pages = handler.build_pages(str(tmp_path))
    assert handler._pdf_delegate is not None

    link_index = handler._pdf_delegate.build_link_index(len(pages))
    links = link_index[0]["links"]
    assert any(link.get("uri") == "https://example.com/lorem-ipsum" for link in links)


def test_markdown_falls_back_to_plain_text_without_weasyprint(sample_md, tmp_path, monkeypatch):
    """With markdown/weasyprint unavailable (simulated here rather
    than relying on this machine's actual install state), a .md file
    must fall through to TextDocument (its own raw Markdown source)
    the same way an RTF file falls through to RtfDocument without
    textutil - not go unclassified entirely."""
    monkeypatch.setattr(pdfless, "_markdown_rendering_available", lambda: False)
    handler = classify(sample_md, tmp_path)
    assert isinstance(handler, pdfless.TextDocument)
    assert not isinstance(handler, pdfless.MarkdownDocument)


def test_markdown_rendering_available_survives_a_missing_system_library(monkeypatch, capsys):
    """Regression test: weasyprint's own import chain reaches into cffi
    to dlopen() the real Cairo/Pango/GLib shared libraries, and a
    missing one there raises a plain OSError, not an ImportError -
    confirmed by hand on a machine without those system libraries
    installed ("cannot load library 'libgobject-2.0-0'"), which used
    to crash the whole program on startup (an except ImportError-only
    clause let it straight through) instead of falling back to plain
    text like every other optional renderer here.

    Also confirms weasyprint's own multi-line "could not import some
    external libraries" print() (confirmed by hand to happen right
    before it raises, on that same missing-libraries path) never
    reaches the real terminal - pdfless spends most of its life with
    the terminal in raw mode showing an alternate screen, where a
    stray print from a library would look like a corrupted screen,
    not just unwanted noise."""
    import builtins

    real_import = builtins.__import__

    def fake_import(name, *args, **kwargs):
        if name == "weasyprint":
            print("\n-----\n\nWeasyPrint could not import some external libraries...\n\n-----\n")
            raise OSError("cannot load library 'libgobject-2.0-0'")
        return real_import(name, *args, **kwargs)

    monkeypatch.setattr(builtins, "__import__", fake_import)
    assert pdfless._markdown_rendering_available() is False

    captured = capsys.readouterr()
    assert captured.out == ""
    assert captured.err == ""


def test_ensure_homebrew_lib_path_adds_existing_dirs_to_dyld_fallback(monkeypatch):
    """Regression test: weasyprint's dlopen() of Cairo/Pango/GLib by
    bare name doesn't search Homebrew's own lib directory when running
    under a uv-managed standalone Python build (confirmed by hand on a
    free-threaded 3.14 install: the exact same Homebrew-installed
    libraries resolve fine under a Homebrew-installed Python, but not
    there) - even though the libraries are genuinely installed.
    _ensure_homebrew_lib_path_for_weasyprint() works around this by
    adding Homebrew's lib directory to DYLD_FALLBACK_LIBRARY_PATH
    (confirmed by hand this alone fixes the failing case) - this
    checks the environment-variable bookkeeping only, since actually
    exercising dlopen() itself needs a real missing-library machine to
    fail on in the first place."""
    monkeypatch.setattr(pdfless.sys, "platform", "darwin")
    monkeypatch.delenv("DYLD_FALLBACK_LIBRARY_PATH", raising=False)
    monkeypatch.setattr(pdfless.os.path, "isdir", lambda path: path == "/opt/homebrew/lib")

    pdfless._ensure_homebrew_lib_path_for_weasyprint()

    assert pdfless.os.environ["DYLD_FALLBACK_LIBRARY_PATH"] == "/opt/homebrew/lib"


def test_ensure_homebrew_lib_path_is_a_noop_off_macos(monkeypatch):
    monkeypatch.setattr(pdfless.sys, "platform", "linux")
    monkeypatch.delenv("DYLD_FALLBACK_LIBRARY_PATH", raising=False)

    pdfless._ensure_homebrew_lib_path_for_weasyprint()

    assert "DYLD_FALLBACK_LIBRARY_PATH" not in pdfless.os.environ
