import pdfless


def test_pdf_page_cache_returns_sized_image_and_hits_cache(sample_pdf, tmp_path):
    handler = pdfless.PdfDocument(sample_pdf)
    cache = pdfless.PageCache(str(tmp_path), handler)
    img = cache.get(1, 400, fit="width")
    assert img.width == 400

    img_again = cache.get(1, 400, fit="width")
    assert img_again is img, "a repeat request at the same size should hit the cache"


def test_image_page_cache_returns_correctly_sized_image(sample_image, tmp_path):
    handler = pdfless.ImageDocument(sample_image)
    cache = pdfless.PageCache(str(tmp_path), handler)
    img = cache.get(1, 128, fit="width")
    # original is 64x48 (4:3) - scaled to 128 wide keeps that ratio
    assert img.width == 128
    assert img.height == 96


def test_office_page_cache_reads_from_handler_pages_live(tmp_path):
    """OfficeDocument._source_for_page() must read self.pages fresh
    each call (not a copy captured elsewhere), since Viewer.reload()
    (after a -F/--follow change) replaces it via a fresh build_pages()
    call on the very same handler instance."""
    from PIL import Image

    page1 = tmp_path / "page1.png"
    page2 = tmp_path / "page2.png"
    Image.new("RGB", (100, 100), "red").save(page1)
    Image.new("RGB", (100, 100), "blue").save(page2)

    handler = pdfless.OfficeDocument("/does/not/matter.pptx")
    handler.pages = [str(page1)]
    cache = pdfless.PageCache(str(tmp_path), handler)
    first = cache.get(1, 50, fit="width")
    assert first.getpixel((0, 0))[:3] == (255, 0, 0)

    # Simulate a -F/--follow reload: build_pages() (via
    # _render_and_remember()) replaces handler.pages, and Viewer clears
    # the cache so the new pages actually get (re)loaded.
    handler.pages = [str(page2)]
    cache.clear()
    second = cache.get(1, 50, fit="width")
    assert second.getpixel((0, 0))[:3] == (0, 0, 255)
