"""Background rendering of the page next to the one(s) on screen (see
Viewer._schedule_page_prefetch()), and the thread-safety PageCache needs
for it: the same page is never rendered twice at once, and a render
that outlives a clear() doesn't put its stale image back."""

import fcntl
import pty
import struct
import tempfile
import termios
import threading
import time

from PIL import Image

import pdfless


def make_viewer(handler, monkeypatch, continuous=False, debug=False):
    monkeypatch.setenv("TERM_PROGRAM", "iTerm.app")
    monkeypatch.delenv("TMUX", raising=False)
    _master, slave = pty.openpty()
    fcntl.ioctl(slave, termios.TIOCSWINSZ, struct.pack("HHHH", 30, 100, 800, 480))
    viewer = pdfless.Viewer(
        [handler], 0, 1, tempfile.mkdtemp(), slave, "width", continuous=continuous, debug=debug,
    )
    viewer.refresh()
    return viewer


def count_pdftoppm(monkeypatch):
    """The pages each pdftoppm run from here on rasterizes."""
    pages = []
    real = pdfless.run_subprocess

    def spy(cmd, *args, **kwargs):
        if cmd[0] == "pdftoppm" and "-f" in cmd:
            pages.append(int(cmd[cmd.index("-f") + 1]))
        return real(cmd, *args, **kwargs)
    monkeypatch.setattr(pdfless, "run_subprocess", spy)
    return pages


def settle(viewer):
    """Run the scheduler the way run_viewer()'s loop does, until it
    has nothing more to start."""
    for _ in range(10):
        viewer._schedule_page_prefetch()
        thread = viewer._page_prefetch_thread
        if thread is None or not thread.is_alive():
            return
        thread.join(10)


def test_the_next_page_is_rendered_in_the_background(sample_pdf, monkeypatch):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), monkeypatch)
    rendered = count_pdftoppm(monkeypatch)
    viewer._schedule_page_prefetch()
    assert viewer._page_prefetch_thread.name == "pdfless-page-prefetch-2"
    viewer._page_prefetch_thread.join(10)
    assert rendered == [2]
    viewer.go_page(2, 0)  # already rasterized: no pdftoppm of its own
    assert rendered == [2]


def test_turning_back_prefetches_the_previous_page_first(sample_pdf, monkeypatch):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), monkeypatch)
    viewer.go_page(5, 0)
    settle(viewer)
    viewer.go_page(4, 0)  # already cached from page 5's prefetch
    rendered = count_pdftoppm(monkeypatch)
    viewer._schedule_page_prefetch()
    viewer._page_prefetch_thread.join(10)
    assert rendered == [3]  # backwards, not 5 (already cached anyway)


def test_both_neighbors_then_nothing_more(sample_pdf, monkeypatch):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), monkeypatch)
    viewer.go_page(3, 0)
    rendered = count_pdftoppm(monkeypatch)
    settle(viewer)
    assert sorted(rendered) == [2, 4]
    viewer._schedule_page_prefetch()
    assert not viewer._page_prefetch_thread.is_alive()
    assert sorted(rendered) == [2, 4]


def test_continuous_prefetches_past_the_last_page_on_screen(sample_pdf, monkeypatch):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), monkeypatch, continuous=True)
    viewer.scroll = viewer.img.height - 10  # page 1's bottom edge, then page 2
    viewer.refresh()
    assert [p for p, _top, _img in viewer._layout] == [1, 2]
    rendered = count_pdftoppm(monkeypatch)
    viewer._schedule_page_prefetch()
    viewer._page_prefetch_thread.join(10)
    assert rendered == [3]


def test_nothing_is_prefetched_in_text_mode(sample_pdf, monkeypatch):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), monkeypatch)
    assert viewer.enter_text_mode()
    viewer._schedule_page_prefetch()
    assert viewer._page_prefetch_thread is None


def test_debug_shows_the_background_page_render(sample_pdf, monkeypatch, capsys):
    viewer = make_viewer(pdfless.PdfDocument(sample_pdf), monkeypatch, debug=True)
    capsys.readouterr()
    viewer._schedule_page_prefetch()
    viewer._page_prefetch_thread.join(10)
    assert "page 2" not in capsys.readouterr().err  # queued, not printed yet
    pdfless.flush_background_debug()
    err = capsys.readouterr().err
    assert "page 2: rendering in the background" in err
    assert "page 2: rendered in the background in" in err


class _SlowHandler(pdfless.DocumentHandler):
    """Renders a blank page of the requested width, slowly, counting
    each render - for PageCache's own thread-safety."""

    def __init__(self):
        self.path = "slow"
        self.renders = []

    def get_page_image(self, cache, page, target_px, fit):
        key = (page, target_px)
        cached = cache._cached(key)
        if cached is not None:
            return cached
        self.renders.append(page)
        time.sleep(0.3)
        img = Image.new("RGB", (target_px, target_px))
        cache._store(key, img)
        return img


def test_a_page_being_rendered_is_waited_for_not_rendered_again(tmp_path):
    handler = _SlowHandler()
    cache = pdfless.PageCache(str(tmp_path), handler)
    background = threading.Thread(target=cache.get, args=(2, 100))
    background.start()
    time.sleep(0.1)
    assert cache.has(2, 100)  # under way counts
    img = cache.get(2, 100)  # waits for the background render
    background.join()
    assert handler.renders == [2]
    assert img.size == (100, 100)
    assert cache.has(2, 100)
    assert not cache.has(2, 200)  # a different size is a different request


def test_a_render_outliving_a_clear_is_not_kept(tmp_path):
    handler = _SlowHandler()
    cache = pdfless.PageCache(str(tmp_path), handler)
    background = threading.Thread(target=cache.get, args=(2, 100))
    background.start()
    time.sleep(0.1)
    cache.clear()  # e.g. the file was reloaded meanwhile
    background.join()
    assert not cache.has(2, 100)
    cache.get(2, 100)
    assert handler.renders == [2, 2]  # rendered afresh


def test_has_forgets_an_evicted_page(tmp_path):
    handler = _SlowHandler()
    cache = pdfless.PageCache(str(tmp_path), handler, size=2)
    for page in (1, 2, 3):
        cache.get(page, 10)
    assert not cache.has(1, 10)
    assert cache.has(2, 10) and cache.has(3, 10)


def test_the_memory_budget_evicts_all_but_the_pages_in_use(tmp_path, monkeypatch):
    """Past PAGE_CACHE_MAX_BYTES, the least recently used pages go -
    but never below PAGE_CACHE_MIN_KEEP (the page on screen and its
    two prefetched neighbors)."""
    monkeypatch.setattr(pdfless, "PAGE_CACHE_MAX_BYTES", 10 * 100 * 100 * 3)  # ten 100x100 RGB pages
    handler = _SlowHandler()
    monkeypatch.setattr(pdfless.time, "sleep", lambda s: None)
    cache = pdfless.PageCache(str(tmp_path), handler, size=20)
    for page in range(1, 13):
        cache.get(page, 100)
    assert [p for p in range(1, 13) if cache.has(p, 100)] == list(range(3, 13))
    cache.get(20, 1000)  # one page far over the budget on its own
    assert [p for p in range(1, 13) if cache.has(p, 100)] == [11, 12]
    assert cache.has(20, 1000)
