"""Background preparation of the next file while one is on screen (see
Viewer._schedule_prefetch()): the next file is classified and, for a
RenderedDocument, rendered off the main thread, and switching to it
while that's still under way waits for it instead of rendering twice."""

import fcntl
import os
import pty
import struct
import tempfile
import termios
import threading
import time

import pdfless


class _SlowRenderedDoc(pdfless.RenderedDocument):
    """A RenderedDocument whose render takes a while and records which
    thread did it - one pre-made image as its single page."""

    renders: list = []
    image = None

    def _cache_key_suffix(self, render_scale):
        return None  # never the persistent cache

    def _renderer(self, tmpdir, debug, render_scale, progress):
        def render():
            _SlowRenderedDoc.renders.append(threading.current_thread().name)
            time.sleep(0.5)
            return [_SlowRenderedDoc.image]
        return render


def make_viewer(files):
    _master, slave = pty.openpty()
    fcntl.ioctl(slave, termios.TIOCSWINSZ, struct.pack("HHHH", 30, 100, 800, 480))
    viewer = pdfless.Viewer(files, 0, 1, tempfile.mkdtemp(), slave, "width")
    viewer.refresh()
    return viewer


def test_the_next_file_renders_in_the_background(sample_pdf, sample_image, monkeypatch):
    _SlowRenderedDoc.renders = []
    _SlowRenderedDoc.image = sample_image
    monkeypatch.setattr(pdfless, "_sniff_file", lambda path, tmpdir, debug=False: _SlowRenderedDoc(path))
    viewer = make_viewer([pdfless.PdfDocument(sample_pdf), "next.slow"])

    viewer._schedule_prefetch()
    time.sleep(0.1)
    assert _SlowRenderedDoc.renders == ["pdfless-prefetch-1"]  # started, off the main thread
    viewer.next_file()  # while it's still rendering: waits for it
    assert viewer.file_index == 1
    assert viewer.npages == 1
    assert _SlowRenderedDoc.renders == ["pdfless-prefetch-1"]  # not rendered a second time


def test_prefetch_goes_one_file_ahead_once(sample_pdf, sample_image, monkeypatch):
    _SlowRenderedDoc.renders = []
    _SlowRenderedDoc.image = sample_image
    monkeypatch.setattr(pdfless, "_sniff_file", lambda path, tmpdir, debug=False: _SlowRenderedDoc(path))
    viewer = make_viewer([pdfless.PdfDocument(sample_pdf), "b.slow", "c.slow"])
    viewer._schedule_prefetch()
    viewer._schedule_prefetch()  # already under way: no second one
    viewer._prefetching[1].wait(5)
    viewer._schedule_prefetch()  # already done for file 2: not again
    assert _SlowRenderedDoc.renders == ["pdfless-prefetch-1"]
    viewer.next_file()  # lands on file 2 and prefetches file 3
    viewer._prefetching[2].wait(5)
    assert _SlowRenderedDoc.renders == ["pdfless-prefetch-1", "pdfless-prefetch-2"]


def test_run_subprocess_leaves_the_tty_alone_off_the_main_thread(monkeypatch):
    calls = []
    monkeypatch.setattr(pdfless, "_CTRL_C_FD", pty.openpty()[1])
    monkeypatch.setattr(pdfless.termios, "tcsetattr", lambda *a: calls.append(a))
    t = threading.Thread(target=pdfless.run_subprocess, args=(["true"],))
    t.start()
    t.join()
    assert calls == []


def test_debug_shows_the_background_render(sample_pdf, sample_image, monkeypatch, capsys):
    """Under -d, a background prefetch's own debug lines (start, stage
    timings, finish) are queued rather than printed from its thread -
    so they can't land in the middle of a screen write - and printed by
    the main thread's flush_background_debug()."""
    _SlowRenderedDoc.renders = []
    _SlowRenderedDoc.image = sample_image
    monkeypatch.setattr(pdfless, "_sniff_file", lambda path, tmpdir, debug=False: _SlowRenderedDoc(path))
    viewer = make_viewer([pdfless.PdfDocument(sample_pdf), "next.slow"])
    viewer.debug = True
    capsys.readouterr()
    viewer._schedule_prefetch()
    viewer._prefetching[1].wait(5)
    viewer._prefetch_thread.join(5)
    assert "next.slow" not in capsys.readouterr().err  # queued, not printed yet
    pdfless.flush_background_debug()
    err = capsys.readouterr().err
    assert "next.slow: preparing in the background (file 2/2)" in err
    assert "next.slow: prepared in the background in" in err
