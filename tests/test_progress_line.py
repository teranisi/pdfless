"""_ProgressLine must stay on one terminal row and fully erase itself -
a long basename in "name: converting..." used to wrap on stderr and
leave ghost lines behind after clear()."""

import io
from collections import namedtuple

import pdfless


class _FakeStderr(io.StringIO):
    def isatty(self):
        return True

    def fileno(self):
        raise OSError("not a real fd")


def test_progress_line_truncates_and_clears_long_filename(monkeypatch):
    cols = 40
    stderr = _FakeStderr()
    monkeypatch.setattr(pdfless.sys, "stderr", stderr)
    size = namedtuple("Size", "columns lines")(columns=cols, lines=24)
    monkeypatch.setattr(pdfless.shutil, "get_terminal_size", lambda: size)

    progress = pdfless._ProgressLine(True)
    long_name = "x" * 100 + ".docx"
    progress.update(f"{long_name}: converting via LibreOffice...")
    written = stderr.getvalue()
    assert "\n" not in written
    assert pdfless.display_width(written.lstrip("\r")) <= cols

    progress.clear()
    assert stderr.getvalue().endswith("\r\x1b[2K")
