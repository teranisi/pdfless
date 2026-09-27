"""pdfless._open_in_default_app(): the macOS-only half of "v" (see
run_viewer()) - hands a file off to macOS's own `open` command. Unit-
tested directly here (monkeypatching sys.platform/subprocess.Popen) since
the key-dispatch/follow-mode side effect lives in run_viewer()'s own
blocking loop, exercised separately via a real pty in
test_viewer_integration.py."""

import pdfless


class FakePopen:
    calls = []

    def __init__(self, args, **kwargs):
        FakePopen.calls.append((args, kwargs))


def test_returns_false_and_does_nothing_off_macos(monkeypatch):
    monkeypatch.setattr(pdfless.sys, "platform", "linux")
    FakePopen.calls = []
    monkeypatch.setattr(pdfless.subprocess, "Popen", FakePopen)

    assert pdfless._open_in_default_app("/tmp/some.pdf") is False
    assert FakePopen.calls == []


def test_launches_open_with_the_given_path_on_macos(monkeypatch):
    monkeypatch.setattr(pdfless.sys, "platform", "darwin")
    FakePopen.calls = []
    monkeypatch.setattr(pdfless.subprocess, "Popen", FakePopen)

    assert pdfless._open_in_default_app("/tmp/some.pdf") is True
    assert len(FakePopen.calls) == 1
    args, kwargs = FakePopen.calls[0]
    assert args == ["open", "/tmp/some.pdf"]
    # Fire-and-forget, detached from pdfless's own raw-mode terminal/
    # session - this is an independent program, not a helper that
    # should share pdfless's tty or die along with it.
    assert kwargs.get("stdin") is pdfless.subprocess.DEVNULL
    assert kwargs.get("stdout") is pdfless.subprocess.DEVNULL
    assert kwargs.get("stderr") is pdfless.subprocess.DEVNULL
    assert kwargs.get("start_new_session") is True


def test_returns_false_if_open_itself_cant_be_started(monkeypatch):
    monkeypatch.setattr(pdfless.sys, "platform", "darwin")

    def raising_popen(*args, **kwargs):
        raise OSError("no such file or directory: open")

    monkeypatch.setattr(pdfless.subprocess, "Popen", raising_popen)

    assert pdfless._open_in_default_app("/tmp/some.pdf") is False
