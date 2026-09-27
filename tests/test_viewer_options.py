"""ViewerOptions: the startup options main() builds once from the parsed
command line and hands through run_viewer() to the Viewer."""

import argparse
import pty
import tempfile

import pytest

import pdfless


def namespace(**overrides):
    """What main()'s argparse produces with no options given, plus
    `overrides`."""
    defaults = dict(
        fit_height=False, border=True, chop_long_lines=False, eol_mark=True,
        line_numbers=False, scrollbar=True, wheel_scroll_step=2,
        incremental_scroll=True, debug=False, rendering_scale=1.0,
        continuous=False, follow=False, quit_if_one_screen=False, keep=False,
    )
    defaults.update(overrides)
    return argparse.Namespace(**defaults)


def test_from_args_maps_the_command_line():
    opts = pdfless.ViewerOptions.from_args(
        namespace(fit_height=True, chop_long_lines=True, border=False, continuous=True,
                  quit_if_one_screen=True, keep=True),
        nfiles=1,
    )
    assert opts.fit == "height"
    assert opts.wrap is False  # -S means "don't wrap"
    assert opts.border is False
    assert opts.continuous is True
    assert opts.quit_if_one_screen is True
    assert opts.keep is True


def test_quit_if_one_screen_only_applies_to_a_single_file():
    opts = pdfless.ViewerOptions.from_args(namespace(quit_if_one_screen=True), nfiles=2)
    assert opts.quit_if_one_screen is False


def test_defaults_match_the_command_line_defaults():
    assert pdfless.ViewerOptions.from_args(namespace(), nfiles=1) == pdfless.ViewerOptions()


def test_viewer_takes_options_or_keywords_but_not_both(sample_pdf):
    handler = pdfless.PdfDocument(sample_pdf)
    fd = pty.openpty()[1]
    viewer = pdfless.Viewer([handler], 0, 1, tempfile.mkdtemp(), fd,
                            options=pdfless.ViewerOptions(continuous=True, scrollbar=False))
    assert viewer.continuous is True and viewer.scrollbar is False
    viewer = pdfless.Viewer([handler], 0, 1, tempfile.mkdtemp(), fd, "height", continuous=True)
    assert viewer.options.fit == "height" and viewer.continuous is True
    with pytest.raises(TypeError):
        pdfless.Viewer([handler], 0, 1, tempfile.mkdtemp(), fd,
                       options=pdfless.ViewerOptions(), continuous=True)
    with pytest.raises(TypeError):
        pdfless.Viewer([handler], 0, 1, tempfile.mkdtemp(), fd, no_such_option=True)
