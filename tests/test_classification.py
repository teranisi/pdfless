import pdfless

from conftest import requires_office_support


def classify(path, tmp_path, debug=False):
    """Mirror main()'s HANDLER_CLASSES dispatch loop: the first sniff()
    that matches wins; a positively-identified-but-broken file raises
    UnusableFile instead of returning None."""
    for cls in pdfless.HANDLER_CLASSES:
        handler = cls.sniff(path, str(tmp_path), debug=debug)
        if handler is not None:
            return handler
    return None


def test_pdf_classified_as_pdf(sample_pdf, tmp_path):
    handler = classify(sample_pdf, tmp_path)
    assert isinstance(handler, pdfless.PdfDocument)
    assert handler.kind == "pdf"
    assert handler.page_count() >= 1


def test_image_classified_as_image(sample_image, tmp_path):
    handler = classify(sample_image, tmp_path)
    assert isinstance(handler, pdfless.ImageDocument)
    assert handler.kind == "image"
    assert handler.page_count() == 1


def test_plain_text_classified_as_text(sample_text, tmp_path):
    handler = classify(sample_text, tmp_path)
    assert isinstance(handler, pdfless.TextDocument)
    assert not isinstance(handler, pdfless.RtfDocument)
    assert handler.kind == "text"
    assert handler.extract_text(1) == ["line one", "line two", "line three"]


@requires_office_support
def test_rtf_classified_as_rtf_office_document(sample_rtf, tmp_path):
    """When qlmanage + Chrome are available, an RTF file is rendered as
    an image via a textutil-to-docx conversion (RtfOfficeDocument, see
    _rtf_to_docx()) - the same as any other Word document, rather than
    only ever being shown as plain text."""
    handler = classify(sample_rtf, tmp_path)
    assert isinstance(handler, pdfless.RtfOfficeDocument)
    assert handler.kind == "office"

    pages = handler.build_pages(str(tmp_path))
    assert pages
    assert len(pages) == 1  # always continuous - see test below

    lines = handler.extract_text(1)
    assert lines is not None
    text = "\n".join(lines)
    assert "Hello from a test RTF file" in text
    # The raw RTF control words must NOT leak into what's shown.
    assert r"\rtf1" not in text


@requires_office_support
def test_rtf_office_document_always_renders_continuous(sample_rtf, tmp_path):
    """A converted RTF's page-height pagination doesn't correspond to
    anything in the original RTF (it's just whatever page size
    textutil's docx conversion happened to declare), so
    RtfOfficeDocument.build_pages() always renders it with
    continuous=True internally."""
    handler = classify(sample_rtf, tmp_path)
    assert isinstance(handler, pdfless.RtfOfficeDocument)

    pages = handler.build_pages(str(tmp_path))
    assert pages is not None
    assert len(pages) == 1


def test_rtf_falls_back_to_plain_text_without_textutil(sample_rtf, tmp_path, monkeypatch):
    """Without soffice or textutil (e.g. a minimal non-macOS install),
    RtfOfficeDocument.sniff() can't render the file at all - via
    soffice directly, or by converting to .docx first - so
    HANDLER_CLASSES falls through to the plain-text-only RtfDocument
    instead (see HANDLER_CLASSES' ordering). find_soffice() checks
    SOFFICE_CANDIDATES' fixed paths before ever calling shutil.which()
    (see its own docstring), so that alone has to be patched too, not
    just shutil.which("soffice") - otherwise a real local LibreOffice
    install (found via one of those fixed paths) would still win."""
    real_which = pdfless.shutil.which
    monkeypatch.setattr(
        pdfless.shutil, "which",
        lambda name: None if name == "textutil" else real_which(name),
    )
    monkeypatch.setattr(pdfless, "find_soffice", lambda: None)
    handler = classify(sample_rtf, tmp_path)
    assert isinstance(handler, pdfless.RtfDocument)
    assert not isinstance(handler, pdfless.RtfOfficeDocument)
    assert handler.kind == "text"


def test_corrupt_pdf_raises_unusable_file_not_silently_skipped(tmp_path):
    bad = tmp_path / "corrupt.pdf"
    bad.write_bytes(b"%PDF-1.4\nnot actually a valid pdf")
    raised = False
    try:
        classify(str(bad), tmp_path)
    except pdfless.UnusableFile as e:
        raised = True
        assert "PDF" in str(e)
    assert raised, "a corrupt PDF should raise UnusableFile, not fall through silently"


def test_encrypted_pdf_classifies_as_pdf_without_prompting(sample_encrypted_pdf, tmp_path):
    """sniff() alone must never prompt for a password - only actually
    reading the file (page_count(), the first such call - see
    _ensure_unlocked()) does, so a password-protected PDF that's merely
    being classified (not the one about to be shown) is left alone."""
    handler = classify(sample_encrypted_pdf, tmp_path)
    assert isinstance(handler, pdfless.PdfDocument)
    assert handler.encrypted


def test_encrypted_pdf_unlocks_with_correct_password(sample_encrypted_pdf, tmp_path, monkeypatch):
    handler = classify(sample_encrypted_pdf, tmp_path)
    monkeypatch.setattr(pdfless, "_prompt_pdf_password", lambda filename, message=None: "secret123")
    assert handler.page_count() == 7
    assert not handler.encrypted
    assert handler.password == "secret123"


def test_encrypted_pdf_retries_after_wrong_password(sample_encrypted_pdf, tmp_path, monkeypatch):
    attempts = iter(["wrong", "still wrong", "secret123"])
    monkeypatch.setattr(pdfless, "_prompt_pdf_password", lambda filename, message=None: next(attempts))
    handler = classify(sample_encrypted_pdf, tmp_path)
    assert handler.page_count() == 7
    assert handler.password == "secret123"


def test_encrypted_pdf_cancelled_prompt_raises_unusable_file(sample_encrypted_pdf, tmp_path, monkeypatch):
    """Esc/^C/^D at the prompt (modeled here by _prompt_pdf_password
    returning None, as both the cooked and raw-mode implementations do
    on cancellation) is reported the same as any other unusable file -
    go_to_file() and main()'s own candidate search already both know
    how to handle that."""
    monkeypatch.setattr(pdfless, "_prompt_pdf_password", lambda filename, message=None: None)
    handler = classify(sample_encrypted_pdf, tmp_path)
    try:
        handler.page_count()
        assert False, "cancelling the password prompt should raise UnusableFile"
    except pdfless.UnusableFile as e:
        assert "password" in str(e)


def test_password_protected_docx_raises_unusable_file_not_silently_skipped(tmp_path):
    """A password-protected .docx/.pptx/... is an OLE/CFB container
    (MS-OFFCRYPTO) instead of the plain ZIP it normally is - detected
    upfront (see is_password_protected_ooxml_or_visio()) so pdfless
    skips it with a clear reason instead of committing to a soffice/
    qlmanage render that's bound to fail uninformatively."""
    bad = tmp_path / "protected.docx"
    bad.write_bytes(pdfless._CFB_MAGIC + b"\x00" * 32)
    raised = False
    try:
        classify(str(bad), tmp_path)
    except pdfless.UnusableFile as e:
        raised = True
        assert "password" in str(e)
    assert raised, "a password-protected .docx should raise UnusableFile, not fall through silently"


def test_password_protected_vsdx_raises_unusable_file(tmp_path):
    bad = tmp_path / "protected.vsdx"
    bad.write_bytes(pdfless._CFB_MAGIC + b"\x00" * 32)
    raised = False
    try:
        classify(str(bad), tmp_path)
    except pdfless.UnusableFile as e:
        raised = True
        assert "password" in str(e)
    assert raised


def test_ordinary_docx_is_unaffected_by_the_cfb_check(sample_docx, tmp_path):
    """A normal (unencrypted) .docx is a plain ZIP, not CFB - make sure
    the new upfront check doesn't misclassify it."""
    assert not pdfless.is_password_protected_ooxml_or_visio(sample_docx)


def test_invalid_utf8_non_pdf_file_raises_unusable_file(tmp_path):
    bad = tmp_path / "bad.txt"
    # No NUL byte (so is_probably_text() says yes), but not valid UTF-8.
    bad.write_bytes(b"\xff\xfe invalid utf8, no nul bytes here")
    raised = False
    try:
        classify(str(bad), tmp_path)
    except pdfless.UnusableFile as e:
        raised = True
        assert "UTF-8" in str(e)
    assert raised


def test_unrecognizable_binary_file_classifies_as_none(tmp_path):
    junk = tmp_path / "junk.bin"
    junk.write_bytes(b"\x00\x01\x02\xff\xfe")
    assert classify(str(junk), tmp_path) is None


def test_capability_matrix_matches_expectations(
    sample_pdf, sample_image, sample_text, tmp_path
):
    pdf = classify(sample_pdf, tmp_path)
    image = classify(sample_image, tmp_path)
    text = classify(sample_text, tmp_path)

    assert (pdf.supports_text_mode(), pdf.supports_search(), pdf.text_mode_is_paginated()) == (
        True, True, True,
    )
    assert (image.supports_text_mode(), image.supports_search(), image.text_mode_is_paginated()) == (
        True, False, False,
    )
    assert (text.supports_text_mode(), text.supports_search(), text.text_mode_is_paginated()) == (
        True, True, False,
    )


