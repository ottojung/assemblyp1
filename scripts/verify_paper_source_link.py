#!/usr/bin/env python3
"""Verify the exact, readable source URL in the PDF reproduction appendix.

Usage: verify_paper_source_link.py PDF [EXPECTED_COMMIT]
paper/build.sh derives EXPECTED_COMMIT from the actual checkout at build time.
The URL must be visible in full, clickable, and absent from the cover page.
"""
from pathlib import Path
import subprocess
import sys

from pypdf import PdfReader


def uri_annotations(page):
    for ref in page.get("/Annots", []):
        annotation = ref.get_object()
        action = annotation.get("/A")
        if not action:
            continue
        action = action.get_object()
        if action.get("/S") != "/URI":
            continue
        yield str(action["/URI"])


def main():
    if len(sys.argv) not in (2, 3):
        raise SystemExit("usage: verify_paper_source_link.py PDF [EXPECTED_COMMIT]")
    path = Path(sys.argv[1])
    sha = (sys.argv[2] if len(sys.argv) > 2 else subprocess.check_output(
        ["git", "rev-parse", "HEAD"], text=True).strip())
    assert len(sha) == 40 and all(c in "0123456789abcdef" for c in sha)
    expected = f"https://github.com/ottojung/assemblyp1/commit/{sha}"

    pdf = PdfReader(str(path))
    assert len(pdf.pages) > 1
    cover = pdf.pages[0]
    assert "Source commit" not in (cover.extract_text() or "")
    assert expected not in list(uri_annotations(cover)), (
        "The source link must not appear on the first page"
    )

    matches = []
    for index, page in enumerate(pdf.pages):
        links = list(uri_annotations(page))
        if expected not in links:
            continue
        text = page.extract_text() or ""
        visible_text = "".join(text.split())
        assert expected in visible_text, (
            "Full URL must be printed as text, not hidden under a label",
            index + 1,
        )
        assert ("Reproducible source revision and proof checks" in text
                or "Reproducing the results" in text), (
            "The URL belongs in the reproduction appendix", index + 1
        )
        matches.append(index + 1)

    assert len(matches) == 1 and matches[0] > 1, (
        "Expected one visible, clickable revision URL in the appendix",
        expected, matches,
    )
    print(f"Reproducibility appendix page {matches[0]} displays and links: {expected}")
    print(f"PDF pages: {len(pdf.pages)}; cover is free of source links")


if __name__ == "__main__":
    main()
