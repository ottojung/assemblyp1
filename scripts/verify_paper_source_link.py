#!/usr/bin/env python3
"""Verify that the first-page permalink targets the CI checkout commit.

Usage: verify_paper_source_link.py PDF [EXPECTED_COMMIT]
The link is created by paper/build.sh (git rev-parse HEAD) at build time.
"""
from pathlib import Path
import subprocess
import sys

from pypdf import PdfReader


def main():
    if len(sys.argv) not in (2, 3):
        raise SystemExit("usage: verify_paper_source_link.py PDF [EXPECTED_COMMIT]")
    path = Path(sys.argv[1])
    sha = (sys.argv[2] if len(sys.argv) > 2 else subprocess.check_output(
        ["git", "rev-parse", "HEAD"], text=True).strip())
    assert len(sha) == 40 and all(c in "0123456789abcdef" for c in sha)
    expected = f"https://github.com/ottojung/assemblyp1/commit/{sha}"

    pdf = PdfReader(str(path))
    first = pdf.pages[0]
    text = first.extract_text()
    assert "Version: untagged" not in text
    assert "Source commit:" not in text
    assert "Source commit" in text

    urls = []
    bottom_urls = []
    height = float(first.mediabox.height)
    for ref in first.get("/Annots", []):
        annotation = ref.get_object()
        action = annotation.get("/A")
        if not action:
            continue
        action = action.get_object()
        if action.get("/S") != "/URI":
            continue
        uri = str(action["/URI"])
        urls.append(uri)
        rect = annotation.get("/Rect")
        if rect is not None and float(rect[1]) < height * .25:
            bottom_urls.append(uri)

    assert expected in urls, (expected, urls)
    assert expected in bottom_urls, ("link must be on bottom quarter", urls)
    print(f"First-page bottom permalink targets CI checkout: {expected}")
    print(f"PDF pages: {len(pdf.pages)}; source link validated")


if __name__ == "__main__":
    main()
