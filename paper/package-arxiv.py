#!/usr/bin/env python3
"""Create a self-contained, minimal arXiv LaTeX source archive.

No git, Guix, Lean, generated metadata, or TeX installation is required.
Compile the extracted archive with pdfLaTeX + Biber.
"""
from __future__ import annotations

import argparse
import re
from pathlib import Path
from zipfile import ZIP_DEFLATED, ZipFile, ZipInfo

PAPER = Path(__file__).resolve().parent
EXPECTED = (
    [Path("main.tex"), Path("preamble.tex"), Path("references.bib")]
    + sorted(p.relative_to(PAPER) for p in (PAPER / "sections").glob("*.tex"))
)
INPUT = re.compile(r"\\(?:input|include|addbibresource)\s*\{([^}]+)\}")
FORBIDDEN = ("build-identity.tex", r"\AssemblyCommit",
             r"\AssemblyPaperTag", r"\AssemblyLeanToolchain",
             r"\AssemblyMathlibRevision", "assemblyp1/commit/")


def validate() -> None:
    names = set(EXPECTED)
    if not EXPECTED[3:]:
        raise ValueError("No manuscript sections found")
    for relative in EXPECTED:
        source = PAPER / relative
        if not source.is_file() or source.is_symlink():
            raise ValueError(f"Missing or invalid source: {relative}")
        text = source.read_text(encoding="utf-8")
        for token in FORBIDDEN:
            if token in text:
                raise ValueError(f"Generated/commit-specific text in {relative}: {token}")
        for match in INPUT.finditer(text):
            path = Path(match.group(1))
            if not path.suffix:
                path = path.with_suffix(".tex")
            if path not in names:
                raise ValueError(f"Unpacked source missing {path} referenced by {relative}")
    main = (PAPER / "main.tex").read_text(encoding="utf-8")
    if r"\begin{document}" not in main or r"\end{document}" not in main:
        raise ValueError("main.tex is not a complete manuscript")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=PAPER / "assemblyp1-arxiv-source.zip")
    options = parser.parse_args()
    validate()
    target = options.output.resolve()
    target.parent.mkdir(parents=True, exist_ok=True)
    with ZipFile(target, "w") as out:
        for relative in EXPECTED:
            # Stable ZIP metadata makes repeated runs byte-identical.
            member = ZipInfo(relative.as_posix(), date_time=(2026, 1, 1, 0, 0, 0))
            member.compress_type = ZIP_DEFLATED
            member.external_attr = 0o644 << 16
            out.writestr(member, (PAPER / relative).read_bytes(), compress_type=ZIP_DEFLATED)
    with ZipFile(target) as check:
        if check.testzip() is not None:
            raise ValueError("Corrupt arXiv source ZIP")
        if set(check.namelist()) != {p.as_posix() for p in EXPECTED}:
            raise ValueError("Unexpected arXiv ZIP members")
    print(f"arXiv source: {target} ({len(EXPECTED)} inputs, {target.stat().st_size} bytes)")


if __name__ == "__main__":
    main()
