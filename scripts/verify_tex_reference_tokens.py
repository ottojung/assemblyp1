#!/usr/bin/env python3
"""Reject broken LaTeX reference commands that still render as literal text.

A mistakenly escaped \ref can silently turn into a newline plus "ef{label}"
without triggering an undefined-reference warning in the PDF build.
"""
from pathlib import Path
import re
import sys

def main():
    failures = []
    for path in sorted(Path("paper").rglob("*.tex")):
        source = path.read_text()
        # This cannot match an intact \ref: its "ef{" is preceded by "r".
        for match in re.finditer(r"(?<![A-Za-z\\])ef\{[A-Za-z0-9:._-]+\}", source):
            line = source.count("\n", 0, match.start()) + 1
            failures.append(f"{path}:{line}: malformed ref token: {match.group()}")
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    print("LaTeX reference tokens: PASS")
    return 0

if __name__ == "__main__":
    sys.exit(main())
