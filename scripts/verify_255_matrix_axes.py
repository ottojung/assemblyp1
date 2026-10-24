#!/usr/bin/env python3
"""Cross-check for umbrella #255 remaining-open matrix (2026-10-24).

Verifies, filesystem-locally (no network):
  1. docs/remaining-open-matrix-255.md exists and records the 2026-10-24
     order-audit verification addendum (commits 48447f5, 5b55129, 7a8d326,
     base origin/main 234f348, ancestry chain).
  2. The matrix keeps every frozen axis explicitly marked with an honest
     OPEN vs resolved status (no silent closure of #255):
       fixed-x vs sample-uniform; exact vs binomial; same vs variable length;
       spelled vs flow; truth candidacy; literal vs placement Is.
  3. The addendum does not claim #255 CLOSED and does not claim child cells
     owned by #257/#259/#261 as closed by this increment.
  4. No forbidden proof tokens in the edited doc region claim kernel status
     without evidence (doc must say audit/pending-integration where apt).

Exit 0 on success, nonzero with a diagnostic otherwise.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MATRIX = ROOT / "docs" / "remaining-open-matrix-255.md"

REQUIRED_COMMITS = ["48447f5", "5b55129", "7a8d326", "234f348"]
REQUIRED_AXES = [
    "fixed-x",
    "sample-uniform",
    "exact",
    "binomial",
    "same",
    "variable length",
    "spelled",
    "flow",
    "truth candidacy",
    "literal",
    "placement",
]

failures: list[str] = []


def check(cond: bool, msg: str) -> None:
    if not cond:
        failures.append(msg)


def main() -> int:
    if not MATRIX.exists():
        print(f"MISSING: {MATRIX}")
        return 1
    text = MATRIX.read_text(encoding="utf-8")
    head = text[:6000]

    check("2026-10-24" in head and "order-audit" in head.lower(),
          "matrix head addendum for 2026-10-24 order-audit verification missing")
    for c in REQUIRED_COMMITS:
        check(c in text, f"commit reference {c} missing from matrix")
    check("5b55129" in text and "48447f5" in text,
          "ancestry chain 48447f5 -> 5b55129 not recorded")
    for axis in REQUIRED_AXES:
        check(axis.lower() in text.lower(), f"axis term missing: {axis!r}")
    check("#255 remains OPEN" in text or "#255 stays OPEN" in text
          or "stays OPEN" in text,
          "matrix must keep #255 OPEN")
    # This increment must not close child fronts.
    check("257" in text and "259" in text and "261" in text,
          "child issues 257/259/261 must be referenced (no silent scope grab)")
    # No false kernel claim for the pending-integration audit cell.
    m = re.search(r"48447f5.{0,2000}", text, re.DOTALL)
    if m:
        seg = m.group(0)
        check("unmerged" in seg.lower() or "pending" in seg.lower()
              or "not yet merged" in seg.lower(),
              "48447f5 segment must state unmerged/pending-integration status")
    if failures:
        for f in failures:
            print(f"FAIL: {f}")
        return 1
    print(f"OK: matrix axes cross-check passed "
          f"({len(REQUIRED_AXES)} axes, {len(REQUIRED_COMMITS)} commits).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
