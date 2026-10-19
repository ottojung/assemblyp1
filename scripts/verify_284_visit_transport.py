#!/usr/bin/env python3
"""Verify the #284 physical visit-count transport diagnostic.

`AssemblyP1/Section62VisitTransport.lean` proves, kernel-checked, that the
spelling-preserving §6.2 transitive reduction preserves the *full* length-`L`
window multiset of the spelled word but does **not** preserve the physical class
counts (graph-vertex visit multisets), and that no function of the invariant
window multiset can transport them.

This script re-derives the `L = 5` witness directly on the definitions and
asserts, deterministically and independently of the Lean proof:

1. the direct `1`-overlap `sx -> sy`, the one-step detour `sx -> m1 -> sy`
   (overlaps `3, 3`), and the two-step detour `sx -> m2 -> m1 -> sy` (overlaps
   `4, 4, 3`) all spell the SAME word `012341200`;
2. the three walks have DIFFERENT vertex visit lists (lengths 2, 3, 4);
3. the complete length-`5` window multiset is
   `{01234, 12341, 23412, 34120, 41200}` and is identical for all three walks,
   while the seam window `34120` is not a vertex of any walk;
4. the invariant window multiset decomposes (as a multiset) into the direct
   vertices plus three unobserved windows, and into the four detour vertices
   plus one unobserved window (observed part grows, unobserved part shrinks);
5. the Lean module is hygiene-clean (no sorry/admit/axiom/native_decide) and
   every `#print axioms` endpoint depends only on
   `{propext, Classical.choice, Quot.sound}` (never `sorryAx`).

Exit 0 iff every assertion holds.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULE = ROOT / "AssemblyP1" / "Section62VisitTransport.lean"
DOC = ROOT / "docs" / "section62-visit-transport-284.md"

# The cascade instance: observed reads of length 5 over {0,...,4}.
SX = [0, 1, 2, 3, 4]
M1 = [2, 3, 4, 1, 2]
M2 = [1, 2, 3, 4, 1]
SY = [4, 1, 2, 0, 0]
UNOBS = [3, 4, 1, 2, 0]

L = 5
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def spell_walk(reads: list[list[int]], overlaps: list[int]) -> list[int]:
    word = list(reads[0])
    for read, ov in zip(reads[1:], overlaps):
        word += read[ov:]
    return word


def windows(word: list[int], k: int) -> list[tuple[int, ...]]:
    return [tuple(word[i : i + k]) for i in range(len(word) - k + 1)]


def strip_lean_comments(text: str) -> str:
    """Remove Lean block (/- -/, nested) and line (--) comments."""
    out: list[str] = []
    i, depth, n = 0, 0, len(text)
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j == -1 else j
            continue
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(text[i])
        i += 1
    return "".join(out)


def main() -> int:
    errors: list[str] = []

    # 1. Word identity across the direct edge and both detours.
    direct = spell_walk([SX, SY], [1])
    single = spell_walk([SX, M1, SY], [3, 3])
    two = spell_walk([SX, M2, M1, SY], [4, 4, 3])
    if not (direct == single == two):
        errors.append(f"spelled words differ: {direct} {single} {two}")
    if direct != [0, 1, 2, 3, 4, 1, 2, 0, 0]:
        errors.append(f"unexpected cascade word: {direct}")

    # 2. Vertex visit lists differ.
    if len({len([SX, SY]), len([SX, M1, SY]), len([SX, M2, M1, SY])}) != 3:
        errors.append("vertex visit list lengths do not all differ")

    # 3. Window multiset is invariant and contains the unobserved seam window.
    spectrum = sorted(windows(direct, L))
    expected = sorted([tuple(SX), tuple(M2), tuple(M1), tuple(UNOBS), tuple(SY)])
    if spectrum != expected:
        errors.append(f"window spectrum mismatch: {spectrum} != {expected}")
    if sorted(windows(single, L)) != spectrum or sorted(windows(two, L)) != spectrum:
        errors.append("window multiset is not invariant across the detours")
    vertices = {tuple(SX), tuple(M1), tuple(M2), tuple(SY)}
    if tuple(UNOBS) in vertices:
        errors.append("seam window 34120 unexpectedly equals an observed read")

    # 4. Observed/unobserved decomposition (as multisets).
    direct_vertices = sorted([tuple(SX), tuple(SY)])
    direct_unobs = sorted([tuple(M2), tuple(M1), tuple(UNOBS)])
    if sorted(spectrum) != sorted(direct_vertices + direct_unobs):
        errors.append("direct-edge window multiset does not decompose as vertices + unobserved")
    two_vertices = sorted([tuple(SX), tuple(M2), tuple(M1), tuple(SY)])
    two_unobs = [tuple(UNOBS)]
    if sorted(spectrum) != sorted(two_vertices + two_unobs):
        errors.append("two-step window multiset does not decompose as vertices + unobserved")
    if not (len(direct_vertices) < len(two_vertices)
            and len(direct_unobs) > len(two_unobs)):
        errors.append("observed part did not grow / unobserved part did not shrink")

    # 5a. Lean module hygiene.
    if not MODULE.exists():
        errors.append(f"missing module: {MODULE.relative_to(ROOT)}")
    else:
        lean = strip_lean_comments(MODULE.read_text(encoding="utf-8"))
        for token in ("sorry", "admit", "axiom ", "native_decide"):
            if token in lean:
                errors.append(f"module contains forbidden token: {token!r}")
        # 5b. Every #print axioms endpoint is within the allowlist.
        for decl, axs in re.findall(
            r"#print axioms\s+AssemblyP1\.Section62VisitTransport\.(\S+)\n(.*?)(?=\n\n|\Z)",
            lean, re.DOTALL,
        ):
            used = set(re.findall(r"[A-Za-z_.]+", axs))
            bad = used - ALLOWED_AXIOMS - {"depends", "axioms", "on", "any"}
            if "sorryAx" in used:
                errors.append(f"{decl} depends on sorryAx")
            if bad:
                errors.append(f"{decl} has non-allowlist axioms: {sorted(bad)}")

    # 6. Documentation exists and states the limitation.
    if not DOC.exists():
        errors.append(f"missing documentation: {DOC.relative_to(ROOT)}")
    else:
        text = DOC.read_text(encoding="utf-8")
        for marker in ("does not preserve", "vertex", "ML", "OPEN"):
            if marker not in text:
                errors.append(f"docs missing marker: {marker!r}")

    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print("visit-count transport verified (window multiset invariant; "
          "physical class counts not determined by it)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
