#!/usr/bin/env python3
"""Preserve the scope distinction of the #284 simultaneous spelling reduction.

`AssemblyP1/Section62SimultaneousReduction.lean` proves that the simultaneous
spelling-preserving transitive reduction preserves the **spelled word** of every
graph edge (including the two-level cascade). It does NOT preserve graph-vertex
visit counts, read multiplicities, §6.2 feasible-flow bounds, or ML likelihood.

This script re-derives the cascade witness directly on the definitions and
asserts, deterministically and independently of the Lean proof:

1. the direct `1`-overlap `sx → sy` and the fully expanded chain
   `sx → m₂ → m₁ → sy` (overlaps `4, 4, 3`) spell the SAME word `012341200`;
2. the two graph paths have DIFFERENT vertex visit sequences
   (`[sx, sy]` vs `[sx, m₂, m₁, sy]`);
3. the complete length-`5` window multiset of the spelled word is
   `{01234, 12341, 23412, 34120, 41200}`, and the window `34120` is NOT any
   observed read (the spelled word has physical windows with no graph vertex);
4. the documentation retains the explicit limitation (the word identity must not
   be upgraded to vertex/flow/ML preservation).

Exit 0 iff every assertion holds.
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DOC = ROOT / "docs" / "section62-simultaneous-reduction-284.md"

# The cascade instance: observed reads of length 5 over {0,...,4}.
SX = [0, 1, 2, 3, 4]
M1 = [2, 3, 4, 1, 2]
M2 = [1, 2, 3, 4, 1]
SY = [4, 1, 2, 0, 0]
OBSERVED = {0: SX, 1: M1, 2: M2, 3: SY}

L = 5


def spell_direct(sx: list[int], sy: list[int], overlap: int) -> list[int]:
    """Word spelled by the direct edge sx -> sy of the given overlap."""
    return sx + sy[overlap:]


def spell_path(reads: list[list[int]], overlaps: list[int]) -> list[int]:
    """Word spelled by following the chain of the given overlaps."""
    word = list(reads[0])
    for read, ov in zip(reads[1:], overlaps):
        word += read[ov:]
    return word


def windows(word: list[int], k: int) -> list[tuple[int, ...]]:
    return [tuple(word[i : i + k]) for i in range(len(word) - k + 1)]


def main() -> int:
    errors: list[str] = []

    # 1. Word identity: direct edge vs fully expanded two-level cascade.
    direct = spell_direct(SX, SY, 1)
    expanded = spell_path([SX, M2, M1, SY], [4, 4, 3])
    if direct != expanded:
        errors.append(f"spelled words differ: direct={direct} expanded={expanded}")
    if direct != [0, 1, 2, 3, 4, 1, 2, 0, 0]:
        errors.append(f"unexpected cascade word: {direct}")

    # 2. Vertex visit sequences differ: the word identity does not preserve
    #    graph-vertex visit counts.
    visits_direct = [0, 3]
    visits_expanded = [0, 2, 1, 3]
    if visits_direct == visits_expanded:
        errors.append("vertex visit sequences unexpectedly coincide")

    # 3. Complete window spectrum of the spelled word: identical for both paths
    #    (it is a function of the word alone), but the window 34120 has no
    #    observed read vertex.
    spectrum = sorted(windows(direct, L))
    expected = sorted(
        [tuple(SX), tuple(M2), tuple(M1), (3, 4, 1, 2, 0), tuple(SY)]
    )
    if spectrum != expected:
        errors.append(f"window spectrum mismatch: {spectrum} != {expected}")
    observed_windows = {tuple(read) for read in OBSERVED.values()}
    unobserved = [w for w in spectrum if w not in observed_windows]
    if unobserved != [(3, 4, 1, 2, 0)]:
        errors.append(f"unexpected unobserved windows: {unobserved}")

    # 4. The documentation retains the explicit limitation.
    if not DOC.exists():
        errors.append(f"missing documentation: {DOC.relative_to(ROOT)}")
    else:
        text = DOC.read_text(encoding="utf-8")
        for marker in (
            "What the word identity does NOT preserve",
            "graph-vertex visit counts",
            "read multiplicities",
            "feasible-flow",
            "ML likelihood",
        ):
            if marker not in text:
                errors.append(
                    f"docs limitation section missing marker: {marker!r}"
                )

    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print("spelling-reduction scope distinction verified "
          "(word identity holds; vertex visits, multiplicities, flow, ML not implied)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
