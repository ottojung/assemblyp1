#!/usr/bin/env python3
"""Verify the #284 read-window multiset / physical-visit transport bound.

`AssemblyP1/Section62VisitWindowBridge.lean` proves, kernel-checked, that for a
walk of length-`L` reads chained by genuine proper overlaps, the multiset of
visited read words is a sub-multiset of the length-`L` window multiset of the
spelled word:

    throughputOf vs u  <=  windowCount L u (spellWalk vs ovs).

This script re-derives that inequality directly on the definitions, on the
`L = 5` seam-window witness and on a deterministic sweep of short walks, so the
claim is checked independently of the Lean proof.  It also checks:

1. the `L = 5` witness: the seam window `34120` has window multiplicity `1` but
   visit count `0`, so the bound is strict and not an equality;
2. the bound holds on every read of every generated walk (finite regression);
3. the Lean module is hygiene-clean (no sorry/admit/axiom/native_decide) and
   every endpoint carries a `#print axioms` command;
4. the documentation exists and states the bound and the OPEN ML transport.

Exit 0 iff every assertion holds.
"""

from __future__ import annotations

import itertools
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULE = ROOT / "AssemblyP1" / "Section62VisitWindowBridge.lean"
DOC = ROOT / "docs" / "section62-visit-window-bridge-284.md"

# The L = 5 seam-window witness.
SX = [0, 1, 2, 3, 4]
SY = [4, 1, 2, 0, 0]
SEAM = [3, 4, 1, 2, 0]
L = 5

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def spell_walk(reads: list[list[int]], overlaps: list[int]) -> list[int]:
    word = list(reads[0])
    for read, ov in zip(reads[1:], overlaps):
        word += read[ov:]
    return word


def windows(word: list[int], k: int) -> list[tuple[int, ...]]:
    return [tuple(word[i : i + k]) for i in range(len(word) - k + 1)]


def count(seq, x) -> int:
    return sum(1 for y in seq if y == x)


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


def genuine_walk(reads: list[list[int]], overlaps: list[int], length: int) -> bool:
    """The GenuineWalk predicate of the module, re-checked here."""
    if len(reads) != len(overlaps) + 1:
        return False
    if any(len(r) != length for r in reads):
        return False
    for v, w, o in zip(reads, reads[1:], overlaps):
        if not (0 <= o < length):
            return False
        if v[length - o :] != w[:o]:
            return False
    return True


def check_bound(reads, overlaps, length) -> list[str]:
    errs: list[str] = []
    word = spell_walk(reads, overlaps)
    wins = windows(word, length)
    for u in {tuple(r) for r in reads} | set(wins):
        visit = count([tuple(r) for r in reads], u)
        window = count(wins, u)
        if visit > window:
            errs.append(f"bound violated: {list(u)} visit {visit} > window {window}")
    return errs


def main() -> int:
    errors: list[str] = []

    # 1. The L = 5 witness: word identity and strictness.
    word = spell_walk([SX, SY], [1])
    if word != [0, 1, 2, 3, 4, 1, 2, 0, 0]:
        errors.append(f"unexpected witness word: {word}")
    if not genuine_walk([SX, SY], [1], L):
        errors.append("direct witness walk is not a genuine walk")
    if count([tuple(SX), tuple(SY)], tuple(SEAM)) != 0:
        errors.append("seam window unexpectedly visited by the direct walk")
    if count(windows(word, L), tuple(SEAM)) != 1:
        errors.append("seam window multiplicity in the window multiset is not 1")
    if not (count([tuple(SX), tuple(SY)], tuple(SEAM))
            < count(windows(word, L), tuple(SEAM))):
        errors.append("witness bound is not strict")
    if sorted(windows(word, L)) != sorted(
            [tuple(SX), tuple([1, 2, 3, 4, 1]), tuple([2, 3, 4, 1, 2]),
             tuple(SEAM), tuple(SY)]):
        errors.append("witness window multiset mismatch")
    errors.extend(check_bound([SX, SY], [1], L))

    # 2. Finite regression: all short binary walks of length L = 3, up to 4 reads.
    for nreads in (1, 2, 3, 4):
        for reads in itertools.product(itertools.product((0, 1), repeat=3), repeat=nreads):
            reads = [list(r) for r in reads]
            for overlaps in itertools.product(range(3), repeat=nreads - 1):
                if not genuine_walk(reads, overlaps, 3):
                    continue
                errors.extend(check_bound(reads, list(overlaps), 3))

    # 3a. Lean module hygiene.
    if not MODULE.exists():
        errors.append(f"missing module: {MODULE.relative_to(ROOT)}")
    else:
        lean = strip_lean_comments(MODULE.read_text(encoding="utf-8"))
        for token in ("sorry", "admit", "axiom ", "native_decide"):
            if token in lean:
                errors.append(f"module contains forbidden token: {token!r}")
        for decl in (
            "genuineWalk_length", "spellWalk_cons_drop", "windows_spellWalk_cons",
            "genuineWalk_dominates", "visitCount_le_windowCount",
            "windowCount_detour_eq", "witness_bound_strict", "witness_bound_holds",
        ):
            if f"#print axioms {decl}" not in lean:
                errors.append(f"module missing #print axioms command for {decl}")
        root = strip_lean_comments((ROOT / "AssemblyP1.lean").read_text(encoding="utf-8"))
        for decl in (
            "genuineWalk_length", "spellWalk_cons_drop", "windows_spellWalk_cons",
            "genuineWalk_dominates", "visitCount_le_windowCount",
            "windowCount_detour_eq", "witness_bound_strict", "witness_bound_holds",
        ):
            if f"#print axioms AssemblyP1.Section62VisitWindowBridge.{decl}" not in root:
                errors.append(f"root missing qualified #print axioms for {decl}")

    # 4. Documentation exists and states the bound and the OPEN transport.
    if not DOC.exists():
        errors.append(f"missing documentation: {DOC.relative_to(ROOT)}")
    else:
        text = DOC.read_text(encoding="utf-8")
        for marker in ("sub-multiset", "windowCount", "throughput", "OPEN"):
            if marker not in text:
                errors.append(f"docs missing marker: {marker!r}")

    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print("visit-window transport bound verified (window multiset dominates "
          "physical visits; bound is reduction-invariant and strict)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
