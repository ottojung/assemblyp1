#!/usr/bin/env python3
"""Verify the #284 real-model `spellChain` window-multiset transport bridge.

`AssemblyP1/Section62SpellChainWindowTransport.lean` proves, kernel-checked,
that the repository's actual §6.2 spelling function `spellChain` (from
`Section62SimultaneousReduction`) of a chain of overlap edges equals the walk
spelling `spellWalk` applied to the visited read words and the overlap lengths,
so the merged window-multiset transport results apply verbatim:

* `spellChain_eq_spellWalk` — the bridge;
* `reduction_preserves_language_windows` — the window multiset is invariant under
  each spelling-preserving detour replacement;
* `chain_visited_dominated` / `genuineChain_visited_dominated` — for a genuine
  chain of proper overlaps, the visited read words are a sub-multiset of the
  length-`L` window multiset of `spellChain`.

This script re-derives the bridge and the domination bound directly on the
definitions, on the `L = 5` witness and on a deterministic sweep of short chains,
so the claim is checked independently of the Lean proof.  It also checks module
hygiene and documentation.  Exit 0 iff every assertion holds.
"""

from __future__ import annotations

import itertools
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULE = ROOT / "AssemblyP1" / "Section62SpellChainWindowTransport.lean"
DOC = ROOT / "docs" / "section62-spellchain-window-transport-284.md"

# The L = 5 witness: sx = 01234, m2 = 12341, m1 = 23412, sy = 41200.
SX = [0, 1, 2, 3, 4]
M2 = [1, 2, 3, 4, 1]
M1 = [2, 3, 4, 1, 2]
SY = [4, 1, 2, 0, 0]
L = 5


def spell_chain(reads: list[list[int]], overlaps: list[int]) -> list[int]:
    """`spellChain` with toList = id, as a recursive function on the read list."""
    if not reads:
        return []
    if len(overlaps) == 0:
        return list(reads[0])
    head, rest = reads[0], reads[1:]
    tail = spell_chain(rest, overlaps[1:])
    return list(head) + tail[overlaps[0]:]


def spell_walk(reads: list[list[int]], overlaps: list[int]) -> list[int]:
    word: list[int] = list(reads[0])
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


def bridge_holds(reads, overlaps) -> bool:
    return spell_chain(reads, overlaps) == spell_walk(reads, overlaps)


def check_bound(reads, overlaps, length) -> list[str]:
    errs: list[str] = []
    word = spell_chain(reads, overlaps)
    wins = windows(word, length)
    for u in {tuple(r) for r in reads} | set(wins):
        visit = count([tuple(r) for r in reads], u)
        window = count(wins, u)
        if visit > window:
            errs.append(f"bound violated: {list(u)} visit {visit} > window {window}")
    return errs


def main() -> int:
    errors: list[str] = []

    # 1. Bridge on the L = 5 witness and the expanded chain.
    for reads, overlaps in (
        ([SX, M1, SY], [3, 3]),
        ([SX, M2, M1, SY], [4, 4, 3]),
        ([SX, SY], [1]),
    ):
        if not bridge_holds(reads, overlaps):
            errors.append(f"bridge failed on {reads}")
    direct_word = spell_chain([SX, SY], [1])
    if direct_word != [0, 1, 2, 3, 4, 1, 2, 0, 0]:
        errors.append(f"unexpected direct witness word: {direct_word}")
    expanded_word = spell_chain([SX, M2, M1, SY], [4, 4, 3])
    if sorted(windows(expanded_word, L)) != sorted(windows(direct_word, L)):
        errors.append("expanded chain window multiset differs from direct")
    errors.extend(check_bound([SX, M2, M1, SY], [4, 4, 3], L))

    # 2. Finite sweep: all short chains of length-L = 3 reads over {0,1}, up to
    #    4 reads, that are genuine (proper suffix/prefix overlaps).  This checks
    #    both the bridge and the domination bound.
    for nreads in (1, 2, 3, 4):
        for reads in itertools.product(itertools.product((0, 1), repeat=3), repeat=nreads):
            reads = [list(r) for r in reads]
            for overlaps in itertools.product(range(3), repeat=nreads - 1):
                # Genuine: proper overlap with matching suffix/prefix.
                if not all(
                    0 < ov < 3 and reads[i][3 - ov :] == reads[i + 1][:ov]
                    for i, ov in enumerate(overlaps)
                ):
                    continue
                if not bridge_holds(reads, list(overlaps)):
                    errors.append(f"bridge failed on {reads} {overlaps}")
                errors.extend(check_bound(reads, list(overlaps), 3))

    # 3. Lean module hygiene and axiom audit coverage.
    if not MODULE.exists():
        errors.append(f"missing module: {MODULE.relative_to(ROOT)}")
    else:
        lean = strip_lean_comments(MODULE.read_text(encoding="utf-8"))
        for token in ("sorry", "admit", "axiom ", "native_decide"):
            if token in lean:
                errors.append(f"module contains forbidden token: {token!r}")
        for decl in (
            "spellChain_eq_spellWalk", "spellChain_windows_congr",
            "reduction_preserves_language_windows", "genuineChain_of_overlapEdges",
            "chainStrands_subset_strandsOf", "chain_visited_dominated",
            "genuineChain_visited_dominated",
        ):
            if f"#print axioms {decl}" not in lean:
                errors.append(f"module missing #print axioms command for {decl}")
        root = strip_lean_comments((ROOT / "AssemblyP1.lean").read_text(encoding="utf-8"))
        if "import AssemblyP1.Section62SpellChainWindowTransport" not in root:
            errors.append("root missing import of the new module")
        for decl in (
            "spellChain_eq_spellWalk", "spellChain_windows_congr",
            "reduction_preserves_language_windows", "genuineChain_of_overlapEdges",
            "chainStrands_subset_strandsOf", "chain_visited_dominated",
            "genuineChain_visited_dominated",
        ):
            if f"#print axioms AssemblyP1.Section62SpellChainWindowTransport.{decl}" not in root:
                errors.append(f"root missing qualified #print axioms for {decl}")
        audit = (ROOT / "AxiomAudit284.lean").read_text(encoding="utf-8")
        if "import AssemblyP1.Section62SpellChainWindowTransport" not in audit:
            errors.append("AxiomAudit284 missing import of the new module")
        for decl in ("spellChain_eq_spellWalk", "genuineChain_visited_dominated"):
            if f"#print axioms AssemblyP1.Section62SpellChainWindowTransport.{decl}" not in audit:
                errors.append(f"AxiomAudit284 missing #print axioms for {decl}")

    # 4. Documentation exists and states the licence boundary.
    if not DOC.exists():
        errors.append(f"missing documentation: {DOC.relative_to(ROOT)}")
    else:
        text = DOC.read_text(encoding="utf-8")
        for marker in ("spellChain", "window multiset", "Does not license", "OPEN"):
            if marker not in text:
                errors.append(f"docs missing marker: {marker!r}")

    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print("spellChain window-transport bridge verified (spellChain = spellWalk; "
          "window multiset invariant under detours and dominating physical visits)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
