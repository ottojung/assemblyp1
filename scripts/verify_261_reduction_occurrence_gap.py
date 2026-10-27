#!/usr/bin/env python3
"""Bounded verifier for issue #261 reduction/occurrence bridge.

Checks the exact small instance used to separate graph-language preservation
from vertex/occurrence correspondence:

  sx=01234, m2=12341, m1=23412, sy=41200, L=5.

Claims checked (all exact, no search):
  1. Direct edge sx->sy has proper overlap 1; detour sx->m1->sy has overlaps
     3,3 with 3+3 = L+1 (ideal Myers spelling identity).
  2. First leg sx->m1 (overlap 3) is itself reducible via m2 with overlaps
     4,4 and 4+4 = L+3.
  3. Terminal irreducible chain sx->m2->m1->sy spells exactly the direct word
     012341200, whose length-5 sliding windows are
     {01234,12341,23412,34120,41200}.
  4. Window 34120 is physical (a window of the spelled word) but absent from
     the observed vertex set, so vertex visits != physical occurrence counts.

This is a counterexample to the strong vertex/occurrence transfer, NOT to
MB09 Observation 7 under its intended walk/occurrence definitions, and NOT to
`Section62SimultaneousReduction.reduction_preserves_language` (which it
instantiates). Candidate universe, truth, likelihood, RC/orientation, and
half-integral axes remain open per the bridge note.
"""

from __future__ import annotations


def overlap(a: str, b: str) -> int:
    """Longest proper-or-full suffix/prefix match length."""
    best = 0
    for k in range(1, min(len(a), len(b)) + 1):
        if a[len(a) - k:] == b[:k]:
            best = k
    return best


def spell_chain(reads: list[str]) -> str:
    out = reads[0]
    for prev, cur in zip(reads, reads[1:]):
        k = overlap(prev, cur)
        out += cur[k:]
    return out


def windows(word: str, ell: int) -> list[str]:
    return [word[i:i + ell] for i in range(len(word) - ell + 1)]


def main() -> None:
    L = 5
    sx, m2, m1, sy = "01234", "12341", "23412", "41200"
    for s in (sx, m2, m1, sy):
        assert len(s) == L, s

    e_direct = overlap(sx, sy)
    assert e_direct == 1, e_direct
    l1, l2 = overlap(sx, m1), overlap(m1, sy)
    assert (l1, l2) == (3, 3), (l1, l2)
    assert l1 + l2 == L + e_direct, "ideal Myers spelling identity"

    e_leg = overlap(sx, m1)
    j1, j2 = overlap(sx, m2), overlap(m2, m1)
    assert (j1, j2) == (4, 4), (j1, j2)
    assert j1 + j2 == L + e_leg, "cascade spelling identity"
    assert all(k < L for k in (e_direct, e_leg, l1, l2, j1, j2)), "proper overlaps"

    direct_word = sx + sy[e_direct:]
    chain_word = spell_chain([sx, m2, m1, sy])
    assert direct_word == "012341200", direct_word
    assert chain_word == direct_word, (chain_word, direct_word)

    wins = windows(direct_word, L)
    assert wins == ["01234", "12341", "23412", "34120", "41200"], wins
    observed = {sx, m2, m1, sy}
    assert "34120" not in observed, "gap window must be unobserved"
    assert set(wins) - observed == {"34120"}, "exactly one unobserved window"

    # Extension lengths strictly decrease along expansion (termination measure).
    assert (L - e_direct) > (L - l1) and (L - e_direct) > (L - l2)
    assert (L - e_leg) > (L - j1) and (L - e_leg) > (L - j2)

    print("PASS: reduction spells same word; vertex visits != occurrence counts")
    print(f"direct overlap={e_direct} detour=({l1},{l2}) cascade=({j1},{j2})")
    print(f"spelled={direct_word} gap-window=34120")


if __name__ == "__main__":
    main()
