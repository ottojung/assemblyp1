#!/usr/bin/env python3
"""Independent exact check for #261 OPEN-4: transitive-reduction interaction with ML.

Scope (deliberately bounded, no overlap with AGA/CTC or ACA/CAC verifiers):
 1. Literal `isReducibleB` vacuity: the conjunction
      0 < l1, 0 < l2, l1 < L, l2 < L, l1 < l, l2 < l, l1+l2-L = l  (l = e.len)
    with proper-overlap bounds l < L, l1 < L, l2 < L is UNSATISFIABLE.
    Proof: l1 < l and l2 < l give l1+l2 < 2*l; the composition law
    l1+l2-L = l gives l1+l2 = l+L > l+l = 2*l (since l < L), contradiction.
    Checked exhaustively for L in 2..8 over all triples, plus the algebra.
 2. Longer-reading (`isReducibleLongerB`) spelling-language witness at L=4:
    verts AAAC, ACCA, CAAA; direct edge AAAC->CAAA at overlap 1 spells
    AAACAAA, while the two-step path via ACCA (overlaps 2,2) spells
    AAACCAAA != AAACAAA.  So longer-only reduction deletes a spelled
    molecule without a spelling-preserving replacement: reduction is NOT
    ML-invariant in general under that reading.  Exact string arithmetic.
 3. Consequence: literal reduction is trivially ML-invariant (vacuous: it
    removes nothing), while the longer reading needs a spelling-equality
    side condition (Myers 2005 / MB09 citation) before any invariance can
    hold.  Both statements recorded as OPEN-4 partial progress, not a full
    maximality criterion.

Exact integer/string arithmetic only; shares no code with Lean.
Primary source: MB09 s6.2; Myers 2005 string-graph reduction.
"""

import itertools
import sys


def suffix_prefix_overlap(a: str, b: str) -> int:
    """Longest k < len(a)=len(b) with suffix_k(a) == prefix_k(b)."""
    L = len(a)
    for k in range(L - 1, -1, -1):
        if a[L - k:] == b[:k] if k > 0 else True:
            return k
    return 0


def spell_pair(a: str, b: str, ov: int) -> str:
    return a + b[ov:]


def check_vacuity(Lmax=8):
    """Exhaust: no (L, l, l1, l2) satisfies the literal reducibility system."""
    bad = []
    for L in range(2, Lmax + 1):
        for l in range(1, L):  # proper overlap
            for l1 in range(L):
                for l2 in range(L):
                    if (0 < l1 and 0 < l2 and l1 < l and l2 < l
                            and l1 + l2 - L == l):
                        bad.append((L, l, l1, l2))
    return bad


def check_algebra():
    """Direct inequality proof witness: l1+l2 = l+L > 2l > l1+l2. Absurd."""
    # symbolic: assume l1<l, l2<l => l1+l2<=2l-2; composition => l1+l2=l+L>=l+...;
    # check the numeric gap on a sample grid
    for l in range(1, 8):
        for L in range(l + 1, 10):
            # max achievable l1+l2 under l1<l,l2<l is 2l-2; required is l+L >= 2l+1
            assert (l + L) > (2 * l - 2), (l, L)
    return True


def main():
    fails = []
    bad = check_vacuity()
    print(f"vacuity-exhaust L=2..8: violating tuples = {bad}")
    if bad:
        fails.append("literal system satisfiable?!")
    check_algebra()
    print("vacuity-algebra: l1+l2=l+L>2l>l1+l2 contradiction confirmed")

    # Longer-reading spelling witness
    A, M, B = "AAAC", "ACCA", "CAAA"
    L = 4
    d = suffix_prefix_overlap(A, B)
    l1 = suffix_prefix_overlap(A, M)
    l2 = suffix_prefix_overlap(M, B)
    print(f"overlaps: direct={d} legs=({l1},{l2})")
    assert (d, l1, l2) == (1, 2, 2), (d, l1, l2)
    direct = spell_pair(A, B, d)
    two_step = spell_pair(spell_pair(A, M, l1), B, l2)
    # spelled the incremental way must equal direct concatenation check:
    assert direct == "AAACAAA", direct
    assert two_step == "AAACCAAA", two_step
    print(f"direct spells {direct}; two-step spells {two_step}")
    if direct == two_step:
        fails.append("expected spelling mismatch did not occur")
    longer_deletes = (l1 > d and l2 > d)
    print(f"longer-reading deletes direct edge: {longer_deletes}")
    if not longer_deletes:
        fails.append("longer reading does not delete here?!")
    # literal reading vacuous here too (no shorter-spelled pair)
    literal_fires = any(
        0 < a and 0 < b and a < d and b < d and a + b - L == d
        for a in range(L) for b in range(L)
    )
    print(f"literal-reading fires on direct edge: {literal_fires}")
    if literal_fires:
        fails.append("literal reading unexpectedly fires")

    if fails:
        print("FAIL:", fails)
        return 1
    print("OK: vacuity + spelling-language-change witness both hold")
    return 0


if __name__ == "__main__":
    sys.exit(main())
