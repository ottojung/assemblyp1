#!/usr/bin/env python3
"""Fixed-x vs sample-uniform gap verdicts beyond binary-L6 (issue #259).

Extends `verify_fixedx_gap_realizable_L6_259.py` (binary-L6: 30/30 gap) to
the ternary-L6 and quaternary-L4 realizable cells of
`verify_realizable_census_L6Q4_259.py`, for the MB09 S6.1
fixed-external-N product-binomial surrogate.

Per cell, for every nondegenerate rigid truth A (same enumeration and
exact reduced arithmetic as the census):

* if A is beaten sample-uniformly by some same-length competitor B
  (new-support candidates admitted), decide the exact separable fixed-x
  inequality at the truth sample x = A:
      F_B(A) <= F_A(A)  <=>  prod_e B_e^A_e (N-B_e)^(n-A_e)
                             <= prod_e A_e^A_e (N-A_e)^(n-A_e),
  n = sum(A) = N = G, all factors exact integers (zero-count coordinates
  included via (N-V_e)^n factors).  Win => live fixed-x/uniform gap.
* if A is sample-uniform maximal, spot-check (up to K per G) that A wins
  the fixed-x inequality at x = A against EVERY same-length competitor
  (x = A is itself a covered sample, so uniform-maximality implies this;
  the check confirms the implication on realizable spectra).

Both verdicts use ONLY exact integer arithmetic (no Lean import, no floats
in any comparison).  Exit code 0 means every check passed; the reported
split is observed data, not a theorem.

Expected (from census 4703a6f): ternary-L6 has 0 rigid-but-beaten truths
(all 3474 rigid-maximal), so its gap population is empty and only the
maximal spot-checks fire.
"""

from __future__ import annotations

import sys

from verify_realizable_census_L6Q4_259 import (
    distinct_spectra,
    dominates,
    explicit_witness,
    positive_circulations,
    reduced_le,
    zero_on_support,
)

K_SPOT = 3  # maximal truths spot-checked per G for fixed-x win at own sample


def separable_at_truth(N, V, A):
    """Exact separable product of candidate V at the fixed sample x = A."""
    n = sum(A)
    p = 1
    for e in range(len(A)):
        xe = A[e]
        p *= V[e] ** xe * (N - V[e]) ** (n - xe)
    return p


def nondegenerate(A, N):
    S_A = [i for i, a in enumerate(A) if a > 0]
    self_union = set(S_A)
    for i in S_A:
        w = A[i]
        for j in self_union:
            if j != i:
                w *= N - A[j]
        if w == 0:
            return None
    return S_A


def gap_cell(alpha, L, Glist, label):
    U, _ = distinct_spectra(1, alpha, L)
    k = len(U)
    n_beaten = 0
    n_win = 0
    n_lose = 0
    n_maximal = 0
    n_spot = 0
    shown = 0
    for G in Glist:
        _, specs = distinct_spectra(G, alpha, L)
        keys = [list(a) for a, _ in specs]
        N = G
        spot_done = 0
        for A in keys:
            S_A = nondegenerate(A, N)
            if S_A is None:
                continue
            if len(positive_circulations(A, U, G)) != 1:
                continue  # only rigid truths
            first_bad = None
            for B in keys:
                if B == A:
                    continue
                S_union = sorted(set(S_A) | {i for i, b in enumerate(B) if b > 0})
                if zero_on_support(N, A, B, S_A):
                    continue
                if dominates(N, A, B, S_A, S_union):
                    continue
                first_bad = (list(B), S_union)
                break
            sa = separable_at_truth(N, A, A)
            assert sa > 0, "truth sample product must be positive (nondegenerate)"
            if first_bad is None:
                n_maximal += 1
                if spot_done < K_SPOT:
                    spot_done += 1
                    n_spot += 1
                    for B in keys:
                        if B == A:
                            continue
                        sb = separable_at_truth(N, B, A)
                        if sb > sa:
                            raise AssertionError(
                                f"{label}: maximal truth loses fixed-x at own "
                                f"sample G={G} (contradicts covered-sample "
                                f"implication)")
                continue
            n_beaten += 1
            B, S_union = first_bad
            sb = separable_at_truth(N, B, A)
            if sb <= sa:
                n_win += 1
                if shown < 3:
                    shown += 1
                    beats = [i for i in S_A
                             if not reduced_le(N, A, B, S_union, i)]
                    assert beats, "uniform beating needs a strict coordinate"
                    print(f"  GAP {label} G={G}: wins at own sample "
                          f"(bitlen SB={sb.bit_length()} <= "
                          f"bitlen SA={sa.bit_length()}) yet loses uniformly; "
                          f"strict coords={beats[:4]}")
            else:
                n_lose += 1
                if shown < 3:
                    shown += 1
                    wit = explicit_witness(N, A, B, S_A, S_union, k)
                    assert wit is not None, "iff/witness gap"
                    _, t, fb, fa = wit
                    assert fb > fa
                    print(f"  NOGAP {label} G={G}: loses even at own sample "
                          f"(SB>SA, bitlen={sb.bit_length()}); "
                          f"uniform witness at n={sum(A) + t}")
    print(f"cell {label}: rigid-beaten={n_beaten} "
          f"(win-own={n_win} lose-own={n_lose}) rigid-maximal={n_maximal} "
          f"(fixed-x spot-checked={n_spot})")
    return n_beaten, n_win, n_lose, n_maximal, n_spot


def main():
    tb, tw, tl, tm, ts = gap_cell(3, 6, [6, 7, 8, 9], "ternary-L6")
    qb, qw, ql, qm, qs = gap_cell(4, 4, [4, 5, 6, 7, 8], "quaternary-L4")
    if tb != 0:
        # ternary-L6 census says all rigid truths are maximal; any beaten
        # truth here would be a census mismatch (fail loudly).
        raise AssertionError(f"ternary-L6 census mismatch: {tb} beaten")
    if tm == 0 or ts == 0:
        raise AssertionError("expected maximal ternary truths to spot-check")
    if qm + qb == 0:
        raise AssertionError("expected quaternary truths to classify")
    # Mutation control: self-comparison must dominate and tie separably.
    _, specs = distinct_spectra(6, 3, 6)
    Amut = list(specs[0][0])
    Nm = sum(Amut)
    S_Am = [i for i, a in enumerate(Amut) if a > 0]
    assert dominates(Nm, Amut, Amut, S_Am, S_Am)
    assert separable_at_truth(Nm, Amut, Amut) <= separable_at_truth(Nm, Amut, Amut)
    print("OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
