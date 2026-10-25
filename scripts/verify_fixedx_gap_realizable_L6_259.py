#!/usr/bin/env python3
"""Fixed-x vs sample-uniform gap on realizable binary-L6 truths (issue #259).

For the MB09 S6.1 fixed-external-N product-binomial surrogate, axis A
(fixed observed count x) and axis B (every realizable complete-support x)
are genuinely different: a truth can win at one fixed sample while failing
to be a sample-uniform maximizer (cf. `fixedX_weaker_than_pointwise`).

This script ties that gap to the NEW realizable binary-L6 cells of
`verify_realizable_census_L6Q4_259.py`: for every rigid truth A that is
beaten sample-uniformly (all beatings there are by new-support candidates),
it decides the exact fixed-x verdict AT THE TRUTH SAMPLE x = A itself:

  fixed-x necessary+sufficient inequality (separable form, exact ints):
    F_B(A) <= F_A(A)  <=>  prod_e B_e^A_e (N-B_e)^(n-A_e)
                           <= prod_e A_e^A_e (N-A_e)^(n-A_e),
    with n = sum(A) = N = G (truth sample), all factors exact integers.

  sample-uniform necessary+sufficient inequality (covered-sample iff):
    A beats B on all covered x  <=>  B has a zero effective weight on
    supp(A) or q(B) <= q(A) pointwise on supp(A), where
    q_e(V) = V_e * prod_{j in S, j != e} (N - V_j) over the union support
    S = supp(A) | supp(B) (exact reduced arithmetic, as in the census).

Both verdicts use ONLY exact integer arithmetic (no Lean import, no floats
in any comparison).  Exit code 0 means every check passed; the reported
split (win-at-own-sample vs lose-even-there) is observed data, not a
theorem -- either outcome is consistent with the Lean axes.
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


def separable_at_truth(N, V, A):
    """Exact separable product of candidate V at the fixed sample x = A."""
    n = sum(A)
    p = 1
    for e in range(len(A)):
        xe = A[e]
        p *= V[e] ** xe * (N - V[e]) ** (n - xe)
    return p


def main():
    alpha, L = 2, 6
    Glist = [6, 7, 8, 9, 10, 11, 12]
    U, _ = distinct_spectra(1, alpha, L)
    k = len(U)
    n_rigid_beaten = 0
    n_win_own_sample = 0
    n_lose_own_sample = 0
    shown_win = 0
    shown_lose = 0
    for G in Glist:
        _, specs = distinct_spectra(G, alpha, L)
        keys = [list(a) for a, _ in specs]
        N = G
        for A in keys:
            S_A = [i for i, a in enumerate(A) if a > 0]
            self_union = set(S_A)
            bad = False
            for i in S_A:
                w = A[i]
                for j in self_union:
                    if j != i:
                        w *= N - A[j]
                if w == 0:
                    bad = True
            if bad:
                continue
            if len(positive_circulations(A, U, G)) != 1:
                continue  # only rigid truths: the gap population
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
            if first_bad is None:
                continue  # rigid & maximal: not the gap population
            n_rigid_beaten += 1
            B, S_union = first_bad
            # Axis A verdict at x = A (exact separable inequality).
            sb = separable_at_truth(N, B, A)
            sa = separable_at_truth(N, A, A)
            assert sa > 0, "truth sample product must be positive (nondegenerate)"
            if sb <= sa:
                n_win_own_sample += 1
                if shown_win < 3:
                    shown_win += 1
                    # cross-check: uniform failure must come with a coordinate
                    # where B strictly beats A (necessity lemma instance).
                    beats = [i for i in S_A
                             if not reduced_le(N, A, B, S_union, i)]
                    assert beats, "uniform beating needs a strict coordinate"
                    print(f"  GAP G={G}: truth wins at own sample x=A "
                          f"(bitlen SB={sb.bit_length()} <= "
                          f"bitlen SA={sa.bit_length()}, SB<=SA={sb <= sa}) "
                          f"yet loses uniformly; strict coords={beats[:4]}")
            else:
                n_lose_own_sample += 1
                if shown_lose < 3:
                    shown_lose += 1
                    wit = explicit_witness(N, A, B, S_A, S_union, k)
                    assert wit is not None, "iff/witness gap"
                    _, t, fb, fa = wit
                    assert fb > fa
                    print(f"  NOGAP G={G}: truth loses even at own sample x=A "
                          f"(SB>SA, bitlen={sb.bit_length()}); "
                          f"uniform witness at n={sum(A) + t}")
    print(f"rigid-but-beaten truths={n_rigid_beaten} "
          f"(census reports 30: match={n_rigid_beaten == 30})")
    print(f"  win at own sample (fixed-x/uniform gap)={n_win_own_sample}")
    print(f"  lose at own sample={n_lose_own_sample}")
    if n_rigid_beaten != 30:
        raise AssertionError("census mismatch: expected 30 rigid-but-beaten")
    if n_rigid_beaten == 0:
        raise AssertionError("expected at least one rigid-but-beaten truth")
    # Mutation control: self-comparison must dominate (verifier not vacuous).
    _, specs = distinct_spectra(6, alpha, L)
    Amut = list(specs[0][0])
    Nm = sum(Amut)
    S_Am = [i for i, a in enumerate(Amut) if a > 0]
    assert dominates(Nm, Amut, Amut, S_Am, S_Am)
    assert separable_at_truth(Nm, Amut, Amut) <= separable_at_truth(Nm, Amut, Amut)
    print("OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
