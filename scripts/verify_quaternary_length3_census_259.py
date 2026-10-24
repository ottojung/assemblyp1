#!/usr/bin/env python3
"""Quaternary length-3 product-binomial census (#259).

New cell: alphabet {0,1,2,3} (prior cells were binary/ternary), circular
candidate length G=3, fixed external normalization N=G=3.

Model: MB09 section 6.1 fixed-external-N product-binomial surrogate (NOT the
exact multinomial of #256, NOT the section 6.2 bidirected-flow objective of
#260/#261). Oriented 2-mer universe E has |E|=16. Sample size n = sum_w x(w)
is free; covered complete-support samples for truth A satisfy x(w) >= A(w)
on supp(A) and x(w) = 0 off supp(A).

Definitions (exact integers, no logarithms, no division, no floats):
    q_B(w) = B(w) * prod_{v != w} (N - B(v))
    F_B(x) = prod_w q_B(w) ** x(w)
The (1-d(w)/N)^(n-x(w)) factors for zero-count coordinates and boundary
probabilities 0/1 are retained inside q; the omitted prod_w choose(n,x_w)
and N^(-n*|E|) factors are candidate-independent and cancel in comparisons.
The exact multinomial of #256 replaces these per-coordinate binomial
factors with a joint multinomial coefficient.

Established covered-sample iff (checked, not re-proved, here): A weakly
maximizes against B on every covered x iff q_B vanishes somewhere on
supp(A) or q_B(w) <= q_A(w) for all w in supp(A) (as exact rationals).

Result (honest negative): NO violations in this cell -- every realizable
truth is sample-uniformly maximal against both the full candidate class
(816 vectors) and the realizable class (24 spectra). All 24 realizable
truths are additionally rigid (unique same-support positive circulation),
consistent with the #259 rigidity-necessity theorem (0 non-rigid maximal).

This script:
  1. re-enumerates words/spectra/candidates from scratch and asserts the
     census sizes (64 words, 24 realizable spectra, 816 total-3 vectors);
  2. asserts q_A > 0 on supp(A) for every realizable truth (F_A > 0 on
     covered samples, so comparisons are meaningful);
  3. decides maximality for every (A,B) pair by the iff with exact
     Fraction per-coordinate ratios, asserting full=0 / realizable=0;
  4. end-to-end checks explicit integer F_B(x) <= F_A(x) on concrete
     covered samples (x=A and x=A+2*e_i per support coordinate i) for
     every pair;
  5. runs a rigidity census (same-support positive circulations of total
     N) and asserts 24/24 rigid, i.e. 0 non-rigid maximal;
  6. runs a mutation control (wrongly including the self factor (N-B(w))
     in q) that must change the verdict counts.

Exit code 0 means every check passed.
"""

from __future__ import annotations

import itertools
import sys
from fractions import Fraction
from math import comb, prod

ALPHABET = (0, 1, 2, 3)
LENGTH = 3
N = LENGTH  # fixed external normalization = candidate length
PAIRS = tuple(itertools.product(ALPHABET, repeat=2))  # 16 oriented 2-mers
DIM = len(PAIRS)


def spectrum(word: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(
        sum(1 for i in range(LENGTH) if (word[i], word[(i + 1) % LENGTH]) == p)
        for p in PAIRS
    )


def eff_q(B: tuple[int, ...], *, mutate: bool = False) -> tuple[int, ...]:
    out = []
    for i in range(DIM):
        w = B[i]
        for j in range(DIM):
            if j != i or mutate:  # mutation: wrongly include self factor
                w *= N - B[j]
        out.append(w)
    return tuple(out)


def eff_F(B: tuple[int, ...], x: tuple[int, ...]) -> int:
    q = eff_q(B)
    return prod(q[i] ** x[i] for i in range(DIM))


def balanced(B: tuple[int, ...]) -> bool:
    for v in ALPHABET:
        inn = sum(B[k] for k, (a, b) in enumerate(PAIRS) if b == v)
        out = sum(B[k] for k, (a, b) in enumerate(PAIRS) if a == v)
        if inn != out:
            return False
    return True


def compositions(rem: int, parts: int):
    if parts == 1:
        yield (rem,)
        return
    for v in range(rem + 1):
        for rest in compositions(rem - v, parts - 1):
            yield (v,) + rest


def covered_maximal_by_iff(
    A: tuple[int, ...], B: tuple[int, ...], Q: dict
) -> bool:
    qa, qb = Q[A], Q[B]
    supp = [i for i, a in enumerate(A) if a]
    if any(qb[i] == 0 for i in supp):
        return True
    if any(qa[i] == 0 for i in supp):
        # F_A vanishes on covered samples; maximality needs F_B = 0
        # there too, i.e. q_B zero somewhere on supp (handled above).
        return False
    return all(Fraction(qb[i], qa[i]) <= 1 for i in supp)


def main() -> int:
    words = list(itertools.product(ALPHABET, repeat=LENGTH))
    assert len(words) == 64, len(words)
    realized = sorted({spectrum(w) for w in words})
    assert len(realized) == 24, len(realized)
    cands = list(compositions(N, DIM))
    assert len(cands) == comb(N + DIM - 1, DIM - 1) == 816, len(cands)
    assert all(A in cands for A in realized)
    print(f"sizes OK: words=64 realized={len(realized)} candidates={len(cands)}")

    Q = {B: eff_q(B) for B in cands}
    for A in realized:
        supp = [i for i, a in enumerate(A) if a]
        assert all(Q[A][i] > 0 for i in supp), f"q_A must be positive on supp: {A}"
    print("positivity OK: q_A > 0 on supp(A) for all 24 realizable truths")

    full_bad = sum(
        1 for A in realized for B in cands
        if B != A and not covered_maximal_by_iff(A, B, Q)
    )
    real_bad = sum(
        1 for A in realized for B in realized
        if B != A and not covered_maximal_by_iff(A, B, Q)
    )
    print(f"violations: full={full_bad} realizable={real_bad}")
    assert full_bad == 0, full_bad
    assert real_bad == 0, real_bad

    # End-to-end explicit integer likelihood check on concrete covered
    # samples for every (truth, competitor) pair.
    nchecked = 0
    for A in realized:
        supp = [i for i, a in enumerate(A) if a]
        samples = [A] + [
            tuple(A[i] + (2 if i == k else 0) for i in range(DIM))
            for k in supp
        ]
        for x in samples:
            fa = eff_F(A, x)
            assert fa > 0
            for B in cands:
                if B == A:
                    continue
                assert eff_F(B, x) <= fa, f"F check failed: A={A} B={B} x={x}"
                nchecked += 1
    print(f"explicit-F OK: {nchecked} (pair, sample) integer comparisons")

    # Rigidity census: same-support positive circulations of total N.
    rigid = 0
    nonrigid_maximal = 0
    for A in realized:
        S = {i for i, a in enumerate(A) if a}
        alts = [
            B for B in cands
            if balanced(B)
            and all(B[i] == 0 for i in range(DIM) if i not in S)
            and all(B[i] >= 1 for i in S)
        ]
        assert A in alts
        if len(alts) == 1:
            rigid += 1
        else:
            # A is maximal here (zero violations above); a non-rigid
            # maximal truth would contradict rigidity-necessity.
            nonrigid_maximal += 1
    print(f"rigidity: rigid={rigid}/24 non-rigid-maximal={nonrigid_maximal}")
    assert rigid == 24, rigid
    assert nonrigid_maximal == 0, nonrigid_maximal

    # Mutation control: self-factor q must change the verdicts.
    Qm = {B: eff_q(B, mutate=True) for B in cands}
    assert sum(1 for B in cands if Qm[B] != Q[B]) == len(cands)
    mfull = sum(
        1 for A in realized for B in cands
        if B != A and not covered_maximal_by_iff(A, B, Qm)
    )
    mreal = sum(
        1 for A in realized for B in realized
        if B != A and not covered_maximal_by_iff(A, B, Qm)
    )
    print(f"mutation control: full={mfull} realizable={mreal} (must differ from 0/0)")
    assert (mfull, mreal) != (0, 0), "mutation control failed to discriminate"

    print("ALL OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
