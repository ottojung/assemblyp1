#!/usr/bin/env python3
"""Independent exact-integer verification of the ternary length-5 census (#259).

Model: MB09 section 6.1 fixed-external-N product-binomial surrogate (NOT the
exact multinomial of #256, NOT the section 6.2 bidirected-flow objective of
#260-#261). Alphabet {0,1,2}, oriented 2-mer universe of size 9, circular
candidate length G=5, fixed normalization N=G=5, sample size n=sum_w x(w).

Definitions (exact integers, no logarithms, no division, no floats):
    q_B(w) = B(w) * prod_{v != w} (N - B(v))
    F_B(x) = prod_w q_B(w) ** x(w)
At fixed x, likelihood comparison uses F_B; the (1-d(w)/N)^(n-x(w)) factors
for zero-count coordinates and boundary probabilities 0/1 are retained
inside q. The exact multinomial of #256 replaces these per-coordinate
binomial factors with a joint multinomial coefficient.

Covered complete-support samples for truth A: x(w) >= A(w) on supp(A),
x(w) = 0 off supp(A). Established covered-sample iff (checked, not
re-proved, here): A weakly maximizes against B on every such x iff q_B
vanishes somewhere on supp(A) or q_B(w) <= q_A(w) for all w in supp(A).

This script independently:
  1. re-enumerates words/spectra/candidates from scratch and asserts the
     census sizes (243 words, 48 realizable spectra, 1287 total-5 vectors);
  2. re-derives full-class and realizable-class violation counts and asserts
     they equal 672 / 78;
  3. takes the lexicographically smallest realizable witness and exhibits an
     EXPLICIT covered sample with exact integer F_B(x) > F_A(x);
  4. checks minimality of the excess parameter t and a t=0 control;
  5. runs a mutation control on the q definition.

Exit code 0 means every check passed.
"""

from __future__ import annotations

import itertools
import sys
from math import prod

ALPHABET = (0, 1, 2)
LENGTH = 5
N = LENGTH  # fixed external normalization = candidate length
PAIRS = tuple(itertools.product(ALPHABET, repeat=2))  # 9 oriented 2-mers


def spectrum(word: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(
        sum(1 for i in range(LENGTH) if (word[i], word[(i + 1) % LENGTH]) == p)
        for p in PAIRS
    )


def gen_compositions(n: int, k: int, prefix: tuple[int, ...] = ()) -> object:
    if k == 1:
        yield prefix + (n,)
        return
    for v in range(n + 1):
        yield from gen_compositions(n - v, k - 1, prefix + (v,))


def eff_q(B: tuple[int, ...], *, mutate: bool = False) -> tuple[int, ...]:
    out = []
    for i in range(len(B)):
        w = B[i]
        for j in range(len(B)):
            if j != i or mutate:  # mutation: wrongly include self factor
                w *= N - B[j]
        out.append(w)
    return tuple(out)


def eff_F(B: tuple[int, ...], x: tuple[int, ...]) -> int:
    q = eff_q(B)
    return prod(q[i] ** x[i] for i in range(len(B)))


def covered_maximal_by_iff(A: tuple[int, ...], B: tuple[int, ...]) -> bool:
    qa, qb = eff_q(A), eff_q(B)
    supp = [i for i, a in enumerate(A) if a]
    return any(qb[i] == 0 for i in supp) or all(qb[i] <= qa[i] for i in supp)


def main() -> int:
    words = list(itertools.product(ALPHABET, repeat=LENGTH))
    assert len(words) == 243, len(words)
    realized = sorted({spectrum(w) for w in words})
    assert len(realized) == 48, len(realized)
    cands = list(gen_compositions(N, len(PAIRS)))
    assert len(cands) == 1287, len(cands)
    assert all(A in cands for A in realized)
    print(f"sizes OK: words=243 realized={len(realized)} candidates=1287")

    full_bad = sum(
        1 for A in realized for B in cands
        if B != A and not covered_maximal_by_iff(A, B)
    )
    real_bad = sum(
        1 for A in realized for B in realized
        if B != A and not covered_maximal_by_iff(A, B)
    )
    print(f"violations: full={full_bad} realizable={real_bad}")
    assert full_bad == 672, full_bad
    assert real_bad == 78, real_bad

    # Lexicographically smallest realizable witness (2-mer order).
    A = (0, 0, 0, 0, 0, 1, 0, 1, 3)
    B = (0, 0, 0, 0, 0, 2, 0, 2, 1)
    assert A in realized and B in realized, "witness spectra must be realizable"
    # Smallest: no lexicographically smaller realizable pair violates the iff.
    for A2 in realized:
        for B2 in realized:
            if B2 != A2 and not covered_maximal_by_iff(A2, B2):
                assert (A2, B2) >= (A, B), f"smaller witness {(A2, B2)}"
                break
        else:
            continue
        break
    qa, qb = eff_q(A), eff_q(B)
    assert qa == (0, 0, 0, 0, 0, 125000, 0, 125000, 750000), qa
    assert qb == (0, 0, 0, 0, 0, 375000, 0, 375000, 140625), qb
    assert qb[5] > qa[5] and qb[7] > qa[7], "iff must fail via strict excess"
    assert not covered_maximal_by_iff(A, B)

    # Explicit covered complete-support sample: x = A + t*e_5, t = 3.
    t = 3
    x = list(A)
    x[5] += t
    x = tuple(x)
    assert all(x[i] >= A[i] for i in range(9))
    assert all(x[i] == 0 for i in range(9) if A[i] == 0)
    fa, fb = eff_F(A, x), eff_F(B, x)
    n = sum(x)
    assert n == 5 + t == 8, n
    print(f"explicit sample x={x} n={n}: F_A={fa} F_B={fb}")
    assert fb > fa, "B must strictly beat A at the explicit covered sample"
    # Cross-check the ratio structure exactly.
    lhs = fb * prod(qa[i] ** x[i] for i in (5, 7, 8))
    rhs = fa * prod(qb[i] ** x[i] for i in (5, 7, 8))
    assert lhs == rhs
    # Minimality of t along e_5: t = 1, 2 must NOT beat; t = 0 control.
    for t0 in (0, 1, 2):
        x0 = list(A)
        x0[5] += t0
        assert not eff_F(B, tuple(x0)) > eff_F(A, tuple(x0)), f"t={t0} must not beat"
    print("explicit exact-integer beating sample OK (t=3, n=8); t=0,1,2 controls OK")

    # Mutation control: wrong q (self factor included) must change the census.
    def bad_iff(A: tuple[int, ...], B: tuple[int, ...]) -> bool:
        qa2 = eff_q(A, mutate=True)
        qb2 = eff_q(B, mutate=True)
        supp = [i for i, a in enumerate(A) if a]
        return any(v == 0 for i, v in enumerate(qb2) if i in supp) or all(
            qb2[i] <= qa2[i] for i in supp
        )

    mutated_full = sum(
        1 for A2 in realized for B2 in cands
        if B2 != A2 and not bad_iff(A2, B2)
    )
    assert mutated_full != full_bad, "mutation control vacuous"
    print(f"mutation control OK (mutated full={mutated_full} != 672)")

    print("ALL OK: ternary L=5 independent exact verification (issue #259)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
