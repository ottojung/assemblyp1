#!/usr/bin/env python3
"""Exact complete-candidate census for ternary circular 2-mers, length 4.

Model (MB09 section 6.1 fixed-external-N product-binomial surrogate, not the
exact multinomial of #256 and not the section 6.2 bidirected-flow objective of
#260-#261): alphabet {0,1,2}, oriented 2-mer universe of size 9, circular
candidate length G=4, fixed normalization N=G=4, sample size n=sum_w x(w).

For a count vector B of total N, q_B(w) = B(w)*prod_{v!=w}(N-B(v)) and
F_B(x) = prod_w q_B(w)^x(w). Binomial likelihood comparison at fixed x uses
F_B; the (1-d(w)/N)^(n-x(w)) factors for zero-count coordinates and boundary
probabilities 0/1 are retained inside q without logarithms or division.

For truth A, covered observations are x(w)>=A(w) on supp(A), zero off that
support. The established covered-sample iff: A weakly maximizes against B for
every such complete-support x iff q_B vanishes on supp(A) or
q_B(w)<=q_A(w) for each w in supp(A). This script checks exactly that iff
criterion exhaustively; it is a finite census for this model point only.
"""

from __future__ import annotations

import itertools
from math import prod

ALPHABET = range(3)
LENGTH = 4
UNIVERSE = tuple(itertools.product(ALPHABET, repeat=2))
N = LENGTH


def spectrum(word: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(
        sum((word[i], word[(i + 1) % LENGTH]) == pair for i in range(LENGTH))
        for pair in UNIVERSE
    )


def q(B: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(
        B[i] * prod(N - B[j] for j in range(len(B)) if j != i)
        for i in range(len(B))
    )


def is_covered_maximal(A: tuple[int, ...], B: tuple[int, ...]) -> bool:
    qa, qb = q(A), q(B)
    support = [i for i, a in enumerate(A) if a]
    return any(qb[i] == 0 for i in support) or all(qb[i] <= qa[i] for i in support)


def main() -> None:
    words = tuple(itertools.product(ALPHABET, repeat=LENGTH))
    realized = sorted({spectrum(word) for word in words})
    candidates = tuple(
        B
        for B in itertools.product(range(N + 1), repeat=len(UNIVERSE))
        if sum(B) == N
    )
    assert len(words) == 81, len(words)
    assert len(candidates) == 495, len(candidates)
    assert all(B in candidates for B in realized)

    rows = []
    for A in realized:
        bad = [B for B in candidates if B != A and not is_covered_maximal(A, B)]
        rows.append((A, len(bad), bad[:1]))
    realizable_bad = sum(
        not is_covered_maximal(A, B)
        for A in realized
        for B in realized
        if B != A
    )
    full_bad = sum(count for _, count, _ in rows)
    assert realizable_bad <= full_bad
    print("ternary circular L=4, oriented 2-mer universe size 9, fixed N=4")
    print(f"words={len(words)} distinct realizable spectra={len(realized)}")
    print(f"same-total integer competitors={len(candidates)}")
    print(f"covered-maximal (truth,competitor) violations: full={full_bad}, realizable={realizable_bad}")
    for A, count, example in rows:
        print(f"  A={A}: {count} full-class violations; example={example[0] if example else None}")
    print("ALL OK; exact finite census, no universal ternary claim")


if __name__ == "__main__":
    main()
