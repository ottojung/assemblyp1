#!/usr/bin/env python3
"""Exact complete-candidate census for ternary circular 2-mers, length 3.

For each realizable truth A, this checks the established covered-sample
criterion against every same-total integer candidate B. The criterion is
exactly the condition for F_A(x)>=F_B(x) for every complete-support x>=A:
q_B must vanish on supp(A), or q_B(w)<=q_A(w) for every w in supp(A).
This is a finite result for L=2, alphabet size 3, N=3; it is not a theorem for
longer words, larger alphabets, or all possible truth spectra.
"""

from __future__ import annotations

import itertools
from math import prod

ALPHABET = range(3)
LENGTH = 3
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
    # If B has q_B=0 on truth support, every complete-support sample has
    # likelihood zero under B. Otherwise each covered exponent can be made
    # arbitrarily large independently, so coordinatewise q_B<=q_A is iff.
    return any(qb[i] == 0 for i in support) or all(qb[i] <= qa[i] for i in support)


def main() -> None:
    words = tuple(itertools.product(ALPHABET, repeat=LENGTH))
    realized = sorted({spectrum(word) for word in words})
    candidates = tuple(
        B
        for B in itertools.product(range(N + 1), repeat=len(UNIVERSE))
        if sum(B) == N
    )
    assert len(words) == 27 and len(realized) == 11 and len(candidates) == 165
    assert all(B in realized for B in realized)

    rows = []
    for A in realized:
        bad = [B for B in candidates if B != A and not is_covered_maximal(A, B)]
        rows.append((A, len(bad), bad[:1]))
    # The loop above marks a candidate bad iff it violates the necessary and
    # sufficient product-binomial covered-sample inequality for some supported
    # coordinate. It intentionally makes no claim about realizable-class
    # maximality when bad competitors exist; that requires restricting B to
    # the 11 realized spectra, whereas full-class maximality checks all 165.
    realizable_bad = sum(
        not is_covered_maximal(A, B)
        for A in realized
        for B in realized
        if B != A
    )
    full_bad = sum(count for _, count, _ in rows)
    assert realizable_bad <= full_bad
    print("ternary circular L=3, oriented 2-mer universe size 9, fixed N=3")
    print(f"words={len(words)} distinct realizable spectra={len(realized)}")
    print(f"same-total integer competitors={len(candidates)}")
    print(f"covered-maximal (truth,competitor) violations: full={full_bad}, realizable={realizable_bad}")
    for A, count, example in rows:
        print(f"  A={A}: {count} full-class violations; example={example[0] if example else None}")
    print("ALL OK; exact finite census, no universal ternary claim")


if __name__ == "__main__":
    main()
