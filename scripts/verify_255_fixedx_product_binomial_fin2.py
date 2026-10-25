#!/usr/bin/env python3
"""Exact-rational check of one finite fixed-x product-binomial cell (#255/#259).

Frozen model: MB09 §6.1 fixed-external-N product-binomial surrogate; two
oriented read types; positive integer candidate spectra summing to N=4; fixed
sample x=(2,2). This checks the complete candidate class and exact scores. It
is a finite computational check, not a general classification theorem.
"""

from fractions import Fraction
from math import prod


def score(candidate, x=(2, 2), N=4):
    n = sum(x)
    return prod(
        Fraction(candidate[i], N) ** x[i]
        * Fraction(N - candidate[i], N) ** (n - x[i])
        for i in range(2)
    )


def main():
    candidates = [(a, 4 - a) for a in range(1, 4)]
    scores = {c: score(c) for c in candidates}
    expected = {
        (1, 3): Fraction(81, 65536),
        (2, 2): Fraction(1, 256),
        (3, 1): Fraction(81, 65536),
    }
    assert scores == expected, scores
    maximizers = {c for c, value in scores.items() if value == max(scores.values())}
    assert maximizers == {(2, 2)}, maximizers
    print("fixed-x product-binomial Fin2 cell verified exactly:")
    print(f"  N=4 x=(2,2), candidates={candidates}")
    print(f"  scores={scores}")
    print(f"  unique maximizer={sorted(maximizers)}")


if __name__ == "__main__":
    main()
