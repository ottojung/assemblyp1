#!/usr/bin/env python3
"""Independent exact-integer test of fixed-N product-binomial factorization.

This is a regression test for AssemblyP1/FixedNBinomialEffectiveWeights.lean.
The product of binomial marginals is a separable approximation, not the true
joint multinomial likelihood. The modeled type universe stays fixed, including
types with zero observations. All values are arbitrary-precision integers.
"""

from fractions import Fraction
from math import comb, prod


def compositions(total, count):
    if count == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in compositions(total - first, count - 1):
            yield (first,) + rest


def numerator(N, B, x):
    n = sum(x)
    return prod(b**xi * max(N - b, 0)**(n - xi) for b, xi in zip(B, x))


def effective(N, B, x):
    return prod(
        (B[i] * prod(max(N - B[j], 0) for j in range(len(B)) if j != i)) ** x[i]
        for i in range(len(B))
    )


def independent_marginal_score(N, B, x):
    n = sum(x)
    return prod(
        (
            Fraction(comb(n, xi) * b**xi * (N - b)**(n - xi), N**n)
            for b, xi in zip(B, x)
        ),
        start=Fraction(1),
    )


def main():
    cases = 0
    prob_cases = 0
    for k in range(1, 5):
        for G in range(1, 9):
            for B in compositions(G, k):
                # Test natural-number subtraction even when B_i > N, but never
                # interpret these cases as conventional binomial probabilities.
                for N in sorted({0, 1, G, G + 1, G + 2}):
                    for n in range(0, 5):
                        for x in compositions(n, k):
                            assert numerator(N, B, x) == effective(N, B, x), (N, B, x)
                            cases += 1
                            if N > 0 and all(b <= N for b in B):
                                coeff = prod(comb(n, xi) for xi in x)
                                normalized = Fraction(
                                    coeff * effective(N, B, x), N ** (n * k)
                                )
                                assert normalized == independent_marginal_score(N, B, x)
                                prob_cases += 1

    # A small covered truth sample from AAABBB (L=2, N=G=6).
    A = (2, 1, 2, 1)
    B = (1, 2, 1, 2)
    x = (1, 2, 1, 2)
    ratio = independent_marginal_score(6, B, x) / independent_marginal_score(6, A, x)
    assert ratio == Fraction(25, 4), ratio
    print(f"PASS {cases} exact natural-number factorizations")
    print(f"PASS {prob_cases} fully normalized fixed-N marginal scores")
    print(f"PASS AAABBB covered-sample binomial ratio: {ratio}")


if __name__ == "__main__":
    main()
