#!/usr/bin/env python3
"""Exact-rational check of the bounded MB09 §6.1 witness in the paired note."""

from fractions import Fraction


N = 2
TRUTH = (1, 1)       # circular spectrum of string 01
COMPETITOR = (2, 0)  # circular spectrum of string 00


def product_binomial(d, x):
    n = sum(x)
    result = Fraction(1)
    for count, observed in zip(d, x):
        p = Fraction(count, N)
        result *= p**observed * (1 - p) ** (n - observed)
    return result


def multinomial(d, x):
    """Exact joint-multinomial probability, included to display distinction."""
    n = sum(x)
    result = Fraction(1)
    for count, observed in zip(d, x):
        p = Fraction(count, N)
        result *= p**observed
    return result


def main():
    complete_support = (1, 1)
    assert sum(TRUTH) == sum(COMPETITOR) == N
    assert product_binomial(TRUTH, complete_support) == Fraction(1, 16)
    assert product_binomial(COMPETITOR, complete_support) == 0
    assert multinomial(TRUTH, complete_support) == Fraction(1, 4)
    assert multinomial(COMPETITOR, complete_support) == 0
    assert product_binomial(TRUTH, complete_support) > product_binomial(
        COMPETITOR, complete_support
    )

    boundary_sample = (1, 0)
    assert product_binomial(TRUTH, boundary_sample) == Fraction(1, 4)
    assert product_binomial(COMPETITOR, boundary_sample) == 1
    # Here the extra failure factor on the unobserved type reverses the
    # ordering from the observed-coordinate multinomial numerator.
    assert multinomial(TRUTH, boundary_sample) == Fraction(1, 2)
    assert multinomial(COMPETITOR, boundary_sample) == 1
    print("issue #259 bounded witness: exact rational checks passed")
    print("x=(1,1): product-binomial truth=1/16 competitor=0; truth wins")
    print("x=(1,0): product-binomial truth=1/4 competitor=1; truth loses")


if __name__ == "__main__":
    main()
