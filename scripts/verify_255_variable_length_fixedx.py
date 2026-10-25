#!/usr/bin/env python3
"""Independent exact-rational check for #255 fixed-x variable-length separation.

Claim (AssemblyP1/FixedXVariableLengthSeparation.lean): on two read types at
fixed observation x = (2, 1), truth A = (3, 1) of total G = 4 is the UNIQUE
maximizer of the exact-multinomial fixed-x spectrum factor among all count
vectors of total 4, yet the different-total candidate B = (2, 1) of total 3
strictly beats it at the same x (4/27 > 9/64).

This script verifies with exact Fractions:
  1. factor(C, 4, x) <= factor(A, 4, x) for every mass-4 vector C, strict
     unless C == A (uniqueness among same-total spectra);
  2. factor(B, 3, x) > factor(A, 4, x) (variable-length beater);
  3. the beater is not an artifact of the two-type universe: it also beats A
     when both compete against every mass-3..8 spectrum (B attains the
     continuous simplex optimum q = x/n, so no spectrum of any total beats B
     at this x).
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product


def factor(c, G, x):
    assert sum(c) == G and G > 0
    out = Fraction(1)
    for ci, xi in zip(c, x):
        out *= Fraction(ci, G) ** xi
    return out


def mass_vectors(total, k):
    if k == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in mass_vectors(total - first, k - 1):
            yield (first,) + rest


def main() -> None:
    A, G, x = (3, 1), 4, (2, 1)
    B, Gp = (2, 1), 3
    fa = factor(A, G, x)
    assert fa == Fraction(9, 64), fa

    # 1. A unique maximizer among same-total spectra.
    same = list(mass_vectors(G, 2))
    assert len(same) == 5, len(same)
    for C in same:
        fc = factor(C, G, x)
        assert fc <= fa, (C, fc, fa)
        if C == A:
            assert fc == fa
        else:
            assert fc < fa, (C, fc, fa)

    # 2. Variable-length beater.
    fb = factor(B, Gp, x)
    assert fb == Fraction(4, 27), fb
    assert fa < fb, (fa, fb)

    # 3. B attains the simplex optimum q = x/n, so nothing beats it at this x.
    n = sum(x)
    opt = Fraction(1)
    for xi in x:
        opt *= Fraction(xi, n) ** xi
    assert fb == opt, (fb, opt)
    for total in range(1, 9):
        for C in mass_vectors(total, 2):
            assert factor(C, total, x) <= fb, (C, total)

    print(f"fa={fa} fb={fb} optimum={opt}")
    print("PASS: same-total unique max + strict variable-length beater, exact rational")


if __name__ == "__main__":
    main()
