#!/usr/bin/env python3
"""Exact parameterized balanced-competitor check for binary 2-mer alternation."""

from fractions import Fraction
from math import prod


def score(N, B, x):
    q = [B[i] * prod(N - B[j] for j in range(4) if j != i)
         for i in range(4)]
    return prod(Fraction(qi) ** xi for qi, xi in zip(q, x))


def main():
    # A cyclic binary word has equal 01 and 10 counts. Write its spectrum
    # B=(a,t,t,d); its length/normalizer is N=a+d+2t.
    # The balanced competitors to A=(0,m,m,0), N=2m, therefore obey
    # a+d+2t=2m and are completely parameterized by a,d>=0,
    # t=m-(a+d)/2, requiring a+d even.
    checked = 0
    strict = []
    for m in range(1, 101):
        A = (0, m, m, 0)
        N = 2 * m
        for a in range(2 * m + 1):
            for d in range(2 * m - a + 1):
                rem = 2 * m - a - d
                if rem % 2:
                    continue
                t = rem // 2
                B = (a, t, t, d)
                checked += 1
                # Covered samples have x>=A. In particular x=A is included.
                # This assertion checks only the competitor parameterization
                # and its score at x=A, not arbitrary covered-sample maximality.
                ratio = score(N, B, A) / score(N, A, A)
                if ratio > 1:
                    strict.append((m, B, ratio))
        assert sum(1 for a in range(2*m+1) for d in range(2*m-a+1)
                   if (2*m-a-d) % 2 == 0) == (m + 1) ** 2
    print(f"parameterized balanced spectra checked: {checked}")
    print(f"strict x=A counterexamples: {len(strict)}")
    if strict:
        print("first:", strict[0])
        raise SystemExit(1)
    print("PASS: no balanced competitor beats alternating truth at x=A for m<=100")


if __name__ == "__main__":
    main()
