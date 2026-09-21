#!/usr/bin/env python3
"""Deterministic checks for docs/source-notes/candidate-universe-source-live-resolution.md.

Self-contained; exact integer/Fraction arithmetic; exits non-zero on failure.

Checks:
  (1) GAACA and GACAA have equal directed length-2 spectra, equal length, and are
      not related by cyclic shift or reverse complement (dihedral inequivalent).
  (2) The exact Medvedev-Brudno SS6.1 likelihood factor depends only on the
      spectrum: GAACA and GACAA receive the same factor for every observation.
  (3) The exact SS6.1 ratio occ/N(D) is invariant under tandem repetition
      D -> D+D (which is why free length ties the truth with S^2).
  (4) The fixed-N binomial product is a function of the count vector d and the
      external parameter N only; it takes no candidate-length argument. Two
      candidates with equal spectra receive the same value.
"""

from collections import Counter
from fractions import Fraction
from itertools import product

DNA = "ACGT"
COMP = {"A": "T", "T": "A", "C": "G", "G": "C"}


def revcomp(s: str) -> str:
    return "".join(COMP[c] for c in reversed(s))


def rotations(s: str):
    return [s[i:] + s[:i] for i in range(len(s))]


def dihedral_canon(s: str) -> str:
    return min(rotations(s) + rotations(revcomp(s)))


def circular_windows(s: str, k: int):
    n = len(s)
    assert 1 <= k <= n, (s, k)
    return ["".join(s[(i + j) % n] for j in range(k)) for i in range(n)]


def spectrum(s: str, k: int) -> Counter:
    return Counter(circular_windows(s, k))


def exact_factor(d: Counter, x: Counter, n_d: int) -> Fraction:
    """prod_t (d_t / N(D))^{x_t}, the candidate-dependent part of M28."""
    f = Fraction(1)
    for t in x:
        if x[t] == 0:
            continue
        f *= Fraction(d.get(t, 0), n_d) ** x[t]
    return f


def binomial_factor(d: Counter, x: Counter, n: int, N: int) -> Fraction:
    """prod_t C(n, x_t) (d_t/N)^{x_t} (1 - d_t/N)^{n - x_t}; external N only."""
    from math import comb

    f = Fraction(1)
    for t in x:
        di = d.get(t, 0)
        xi = x[t]
        f *= comb(n, xi) * Fraction(di, N) ** xi * Fraction(N - di, N) ** (n - xi)
    return f


def check(cond, msg):
    if not cond:
        raise AssertionError(msg)


def main():
    A, B = "GAACA", "GACAA"

    # (1) equal directed 2-spectra, same length, dihedral inequivalent.
    sa, sb = spectrum(A, 2), spectrum(B, 2)
    check(sa == sb, f"2-spectra differ: {sa} vs {sb}")
    check(len(A) == len(B) == 5, "lengths differ")
    check(dihedral_canon(A) != dihedral_canon(B),
          "A and B are dihedrally equivalent")
    check(A not in rotations(B) and B not in rotations(A),
          "A and B are cyclic shifts")
    check(revcomp(A) not in rotations(B), "B is a reverse-complement rotation of A")
    print("(1) GAACA/GACAA: equal directed 2-spectra, length 5, dihedrally inequivalent OK")

    # (2) exact SS6.1 factor depends only on the spectrum.
    # Every observation over the union support gives equal factors.
    support = sorted(set(sa) | set(sb))
    checked = 0
    for counts in product(range(3), repeat=len(support)):
        x = Counter({support[i]: counts[i] for i in range(len(support)) if counts[i]})
        if not x:
            continue
        fa = exact_factor(sa, x, len(A))
        fb = exact_factor(sb, x, len(B))
        check(fa == fb, f"exact factor differs for {x}: {fa} vs {fb}")
        checked += 1
    print(f"(2) exact SS6.1 factor equal on {checked} observations OK")

    # (3) tandem invariance of occ/N(D) for a range of candidates and L.
    tandem_checked = 0
    for D in ["ACGT", "GAACA", "AABAC".replace("B", "C"), "ACGTACGT"]:
        for L in range(1, len(D) + 1):
            d = spectrum(D, L)
            d2 = spectrum(D + D, L)
            n1, n2 = len(D), len(D + D)
            for t in set(d) | set(d2):
                check(d2.get(t, 0) == 2 * d.get(t, 0),
                      f"occ not doubled for {D},{L},{t}")
                check(Fraction(d2.get(t, 0), n2) == Fraction(d.get(t, 0), n1),
                      f"ratio not preserved for {D},{L},{t}")
            tandem_checked += 1
    print(f"(3) tandem invariance of occ/N(D) on {tandem_checked} (D,L) pairs OK")

    # (4) fixed-N binomial is a function of the count vector only; no length arg.
    x = Counter(circular_windows(A, 2))
    n, N = sum(x.values()), 5
    ba = binomial_factor(sa, x, n, N)
    bb = binomial_factor(sb, x, n, N)
    check(ba == bb, "fixed-N binomial differs on equal spectra")
    # The signature has no candidate-length parameter: a candidate and its tandem
    # repetition are compared only through their count vectors.
    d_tandem = Counter({t: 2 * v for t, v in sa.items()})
    b_tandem = binomial_factor(d_tandem, x, n, N)
    check(b_tandem != ba, "tandem count vector unexpectedly scored identically")
    print("(4) fixed-N binomial depends on count vector (external N) only OK")

    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
