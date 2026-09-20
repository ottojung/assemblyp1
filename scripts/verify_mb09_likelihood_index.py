#!/usr/bin/env python3
"""Independent, self-contained check of the Medvedev-Brudno (2009) Section 6.1
likelihood index set against the Section 6.2 DNA-molecule vertices, and of the
same-length `AAATAT -> AAAAAT` witness under the faithful combined reading.

This script imports no repository code. It uses exact ``Fraction`` arithmetic.
It exits non-zero on any failed assertion.

Claims checked:
  (A) #molecule classes of length k over a 4-letter alphabet is
      (4^k + p_k)/2 with p_k = 4^(k/2) for even k and 0 for odd k, so the
      literal "4^k" of Section 6.1 is not the number of trial outcomes.
  (B) On the witness, the molecule-class spectrum of the truth has support
      equal to the observed support, while the oriented spectrum does not.
  (C) The Section 6.1 separable-binomial ratio D/S is exactly 5; the
      same-length exact-multinomial ratio is exactly 3.
  (D) The oriented counts of a one-strand double-stranded candidate need not
      be orientation-symmetric: d_S(ATA)=2, d_S(TAT)=1, summing to the class
      count d_S(ATA-class)=3.
"""

from fractions import Fraction
from itertools import product
from math import comb
from collections import Counter

COMP = {"A": "T", "T": "A", "C": "G", "G": "C"}
ALPHA = "ACGT"


def rc(w):
    return "".join(COMP[c] for c in reversed(w))


def cls(w):
    return min(w, rc(w))


def windows_circular(s, L):
    n = len(s)
    return ["".join(s[(t + j) % n] for j in range(L)) for t in range(n)]


def molecule_class_count(k):
    """Enumerate revcomp orbits of ALPHA^k and return (#orbits, self-revcomp)."""
    orbits, pal = 0, 0
    for w in map("".join, product(ALPHA, repeat=k)):
        if cls(w) == w:
            orbits += 1
        if w == rc(w):
            pal += 1
    return orbits, pal


def predicted_class_count(k):
    p = 4 ** (k // 2) if k % 2 == 0 else 0
    return (4 ** k + p) // 2, p


def binomial_pmf_ratio(x, dS, dD, N, n):
    """Ratio of the Section 6.1 fixed-N product-of-binomials likelihoods."""
    def like(xc, dc):
        f = Fraction(1)
        for c, xv in xc.items():
            dv = dc.get(c, 0)
            # C(n, x) * (d/N)^x * (1 - d/N)^(n-x); ignore d=0&x=0 term (=1)
            if xv == 0 and dv == 0:
                continue
            if dv == 0:
                return Fraction(0)
            f *= comb(n, xv) * Fraction(dv, N) ** xv \
                 * Fraction(N - dv, N) ** (n - xv)
        return f
    return like(x, dD) / like(x, dS)


def exact_multinomial_ratio(x, dS, dD, N):
    """Ratio of candidate-dependent parts of the exact multinomial (same N)."""
    def like(xc, dc):
        f = Fraction(1)
        for c, xv in xc.items():
            dv = dc.get(c, 0)
            if xv == 0:
                continue
            if dv == 0:
                return Fraction(0)
            f *= Fraction(dv, N) ** xv
        return f
    return like(x, dD) / like(x, dS)


def main():
    # ---- (A) molecule-class count --------------------------------------
    for k in range(1, 7):
        got, pal = molecule_class_count(k)
        pred, ppal = predicted_class_count(k)
        assert got == pred, (k, got, pred)
        assert pal == ppal, (k, pal, ppal)
        assert 4 ** k != pred, k
    assert molecule_class_count(3)[0] == 32
    assert molecule_class_count(4)[0] == 136
    print("(A) molecule-class counts OK: k=3 -> 32, k=4 -> 136 (not 64/256)")

    # ---- witness data --------------------------------------------------
    L = 3
    S, D, N, n = "AAATAT", "AAAAAT", 6, 5
    starts = [0, 0, 1, 3, 5]
    reads = [windows_circular(S, L)[t] for t in starts]

    wS, wD = windows_circular(S, L), windows_circular(D, L)
    dS_or, dD_or = Counter(wS), Counter(wD)
    dS_cl = Counter(cls(w) for w in wS)
    dD_cl = Counter(cls(w) for w in wD)
    x_or = Counter(reads)
    x_cl = Counter(cls(w) for w in reads)

    # ---- (B) support under the two index sets --------------------------
    assert set(x_cl) == set(dS_cl) == set(dD_cl), (x_cl, dS_cl, dD_cl)
    # oriented reading: ATA is in the truth/competitor spectra but unobserved
    assert "ATA" not in x_or and dS_or["ATA"] >= 1 and dD_or["ATA"] >= 1
    assert (set(dS_or) - set(x_or)) == {"ATA"}
    assert (set(dD_or) - set(x_or)) == {"ATA"}
    print("(B) class support equality holds for S and D; "
          "oriented support fails (unobserved ATA)")

    # ---- (C) objective ratios -----------------------------------------
    b = binomial_pmf_ratio(x_cl, dS_cl, dD_cl, N, n)
    e = exact_multinomial_ratio(x_cl, dS_cl, dD_cl, N)
    assert b == 5, b
    assert e == 3, e
    print(f"(C) Section 6.1 binomial D/S = {b}; exact multinomial D/S = {e}")

    # ---- (D) no orientation symmetry is required -----------------------
    assert dS_or["ATA"] == 2 and dS_or["TAT"] == 1
    assert dS_or["ATA"] + dS_or["TAT"] == dS_cl[cls("ATA")] == 3
    print("(D) d_S(ATA)=2, d_S(TAT)=1, class total=3: oriented counts of a "
          "one-strand genome are not symmetric; they sum to the class count")

    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
