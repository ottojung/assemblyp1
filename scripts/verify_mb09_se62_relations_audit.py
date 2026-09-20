#!/usr/bin/env python3
"""Independent check for docs/source-notes/mb09-se62-relations-independent-audit-2026-09-20.md.

Recomputes, from scratch, the MB09 Section 6.1/6.2 relation facts used in that
audit and the same-length Section 6.2 witness AAATAT -> AAAAAT:

  * cyclic length-3 windows and reverse-complement molecule classes;
  * observed multiplicities x from the realized starts;
  * truth and competitor spectra d_S, d_D;
  * support equality (the Section 6.2 per-vertex lower-bound condition for a
    spelled molecule, under the molecule-class reading);
  * the Section 6.1 fixed-N product-of-binomial-marginals ratio;
  * the same-length exact multinomial ratio.

Exact Fraction/integer arithmetic only, deterministic, exits non-zero on any
failed assertion.  Shares no code with the repository's other searches.
"""

from fractions import Fraction
from math import comb

COMP = {"A": "T", "T": "A"}


def rc(word: str) -> str:
    return "".join(COMP[c] for c in reversed(word))


def mol_class(word: str) -> str:
    return min(word, rc(word))


def windows(seq: str, L: int):
    n = len(seq)
    return ["".join(seq[(i + j) % n] for j in range(L)) for i in range(n)]


def spectrum(seq: str, L: int):
    d = {}
    for w in windows(seq, L):
        c = mol_class(w)
        d[c] = d.get(c, 0) + 1
    return d


def observed(starts, seq: str, L: int):
    x = {}
    n = len(seq)
    for i in starts:
        w = "".join(seq[(i + j) % n] for j in range(L))
        c = mol_class(w)
        x[c] = x.get(c, 0) + 1
    return x


def binomial_lik(x, d, n, N):
    p = Fraction(1)
    for c in set(x) | set(d):
        xc, dc = x.get(c, 0), d.get(c, 0)
        p *= comb(n, xc) * Fraction(dc, N) ** xc * (1 - Fraction(dc, N)) ** (n - xc)
    return p


def exact_lik(x, d):
    tot = sum(d.values())
    p = Fraction(1)
    for c in set(x) | set(d):
        xc, dc = x.get(c, 0), d.get(c, 0)
        p *= Fraction(dc, tot) ** xc
    return p


def main():
    L = 3
    truth, competitor = "AAATAT", "AAAAAT"
    starts = (0, 0, 1, 3, 5)
    N = len(truth)
    n = len(starts)

    x = observed(starts, truth, L)
    dS = spectrum(truth, L)
    dD = spectrum(competitor, L)

    assert windows(truth, L) == ["AAA", "AAT", "ATA", "TAT", "ATA", "TAA"]
    assert windows(competitor, L) == ["AAA", "AAA", "AAA", "AAT", "ATA", "TAA"]
    assert x == {"AAA": 2, "AAT": 1, "ATA": 1, "TAA": 1}, x
    assert dS == {"AAA": 1, "AAT": 1, "ATA": 3, "TAA": 1}, dS
    assert dD == {"AAA": 3, "AAT": 1, "ATA": 1, "TAA": 1}, dD

    assert len(truth) == len(competitor) == N
    assert sum(dS.values()) == sum(dD.values()) == N
    assert sorted(x) == sorted(dS) == sorted(dD)

    b_ratio = binomial_lik(x, dD, n, N) / binomial_lik(x, dS, n, N)
    e_ratio = exact_lik(x, dD) / exact_lik(x, dS)
    assert b_ratio == 5, b_ratio
    assert e_ratio == 3, e_ratio
    assert b_ratio > 1 and e_ratio > 1

    # The truth is a candidate only under the per-vertex lower bound 1, not
    # under the per-occurrence strengthening d >= x.
    assert dS["AAA"] == 1 < x["AAA"] == 2

    print("MB09 Section 6.2 same-length witness AAATAT -> AAAAAT")
    print("  x   =", x)
    print("  d_S =", dS)
    print("  d_D =", dD)
    print("  support equality holds for both molecules")
    print("  Section 6.1 binomial ratio D/S =", b_ratio)
    print("  same-length exact ratio D/S   =", e_ratio)
    print("OK")


if __name__ == "__main__":
    main()
