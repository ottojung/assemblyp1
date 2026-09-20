#!/usr/bin/env python3
"""Independent exact check for the MB09 Section 6.1 index-orientation note.

Resolves whether the literal 4^k index set is oriented or reverse-complement
classed, and whether the PR #43 same-length witness AAATAT -> AAAAAT survives
the source-faithful Section 6.2 (molecule-class) objective.

Self-contained: exact integer/Fraction arithmetic, deterministic, exits non-zero
on any failed assertion. Shares no code with the repository's searches.
"""

from collections import Counter
from fractions import Fraction

COMP = {"A": "T", "T": "A", "C": "G", "G": "C"}


def rc(w):
    return "".join(COMP[c] for c in reversed(w))


def windows(s, L):
    n = len(s)
    return ["".join(s[(i + j) % n] for j in range(L)) for i in range(n)]


def klass(w):
    return min(w, rc(w))


def palindromic_count(k):
    return 4 ** (k // 2) if k % 2 == 0 else 0


def class_count(k):
    return (4 ** k + palindromic_count(k)) // 2


def check_class_counts():
    expected = {1: 2, 2: 10, 3: 32, 4: 136, 5: 512, 6: 2080}
    for k, e in expected.items():
        assert class_count(k) == e, (k, class_count(k), e)
        assert class_count(k) < 4 ** k or k == 1
    print("class counts (4^k+p_k)/2 for k<=6:", [class_count(k) for k in range(1, 7)])


def check_witness():
    S, D, L = "AAATAT", "AAAAAT", 3
    starts = [0, 0, 1, 3, 5]
    ws, wd = windows(S, L), windows(D, L)
    obs = [ws[i] for i in starts]

    assert ws == ["AAA", "AAT", "ATA", "TAT", "ATA", "TAA"], ws
    assert wd == ["AAA", "AAA", "AAA", "AAT", "ATA", "TAA"], wd
    assert obs == ["AAA", "AAA", "AAT", "TAT", "TAA"], obs

    dS, dD = Counter(map(klass, ws)), Counter(map(klass, wd))
    x = Counter(map(klass, obs))
    assert dS == {"AAA": 1, "AAT": 1, "ATA": 3, "TAA": 1}, dS
    assert dD == {"AAA": 3, "AAT": 1, "ATA": 1, "TAA": 1}, dD
    assert x == {"AAA": 2, "AAT": 1, "ATA": 1, "TAA": 1}, x

    supp = set(x)
    assert set(dS) == supp, (set(dS), supp)
    assert set(dD) == supp, (set(dD), supp)
    print("class support equality holds: supp(x)=supp(dS)=supp(dD)=", sorted(supp))

    N, n = 6, 5
    num = den = Fraction(1)
    for i in set(dS) | set(dD):
        num *= Fraction(dD[i]) ** x[i] * Fraction(N - dD[i]) ** (n - x[i])
        den *= Fraction(dS[i]) ** x[i] * Fraction(N - dS[i]) ** (n - x[i])
    ratio_binom = num / den
    assert ratio_binom == 5, ratio_binom

    num = den = Fraction(1)
    for i in set(dS) | set(dD):
        num *= Fraction(dD[i]) ** x[i]
        den *= Fraction(dS[i]) ** x[i]
    ratio_exact = num / den
    assert ratio_exact == 3, ratio_exact
    print("objective ratios L(D)/L(S): §6.1 binomial =", ratio_binom,
          " same-length exact =", ratio_exact)

    # strict oriented indexing
    doS, doD, xo = Counter(ws), Counter(wd), Counter(obs)
    assert xo["TAT"] == 1 and doD["TAT"] == 0, (xo["TAT"], doD["TAT"])
    assert doS["TAT"] == 1, doS["TAT"]
    assert set(xo) - set(doD) == {"TAT"}, set(xo) - set(doD)
    print("strict oriented indexing: competitor d_D(TAT)=0 vs observed x(TAT)=1 "
          "=> competitor factor 0 (witness inverts)")

    # why the oriented and classed counts differ: no forced symmetry
    assert doS["ATA"] == 2 and doS["TAT"] == 1 and dS["ATA"] == 3
    print("non-symmetry: d_S(ATA)=%d, d_S(TAT)=%d, class ATA=%d"
          % (doS["ATA"], doS["TAT"], dS["ATA"]))


def main():
    check_class_counts()
    check_witness()
    print("OK")


if __name__ == "__main__":
    main()
