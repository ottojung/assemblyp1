#!/usr/bin/env python3
"""Independent verifier for the AAATT witness across the source convention axes.

Self-contained: no repository imports. Exact integer / Fraction arithmetic,
deterministic, exits non-zero on any failed assertion.

Run:  python3 scripts/verify_issue36_aaatt_faithful_conventions.py
"""

from collections import Counter
from fractions import Fraction
from itertools import product

A, T = "A", "T"


def rc(w):
    return "".join(T if c == A else A for c in reversed(w))


def mol(w):
    return min(w, rc(w))


def windows(s, L):
    return ["".join(s[(i + j) % len(s)] for j in range(L)) for i in range(len(s))]


def truth_instance():
    S, L, starts = "AAATT", 3, (0, 1, 4)
    truth_windows_oriented = windows(S, L)
    truth_windows_mol = [mol(w) for w in truth_windows_oriented]
    obs_oriented = ["".join(S[(i + j) % len(S)] for j in range(L)) for i in starts]
    obs_mol = [mol(w) for w in obs_oriented]
    return S, L, starts, truth_windows_oriented, Counter(truth_windows_mol), Counter(obs_mol), Counter(obs_oriented)


def exact(candidate, x, oriented):
    """Exact candidate-intrinsic-N(D) multinomial, dropping x=0 factors."""
    G = len(candidate)
    d = Counter(windows(candidate, L=3) if oriented else (mol(w) for w in windows(candidate, 3)))
    p = Fraction(1)
    for typ in set(d) | set(x):
        di, xi = d.get(typ, 0), x.get(typ, 0)
        if di == 0 and xi > 0:
            return Fraction(0)
        p *= Fraction(di, G) ** xi
    return p


def binom(candidate, x, n, N, oriented):
    """MB09 Sec. 6.1 product of binomial marginals over all types, external N."""
    d = Counter(windows(candidate, 3) if oriented else (mol(w) for w in windows(candidate, 3)))
    p = Fraction(1)
    for typ in set(d) | set(x):
        di, xi = d.get(typ, 0), x.get(typ, 0)
        if di > N or (di == 0 and xi > 0):
            return Fraction(0)
        p *= Fraction(di, N) ** xi * Fraction(N - di, N) ** (n - xi)
    return p


def best(candidate_class, x, n, N, oriented, objective):
    base = objective(S, x, n, N, oriented) if objective is binom else objective(S, x, oriented)
    best_ratio, best_words = Fraction(0), []
    for tup in product(A + T, repeat=len(S)):
        D = "".join(tup)
        val = objective(D, x, n, N, oriented) if objective is binom else objective(D, x, oriented)
        ratio = val / base if base > 0 else val
        if ratio > best_ratio:
            best_ratio, best_words = ratio, [D]
        elif ratio == best_ratio and ratio > 0:
            best_words.append(D)
    return best_ratio, sorted(set(best_words))


def main():
    global S
    S, L, starts, tw_oriented, dS_mol, x_mol, x_oriented = truth_instance()
    n, N = sum(x_mol.values()), len(S)

    # --- Panel A: variable-length, molecule classes, Sec. 6.1 binomial ---
    D6 = "AAAATT"
    ratio_A = binom(D6, x_mol, n, N, False) / binom(S, x_mol, n, N, False)
    assert ratio_A == Fraction(9, 8), ratio_A
    dD6 = Counter(mol(w) for w in windows(D6, L))
    assert Counter(mol(w) for w in windows(S, L)) == Counter({mol("AAA"): 1, mol("AAT"): 2, mol("TAA"): 2})
    assert dD6 == Counter({mol("AAA"): 2, mol("AAT"): 2, mol("TAA"): 2})

    # --- Panel B: fixed length G=5, molecule classes ---
    rB_binom, wB_binom = best(S, x_mol, n, N, False, binom)
    assert rB_binom == 1, rB_binom
    assert len(wB_binom) == 10, wB_binom
    rB_exact, wB_exact = best(S, x_mol, n, N, False, exact)
    assert rB_exact == 1 and len(wB_exact) == 10

    # --- Panel C: fixed length G=5, single-strand oriented read types ---
    rC_binom, wC_binom = best(S, x_oriented, n, N, True, binom)
    assert rC_binom == Fraction(1125, 512), rC_binom
    assert wC_binom == ["AAAAT", "AAATA", "AATAA", "ATAAA", "TAAAA"], wC_binom
    rC_exact, wC_exact = best(S, x_oriented, n, N, True, exact)
    assert rC_exact == 2 and wC_exact == wC_binom, (rC_exact, wC_exact)

    # Oriented truth support strictly exceeds the observed oriented support.
    assert set(tw_oriented) == {"AAA", "AAT", "ATT", "TTA", "TAA"}
    assert set(x_oriented) == {"AAA", "AAT", "TAA"}
    assert not set(tw_oriented) <= set(x_oriented)

    print("AAATT faithful-convention verifier: all assertions passed")
    print("  Panel A  variable-length + molecule classes + Sec.6.1 binomial : D/S =", ratio_A)
    print("  Panel B  fixed G=5 + molecule classes   : best ratio", rB_binom, "over", len(wB_binom), "tie maximizers (dihedral orbit of AAATT)")
    print("  Panel C  fixed G=5 + oriented single-strand: best ratio", rC_binom, "(binom) /", rC_exact, "(exact), winners", wC_binom)
    print("  oriented truth windows :", tw_oriented)
    print("  oriented observed      :", sorted(x_oriented))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
