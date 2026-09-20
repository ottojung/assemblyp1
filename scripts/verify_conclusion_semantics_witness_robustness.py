#!/usr/bin/env python3
"""Verify that the integrated strict Section 6.2 witnesses are robust to every
source-supported genome-equivalence convention.

This is a focused conclusion-semantics check, not a new counterexample search.

Two integrated witnesses are checked:

  * same-length  (PR #43): truth AAATAT (G=6), competitor AAAAAT (|D|=6),
    starts (0,0,1,3,5), N=6, L=3;
  * variable-length (PR #40): truth AAATT (G=5), competitor AAAATT (|D|=6),
    starts (0,1,4), N=5, L=3.

For each witness the script checks, with exact rational arithmetic:

  1. the literal Medvedev-Brudno Sec. 6.1 product-of-binomials strictly
     improves on the competitor;
  2. the candidate-intrinsic exact multinomial strictly improves on the
     competitor (to fix the objective convention);
  3. the likelihood statistic is invariant under cyclic rotation of a
     candidate and under reverse complement of a candidate (molecule-class
     index set) -- so the comparison is well defined on equivalence classes;
  4. the competitor is NOT related to the truth by any cyclic shift and/or
     reverse complement -- the only genome-equivalence conventions supported
     by Shomorony et al. (2016) / Medvedev-Brudno (2009).

Exit status is non-zero on any failed assertion.
"""

from fractions import Fraction as F
from functools import reduce
from math import comb
import sys

COMP = {"A": "T", "T": "A", "C": "G", "G": "C"}


def rc(w):
    return tuple(COMP[c] for c in reversed(w))


def rotations(w):
    return {tuple(w[i:] + w[:i]) for i in range(len(w))}


def dihedral_orbit(w):
    """All cyclic shifts of w and of its reverse complement (circular words)."""
    return rotations(w) | rotations(rc(w))


def windows(g, L):
    n = len(g)
    return [tuple(g[(i + j) % n] for j in range(L)) for i in range(n)]


def molecule_class(w):
    return min(w, rc(w))


def observed_counts(truth, starts, L):
    x = {}
    w = windows(truth, L)
    for r in starts:
        c = molecule_class(w[r])
        x[c] = x.get(c, 0) + 1
    return x


def spectrum(candidate, L):
    d = {}
    for w in windows(candidate, L):
        c = molecule_class(w)
        d[c] = d.get(c, 0) + 1
    return d


def binom_marginal(d, x, N, n):
    """Literal Medvedev-Brudno Sec. 6.1 product of binomial marginals."""
    types = set(d) | set(x)
    out = F(1)
    for t in types:
        di, xi = d.get(t, 0), x.get(t, 0)
        out *= F(comb(n, xi)) * F(di, N) ** xi * F(N - di, N) ** (n - xi)
    return out


def exact_multinomial(d, x):
    """Candidate-intrinsic exact multinomial, constants cancelled.

    Medvedev-Brudno Sec. 6.1 uses the candidate's own length N(D) as the
    denominator of every type probability.  The n! and 1/(prod x_i!) factors
    are observation-only and cancel in a ratio of two candidates on the same
    observation, so we keep only prod (d_t / N(D))^{x_t}.
    """
    ND = sum(d.values())
    types = set(d) | set(x)
    out = F(1)
    for t in types:
        out *= F(d.get(t, 0), ND) ** x.get(t, 0)
    return out


def check_witness(name, truth, competitor, starts, N, L):
    x = observed_counts(truth, starts, L)
    dS = spectrum(truth, L)
    dD = spectrum(competitor, L)
    n = len(starts)

    assert sum(dS.values()) == len(truth)
    assert sum(dD.values()) == len(competitor), (name, "D length mismatch")

    b_inv = binom_marginal(dS, x, N, n)
    b_comp = binom_marginal(dD, x, N, n)
    e_inv = exact_multinomial(dS, x)
    e_comp = exact_multinomial(dD, x)

    assert e_inv > 0 and e_comp > 0, (name, "nonpositive likelihood")
    assert b_comp > b_inv, (name, "Sec. 6.1 binomial not strict", b_comp, b_inv)
    assert e_comp > e_inv, (name, "exact multinomial not strict", e_comp, e_inv)

    # Invariance of both objectives under cyclic shift and reverse complement.
    for label, cand in (("truth", truth), ("competitor", competitor)):
        base_d = spectrum(cand, L)
        base_b = binom_marginal(base_d, x, N, n)
        base_e = exact_multinomial(base_d, x)
        for c2 in dihedral_orbit(cand):
            d2 = spectrum(c2, L)
            assert d2 == base_d, (name, label, "spectrum not dihedral-invariant", cand, c2)
            assert binom_marginal(d2, x, N, n) == base_b, (name, label, "binomial not invariant")
            assert exact_multinomial(d2, x) == base_e, (name, label, "exact not invariant")

    # The only source-supported genome equivalences: cyclic shift and
    # reverse complement. The competitor must be outside the truth's orbit.
    orb_S = dihedral_orbit(truth)
    orb_D = dihedral_orbit(competitor)
    assert orb_S.isdisjoint(orb_D), (name, "competitor equivalent to truth", orb_S & orb_D)

    if e_comp > e_inv:
        print(f"[{name}] truth={''.join(truth)}  competitor={''.join(competitor)}")
        print(f"    Sec. 6.1 binomial ratio   = {b_comp / b_inv}")
        print(f"    exact multinomial ratio   = {e_comp / e_inv}")
        print(f"    truth orbit size          = {len(orb_S)}")
        print(f"    competitor orbit size     = {len(orb_D)}  (disjoint: yes)")
        print(f"    both objectives strict, dihedral-invariant, orbit-disjoint: OK")


def main():
    check_witness(
        "same-length PR#43",
        tuple("AAATAT"), tuple("AAAAAT"), (0, 0, 1, 3, 5), 6, 3,
    )
    check_witness(
        "variable-length PR#40",
        tuple("AAATT"), tuple("AAAATT"), (0, 1, 4), 5, 3,
    )
    print("\nAll conclusion-semantics robustness checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
