#!/usr/bin/env python3
"""Independent exact-arithmetic cross-check for the #269 dihedral orbit quotient.

This script does NOT import any Lean code.  It re-derives the finite circular
oriented read model from its definition and checks, by exhaustive enumeration
over small instances, the claims that the Lean module
`AssemblyP1/DihedralOrbitQuotient.lean` kernel-checks:

  (A) rotation invariance of the raw read pmf and the well-defined rotation
      quotient;
  (B) the reverse-complement obstruction: the raw read pmf is *not* RC
      invariant on a concrete instance and therefore does not descend to
      dihedral classes;
  (C) the strand-symmetrized read law is rotation- and RC-invariant and
      normalized on every enumerated instance;
  (D) on an RC-invariant (symmetrized) model, the uniform-dihedral-prior MAP
      decision is exactly a maximum-likelihood decision, with explicit ties;
  (E) prior-averaged MAP success is nondecreasing in the number of reads.

Every assertion is exact (Python fractions); the script exits nonzero on the
first failure and prints the total number of assertions performed.
"""

from __future__ import annotations

import itertools
import sys
from fractions import Fraction

ASSERTIONS = 0


def check(cond: bool, message: str) -> None:
    global ASSERTIONS
    ASSERTIONS += 1
    if not cond:
        raise AssertionError(message)


# ---------------------------------------------------------------------------
# The finite circular oriented read model
# ---------------------------------------------------------------------------

def all_words(alpha, L):
    return [tuple(x) for x in itertools.product(alpha, repeat=L)]


def all_genomes(alpha, G):
    return [tuple(x) for x in itertools.product(alpha, repeat=G)]


def rot(genome, j):
    G = len(genome)
    return tuple(genome[(i + j) % G] for i in range(G))


def rc_word(genome, comp):
    """Reverse complement: (rc S) i = comp (S (-i))."""
    G = len(genome)
    return tuple(comp[genome[(-i) % G]] for i in range(G))


def read_pmf(genome, L, words):
    """Exact read pmf p_S(w) = mult_S(w)/|G| over the given word universe."""
    G = len(genome)
    counts = {}
    for s in range(G):
        w = tuple(genome[(s + d) % G] for d in range(L))
        counts[w] = counts.get(w, 0) + 1
    return {w: Fraction(counts.get(w, 0), G) for w in words}


def sym_pmf(genome, L, comp, words):
    p = read_pmf(genome, L, words)
    q = read_pmf(rc_word(genome, comp), L, words)
    return {w: (p[w] + q[w]) / 2 for w in words}


def involutions(alpha):
    for perm in itertools.permutations(alpha):
        comp = dict(zip(alpha, perm))
        if all(comp[comp[a]] == a for a in alpha):
            yield comp


def dihedral_classes(genomes, comp):
    seen = set()
    classes = []
    for g in genomes:
        if g in seen:
            continue
        cls = set()
        for j in range(len(g)):
            r = rot(g, j)
            cls.add(r)
            cls.add(rc_word(r, comp))
        seen |= cls
        classes.append(cls)
    return classes


def dihedral_index(genomes, comp):
    classes = dihedral_classes(genomes, comp)
    idx = {}
    for k, cls in enumerate(classes):
        for g in cls:
            idx[g] = k
    return classes, idx


# ---------------------------------------------------------------------------
# (A) rotation invariance and rotation quotient
# ---------------------------------------------------------------------------

def check_rotation_invariance(alpha, G, L):
    words = all_words(alpha, L)
    for g in all_genomes(alpha, G):
        base = read_pmf(g, L, words)
        for j in range(G):
            other = read_pmf(rot(g, j), L, words)
            check(base == other,
                  f"rotation invariance failed G={G} L={L} g={g} j={j}")


# ---------------------------------------------------------------------------
# (B) reverse-complement obstruction
# ---------------------------------------------------------------------------

def check_rc_obstruction():
    alpha = (0, 1)
    comp = {0: 1, 1: 0}
    G, L = 3, 2
    S = (0, 0, 1)
    words = all_words(alpha, L)
    pS = read_pmf(S, L, words)
    pR = read_pmf(rc_word(S, comp), L, words)
    check(pS[(0, 0)] == Fraction(1, 3), "p_S(00) must be 1/3")
    check(pR[(0, 0)] == Fraction(0), "p_rcS(00) must be 0")
    check(pS != pR, "raw read pmf must not be RC invariant on 001")
    check(rc_word(S, comp) not in {rot(S, j) for j in range(G)},
          "rc(001) must not be a rotation of 001")
    # no dihedral descent: some dihedral class carries two distinct pmfs
    found = False
    for cls in dihedral_classes(all_genomes(alpha, G), comp):
        vals = {tuple(sorted(read_pmf(g, L, words).items())) for g in cls}
        if len(vals) > 1:
            found = True
    check(found, "some dihedral class must have non-constant raw read pmf")


# ---------------------------------------------------------------------------
# (C) strand-symmetrized model
# ---------------------------------------------------------------------------

def check_symmetrized(alpha, G, L):
    words = all_words(alpha, L)
    for comp in involutions(alpha):
        for g in all_genomes(alpha, G):
            u = sym_pmf(g, L, comp, words)
            check(sum(u.values()) == 1, f"sym normalization failed g={g}")
            check(all(v >= 0 for v in u.values()), "sym nonnegativity failed")
            for j in range(G):
                check(u == sym_pmf(rot(g, j), L, comp, words),
                      f"sym rotation invariance failed g={g} j={j}")
            check(u == sym_pmf(rc_word(g, comp), L, comp, words),
                  f"sym RC invariance failed g={g} comp={comp}")


# ---------------------------------------------------------------------------
# (D) uniform dihedral prior: MAP = ML, with ties
# ---------------------------------------------------------------------------

def check_map_ml(alpha, G, L, n):
    words = all_words(alpha, L)
    for comp in involutions(alpha):
        classes, _ = dihedral_index(all_genomes(alpha, G), comp)
        reps = [next(iter(cls)) for cls in classes]
        pmf = [sym_pmf(rep, L, comp, words) for rep in reps]
        K = len(classes)
        pi = Fraction(1, K)
        for sample in itertools.product(words, repeat=n):
            lik = []
            for k in range(K):
                v = Fraction(1)
                for w in sample:
                    v *= pmf[k][w]
                lik.append(v)
            maxlik = max(lik)
            maxjoint = max(pi * v for v in lik)
            ml_set = {k for k in range(K) if lik[k] == maxlik}
            map_set = {k for k in range(K) if pi * lik[k] == maxjoint}
            check(ml_set == map_set,
                  f"MAP != ML on sample={sample} G={G} L={L} comp={comp}")


def check_tie_symmetrized_G2L1():
    alpha = (0, 1)
    comp = {0: 1, 1: 0}
    G, L = 2, 1
    words = all_words(alpha, L)
    classes, _ = dihedral_index(all_genomes(alpha, G), comp)
    reps = [next(iter(cls)) for cls in classes]
    for r in reps:
        u = sym_pmf(r, L, comp, words)
        for w in words:
            check(u[w] == Fraction(1, 2),
                  "G=2,L=1 symmetrized law must be uniform")
    check(len(classes) >= 2, "G=2,L=1 must have at least two dihedral classes")


# ---------------------------------------------------------------------------
# (E) prior-averaged MAP success nondecreasing in n
# ---------------------------------------------------------------------------

def map_success_exact(alpha, G, L, comp, pi, n):
    words = all_words(alpha, L)
    classes, _ = dihedral_index(all_genomes(alpha, G), comp)
    reps = [next(iter(cls)) for cls in classes]
    pmf = [sym_pmf(rep, L, comp, words) for rep in reps]
    K = len(classes)
    total = Fraction(0)
    for sample in itertools.product(words, repeat=n):
        J = []
        for k in range(K):
            v = pi[k]
            for w in sample:
                v *= pmf[k][w]
            J.append(v)
        best = max(range(K), key=lambda k: (J[k], -k))
        total += J[best]
    return total


def check_monotonicity(alpha, G, L, maxn):
    for comp in involutions(alpha):
        classes, _ = dihedral_index(all_genomes(alpha, G), comp)
        K = len(classes)
        pi = [Fraction(1, K)] * K
        prev = None
        for n in range(0, maxn + 1):
            v = map_success_exact(alpha, G, L, comp, pi, n)
            if prev is not None:
                check(prev <= v,
                      f"monotonicity failed G={G} L={L} comp={comp} n={n}")
            prev = v


# ---------------------------------------------------------------------------

def main() -> int:
    for (G, L) in [(2, 1), (3, 1), (3, 2), (4, 2), (4, 3)]:
        check_rotation_invariance((0, 1), G, L)
    check_rc_obstruction()
    for (G, L) in [(2, 1), (2, 2), (3, 1), (3, 2), (4, 2)]:
        check_symmetrized((0, 1), G, L)
    for n in range(0, 3):
        check_map_ml((0, 1), 2, 1, n)
        check_map_ml((0, 1), 3, 1, n)
    check_tie_symmetrized_G2L1()
    check_monotonicity((0, 1), 2, 1, 4)
    check_monotonicity((0, 1), 3, 1, 3)

    print(f"PASS: {ASSERTIONS} exact assertions")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
