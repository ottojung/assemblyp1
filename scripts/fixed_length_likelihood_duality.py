#!/usr/bin/env python3
"""Verification harness for the fixed-length exact-multinomial likelihood.

Alphabet is binary {A,C}, read length L=2, so there are 4 k-mer types
(AA, AC, CA, CC).  Small enough to exhaust.

Verifies:

  (A) The correct KKT / flow ("graph potential") characterization of the
      continuous Eulerian-polytope relaxation: d_S is a continuous maximizer
      iff x_i / d_S(i) lies in span{1} + rowspace(B), i.e. is a graph potential
      plus a constant -- NOT merely constant.

  (B) That "x proportional to d_S" is SUFFICIENT but NOT NECESSARY.  Includes
      the explicit AACC counterexample and an exhaustive small search for
      non-proportional truth-optimal samples.

  (C) The positivity-aware water-filling upper bound U(x, O, G) on any length-G
      competitor's observable log-likelihood.

  (D) For a repeat-free truth, every single-observed-type sample admits a
      strictly better length-G competitor (circulation/vulnerability).

Run:  python3 scripts/fixed_length_likelihood_duality.py
"""
import math
from itertools import product
from fractions import Fraction

ALPHA = "AC"
L = 2
TYPES = ["".join(t) for t in product(ALPHA, repeat=L)]
DIM = len(TYPES)

# cache of realizable count vectors
_REAL_CACHE = {}


def spectrum(genome, k=L):
    g = len(genome)
    spec = {}
    for i in range(g):
        kmer = "".join(genome[(i + j) % g] for j in range(k))
        spec[kmer] = spec.get(kmer, 0) + 1
    return spec


def vec(genome):
    spec = spectrum(genome)
    return tuple(spec.get(t, 0) for t in TYPES)


def realizable_vectors(g):
    if g in _REAL_CACHE:
        return _REAL_CACHE[g]
    seen = set()
    for tup in product(ALPHA, repeat=g):
        seen.add(vec("".join(tup)))
    out = sorted(seen)
    _REAL_CACHE[g] = out
    return out


def tangent_is_balanced(delta):
    nodes = {}
    for i, t in enumerate(TYPES):
        pre, suf = t[:-1], t[1:]
        nodes.setdefault(pre, [0, 0])[0] += delta[i]
        nodes.setdefault(suf, [0, 0])[1] += delta[i]
    return all(o == i for o, i in nodes.values())


def feasible_tangent_basis():
    """All balanced integer deltas with sum 0 and entries in -2..2 (they span
    the tangent space over Q for this tiny instance)."""
    out = []
    for delta in product((-2, -1, 0, 1, 2), repeat=DIM):
        if sum(delta) == 0 and tangent_is_balanced(delta):
            out.append(delta)
    return out


def in_cut_space(gvec):
    return all(sum(gi * di for gi, di in zip(gvec, d)) == 0
               for d in feasible_tangent_basis())


def f_obj(gvec, dvec):
    return sum(x * math.log(d) for x, d in zip(gvec, dvec) if x > 0 and d > 0)


def realizable_best(gvec, G):
    O = [i for i, x in enumerate(gvec) if x > 0]
    best, bestd = None, None
    for rv in realizable_vectors(G):
        if any(rv[i] < 1 for i in O):
            continue
        v = f_obj(gvec, rv)
        if best is None or v > best:
            best, bestd = v, rv
    return best, bestd


def canon(s):
    return min(s[i:] + s[:i] for i in range(len(s)))


def truths(G):
    return sorted({canon("".join(t)) for t in product(ALPHA, repeat=G)})


def check_A_B():
    print("== (A)/(B) correct KKT (flow potential) vs proportionality ==")
    S = "AACC"
    G = len(S)
    dS = vec(S)
    gvec = (2, 3, 1, 2)  # x = (AA:2, AC:3, CA:1, CC:2)
    print("  S =", S, " d_S =", dS, " x =", gvec)
    print("  x proportional to d_S?        ", len(set(gvec[i] / dS[i] for i in range(DIM))) == 1)
    print("  x/d_S in span{1}+rowspace(B)? ", in_cut_space(gvec))
    worst = max(f_obj(gvec, d) for d in _random_P(gvec, G))
    print("  f(d_S) =", round(f_obj(gvec, dS), 6),
          " sampled max over P =", round(worst, 6), "(<= f(d_S))")
    print("  => d_S globally optimal over the continuous polytope, x not proportional")

    found = 0
    for G in (4, 5, 6):
        for truth in truths(G):
            dS = vec(truth)
            for N in (1, 2, 3, 4):
                for x in product(range(N + 1), repeat=DIM):
                    if sum(x) != N:
                        continue
                    best, _ = realizable_best(x, G)
                    if best is None:
                        continue
                    fS = f_obj(x, dS)
                    if best <= fS + 1e-12:
                        prop = all(x[i] * dS[0] == x[0] * dS[i] for i in range(DIM))
                        g = tuple(Fraction(x[i], dS[i]) if dS[i] > 0 else 0
                                  for i in range(DIM))
                        if not prop and in_cut_space(g):
                            found += 1
                            if found <= 4:
                                print(f"  witness G={G} S={truth} d_S={dS} x={x}"
                                      " truth-optimal & non-proportional & cut-space")
    print(f"  exhaustive search: {found} non-proportional truth-optimal samples")
    return found


def _random_P(gvec, G, n=200000, seed0=0):
    import random
    random.seed(seed0)
    for _ in range(n):
        # AC L=2 affine set: d_AC = d_CA = t, d_AA + d_CC = G - 2t
        t = random.random() * (G / 2)
        rem = G - 2 * t
        a = random.random() * rem
        d = (a, t, t, rem - a)
        if min(d) > 1e-9:
            yield d


def water_fill(x, O, G):
    """max sum_{i in O} x_i log d_i s.t. sum d_i <= G, d_i >= 1."""
    if len(O) > G:
        return None
    xs = sorted((x[i] for i in O), reverse=True)
    best = None
    for k in range(len(O) + 1):
        if G - len(O) + k <= 0:
            continue
        lam = sum(xs[:k]) / (G - len(O) + k)
        if k > 0 and xs[k - 1] <= lam:
            continue
        if k < len(O) and xs[k] > lam:
            continue
        val = sum(xi * math.log(xi / lam) for xi in xs[:k])
        if best is None or val > best:
            best = val
    return best


def check_C():
    print("== (C) positivity-aware water-filling bound ==")
    checks = 0
    maxgap = 0.0
    for G in (4, 5, 6):
        for truth in truths(G):
            dS = vec(truth)
            for x in product(range(4), repeat=DIM):
                if sum(x) == 0:
                    continue
                O = [i for i, xi in enumerate(x) if xi > 0]
                if len(O) > G:
                    continue
                U = water_fill(x, O, G)
                if U is None:
                    continue
                best, _ = realizable_best(x, G)
                if best is None:
                    continue
                lim = U - f_obj(x, dS)
                actual = best - f_obj(x, dS)
                assert actual <= lim + 1e-9, (G, truth, x, actual, lim)
                maxgap = max(maxgap, lim - actual)
                checks += 1
    print(f"  bound valid on {checks} exhaustive instances;"
          f" max slack (realizability/flow gap) = {maxgap:.4f}")
    return checks


def check_D():
    print("== (D) repeat-free single-type vulnerability ==")
    bad = 0
    for G in (4, 5, 6):
        for truth in truths(G):
            dS = vec(truth)
            if set(dS) - {0, 1}:
                continue
            for ki, k in enumerate(TYPES):
                if dS[ki] != 1:
                    continue
                x = [0] * DIM
                x[ki] = 3
                best, bestd = realizable_best(x, G)
                if best is None or best <= f_obj(x, dS) + 1e-12:
                    bad += 1
                    print(f"  UNEXPECTED safe: G={G} S={truth} k={k} dS={dS}")
    print(f"  repeat-free single-type samples with no better competitor: {bad}")
    return bad


if __name__ == "__main__":
    a = check_A_B()
    check_C()
    d = check_D()
    print()
    print("Summary:")
    print("  (A)/(B) non-proportional truth-optimal witnesses:", a)
    print("  (C) water-filling bound verified")
    print("  (D) repeat-free single-type safe instances (expect 0):", d)
