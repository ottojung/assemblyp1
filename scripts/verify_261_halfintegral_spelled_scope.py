#!/usr/bin/env python3
"""Half-integral x spelled-circuit interaction cell (#261).

Reduced AAT/TAA graph (4 maximal-overlap L-1=2 edges), same conventions as
the half-integral scope cell and the spelled-circuit scope cell:
integer flows mult 0..2, half-integral mult in {0,1/2,1,3/2,2}, edge lower
bound 0, vertex throughput lower bound 1, zero signed-incidence balance.
Fixed-N (N=4, sample x=(1,2)) product-binomial core and exact-multinomial
scores (formal fractional-mass extension for H), same box universe.

Spelling rule: a flow spells one circular genome only if every unit is an
integral edge traversal admitting a closed trail using every unit exactly
once (Eulerian circuit in the directed strand multigraph: balanced
indeg==outdeg at every strand node plus weak connectivity over used edges).
A flow with any strictly fractional multiplicity has no such certificate,
hence is non-spelling by definition.

Claim:
  (H) census: exactly the 10 parent images; winner {(3/2,5/2)} under both
      likelihoods (Kfix=5625/64, Kex=75/512), witness (1,3/2,1/2,1).
  (H-spelled) census: exactly {(2,2),(4,4)}, witnessed by (1,1,1,1) and
      (2,2,2,2) -- identical to the integer spelled class (S). No
      fractional flow is spelled.
  The (H) winner is fractional, hence non-spelling; the spelled-class ML
  answer is unchanged: fixed-N winner {(2,2)} K=64 (truth), exact tie
      {(2,2),(4,4)} K=1/8.
  So the half-integral relaxation adds no new spelled candidates on this
  cell, while changing the unrestricted-flow answer: spelling and
  relaxation do not commute here.

Exit 0 on PASS; embedded mutants exit non-zero. Usage:
  python3 scripts/verify_261_halfintegral_spelled_scope.py
  python3 scripts/verify_261_halfintegral_spelled_scope.py --mutant census|sample
"""

from __future__ import annotations

import sys
from fractions import Fraction as F
from itertools import product

X = (1, 2)
N = 4


def Kfix(d, samp=X):
    return (d[0] ** samp[0] * d[1] ** samp[1]
            * (N - d[0]) ** (sum(samp) - samp[0])
            * (N - d[1]) ** (sum(samp) - samp[1]))


def Kex(d, samp=X):
    T = sum(d)
    assert T > 0
    return F(d[0], T) ** samp[0] * F(d[1], T) ** samp[1]


def build():
    COMP = {0: 3, 3: 0, 1: 2, 2: 1}

    def rc(w):
        return tuple(COMP[x] for x in reversed(w))

    a, b = (0, 0, 3), (3, 0, 0)
    strands = list(dict.fromkeys((a, b, rc(a), rc(b))))
    rep = {s: min(s, rc(s)) for s in strands}
    verts = (a, b)
    L, omin = 3, 1

    def overlap_len(x, y):
        for n in range(L - 1, omin - 1, -1):
            if x[L - n:] == y[:n]:
                return n
        return 0

    edges = [(x, y, overlap_len(x, y), 1 if x == rep[x] else -1,
              -1 if y == rep[y] else 1)
             for x in strands for y in strands if overlap_len(x, y) >= omin]
    assert len(edges) == 10, edges
    red = [e for e in edges if e[2] == 2]
    assert len(red) == 4, red
    return verts, rep, red


def throughput(f, v, edges, rep):
    return sum(f[i] for i, e in enumerate(edges) if rep[e[0]] == v)


def balance(f, v, edges, rep):
    return (sum(f[i] * e[3] for i, e in enumerate(edges) if rep[e[0]] == v)
            + sum(f[i] * e[4] for i, e in enumerate(edges) if rep[e[1]] == v))


def feasible(f, verts, edges, rep):
    return all(throughput(f, v, edges, rep) >= 1
               and balance(f, v, edges, rep) == 0 for v in verts)


def is_integral(f):
    return all(v.denominator == 1 for v in f)


def spells_int(f, edges):
    """Eulerian-circuit test; caller must ensure f is integral."""
    nodes = sorted(set([e[0] for e in edges] + [e[1] for e in edges]))
    indegr = {s: 0 for s in nodes}
    outdegr = {s: 0 for s in nodes}
    for i, e in enumerate(edges):
        outdegr[e[0]] += f[i]
        indegr[e[1]] += f[i]
    if any(indegr[s] != outdegr[s] for s in nodes):
        return False
    used = [s for s in nodes if indegr[s] + outdegr[s] > 0]
    if not used:
        return False
    adj = {s: set() for s in used}
    for i, e in enumerate(edges):
        if f[i] > 0:
            adj[e[0]].add(e[1])
            adj[e[1]].add(e[0])
    stack, seen = [used[0]], {used[0]}
    while stack:
        s = stack.pop()
        for t in adj[s]:
            if t not in seen:
                seen.add(t)
                stack.append(t)
    return seen == set(used)


def spells(f, edges):
    # Fractional multiplicities admit no unit-trail certificate.
    if not is_integral(f):
        return False
    return spells_int(tuple(int(v) for v in f), edges)


def check(mutant=""):
    verts, rep, red = build()
    half_vals = [F(i, 2) for i in range(5)]
    hfeas = [f for f in product(half_vals, repeat=len(red))
             if feasible(f, verts, red, rep)]
    himgs = {}
    for f in hfeas:
        himgs.setdefault(
            tuple(throughput(f, v, red, rep) for v in verts), []).append(f)
    expect = sorted([(F(1), F(1)), (F(1), F(3)), (F(3, 2), F(5, 2)),
                     (F(2), F(2)), (F(5, 2), F(3, 2)), (F(5, 2), F(7, 2)),
                     (F(3), F(1)), (F(3), F(3)), (F(7, 2), F(5, 2)),
                     (F(4), F(4))])
    got = sorted(himgs)
    if mutant == "census":
        expect = expect[:-1]  # wrong: drop (4,4)
    assert got == expect, got

    # H winners under both likelihoods (parent result, reproduced)
    samp = (2, 1) if mutant == "sample" else X
    kf = lambda d: Kfix(d, samp)  # noqa: E731
    ke = lambda d: Kex(d, samp)  # noqa: E731
    mf = max(kf(d) for d in got)
    wf = sorted(d for d in got if kf(d) == mf)
    assert wf == [(F(3, 2), F(5, 2))] and mf == F(5625, 64), (wf, mf)
    me = max(ke(d) for d in got)
    we = sorted(d for d in got if ke(d) == me)
    assert we == [(F(3, 2), F(5, 2))] and me == F(75, 512), (we, me)

    # The H winner witness is fractional, hence non-spelling by definition.
    w = (F(1), F(3, 2), F(1, 2), F(1))
    assert feasible(w, verts, red, rep)
    assert tuple(throughput(w, v, red, rep) for v in verts) == (F(3, 2), F(5, 2))
    assert not is_integral(w)
    assert not spells(w, red)

    # No fractional feasible flow is spelled: spelled (H) == spelled (S).
    hspelled = sorted({d for d, fs in himgs.items()
                       if any(spells(f, red) for f in fs)})
    assert hspelled == [(F(2), F(2)), (F(4), F(4))], hspelled
    for d, fs in himgs.items():
        for f in fs:
            if not is_integral(f):
                assert not spells(f, red), (d, f)
    # Integer spelled witnesses are exactly the parent (S) witnesses.
    int_sp = {d: fs for d, fs in himgs.items()
              if any(is_integral(f) and spells(f, red) for f in fs)}
    assert sorted(int_sp) == [(F(2), F(2)), (F(4), F(4))], sorted(int_sp)
    assert (1, 1, 1, 1) in [tuple(int(v) for v in f) for f in int_sp[(F(2), F(2))]]
    assert (2, 2, 2, 2) in [tuple(int(v) for v in f) for f in int_sp[(F(4), F(4))]]

    # Spelled-class ML answer unchanged: fixed-N truth, exact tie.
    S = hspelled
    msf = max(Kfix(d) for d in S)
    wsf = sorted(d for d in S if Kfix(d) == msf)
    assert wsf == [(F(2), F(2))] and msf == 64, (wsf, msf)
    mse = max(Kex(d) for d in S)
    wse = sorted(d for d in S if Kex(d) == mse)
    assert wse == [(F(2), F(2)), (F(4), F(4))] and mse == F(1, 8), (wse, mse)
    print("PASS: half-integral x spelled cell; (H) 10 imgs winner (3/2,5/2) "
          "fractional hence non-spelling; (H-spelled)={(2,2),(4,4)} "
          "fixed-N winner (2,2) K=64, exact tie K=1/8; relaxation adds no "
          "spelled candidates")


if __name__ == "__main__":
    mut = ""
    if len(sys.argv) > 1 and sys.argv[1] == "--mutant":
        mut = sys.argv[2] if len(sys.argv) > 2 else "census"
    try:
        check(mut)
    except AssertionError as e:
        print(f"FAIL: {e}")
        sys.exit(1)
