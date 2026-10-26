#!/usr/bin/env python3
"""Spelled-circuit vs non-spelling flow cell (#261): spelling is NOT neutral.

Reduced AAT/TAA graph (4 maximal-overlap L-1=2 edges) from the
transitive-reduction scope cell. Integer flows (mult 0..2, edge lower
bound 0, vertex throughput lower bound 1, zero signed-incidence balance,
zero terminal usage) under fixed-N (N=4, sample x=(1,2)) and
exact-multinomial scores.

Candidate classes (fixed reduced graph; class varied):
  (F) all integer feasible flows;
  (S) spelled-circuit flows: feasible flows whose edge multiset admits a
      closed trail using every unit exactly once (Eulerian circuit in the
      directed strand multigraph), i.e. flows that spell one circular
      genome. Eulerian circuit <=> balanced (indeg == outdeg at every
      strand node) + weakly connected over used edges.

Claim:
  (F) census: 4 images {(1,3),(2,2),(3,1),(4,4)}; fixed-N and exact
      winners both {(1,3)} (Kfix=81, Kex=9/64).
  (S) census: exactly {(2,2),(4,4)}; witnesses (1,1,1,1) and (2,2,2,2).
      The (F) winners (1,3)/(3,1) have unique witnesses (1,2,0,1) and
      (1,0,2,1), both Eulerian-unbalanced, hence non-spelling.
  (S) fixed-N winner {(2,2)} K=64 (truth!); exact winners {(2,2),(4,4)}
      tied at K=1/8. So truth (2,2) is maximal in (S) under fixed-N but
      only tied-maximal under exact; maximal in neither under (F).
  Hence restricting to spelled circuits changes the ML answer: the
  full-flow winner is not even admitted in (S). Criteria must declare
  flows vs spelled circuits vs circular genomes.

Exit 0 on PASS; embedded mutants exit non-zero. Usage:
  python3 scripts/verify_261_spelled_circuit_scope.py
  python3 scripts/verify_261_spelled_circuit_scope.py --mutant census|sample
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


def spells(f, edges):
    """Eulerian-circuit test on the directed strand multigraph."""
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


def check(mutant=""):
    verts, rep, red = build()
    feas = [f for f in product(range(3), repeat=len(red))
            if feasible(f, verts, red, rep)]
    assert len(feas) == 4, feas
    imgs = {}
    for f in feas:
        imgs.setdefault(
            tuple(throughput(f, v, red, rep) for v in verts), []).append(f)
    assert sorted(imgs) == [(1, 3), (2, 2), (3, 1), (4, 4)], sorted(imgs)
    U = sorted(imgs)
    assert sorted(d for d in U if Kfix(d) == max(Kfix(d) for d in U)) == [(1, 3)]
    assert max(Kfix(d) for d in U) == 81
    assert sorted(d for d in U if Kex(d) == max(Kex(d) for d in U)) == [(1, 3)]
    assert max(Kex(d) for d in U) == F(9, 64)

    # spelling classification: each image has a unique witness here
    assert all(len(v) == 1 for v in imgs.values()), imgs
    wit = {d: v[0] for d, v in imgs.items()}
    assert wit[(2, 2)] == (1, 1, 1, 1), wit
    assert wit[(4, 4)] == (2, 2, 2, 2), wit
    assert wit[(1, 3)] == (1, 2, 0, 1), wit
    assert wit[(3, 1)] == (1, 0, 2, 1), wit
    spelled = sorted(d for d, f in wit.items() if spells(f, red))
    expect = [(2, 2), (4, 4)] if mutant != "census" else [(2, 2)]
    assert spelled == expect, (spelled, {d: wit[d] for d in wit})
    nonsp = sorted(set(wit) - set(spelled))
    assert nonsp == [(1, 3), (3, 1)], nonsp
    # Eulerian-balance detail: the non-spelling witnesses are unbalanced
    # (indeg != outdeg somewhere), not merely disconnected
    assert not spells((1, 2, 0, 1), red)
    assert not spells((1, 0, 2, 1), red)
    assert spells((1, 1, 1, 1), red) and spells((2, 2, 2, 2), red)

    samp = (2, 1) if mutant == "sample" else X
    kf = lambda d: Kfix(d, samp)  # noqa: E731
    ke = lambda d: Kex(d, samp)  # noqa: E731
    S = [d for d in spelled]
    mf = max(kf(d) for d in S)
    wf = sorted(d for d in S if kf(d) == mf)
    assert wf == [(2, 2)] and mf == 64, (wf, mf)
    me = max(ke(d) for d in S)
    we = sorted(d for d in S if ke(d) == me)
    if mutant == "sample":
        we = [(2, 2)]  # wrong: drops the (4,4) exact tie
    assert we == [(2, 2), (4, 4)] and me == F(1, 8), (we, me)
    # truth (2,2): spelled, fixed-N-maximal in (S), tied in exact, beaten in (F)
    assert (2, 2) in spelled
    assert Kfix((2, 2)) == 64 < 81  # beaten in (F) by non-spelling (1,3)
    assert Kex((2, 2)) == F(1, 8) < F(9, 64)  # beaten in (F) likewise
    print("PASS: spelled-circuit scope cell; (F) winners {(1,3)} "
          "non-spelling; (S)={(2,2),(4,4)} fixed-N winner (2,2) K=64, "
          "exact tie (2,2)~(4,4) K=1/8; truth maximal in (S)/fixed-N only")


if __name__ == "__main__":
    mut = ""
    if len(sys.argv) > 1 and sys.argv[1] == "--mutant":
        mut = sys.argv[2] if len(sys.argv) > 2 else "census"
    try:
        check(mut)
    except AssertionError as e:
        print(f"FAIL: {e}")
        sys.exit(1)
