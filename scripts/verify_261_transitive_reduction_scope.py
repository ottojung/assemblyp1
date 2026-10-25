#!/usr/bin/env python3
"""Transitive-reduction scope cell (#261): reduction is NOT neutral here.

Same AAT/TAA (L=3, o_min=1) support as the likelihood-sensitivity cell
(docs/issue261-likelihood-sensitivity-20261025.md) and the disconnected-flow
cell (docs/issue261-disconnected-flow-cell-20261025.md).

Candidate class (F): integer edge-multiplicity flows, edge lower bound 0,
vertex throughput lower bound 1, zero signed-incidence balance, zero terminal
usage, multiplicities 0..2, on two graphs over the same 4 strands:
  COMPLETE: all 10 o_min=1 overlap edges (audited parent graph).
  REDUCED:  MB09-style transitive reduction keeping only maximal-overlap
            (L-1=2) edges: exactly 4 edges forming the cycle
            AAT->ATT->TTA->TAA->AAT. Each dropped overlap-1 edge is backed by
            a 2-step overlap->=1 path (e.g. AAT->TAA via AAT->ATT->TAA), so
            the reduction is genuine: 10 -> 4 edges.

Claim (exact arithmetic):
  complete census: 78 flow throughput images; shared N=4-box universe U of 16;
    fixed-N winner {(1,3)} K=81; exact-multinomial winners {(1,2),(2,4)}
    K=4/27 (disjoint -- likelihood sensitivity, as audited in the parent cell).
  reduced census: exactly 4 images {(1,3),(2,2),(3,1),(4,4)}; U_red = same 4;
    fixed-N winner {(1,3)} K=81; exact-multinomial winner {(1,3)} K=9/64.
  So under the transitive reduction the likelihood-sensitivity VANISHES: both
  likelihoods agree on {(1,3)}. Transitive reduction is therefore not a
  neutral preprocessing step for ML maximality on this cell -- it changes the
  exact-likelihood answer from {(1,2),(2,4)} to {(1,3)}.
  Truth (2,2) is admitted (feasible, spelled) under both graphs, maximal
  under neither objective on either graph (fixed-N: 64 < 81; exact complete:
  1/8 < 4/27; exact reduced: 1/8 < 9/64).

Exit 0 on PASS; embedded mutants (wrong reduced census, swapped-sample exact
claim) exit non-zero.
"""

from __future__ import annotations

from fractions import Fraction as F
from itertools import product

COMP = {0: 3, 3: 0, 1: 2, 2: 1}


def rc(w):
    return tuple(COMP[x] for x in reversed(w))


X = (1, 2)
N = 4


def Kfix(d):
    return (d[0] ** X[0] * d[1] ** X[1]
            * (N - d[0]) ** (sum(X) - X[0]) * (N - d[1]) ** (sum(X) - X[1]))


def Kex(d):
    T = sum(d)
    assert T > 0
    return F(d[0], T) ** X[0] * F(d[1], T) ** X[1]


def build():
    a, b = (0, 0, 3), (3, 0, 0)  # AAT, TAA
    assert rc(a) == (0, 3, 3) and rc(b) == (3, 3, 0)
    strands = list(dict.fromkeys((a, b, rc(a), rc(b))))
    assert len(strands) == 4 and all(rc(rc(w)) == w for w in strands)
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
    return verts, rep, edges


def throughput(f, v, edges, rep):
    return sum(f[i] for i, e in enumerate(edges) if rep[e[0]] == v)


def balance(f, v, edges, rep):
    return (sum(f[i] * e[3] for i, e in enumerate(edges) if rep[e[0]] == v)
            + sum(f[i] * e[4] for i, e in enumerate(edges) if rep[e[1]] == v))


def feasible(f, verts, edges, rep):
    return all(throughput(f, v, edges, rep) >= 1
               and balance(f, v, edges, rep) == 0 for v in verts)


def census(edges, verts, rep):
    imgs = set()
    for f in product(range(3), repeat=len(edges)):
        if feasible(f, verts, edges, rep):
            imgs.add(tuple(throughput(f, v, edges, rep) for v in verts))
    return imgs


def verify():
    verts, rep, edges = build()
    # T0: complete graph census reproduces the parent cell (78 images).
    imgs = census(edges, verts, rep)
    assert len(imgs) == 78, sorted(imgs)
    U = sorted(d for d in imgs if all(0 <= c <= N for c in d))
    assert len(U) == 16, U
    mf = max(Kfix(d) for d in U)
    assert sorted(d for d in U if Kfix(d) == mf) == [(1, 3)] and mf == 81, mf
    me = max(Kex(d) for d in U)
    assert (sorted(d for d in U if Kex(d) == me) == [(1, 2), (2, 4)]
            and me == F(4, 27)), (me, U)

    # T1: transitive reduction keeps exactly the 4 overlap-2 edges, and every
    # dropped overlap-1 edge has a 2-step overlap->=1 witness path.
    red = [e for e in edges if e[2] == 2]
    assert len(red) == 4, red
    E = {(e[0], e[1]) for e in edges}
    for e in edges:
        if e[2] < 2:
            x, y = e[0], e[1]
            wit = [z for (a2, b2) in E for z in [b2]
                   if a2 == x and (z, y) in E and z != x and z != y]
            assert wit, (x, y)

    # T2: reduced census is exactly 4 images; both likelihoods agree on (1,3).
    imgs_r = census(red, verts, rep)
    assert sorted(imgs_r) == [(1, 3), (2, 2), (3, 1), (4, 4)], sorted(imgs_r)
    U_r = sorted(d for d in imgs_r if all(0 <= c <= N for c in d))
    assert U_r == [(1, 3), (2, 2), (3, 1), (4, 4)], U_r
    mf_r = max(Kfix(d) for d in U_r)
    assert ([d for d in U_r if Kfix(d) == mf_r] == [(1, 3)]
            and mf_r == 81), mf_r
    me_r = max(Kex(d) for d in U_r)
    assert ([d for d in U_r if Kex(d) == me_r] == [(1, 3)]
            and me_r == F(9, 64)), (me_r, U_r)

    # T3: truth admitted under both graphs, maximal under neither complete
    # objective (fixed-N: 64 < 81; exact: (2,2) K=1/8 < 4/27), and under
    # neither reduced objective either (fixed-N: 64 < 81; exact: 1/8 < 9/64
    # since (1,3): (1/4)(3/4)^2 = 9/64 = 0.140625 > 0.125).
    assert (2, 2) in imgs and (2, 2) in imgs_r
    assert Kfix((2, 2)) == 64 < 81
    assert Kex((2, 2)) == F(1, 8) < me
    assert Kex((2, 2)) == F(1, 8) < me_r
    print("PASS: transitive-reduction scope cell; complete 78 imgs, "
          "reduced 4 imgs; sensitivity vanishes under reduction "
          "(exact {(1,2),(2,4)} -> {(1,3)}); truth (2,2) admitted throughout")


def mutant_wrong_census():
    verts, rep, edges = build()
    red = [e for e in edges if e[2] == 2]
    imgs_r = census(red, verts, rep)
    assert sorted(imgs_r) == [(1, 3), (2, 2), (3, 1)], sorted(imgs_r)


def mutant_swapped_sample():
    verts, rep, edges = build()
    imgs = census(edges, verts, rep)
    U = sorted(d for d in imgs if all(0 <= c <= N for c in d))

    def Kex_swap(d):
        T = sum(d)
        return F(d[0], T) ** X[1] * F(d[1], T) ** X[0]

    me = max(Kex_swap(d) for d in U)
    assert (sorted(d for d in U if Kex_swap(d) == me) == [(1, 2), (2, 4)]
            and me == F(4, 27)), (me, U)


if __name__ == "__main__":
    import sys

    if len(sys.argv) > 1 and sys.argv[1] == "mutant1":
        mutant_wrong_census()
    elif len(sys.argv) > 1 and sys.argv[1] == "mutant2":
        mutant_swapped_sample()
    else:
        verify()
