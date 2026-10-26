#!/usr/bin/env python3
"""Half-integral relaxation cell (#261): relaxation is NOT neutral here.

Reduced AAT/TAA graph (4 maximal-overlap L-1=2 edges) from the
transitive-reduction scope cell. Compares integer flows (mult 0..2) against
the half-integral relaxation (mult in {0,1/2,1,3/2,2}) under fixed-N (N=4,
sample x=(1,2)) and exact-multinomial scores.

Claim:
  integer census: 4 images {(1,3),(2,2),(3,1),(4,4)};
    fixed-N winner {(1,3)} K=81; exact winner {(1,3)} K=9/64.
  half-integral census: exactly 10 images (strict superset, incl. (1,1),
    (3/2,5/2), (3,3), ...); fixed-N and exact winners both {(3/2,5/2)}
    with Kfix=5625/64 > 81, Kex=75/512 > 9/64. Witness flow (1,3/2,1/2,1).
  Truth (2,2) admitted throughout, maximal under neither in either class.

Exit 0 on PASS; embedded mutants exit non-zero. Usage:
  python3 scripts/verify_261_halfintegral_scope.py
  python3 scripts/verify_261_halfintegral_scope.py --mutant census|sample
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


def census(edges, verts, rep, vals):
    imgs = {}
    for f in product(vals, repeat=len(edges)):
        if feasible(f, verts, edges, rep):
            imgs.setdefault(
                tuple(throughput(f, v, edges, rep) for v in verts), f)
    return imgs


def check(mutant=""):
    verts, rep, red = build()
    int_imgs = census(red, verts, rep, list(range(3)))
    assert sorted(int_imgs) == [(1, 3), (2, 2), (3, 1), (4, 4)], sorted(int_imgs)
    U = sorted(int_imgs)
    assert sorted(d for d in U if Kfix(d) == max(Kfix(d) for d in U)) == [(1, 3)]
    assert max(Kfix(d) for d in U) == 81
    assert sorted(d for d in U if Kex(d) == max(Kex(d) for d in U)) == [(1, 3)]
    assert max(Kex(d) for d in U) == F(9, 64)

    half_vals = [F(i, 2) for i in range(5)]
    himgs = census(red, verts, rep, half_vals)
    expect = sorted([(F(1), F(1)), (F(1), F(3)), (F(3, 2), F(5, 2)),
                     (F(2), F(2)), (F(5, 2), F(3, 2)), (F(5, 2), F(7, 2)),
                     (F(3), F(1)), (F(3), F(3)), (F(7, 2), F(5, 2)),
                     (F(4), F(4))])
    got = sorted(himgs)
    if mutant == "census":
        expect = expect[:-1]  # wrong: drop (4,4)
    assert got == expect, got
    assert set(int_imgs) < set(himgs)  # strict expansion

    # witness flow for the defeater
    w = (F(1), F(3, 2), F(1, 2), F(1))
    assert feasible(w, verts, red, rep)
    assert tuple(throughput(w, v, red, rep) for v in verts) == (F(3, 2), F(5, 2))

    samp = (2, 1) if mutant == "sample" else X
    kf = lambda d: Kfix(d, samp)  # noqa: E731
    ke = lambda d: Kex(d, samp)  # noqa: E731
    mf = max(kf(d) for d in got)
    wf = sorted(d for d in got if kf(d) == mf)
    assert wf == [(F(3, 2), F(5, 2))] and mf == F(5625, 64), (wf, mf)
    me = max(ke(d) for d in got)
    we = sorted(d for d in got if ke(d) == me)
    assert we == [(F(3, 2), F(5, 2))] and me == F(75, 512), (we, me)
    # truth admitted, maximal under neither
    assert (F(2), F(2)) in himgs
    assert kf((F(2), F(2))) == 64 < mf
    assert ke((F(2), F(2))) == F(1, 8) < me
    # integer winner defeated in the relaxed class
    assert kf((F(1), F(3))) == 81 < mf
    assert ke((F(1), F(3))) == F(9, 64) < me
    # genuinely fractional image: (1,1) has no integer witness
    assert himgs[(F(1), F(1))] is not None
    assert all(v.denominator == 2 for v in himgs[(F(1), F(1))])
    print("PASS: half-integral scope cell; integer 4 imgs winner (1,3); "
          "half 10 imgs, winner (3/2,5/2) defeats integer winner under both "
          "likelihoods (5625/64>81, 75/512>9/64); truth (2,2) admitted, "
          "maximal under neither")


if __name__ == "__main__":
    mut = ""
    if len(sys.argv) > 1 and sys.argv[1] == "--mutant":
        mut = sys.argv[2] if len(sys.argv) > 2 else "census"
    try:
        check(mut)
    except AssertionError as e:
        print(f"FAIL: {e}")
        sys.exit(1)
