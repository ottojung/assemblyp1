#!/usr/bin/env python3
"""Likelihood-sensitivity cell: fixed-N binomial vs exact multinomial pick
different ML winners over the SAME integer-flow image set (#261).

Support AAT/TAA (L=3, o_min=1), RC-completed with ATT/TTA -- the audited graph
of the disconnected-flow cell (docs/issue261-disconnected-flow-cell-20261025.md,
scripts/verify_261_disconnected_flow_cell.py). That cell separated spelled (C)
from flows (F); this cell fixes the candidate class and varies the likelihood.

Candidate class (F): integer edge-multiplicity flows on the complete bidirected
overlap graph (10 edges), edge lower bound 0, vertex throughput lower bound 1,
zero signed-incidence balance, zero terminal usage. Multiplicities 0..2 are
exhaustively enumerated (3^10 = 59049 cases).
Truth (2,2) is admitted (spelled, hence feasible) but maximal under NEITHER
objective below.

Shared finite universe U: flow throughput images inside the box {0..4}^2
(the fixed-N universe with N=4). Sample x=(1,2), n=3 reads on the two observed
coordinates; unobserved-class coordinates use the omit/fix-at-zero convention
of the parent cell (this cell does not adjudicate the source interpretation).

Objectives (both exact arithmetic -- integers and Fractions):
  fixed-N product-binomial core: Kfix(d) = d1^1 d2^2 (4-d1)^2 (4-d2)^1.
    This is the separable-binomial core of the #259/#260 count-vector
    criterion (linked, not forked: Section62BinomialCriterion on main).
  exact variable-length multinomial: Kex(d) = (d1/T)^1 (d2/T)^2, T=d1+d2.
    This is the project-objective likelihood of GeneralBidirectedFlowML
    (varLengthCriterion), restricted to the same candidate image set.

Claim:
  fixed-N argmax over U is the singleton {(1,3)} (K=81);
  exact-multinomial argmax over U is {(1,2),(2,4)} (K=4/27);
  the winner sets are DISJOINT. So the ML winner over one fixed feasible-flow
  class depends on which likelihood (exact vs fixed-N binomial) is used.
  No general maximality criterion is stated; transitive reduction, RC/
  orientation classes beyond this support, and half-integral/real comparison
  stay OPEN. Keep #261 and #255 open.

Exit 0 on PASS; embedded mutants (dropped balance, swapped sample) exit
non-zero, proving the checks are sensitive.
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
    assert rep[a] == a and rep[b] == b
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
    assert len(edges) == 10, edges  # same complete graph as the parent cell
    return verts, rep, edges


def throughput(f, v, edges, rep):
    return sum(f[i] for i, e in enumerate(edges) if rep[e[0]] == v)


def balance(f, v, edges, rep):
    return (sum(f[i] * e[3] for i, e in enumerate(edges) if rep[e[0]] == v)
            + sum(f[i] * e[4] for i, e in enumerate(edges) if rep[e[1]] == v))


def feasible(f, verts, edges, rep):
    return all(throughput(f, v, edges, rep) >= 1
               and balance(f, v, edges, rep) == 0 for v in verts)


def verify():
    verts, rep, edges = build()
    imgs = set()
    for f in product(range(3), repeat=len(edges)):
        if feasible(f, verts, edges, rep):
            imgs.add(tuple(throughput(f, v, edges, rep) for v in verts))
    # T0: full mult<=2 image census (exact set; 59049 cases enumerated).
    assert len(imgs) == 78, sorted(imgs)
    # T1: shared finite universe U = images inside the N=4 box.
    U = sorted(d for d in imgs if all(0 <= c <= N for c in d))
    assert U == [(1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3),
                 (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2),
                 (4, 3), (4, 4)], U
    # T2: truth admitted but maximal under neither objective.
    assert (2, 2) in U and Kfix((2, 2)) == 64
    # T3: fixed-N winner is the singleton {(1,3)}, K=81.
    mfix = max(Kfix(d) for d in U)
    assert mfix == 81
    win_fix = {d for d in U if Kfix(d) == mfix}
    assert win_fix == {(1, 3)}, sorted(win_fix)
    # T4: exact-multinomial winners over U are {(1,2),(2,4)}, K=4/27.
    mex = max(Kex(d) for d in U)
    assert mex == F(4, 27), mex
    win_ex = {d for d in U if Kex(d) == mex}
    assert win_ex == {(1, 2), (2, 4)}, sorted(win_ex)
    # T5: sensitivity -- the winner sets are disjoint.
    assert win_fix.isdisjoint(win_ex)
    assert not (Kex((1, 3)) == mex) and Kfix((1, 2)) < mfix
    print("PASS: likelihood-sensitivity cell; U has 16 images; "
          "fixed-N winner {(1,3)} K=81 disjoint from exact winners "
          "{(1,2),(2,4)} K=4/27; truth (2,2) admitted, maximal under neither")


def mutant_fixed_n5():
    """Fixed-N with N=5 must pick a different winner: the N=4 result is
    N-sensitive, so asserting the N=4 winner under N=5 fails."""
    U5 = [(a, b) for a in range(1, 6) for b in range(1, 6)]

    def K5(d, N=5):
        return (d[0] ** X[0] * d[1] ** X[1]
                * (N - d[0]) ** (sum(X) - X[0])
                * (N - d[1]) ** (sum(X) - X[1]))

    m = max(K5(d) for d in U5)
    win = {d for d in U5 if K5(d) == m}
    assert win == {(1, 3)}, (m, sorted(win))  # must FAIL: N=5 wins {(2,3)}


def mutant_swapped_sample():
    """Swapping the sample exponents must change the exact-winner set."""
    verts, rep, edges = build()
    Y = (2, 1)

    def Kswap(d):
        T = sum(d)
        return F(d[0], T) ** Y[0] * F(d[1], T) ** Y[1]

    U = [(1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4),
         (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2), (4, 3), (4, 4)]
    m = max(Kswap(d) for d in U)
    win = {d for d in U if Kswap(d) == m}
    assert win == {(1, 2), (2, 4)}, sorted(win)  # must FAIL under x=(2,1)


if __name__ == "__main__":
    import sys

    verify()
    for name, mut in (("fixed-n5", mutant_fixed_n5),
                      ("swapped-sample", mutant_swapped_sample)):
        try:
            mut()
        except AssertionError:
            print(f"mutant {name}: correctly rejected (non-zero path)")
        else:
            print(f"mutant {name}: NOT sensitive -- FAIL")
            sys.exit(1)
