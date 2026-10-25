#!/usr/bin/env python3
"""Real-relaxation no-gap cell (#261): clearing denominators preserves exact likelihood.

Closes the explicitly OPEN "real (non-half-integral) LP relaxation" subclaim of
docs/issue261-half-integral-source-ml.md -- but ONLY for the exact
variable-length multinomial likelihood (candidate's own N = sum d).

Candidate class (F): rational/real edge-multiplicity flows on the 4-edge
MB09-style overlap-2 cycle AAT->ATT->TTA->TAA->AAT (the transitively reduced
graph of docs/issue261-transitive-reduction-scope-20261025.md), edge lower
bound 0, vertex throughput lower bound 1, zero signed-incidence balance, zero
terminal usage. Flows, not spelled circuits, not circular genomes.
Truth admitted. Likelihood: exact multinomial Kex(d) = prod_v (d_v/T)^x_v with
T = sum d, sample x = (1,2). Length universe: variable (own N).

Claim (exact arithmetic over Fractions):
  T1: f = (2/3,2/3,2/3,2/3) is feasible (throughputs (4/3,4/3) >= 1, zero
      balance) and is NOT half-integral (2*(2/3) = 4/3 not an integer), so the
      real relaxation strictly enlarges the half-integral set at this point.
  T2: clearing denominators (D=3) gives the integer flow g = (2,2,2,2) with
      throughput (4,4), feasible, and Kex identical: Kex(4/3,4/3) = Kex(4,4)
      = Kex(1,1) = 1/8. In general Kex is scale-invariant, so EVERY real
      feasible flow with rational values shares its exact likelihood with an
      integer feasible flow; the real relaxation cannot change the exact-ML
      optimum or the truth's maximality status.
  T3: no claim about the fixed-external-N binomial (which DOES have a
      half-integral gap per docs/issue261-general-bidirected-flow-ml.md
      Class 3): different objective, different length universe.

Exit 0 on PASS; embedded mutants (wrong throughput, denied scale invariance)
exit non-zero.
"""

from __future__ import annotations

from fractions import Fraction as F

COMP = {0: 3, 3: 0, 1: 2, 2: 1}


def rc(w):
    return tuple(COMP[x] for x in reversed(w))


X = (1, 2)


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
    red = [e for e in edges if e[2] == 2]
    assert len(red) == 4, red
    return verts, rep, red


def throughput(f, verts, edges, rep):
    return tuple(sum(f[i] for i, e in enumerate(edges) if rep[e[0]] == v)
                 for v in verts)


def balance(f, v, edges, rep):
    return (sum(f[i] * e[3] for i, e in enumerate(edges) if rep[e[0]] == v)
            + sum(f[i] * e[4] for i, e in enumerate(edges) if rep[e[1]] == v))


def feasible(f, verts, edges, rep):
    return all(throughput(f, verts, edges, rep)[j] >= 1 for j in range(2)) \
        and all(balance(f, v, edges, rep) == 0 for v in verts)


def is_half_integral(f):
    return all((2 * v).denominator == 1 for v in f)


def verify():
    verts, rep, red = build()
    # T1: real witness feasible, strictly beyond half-integral.
    f = (F(2, 3), F(2, 3), F(2, 3), F(2, 3))
    d = throughput(f, verts, red, rep)
    assert d == (F(4, 3), F(4, 3)), d
    assert feasible(f, verts, red, rep), (d, [balance(f, v, red, rep) for v in verts])
    assert not is_half_integral(f), f  # 2*(2/3) = 4/3 not integral
    assert (2 * f[0]).denominator != 1

    # T2: denominator clearing preserves feasibility and exact likelihood.
    D = 3
    g = tuple(int(v * D) for v in f)
    assert g == (2, 2, 2, 2), g
    dg = throughput(g, verts, red, rep)
    assert dg == (4, 4), dg
    assert feasible(g, verts, red, rep)
    assert Kex(d) == Kex(dg) == Kex((1, 1)) == F(1, 8), (Kex(d), Kex(dg))
    # General scale invariance on this cell's witnesses.
    assert Kex((F(4, 3), F(4, 3))) == Kex((4, 4)) == Kex((2, 2))

    # T3 (scope guard): the half-integral circulation (1/2 x4, throughput
    # (1,1)) is still feasible here, so the chain integer < half-integral <
    # real of feasible sets is strict at both steps on this graph.
    h = (F(1, 2),) * 4
    assert feasible(h, verts, red, rep)
    assert throughput(h, verts, red, rep) == (1, 1)
    assert is_half_integral(h) and not all(float(v).is_integer() for v in h)
    print("PASS: real-relaxation no-gap cell; (2/3 x4) feasible non-half-"
          "integral, clears to (2 x4); Kex = 1/8 throughout; integer < "
          "half-integral < real strict, optimum unchanged")


def mutant_wrong_throughput():
    verts, rep, red = build()
    f = (F(2, 3), F(2, 3), F(2, 3), F(2, 3))
    assert throughput(f, verts, red, rep) == (1, 1)


def mutant_denied_invariance():
    assert Kex((F(4, 3), F(4, 3))) != Kex((4, 4))


if __name__ == "__main__":
    import sys

    if len(sys.argv) > 1 and sys.argv[1] == "mutant1":
        mutant_wrong_throughput()
    elif len(sys.argv) > 1 and sys.argv[1] == "mutant2":
        mutant_denied_invariance()
    else:
        verify()
