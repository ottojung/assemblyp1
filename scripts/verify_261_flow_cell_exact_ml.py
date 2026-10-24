#!/usr/bin/env python3
"""Issue #261 bounded flow cell, exact-likelihood axis: spelled-maximal truth
with a strict flow defeater under the EXACT multinomial core.

Same source-faithful MB09 Sec.6.2 instance as
`scripts/verify_261_flow_cell_acac.py` (L=3, o_min=1, observed RC support
verts={ACA,CAC}, genuine DNA RC, vacuous literal reduction, zero-terminal
`Feasible62`), but scored with the exact iid multinomial core instead of the
fixed-external-N product-binomial surrogate:

    E(d;x) = prod_i (d_i / T)^{x_i},   T = sum_i d_i  (total throughput mass)

computed in exact rational arithmetic (`Fraction`; no floating point, no trust
in Lean output).  The multinomial coefficient n!/(prod x_i!) is constant across
candidates for fixed sample x and hence omitted (ranking-valid).

Candidate class: integer zero-terminal feasible flows (edgeLB 0, vertexLB 1,
signed-incidence balance 0), length universe = ALL feasible flows (unbounded
total mass; no external-N probability-domain exclusion -- every throughput
with T>0 is comparable).  Truth admitted as the spelled 2-circuit walk flow.
Unobserved molecule coordinates fixed at 0 for all candidates (common factor).

Result: truth d*=(1,1) scores E=1/8, spelled rival (2,2) scores E=1/8 (tie, so
truth is spelled-maximal over {(1,1),(2,2)} at n<=4), while the feasible
(non-spelled) flow throughput (2,1) scores E=4/27 > 1/8 (32/216 > 27/216): a
strict flow defeater.  So spelled-maximal does NOT imply flow-maximal under the
exact likelihood either.  Both spelled visit vectors are realized by explicit
feasible flows (inclusion premise, finite check).
"""
import itertools
from collections import Counter
from fractions import Fraction
from math import prod

COMP = {0: 3, 3: 0, 1: 2, 2: 1}
NAMES = {(0, 1, 0): "ACA", (1, 0, 1): "CAC", (3, 2, 3): "TGT", (2, 3, 2): "GTG"}

def rcw(w):
    return tuple(COMP[c] for c in reversed(w))

def canon(w):
    return min(w, rcw(w))

V0, V1 = (0, 1, 0), (1, 0, 1)  # ACA, CAC
STRANDS = list(dict.fromkeys([V0, V1, rcw(V0), rcw(V1)]))
IDX = {s: i for i, s in enumerate(STRANDS)}
REP = {IDX[s]: IDX[canon(s)] for s in STRANDS}
TOLIST = {IDX[s]: list(s) for s in STRANDS}
RC = {IDX[s]: IDX[rcw(s)] for s in STRANDS}
VERTS = [IDX[V0], IDX[V1]]
S = list(IDX.values())
READLEN, OMIN = 3, 1

def suf(a, l):
    return a[len(a) - l:] if l else []

def pre(a, l):
    return a[:l]

def sgnRep(s, mx):
    return 1 if s == mx else -1

def sgnTgt(s, my):
    return -1 if s == my else 1

EDGES = [(sx, sy, ln, sgnRep(sx, REP[sx]), sgnTgt(sy, REP[sy]))
         for ln in range(READLEN) if ln >= OMIN
         for sx in S for sy in S
         if suf(TOLIST[sx], ln) == pre(TOLIST[sy], ln)]

def throughput(f, v):
    return sum(f[i] for i, e in enumerate(EDGES) if REP[e[0]] == v)

def balance(f, v):
    return (sum(f[i] * e[3] for i, e in enumerate(EDGES) if REP[e[0]] == v)
            + sum(f[i] * e[4] for i, e in enumerate(EDGES) if REP[e[1]] == v))

def feasible(f):
    return (all(throughput(f, v) >= 1 for v in VERTS)
            and all(balance(f, v) == 0 for v in VERTS))

def maxOverlap(a, b):
    best = 0
    for l in range(READLEN):
        if suf(TOLIST[a], l) == pre(TOLIST[b], l):
            best = l
    return best

def isReducible(e):
    sx, sy, ln = e[0], e[1], e[2]
    for m in S:
        for l1 in range(READLEN):
            for l2 in range(READLEN):
                if (maxOverlap(sx, m) == l1 and maxOverlap(m, sy) == l2
                        and 0 < l1 < ln and 0 < l2 < ln
                        and l1 + l2 - READLEN == ln):
                    return True
    return False

def E_exact(d, x):
    """Exact multinomial core prod (d_i/T)^{x_i} as an exact Fraction."""
    T = sum(d)
    assert T > 0 and all(c >= 0 for c in d)
    return prod((Fraction(c, T) ** xi for c, xi in zip(d, x)), start=Fraction(1))

def spelled_visits(n):
    out = set()
    for seq in itertools.product(S, repeat=n):
        if set(REP[s] for s in seq) != set(REP[v] for v in VERTS):
            continue
        steps = [(seq[i], seq[(i + 1) % n], READLEN - 1,
                  sgnRep(seq[i], REP[seq[i]]),
                  sgnTgt(seq[(i + 1) % n], REP[seq[(i + 1) % n]])) for i in range(n)]
        if (all(s in EDGES for s in steps)
                and all(steps[i][3] == -steps[(i - 1) % n][4] for i in range(n))):
            c = Counter(REP[s] for s in seq)
            out.add((c[REP[VERTS[0]]], c[REP[VERTS[1]]]))
    return out

def main():
    # genuine DNA RC check
    for s in STRANDS:
        assert list(rcw(s)) == [COMP[c] for c in reversed(list(s))]
    # reduction vacuous on this instance (literal predicate)
    assert not any(isReducible(e) for e in EDGES), "reduction must be vacuous here"
    assert len(EDGES) == 8 and sum(1 for e in EDGES if e[2] == 2) == 4
    # spelled class (n<=4, both vertices visited)
    spell = set()
    for n in (2, 3, 4):
        spell |= spelled_visits(n)
    assert (1, 1) in spell and (2, 1) not in spell, spell
    assert spell == {(1, 1), (2, 2)}, spell
    # truth spelled circuit -> walk-flow feasibility (throughput == visits, balance 0)
    seq = (IDX[V0], IDX[V1])
    steps = [(seq[i], seq[(i + 1) % 2], 2, sgnRep(seq[i], REP[seq[i]]),
              sgnTgt(seq[(i + 1) % 2], REP[seq[(i + 1) % 2]])) for i in range(2)]
    assert all(s in EDGES for s in steps)
    assert all(steps[i][3] == -steps[(i - 1) % 2][4] for i in range(2))
    assert Counter(REP[s] for s in seq) == Counter({REP[VERTS[0]]: 1, REP[VERTS[1]]: 1})
    # explicit feasible flows: truth walk, doubled walk (spelled (2,2) realization),
    # and the non-spelled defeater
    F_TRUTH = (0, 0, 0, 0, 1, 1, 0, 0)  # spelled walk (0->1)+(1->0), d=(1,1)
    F_DOUBLE = (0, 0, 0, 0, 2, 2, 0, 0)  # doubled walk, d=(2,2)
    F_DEFEAT = (0, 0, 0, 1, 1, 0, 1, 0)  # + self-loop (3->3), d=(2,1)
    for f in (F_TRUTH, F_DOUBLE, F_DEFEAT):
        assert feasible(f), f
    d_star = (throughput(F_TRUTH, VERTS[0]), throughput(F_TRUTH, VERTS[1]))
    d_dbl = (throughput(F_DOUBLE, VERTS[0]), throughput(F_DOUBLE, VERTS[1]))
    d_bad = (throughput(F_DEFEAT, VERTS[0]), throughput(F_DEFEAT, VERTS[1]))
    assert d_star == (1, 1) and d_dbl == (2, 2) and d_bad == (2, 1)
    # exact-likelihood comparison, sample x=(2,1): spelled tie, strict flow defeater
    x = (2, 1)
    assert E_exact(d_star, x) == Fraction(1, 8)
    assert E_exact(d_dbl, x) == Fraction(1, 8)
    assert all(E_exact(d, x) <= Fraction(1, 8) for d in spell)
    assert E_exact(d_bad, x) == Fraction(4, 27) > E_exact(d_star, x)
    print("ALL CHECKS PASSED")
    print(f"truth {d_star} E=1/8 spelled-maximal over {sorted(spell)}; "
          f"flow {d_bad} E=4/27 strict defeater (exact multinomial core)")

if __name__ == "__main__":
    main()
