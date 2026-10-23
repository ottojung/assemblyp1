#!/usr/bin/env python3
"""Issue #261 bounded flow cell: spelled-maximal truth with a strict flow defeater.

Single source-faithful MB09 Sec.6.2 instance (exact integer arithmetic, no trust
in Lean output). Mirrors `AssemblyP1/Section62BidirectedFlow` definitions:
`overlapEdges` (proper overlaps o_min<=len<L), `sgnRep`/`sgnTgt` incidences,
`throughput` (departures per molecule class), `balCore` signed balance,
zero-terminal `Feasible62` (edgeLB 0, vertexLB 1, balance 0), literal
`isReducibleB` reduction check, and the Sec.6.1 fixed-external-N product-binomial
core K(d;x) = prod d_i^{x_i} (N-d_i)^{n-x_i} over the observed support with the
flow convention that unobserved molecule coordinates are fixed at 0 (common
factor, ranking-valid within this convention; see docs/issue261 doc OPEN-2).

Instance: L=3 (readLen), o_min=1, observed RC support verts={ACA,CAC} with
genuine DNA reverse complements (ACA<->TGT, CAC<->GTG; verified against
Watson-Crick complement). Alphabet A=0,C=1,G=2,T=3.

Result: truth d*=(1,1) is the visit vector of the spelled bidirected 2-circuit
(ACA->CAC->ACA, maximal overlaps len 2), hence a feasible spelled truth. Among
spelled candidates visiting both vertices {(1,1),(2,2)} it is maximal (tie 8=8)
for sample x=(2,1), n=3, N=3. The feasible integer flow throughput (2,1)
(non-spelled: no spelled circuit has visit vector (2,1)) scores 16>8: a strict
flow defeater. So spelled-maximal does NOT imply flow-maximal on this instance.
Throughputs with any coordinate >N are outside the binomial probability domain
and excluded from the comparison (explicit probability-feasibility restriction).
"""
import itertools
from collections import Counter
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

def K(d, x, N):
    n = sum(x)
    assert all(0 <= c <= N for c in d), "probability domain"
    return prod(c ** xi * (N - c) ** (n - xi) for c, xi in zip(d, x))

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
    # truth spelled circuit -> walk-flow feasibility (throughput == visits, balance 0)
    seq = (IDX[V0], IDX[V1])
    steps = [(seq[i], seq[(i + 1) % 2], 2, sgnRep(seq[i], REP[seq[i]]),
              sgnTgt(seq[(i + 1) % 2], REP[seq[(i + 1) % 2]])) for i in range(2)]
    assert all(s in EDGES for s in steps)
    assert all(steps[i][3] == -steps[(i - 1) % 2][4] for i in range(2))
    assert Counter(REP[s] for s in seq) == Counter({REP[VERTS[0]]: 1, REP[VERTS[1]]: 1})
    # explicit feasible flows
    F_TRUTH = (0, 0, 0, 0, 1, 1, 0, 0)  # spelled walk (0->1)+(1->0), d=(1,1)
    F_DEFEAT = (0, 0, 0, 1, 1, 0, 1, 0)  # + self-loop (3->3), d=(2,1)
    for f in (F_TRUTH, F_DEFEAT):
        assert feasible(f), f
    d_star = (throughput(F_TRUTH, VERTS[0]), throughput(F_TRUTH, VERTS[1]))
    d_bad = (throughput(F_DEFEAT, VERTS[0]), throughput(F_DEFEAT, VERTS[1]))
    assert d_star == (1, 1) and d_bad == (2, 1)
    # fixed-N binomial comparison, N=3, x=(2,1): truth spelled-maximal, flow-defeated
    N, x = 3, (2, 1)
    assert K(d_star, x, N) == 8
    assert all(K(d, x, N) <= 8 for d in spell if all(0 <= c <= N for c in d))
    assert K(d_bad, x, N) == 16 > K(d_star, x, N)
    print("ALL CHECKS PASSED")
    print(f"truth {d_star} K=8 spelled-maximal over {sorted(spell)}; flow {d_bad} K=16 strict defeater")

if __name__ == "__main__":
    main()
