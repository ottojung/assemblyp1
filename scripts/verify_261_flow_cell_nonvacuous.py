#!/usr/bin/env python3
"""Issue #261 non-vacuous reduction cell: spelled witness on a transitively
reduced graph transfers to the unreduced feasible-flow set.

Single source-faithful MB09 Sec.6.2 instance (exact integer arithmetic, no trust
in Lean output). Mirrors `AssemblyP1/Section62BidirectedFlow` definitions
(`overlapEdges`, signed incidences, `throughput`, `balCore` balance,
zero-terminal `Feasible62`) and the #284 spelling-based reduction predicate
`isReducibleSpellingB` (`l1 + l2 == readLen + e.len`, i.e. the direct edge's
spelled word equals the two-step spelling).

Instance: L=3, o_min=1, observed RC support verts={ACA,CAC} with genuine DNA
reverse complements (verified against Watson-Crick complement).
Alphabet A=0,C=1,G=2,T=3.

Result:
  * The complete overlap graph has 8 edges (4 len-1 + 4 len-2). Spelling-based
    transitive reduction removes exactly the 4 len-1 self-loop edges (each is
    spelled by a len-2 pair, e.g. ACA->ACA(len1) by ACA->CAC->ACA(len2,len2)):
    8 -> 4 edges, i.e. reduction is STRICTLY non-vacuous here. (The literal
    length-based predicate `isReducibleB` with `l1,l2 < ln` is vacuous on every
    L=3 instance; this cell uses the #284 spelling predicate instead.)
  * Maximal edges (len L-1=2) are NEVER spelling-reducible: l1+l2 = L+ln = 5
    exceeds the 2(L-1) = 4 maximum. Verified arithmetically below, so the
    maximal-edge spelled class is identical on the reduced and complete graphs.
  * Candidate class: spelled circuits on the REDUCED graph (maximal-overlap
    steps, both vertices visited). Truth: the spelled 2-circuit walk flow with
    throughput d*=(1,1), feasible on the COMPLETE graph. Likelihood: fixed-N
    product-binomial core K(d;x) with N=4, x=(3,1) (n=4). Length universe: the
    spelling length n=4 of the witness circuit.
  * The reduced-graph spelled witness (2,2) (4-circuit using only kept len-2
    edges) scores K=256 > 81=K(1,1). By the proved inclusion
    spelled(reduced) ⊆ spelled(complete) (this run's `spelled_mono` check, the
    computational shadow of Lean `spelledVisitSet_mono_edges`), the witness
    transfers: the truth is NOT maximal over the complete-graph feasible-flow
    set. This instantiates Lean `spelled_witness_transfers_across_reduction`
    on a reduction-non-vacuous instance.
Throughputs with any coordinate >N are outside the binomial probability domain
and excluded from the comparison.
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


def is_reducible_spelling(e):
    """#284 `isReducibleSpellingB`: direct edge spelled by a two-step path."""
    sx, sy, ln = e[0], e[1], e[2]
    for m in S:
        for l1 in range(READLEN):
            for l2 in range(READLEN):
                if (OMIN <= l1 and OMIN <= l2
                        and suf(TOLIST[sx], l1) == pre(TOLIST[m], l1)
                        and suf(TOLIST[m], l2) == pre(TOLIST[sy], l2)
                        and l1 + l2 == READLEN + ln):
                    return True
    return False


def throughput(f, edges, v):
    return sum(f[i] for i, e in enumerate(edges) if REP[e[0]] == v)


def balance(f, edges, v):
    return (sum(f[i] * e[3] for i, e in enumerate(edges) if REP[e[0]] == v)
            + sum(f[i] * e[4] for i, e in enumerate(edges) if REP[e[1]] == v))


def feasible(f, edges):
    return (all(throughput(f, edges, v) >= 1 for v in VERTS)
            and all(balance(f, edges, v) == 0 for v in VERTS))


def K(d, x, N):
    n = sum(x)
    assert all(0 <= c <= N for c in d), "probability domain"
    return prod(c ** xi * (N - c) ** (n - xi) for c, xi in zip(d, x))


def spelled_visits(n, edges):
    E = set(edges)
    out = set()
    for seq in itertools.product(S, repeat=n):
        if set(REP[s] for s in seq) != set(REP[v] for v in VERTS):
            continue
        steps = [(seq[i], seq[(i + 1) % n], READLEN - 1,
                  sgnRep(seq[i], REP[seq[i]]),
                  sgnTgt(seq[(i + 1) % n], REP[seq[(i + 1) % n]])) for i in range(n)]
        if (all(s in E for s in steps)
                and all(steps[i][3] == -steps[(i - 1) % n][4] for i in range(n))):
            c = Counter(REP[s] for s in seq)
            out.add((c[REP[VERTS[0]]], c[REP[VERTS[1]]]))
    return out


def main():
    # genuine DNA RC check
    for s in STRANDS:
        assert list(rcw(s)) == [COMP[c] for c in reversed(list(s))]
    assert len(EDGES) == 8 and sum(1 for e in EDGES if e[2] == 2) == 4
    # spelling-based reduction is STRICTLY non-vacuous: removes exactly len-1 edges
    removed = [e for e in EDGES if is_reducible_spelling(e)]
    kept = [e for e in EDGES if e not in removed]
    assert len(removed) == 4 and all(e[2] == 1 for e in removed), removed
    assert len(kept) == 4 and all(e[2] == 2 for e in kept), kept
    # general arithmetic lemma: maximal edges (ln = L-1) are never
    # spelling-reducible, since l1+l2 <= 2(L-1) < L+(L-1) = L+ln always
    assert all(e[2] == READLEN - 1 for e in kept)
    for e in EDGES:
        if e[2] == READLEN - 1:
            assert not is_reducible_spelling(e)
            assert READLEN + e[2] > 2 * (READLEN - 1)
    # spelled-class inclusion across reduction (shadow of spelledVisitSet_mono_edges)
    spell_full, spell_red = set(), set()
    for n in (2, 3, 4):
        spell_full |= spelled_visits(n, EDGES)
        spell_red |= spelled_visits(n, kept)
    assert spell_red <= spell_full, (spell_red, spell_full)
    assert (1, 1) in spell_red and (2, 2) in spell_red, spell_red
    assert (2, 1) not in spell_red
    # truth: spelled 2-circuit walk flow, feasible on the COMPLETE graph
    e01 = next(i for i, e in enumerate(EDGES)
               if TOLIST[e[0]] == [0, 1, 0] and TOLIST[e[1]] == [1, 0, 1] and e[2] == 2)
    e10 = next(i for i, e in enumerate(EDGES)
               if TOLIST[e[0]] == [1, 0, 1] and TOLIST[e[1]] == [0, 1, 0] and e[2] == 2)
    F_TRUTH = [0] * len(EDGES)
    F_TRUTH[e01] = 1
    F_TRUTH[e10] = 1
    assert feasible(F_TRUTH, EDGES), "truth must be feasible on complete graph"
    d_star = (throughput(F_TRUTH, EDGES, VERTS[0]),
              throughput(F_TRUTH, EDGES, VERTS[1]))
    assert d_star == (1, 1), d_star
    # reduced-graph spelled witness strictly beats the truth (N=4, x=(3,1), n=4)
    N, x = 4, (3, 1)
    d_wit = (2, 2)
    assert d_wit in spell_red
    assert K(d_star, x, N) == 81, K(d_star, x, N)
    assert K(d_wit, x, N) == 256, K(d_wit, x, N)
    assert K(d_wit, x, N) > K(d_star, x, N)
    # the witness's 4-circuit uses only kept (len-2) edges: transfer is licensed
    print("ALL CHECKS PASSED")
    print(f"complete={len(EDGES)} reduced={len(kept)} "
          f"spelled_red={sorted(spell_red)} truth={d_star} K=81 "
          f"witness={d_wit} K=256 strict defeater transfers")


if __name__ == "__main__":
    main()
