#!/usr/bin/env python3
"""The last #89 bridge: can an `AltF` transposition-orbit crossing from a
*genuine* `EulerianCycle` realize the non-interleaving-extension behaviour?

Setting
-------
`AssemblyP1/BBTUniqueEulerian.lean` recasts the alternative Eulerian cycle as a
permutation `AltF = Succ σ ∘ prevPos` of the starts with

  * `AltF_vtx`  : `W (AltF q) = W q`  (label preserving), and
  * `AltF_bijective`,

so under the multiplicity cap (`P2.imp_nodeCount_le_two`: on a primitive `P2`
truth every `(L-1)`-mer occurs at most twice) `AltF` is a product of
disjoint transpositions, one per *doubled* `(L-1)`-mer, plus fixed points.
Its transposition orbits are the chords of the doubled `(L-1)`-mers.

`P2.imp_ExtCrossing` (commit `1c67a14`) says: on a primitive `P2` truth, if
two doubled pairs interleave, then their **maximal extensions** do *not*
interleave.  So the last bridge needed for `thm:BBT` is:

  (B)  a genuine `EulerianCycle` whose `AltF` has an interleaving pair of
       transposition orbits forces either
         (B1) those two maximal extensions to interleave -- contradicting
              `P2.imp_ExtCrossing`; or
         (B2) the traversal's vertex cycle to be the truth's own vertex
              cycle -- i.e. the harmless `VertexCycleEq` disjunct.

(B) is exactly `EulerianCycleObstruction`.  This script tests it, and in
particular tests whether (B2) can fail, i.e. whether a genuine `EulerianCycle`
can realize a crossing pair of `AltF` transposition orbits whose maximal
extensions do not interleave *while the vertex cycle is genuinely different
from the truth's*.  Such an instance would be a counterexample to `thm:BBT`.

Objects are the real ones: a traversal is a listing `σ 0 … σ (G-1)` with
`W (σ (i+1)) = W (σ i + 1)` (the `traverses` clause) and `Succ σ` a `G`-cycle
(the `VisitsAll` clause).  `AltF = Succ σ ∘ prevPos`.

Run:  python3 scripts/verify_AltF_bridge_89.py [G] [alphabet]
"""

import sys
from itertools import product


# ----------------------------------------------------------------- basics

def win(S, e, r):
    return tuple(S[(r + i) % len(S)] for i in range(e))


def prec(S, t):
    return S[(t - 1) % len(S)]


def foll(S, e, t):
    return S[(t + e) % len(S)]


def agrees(S, e, a, b):
    return win(S, e, a) == win(S, e, b)


def max_agree(S, a, b):
    G = len(S)
    e = 0
    while e < G and agrees(S, e + 1, a, b):
        e += 1
    return e


def in_arc(G, a, b, p):
    return 0 < (p - a) % G < (b - a) % G


def interleaved(G, a, b, c, d):
    return (len({a, b, c, d}) == 4
            and in_arc(G, a, b, c) != in_arc(G, a, b, d))


def is_repeat(S, e, a, b):
    G = len(S)
    return (1 <= e < G and a != b and win(S, e, a) == win(S, e, b)
            and prec(S, a) != prec(S, b) and foll(S, e, a) != foll(S, e, b))


def is_primitive(S):
    G = len(S)
    for d in range(1, G):
        if G % d == 0 and list(S) == [S[i % d] for i in range(G)]:
            return False
    return True


def p2_holds(S, K):
    """`P2` at read length `L = K + 1` (equivalently `Ukkonen` at `K`)."""
    G = len(S)
    for e in range(max(K, 1), G):
        for a in range(G):
            for b in range(G):
                for c in range(G):
                    if (is_repeat(S, e, a, b) and is_repeat(S, e, a, c)
                            and is_repeat(S, e, b, c)
                            and len({prec(S, a), prec(S, b), prec(S, c)}) != 1
                            and len({foll(S, e, a), foll(S, e, b),
                                     foll(S, e, c)}) != 1):
                        return False
    R = [(e, a, b) for e in range(max(K, 1), G) for a in range(G)
         for b in range(G) if is_repeat(S, e, a, b)]
    for i, (e1, a, b) in enumerate(R):
        for (e2, c, d) in R[i + 1:]:
            if interleaved(G, a, b, c, d):
                return False
    return True


# ------------------------------------------------------- the word objects

def W_of(S, K):
    G = len(S)
    return [win(S, K, i) for i in range(G)]


def cap_holds(S, K):
    c = {}
    for w in W_of(S, K):
        c[w] = c.get(w, 0) + 1
    return max(c.values()) <= 2


def tstar(S, a, b):
    """`maxPairStart`-shift: the largest `t` with the two occurrences agreeing
    on the `t` positions *preceding* their starts (`max_back_agrees`,
    `pairBack`)."""
    G = len(S)
    t = 0
    while t < G and prec(S, (a - t) % G) == prec(S, (b - t) % G):
        t += 1
    return t


def maxPair(S, a, b):
    """`(u, v, e)`: the maximal extension at shifted starts, as in
    `P2RepeatResidual.maxPairStart` / `maxPairLen`.  `None` if the two
    occurrences agree all the way round (periodic; excluded by primitivity)."""
    G = len(S)
    t = 0
    while t < G and prec(S, (a - t) % G) == prec(S, (b - t) % G):
        t += 1
    if t >= G:
        return None
    u, v = (a - t) % G, (b - t) % G
    return (u, v, max_agree(S, u, v))


# --------------------------------------------------- the traversal objects

def traversals(S, K):
    """All `EulerianCycle` listings: the `traverses` clause plus the
    `VisitsAll` (single circuit) clause."""
    G = len(S)
    W = W_of(S, K)
    fibres = {}
    for i in range(G):
        fibres.setdefault(W[i], []).append(i)
    succ = {x: fibres[W[(x + 1) % G]] for x in range(G)}
    out = []
    used = [False] * G
    path = []

    def dfs(x):
        if len(path) == G:
            if W[(path[-1] + 1) % G] == W[0]:
                out.append(tuple(path))
            return
        for y in succ[x]:
            if not used[y]:
                used[y] = True
                path.append(y)
                dfs(y)
                path.pop()
                used[y] = False

    used[0] = True
    path.append(0)
    dfs(0)
    return out


def vertex_cycle(S, K, listing):
    W = W_of(S, K)
    seq = [W[x] for x in listing]
    return min(tuple(seq[k:] + seq[:k]) for k in range(len(seq)))


def altF(S, K, listing):
    """`AltF = Succ σ ∘ prevPos`, as a function on starts.

    `Succ σ (σ i) = σ (i+1)`, so `Succ σ` is the successor permutation of the
    listing and `AltF q = Succ σ (q - 1)`."""
    G = len(S)
    succ = {listing[i]: listing[(i + 1) % G] for i in range(G)}
    return {q: succ[(q - 1) % G] for q in range(G)}


def transposition_orbits(S, K, f):
    """The 2-element orbits of `AltF`, i.e. the doubled `(L-1)`-mers that the
    alternative traversal actually swaps."""
    G = len(S)
    seen = set()
    out = []
    for x in range(G):
        if x in seen:
            continue
        y = f[x]
        if y != x and f[y] == x:
            seen.add(x)
            seen.add(y)
            out.append((x, y))
    return out


def ladder_of(S, K, x, y, e, u, v):
    """Is the collapsing pair `x` a rung at shift `t` and `y` a rung at a
    distinct shift `t'`, of the single ladder with maximal repeat `(u, v)` of
    length `e`?  (`LADDER` of the docstring.)"""
    G = len(S)
    for t in range(0, e - K + 1):
        for tp in range(0, e - K + 1):
            if t == tp:
                continue
            r1 = {(u + t) % G, (v + t) % G}
            r2 = {(u + tp) % G, (v + tp) % G}
            if r1 == set(x) and r2 == set(y):
                return True
            if r1 == set(y) and r2 == set(x):
                return True
    return False


# ------------------------------------------------------------------- main

def main():
    G = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    q = int(sys.argv[2]) if len(sys.argv) > 2 else 2

    n_cycles = 0            # genuine EulerianCycle objects
    n_nontrivial = 0        # of those, vertex cycle != truth's
    n_cross = 0             # (traversal, crossing orbit pair) configurations
    n_benign = 0            # ... whose maximal extensions do not interleave
    bad = []                # (B2) failures: non-interleaving AND different cycle
    on_p2 = []              # collapse configurations on a genuine P2 word
    p2_cycles = 0           # genuine EulerianCycles on P2 words
    p2_nontrivial = 0
    n_collapse = 0          # collapsing crossing doubled pairs (traversal-free)
    ladder_bad = []         # `LADDER` characterisation failures
    min_benign = None       # smallest benign-collapse instance found

    for S in product(range(q), repeat=G):
        S = list(S)
        if not is_primitive(S):
            continue
        for K in range(1, G + 1):
            if not cap_holds(S, K):
                continue
            hp2 = p2_holds(S, K)
            truth = vertex_cycle(S, K, list(range(G)))

            # --- the word-level characterisation of a collapse (`LADDER`)
            cnt = {}
            for i in range(G):
                cnt.setdefault(win(S, K, i), []).append(i)
            pr = [tuple(v) for v in cnt.values() if len(v) == 2]
            mp = {x: maxPair(S, x[0], x[1]) for x in pr}
            for i in range(len(pr)):
                for j in range(i + 1, len(pr)):
                    x, y = pr[i], pr[j]
                    if not interleaved(G, x[0], x[1], y[0], y[1]):
                        continue
                    if mp[x] is None or mp[y] is None:
                        continue
                    if {mp[x][0], mp[x][1]} != {mp[y][0], mp[y][1]}:
                        continue
                    n_collapse += 1
                    (u, v, e) = mp[x]
                    if not ladder_of(S, K, x, y, e, u, v):
                        ladder_bad.append((''.join(map(str, S)), K, x, y,
                                           mp[x], mp[y]))

            # --- the traversal-level statements (B1), (B2)
            for c in traversals(S, K):
                n_cycles += 1
                nontriv = vertex_cycle(S, K, c) != truth
                if nontriv:
                    n_nontrivial += 1
                if hp2:
                    p2_cycles += 1
                    if nontriv:
                        p2_nontrivial += 1
                f = altF(S, K, c)
                orb = transposition_orbits(S, K, f)
                for i in range(len(orb)):
                    for j in range(i + 1, len(orb)):
                        (a, b) = orb[i]
                        (cc, d) = orb[j]
                        if not interleaved(G, a, b, cc, d):
                            continue
                        n_cross += 1
                        e1 = maxPair(S, a, b)
                        e2 = maxPair(S, cc, d)
                        if e1 is None or e2 is None:
                            continue
                        (u, v, L1) = e1
                        (w, z, L2) = e2
                        inter = (interleaved(G, u, v, w, z)
                                 or interleaved(G, v, u, w, z))
                        if not inter:
                            n_benign += 1
                            rec = (''.join(map(str, S)), K, (a, b), (cc, d),
                                   (u, v, L1), (w, z, L2), nontriv)
                            if min_benign is None or G < min_benign[1]:
                                min_benign = (''.join(map(str, S)), G, K, rec)
                            if hp2:
                                on_p2.append(rec)
                            if nontriv:
                                bad.append(rec)

    print("G = %d, alphabet size %d" % (G, q))
    print("  genuine EulerianCycle objects (primitive, cap<=2) : %d" % n_cycles)
    print("    of those, vertex cycle differs from truth's     : %d" % n_nontrivial)
    print("  genuine EulerianCycles on words satisfying P2     : %d" % p2_cycles)
    print("    of those, vertex cycle differs from truth's     : %d" % p2_nontrivial)
    print()
    print("  crossing AltF transposition-orbit pairs          : %d" % n_cross)
    print("    maximal extensions DO interleave (B1)          : %d"
          % (n_cross - n_benign))
    print("    maximal extensions do NOT interleave (collapse) : %d" % n_benign)
    print("  (B2) failures: collapse AND different vertex cycle: %d" % len(bad))
    for t in bad[:8]:
        print("      S=%s K=%d orbits %s x %s -> ext %s x %s nontriv=%s" % t)
    print()
    print("  LADDER: collapsing crossing doubled pairs         : %d" % n_collapse)
    print("    not two rungs of one ladder                     : %d"
          % len(ladder_bad))
    for t in ladder_bad[:6]:
        print("      S=%s K=%d %s x %s -> ext %s x %s" % t)
    if min_benign is not None:
        print()
        print("  smallest benign-collapse instance: S=%s G=%d K=%d" % min_benign[:3])
        print("      orbits %s x %s -> ext %s x %s   nontriv=%s" % min_benign[3])
    print()
    print("  collapse configurations sitting on a P2 word     : %d" % len(on_p2))
    for t in on_p2[:4]:
        print("      S=%s K=%d orbits %s x %s -> ext %s x %s nontriv=%s" % t)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
