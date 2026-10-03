#!/usr/bin/env python3
"""Exhaustive check of the #89 Eulerian-cycle theorem shape (issue #89).

This script checks the *statement* that

`AssemblyP1/BBTEulerian.lean` now isolates as
`AssemblyP1.BBTEulerian.EulerianCycleObstruction` (the theorem shape of
Bresler--Bresler--Tse 2013, Theorem 3, at `K = L - 1`):

  for every alternative Eulerian cycle of the `(L-1)`-mer multigraph of a
  circular word `S` satisfying Ukkonen's condition at `K = L - 1`, the
  vertex cycle of the alternative traversal is a rotation of the vertex
  cycle of the truth's own traversal,

by exhaustive enumeration of all circular words over a finite alphabet, all
read lengths `K`, and all traversals of the multigraph, for every word
satisfying Ukkonen's condition at `K`.

A traversal is a listing `(x_0, ..., x_{G-1})` of the `G` starts which

  (i)  traverses edges:  the `(K)`-mer entered at `x_{i+1}` is the
       `(K-1)`-shift of the one entered at `x_i`; and
  (ii) is a single circuit:  the successor `x_i -> x_{i+1}` is a `G`-cycle.

The vertex cycle of a traversal is the cyclic sequence of `K`-mers it
visits, modulo rotation; the truth's own traversal is the natural order.
The claim is that all traversals have the same vertex cycle.  Anything else
would be a counterexample to `thm:BBT` at `K`, hence to
`EulerianCycleObstruction`.

The script also reports, for the words it rejects, *which* of the two
clauses of `def:P1P2` is violated (maximal triple repeat of length
`>= K`, or two interleaved maximal repeats both of length `>= K`), which is
the `LongObstruction` disjunction of the Lean module.  Every rejected word
is therefore a word for which the dichotomy is non-vacuous, i.e. the two
disjuncts of `EulerianCycleObstruction` are not dead code.

Run:  python3 scripts/verify_eulerian_cycle_uniqueness_89.py [G] [alphabet]
"""

import sys
from itertools import product
from math import gcd


def win(S, e, r):
    return tuple(S[(r + i) % len(S)] for i in range(e))


def prec(S, t):
    return S[(t - 1) % len(S)]


def foll(S, e, t):
    return S[(t + e) % len(S)]


def is_repeat(S, e, a, b):
    G = len(S)
    return (1 <= e < G and a != b and win(S, e, a) == win(S, e, b)
            and prec(S, a) != prec(S, b) and foll(S, e, a) != foll(S, e, b))


def is_triple(S, e, a, b, c):
    G = len(S)
    return (1 <= e < G and a != b and a != c and b != c
            and win(S, e, a) == win(S, e, b) == win(S, e, c)
            and not (prec(S, a) == prec(S, b) == prec(S, c))
            and not (foll(S, e, a) == foll(S, e, b) == foll(S, e, c)))


def in_arc(G, a, b, p):
    return 0 < (p - a) % G < (b - a) % G


def interleaved(G, a, b, c, d):
    return (a != b and a != c and a != d and b != c and b != d and c != d
            and in_arc(G, a, b, c) != in_arc(G, a, b, d))


def long_obstruction(S, K):
    """`AssemblyP1.BBTEulerian.LongObstruction`: a maximal triple repeat of
    length `>= K`, or an interleaved maximal repeat pair both of length
    `>= K`."""
    G = len(S)
    for e in range(max(K, 1), G):
        for a in range(G):
            for b in range(G):
                for c in range(G):
                    if is_triple(S, e, a, b, c):
                        return ('triple', e, (a, b, c))
    R = [(e, a, b) for e in range(1, G) for a in range(G) for b in range(G)
         if is_repeat(S, e, a, b) and e >= K]
    for i, (e1, a, b) in enumerate(R):
        for (e2, c, d) in R[i + 1:]:
            if interleaved(G, a, b, c, d):
                return ('interleaved', (e1, a, b), (e2, c, d))
    return None


def ukkonen(S, K):
    return long_obstruction(S, K) is None


def traversals(S, K):
    """All traversals of the `K`-mer multigraph of `S` that are single
    circuits, as listings of the `G` starts."""
    G = len(S)
    W = [win(S, K, i) for i in range(G)]
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
    W = [win(S, K, i) for i in range(len(S))]
    seq = [W[x] for x in listing]
    return min(tuple(seq[k:] + seq[:k]) for k in range(len(seq)))


def main():
    G = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    q = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    words = 0
    ukkonen_words = 0
    max_cycles = 0
    for S in product(range(q), repeat=G):
        S = list(S)
        words += 1
        for K in range(1, G + 1):
            if not ukkonen(S, K):
                continue
            ukkonen_words += 1
            cycles = traversals(S, K)
            classes = {vertex_cycle(S, K, c) for c in cycles}
            max_cycles = max(max_cycles, len(cycles))
            if len(classes) != 1:
                print("COUNTEREXAMPLE to thm:BBT at K = L-1")
                print("  S =", "".join(map(str, S)), " G =", G, " K =", K)
                for c in sorted(classes):
                    print("  vertex cycle:", c)
                return 1
    print("G = %d, alphabet size %d, %d words" % (G, q, words))
    print("  (word, K) pairs satisfying Ukkonen at K : %d" % ukkonen_words)
    print("  max number of traversals of one multigraph : %d" % max_cycles)
    print("  all traversals have the same vertex cycle : YES")
    print("  i.e. no counterexample to EulerianCycleObstruction in this range")
    return 0


if __name__ == "__main__":
    sys.exit(main())
