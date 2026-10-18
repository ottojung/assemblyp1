#!/usr/bin/env python3
"""Independent exhaustive check of the #261 Layer-A bidirected Euler theorem.

Primary source: Medvedev & Brudno, *Maximum Likelihood Genome Assembly* (2009),
section 3.4 Observation 1: a bidirected graph has an Eulerian circuit iff it is
connected and balanced.  See https://medvedevgroup.com/papers/jcb09.pdf .

This verifier shares no code with Lean.  It enumerates all finite signed
bidirected multigraphs (physical edge IDs, two endpoint occurrences per edge,
independent endpoint signs, loops and parallel IDs allowed) on a small vertex
set and, for each, checks the exact correspondence

    (Balanced and SupportConnected and #edges > 0)
        <=>  (exists a single cyclic alternately-signed tour using every edge once)

with the *same* definitions the Lean module `AssemblyP1.BidirectedEulerian`
uses:

  * a half-edge is (edge id, endpoint bit); `flip` swaps the bit;
  * `ValidStep a b` means `b` departs the vertex at which `a` arrives with the
    opposite sign;
  * `Balanced` means at every vertex the number of positive incidences equals
    the number of negative incidences (a loop contributes two occurrences);
  * `SupportConnected` means the vertices incident to some edge form one class
    under the edge relation.

A deliberate mutation of the tour predicate is included so a silent failure to
actually search cannot masquerade as agreement.
"""

import itertools
import sys
from collections import Counter


def balanced(V, endVtx, endSgn):
    pos = Counter()
    neg = Counter()
    for e in range(len(endVtx)):
        for b in (0, 1):
            (pos if endSgn[e][b] == 1 else neg)[endVtx[e][b]] += 1
    return all(pos[v] == neg[v] for v in range(V))


def support_connected(V, endVtx):
    parent = list(range(V))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    support = set()
    for e in range(len(endVtx)):
        u, w = endVtx[e]
        support.add(u)
        support.add(w)
        if u != w:
            union(u, w)
    if not support:
        return True
    root = find(next(iter(support)))
    return all(find(v) == root for v in support)


def valid_step(endVtx, endSgn, a, b):
    # a, b are half-edges (edge, bit)
    ea, ba = a
    eb, bb = b
    # arrival half-edge of a is flip a = (ea, 1-ba)
    arr_vtx = endVtx[ea][1 - ba]
    arr_sgn = endSgn[ea][1 - ba]
    return endVtx[eb][bb] == arr_vtx and endSgn[eb][bb] != arr_sgn


def is_euler_tour(endVtx, endSgn, perm, dirs):
    n = len(perm)
    if n == 0:
        return True
    half = [(perm[i], dirs[i]) for i in range(n)]
    return all(valid_step(endVtx, endSgn, half[i], half[(i + 1) % n]) for i in range(n))


def exists_euler(V, endVtx, endSgn):
    m = len(endVtx)
    if m == 0:
        return True
    for perm in itertools.permutations(range(m)):
        for dirs in itertools.product((0, 1), repeat=m):
            if is_euler_tour(endVtx, endSgn, perm, dirs):
                return True
    return False


def exists_euler_mutated(V, endVtx, endSgn):
    """Deliberate mutation: drop the wrap-around transition.

    A tour using every edge with consecutive valid steps but no closing step is
    generally not an Euler circuit, so this predicate must disagree with the
    real one on at least one balanced connected graph.
    """
    m = len(endVtx)
    if m == 0:
        return True
    for perm in itertools.permutations(range(m)):
        for dirs in itertools.product((0, 1), repeat=m):
            half = [(perm[i], dirs[i]) for i in range(m)]
            if all(valid_step(endVtx, endSgn, half[i], half[i + 1]) for i in range(m - 1)):
                return True
    return False


def gen_graphs(V, max_edges):
    opts = [(u, w, a, b) for u in range(V) for w in range(V)
            for a in (0, 1) for b in (0, 1)]
    for m in range(1, max_edges + 1):
        for combo in itertools.combinations_with_replacement(opts, m):
            endVtx = [(c[0], c[1]) for c in combo]
            endSgn = [(1 if c[2] else -1, 1 if c[3] else -1) for c in combo]
            yield endVtx, endSgn


def main():
    V = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    max_edges = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    checked = 0
    balanced_connected = 0
    disagreements = 0
    mutation_disagreements = 0
    for endVtx, endSgn in gen_graphs(V, max_edges):
        checked += 1
        bal = balanced(V, endVtx, endSgn)
        conn = support_connected(V, endVtx)
        has = exists_euler(V, endVtx, endSgn)
        if bal and conn and len(endVtx) > 0:
            balanced_connected += 1
        if (bal and conn and len(endVtx) > 0) != has:
            disagreements += 1
            if disagreements <= 5:
                print("DISAGREEMENT", endVtx, endSgn, "bal", bal, "conn", conn, "has", has)
        # necessary direction: an Euler tour forces balanced + connected
        if has and not (bal and conn):
            disagreements += 1
            print("NECESSARY-DIRECTION FAILURE", endVtx, endSgn)
        # mutation control
        if exists_euler_mutated(V, endVtx, endSgn) != has:
            mutation_disagreements += 1
    print(f"V={V} max_edges={max_edges}: checked={checked} "
          f"balanced_connected_nonempty={balanced_connected} "
          f"theorem_disagreements={disagreements} "
          f"mutation_disagreements={mutation_disagreements}")
    if disagreements != 0:
        print("FAIL")
        return 1
    if mutation_disagreements == 0:
        print("WARNING: mutation never disagreed; the tour search may be vacuous")
        return 1
    print("OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
