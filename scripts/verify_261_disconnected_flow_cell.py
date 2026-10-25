#!/usr/bin/env python3
"""Exact bounded cell: integer flow defeats truth but spells NO single genome.

Support AAT/TAA (L=3, o_min=1), RC-completed with ATT/TTA. Vertices are the
two observed molecule classes a=AAT, b=TAA. Candidate class (F): integer edge
multiplicities on the complete bidirected overlap graph (10 edges), edge lower
bound 0, vertex throughput lower bound 1, zero signed-incidence balance, zero
terminal usage. Comparison class (G): single closed-walk (one circular genome)
throughput images, i.e. flows whose edge support is connected (a single closed
walk has connected support). Spelled class (C): maximal-overlap (L-1=2)
opposite-incidence circuits visiting both observed classes. Likelihood: fixed
external N=4 product-binomial core on the two observed coordinates,
K(d) = d1^1 d2^2 (4-d1)^2 (4-d2)^1 with x=(1,2), n=3. Length universe: bounded
spelling lengths 2..4; flow search over multiplicities 0..2 (0/1 sub-case also
checked). Truth (2,2) is admitted (spelled, hence feasible). Unobserved-class
coordinates use the stated omit/fix-at-zero convention; this finite cell does
not adjudicate the source interpretation of those coordinates.

Claim: truth (2,2), K=64, is spelled-maximal (only spelled image) but NOT
maximal over integer flows: the explicit feasible flow
f=(0,0,0,0,2,1,0,1,0,0) has image (1,3), K=81>64, is off the spelled set, and
has DISCONNECTED edge support ({TAA,ATT} + {TTA,AAT}), so no single closed
walk (single circular genome) can realize it. All arithmetic is integral.
"""

from collections import Counter
from itertools import product

COMP = {0: 3, 3: 0, 1: 2, 2: 1}


def rc(w):
    return tuple(COMP[x] for x in reversed(w))


def K(d, N=4, x=(1, 2)):
    assert all(0 <= c <= N for c in d)
    return d[0] ** x[0] * d[1] ** x[1] * (N - d[0]) ** (sum(x) - x[0]) * (N - d[1]) ** (sum(x) - x[1])


def support_components(used_edges):
    nodes = set()
    for x, y, _, _, _ in used_edges:
        nodes.add(x)
        nodes.add(y)
    if len(nodes) <= 1:
        return 1
    adj = {u: set() for u in nodes}
    for x, y, _, _, _ in used_edges:
        adj[x].add(y)
        adj[y].add(x)
    seed = next(iter(nodes))
    seen, stack = {seed}, [seed]
    while stack:
        u = stack.pop()
        for v in adj[u]:
            if v not in seen:
                seen.add(v)
                stack.append(v)
    return 1 if len(seen) == len(nodes) else 2


def verify():
    a, b = (0, 0, 3), (3, 0, 0)  # AAT, TAA
    assert rc(a) == (0, 3, 3) and rc(b) == (3, 3, 0)  # ATT, TTA, no palindromes
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
    # T0: complete graph at o_min=1 has exactly 10 edges (no self-loops here:
    # AAT/TAA lack overlap-2/1 self-overlap; connectivity holds overall).
    assert len(edges) == 10, edges

    def throughput(f, v):
        return sum(f[i] for i, e in enumerate(edges) if rep[e[0]] == v)

    def balance(f, v):
        return (sum(f[i] * e[3] for i, e in enumerate(edges) if rep[e[0]] == v)
                + sum(f[i] * e[4] for i, e in enumerate(edges) if rep[e[1]] == v))

    def feasible(f):
        return all(throughput(f, v) >= 1 and balance(f, v) == 0 for v in verts)

    eset = set(edges)

    # T1: spelled images (maximal-overlap, opposite incidence, visit both).
    spell_images = set()
    for n in range(2, 5):
        for seq in product(strands, repeat=n):
            if {rep[s] for s in seq} != set(verts):
                continue
            steps = [(seq[i], seq[(i + 1) % n], L - 1,
                      1 if seq[i] == rep[seq[i]] else -1,
                      -1 if seq[(i + 1) % n] == rep[seq[(i + 1) % n]] else 1)
                     for i in range(n)]
            if not all(e in eset for e in steps):
                continue
            if not all(steps[i][3] == -steps[i - 1][4] for i in range(n)):
                continue
            counts = Counter(rep[s] for s in seq)
            spell_images.add(tuple(counts[v] for v in verts))
    # T1: truth (2,2) is the ONLY spelled image: spelled-maximal.
    assert spell_images == {(2, 2)}, sorted(spell_images)
    assert K((2, 2)) == 64

    # T2: explicit disconnected defeater, mult <= 2.
    f_def = (0, 0, 0, 0, 2, 1, 0, 1, 0, 0)
    assert all(m <= 2 for m in f_def)
    assert feasible(f_def), "defeater must satisfy balance + vertex bound 1"
    img = (throughput(f_def, a), throughput(f_def, b))
    assert img == (1, 3), img
    assert K(img) == 81 and K(img) > K((2, 2))
    assert img not in spell_images

    # T3: support is disconnected -> no single closed walk (one circular
    # genome) realizes this flow; a closed walk has connected edge support.
    used = [edges[i] for i, m in enumerate(f_def) if m]
    assert support_components(used) == 2, used
    used_strands = {s for e in used for s in (e[0], e[1])}
    assert used_strands == {b, rc(a), rc(b), a}, used_strands

    # T4: 0/1-cube sanity: (1,3) already appears among 0/1 feasible flows,
    # so the separation is not a multiplicity->=2 artefact. (The certified
    # witness above uses mult 2 but stays within the stated bound.)
    imgs01 = {tuple(throughput(f, v) for v in verts)
              for f in product(range(2), repeat=len(edges)) if feasible(f)}
    assert (1, 3) in imgs01 and (2, 2) in imgs01

    print("PASS: AAT/TAA L=3 o_min=1; 10 edges; spelled={(2,2)} K=64; "
          "disconnected integer-flow defeater (1,3) K=81>64, "
          "support {TAA,ATT}+{TTA,AAT}, no single-genome walk")


if __name__ == "__main__":
    verify()
