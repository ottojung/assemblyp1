#!/usr/bin/env python3
"""Exact small-instance verifier: ACAC/CACA RC support spelled-vs-flow gap.

Genuine MB09 section 6.2 bidirected overlap graph on reads of length L=4 with
overlap floor o_min=2: vertices are the two observed molecule classes ACAC and
CACA completed by their genuine DNA reverse complements GTGT and TGTG (no
palindromes). Candidate flows are integer edge multiplicities on the complete
graph with edge lower bound 0, vertex throughput lower bound 1, zero
signed-incidence balance and zero terminal usage. The spelled comparison class
is circular maximal-overlap (L-1=3) circuits visiting both observed classes and
satisfying the opposite-incidence condition. The objective is the
fixed-external-N product-binomial core on the two observed coordinates with
N=4, sample x=(1,2), n=3 reads: K(d;x)=prod d_i^xi (N-d_i)^(n-xi).
Unobserved-class coordinates use the stated omit/fix-at-zero convention; this
finite cell does not adjudicate the source interpretation of those coordinates.
All arithmetic is integral.
"""
from collections import Counter
from itertools import product
from math import prod

COMP = {0: 3, 3: 0, 1: 2, 2: 1}


def rc(w):
    return tuple(COMP[x] for x in reversed(w))


def verify():
    # Two distinct, non-palindromic DNA RC classes: ACAC<->GTGT, CACA<->TGTG.
    a, b = (0, 1, 0, 1), (1, 0, 1, 0)
    strands = list(dict.fromkeys((a, b, rc(a), rc(b))))
    assert rc(a) == (2, 3, 2, 3) and rc(b) == (3, 2, 3, 2)
    assert len(strands) == 4 and all(rc(rc(w)) == w for w in strands)
    rep = {s: min(s, rc(s)) for s in strands}
    assert rep[a] == a and rep[rc(a)] == a
    assert rep[b] == b and rep[rc(b)] == b
    verts = (a, b)
    L, omin = 4, 2

    def overlap(x, y, n):
        return x[L - n:] == y[:n]

    # Edge tuple: (source strand, target strand, overlap, source sign, target sign).
    edges = [(x, y, n, 1 if x == rep[x] else -1,
              -1 if y == rep[y] else 1)
             for n in range(omin, L) for x in strands for y in strands
             if overlap(x, y, n)]
    assert len(edges) == 8 and sum(e[2] == 3 for e in edges) == 4

    def throughput(f, v):
        return sum(f[i] for i, e in enumerate(edges) if rep[e[0]] == v)

    def balance(f, v):
        return (sum(f[i] * e[3] for i, e in enumerate(edges) if rep[e[0]] == v)
                + sum(f[i] * e[4] for i, e in enumerate(edges) if rep[e[1]] == v))

    def feasible(f):
        return all(throughput(f, v) >= 1 and balance(f, v) == 0 for v in verts)

    # Bounded exact search over simple (0/1 edge) flows; the witnesses below are
    # independently re-certified against incidence and vertex bounds.
    flow_images = set()
    for f in product(range(2), repeat=len(edges)):
        if feasible(f):
            flow_images.add(tuple(throughput(f, v) for v in verts))

    # Circular strand sequences of length 2..4, maximal overlaps, opposite
    # incidence at every cyclic vertex, visiting both observed classes.
    spell_images = set()
    for n in range(2, 5):
        for seq in product(strands, repeat=n):
            if {rep[s] for s in seq} != set(verts):
                continue
            steps = [(seq[i], seq[(i + 1) % n], L - 1,
                      1 if seq[i] == rep[seq[i]] else -1,
                      -1 if seq[(i + 1) % n] == rep[seq[(i + 1) % n]] else 1)
                     for i in range(n)]
            if not all(e in edges for e in steps):
                continue
            if not all(steps[i][3] == -steps[i - 1][4] for i in range(n)):
                continue
            counts = Counter(rep[s] for s in seq)
            spell_images.add(tuple(counts[v] for v in verts))

    truth = (2, 2)
    assert spell_images == {(1, 1), truth}, spell_images

    # Truth flow: the length-4 spelled circuit ACAC->CACA->ACAC->CACA
    # (overlap 3 each), i.e. multiplicity 2 on each of the two directed edges.
    f_truth = tuple(2 * int((e[0], e[1], e[2]) in {(a, b, 3), (b, a, 3)})
                    for e in edges)
    assert feasible(f_truth)
    assert tuple(throughput(f_truth, v) for v in verts) == truth

    # Strict flow defeater with throughput (1,2): searched in the 0/1 cube,
    # then re-certified against the explicit incidence/vertex constraints.
    f_def = next(f for f in product(range(2), repeat=len(edges))
                 if feasible(f)
                 and tuple(throughput(f, v) for v in verts) == (1, 2))
    assert feasible(f_def)
    defeat = tuple(throughput(f_def, v) for v in verts)
    assert defeat == (1, 2) and defeat in flow_images
    assert defeat not in spell_images

    # Fixed N=4, n=3, x=(1,2): K(d;x)=prod d_i^xi (N-d_i)^(3-xi).
    N, x = 4, (1, 2)

    def K(d):
        assert all(0 <= c <= N for c in d)
        return prod(c ** xi * (N - c) ** (sum(x) - xi) for c, xi in zip(d, x))

    assert K(truth) == 64 and K(defeat) == 72 and K(defeat) > K(truth)
    assert all(K(d) <= K(truth) for d in spell_images)
    print("PASS: support ACAC/CACA (RC-completed, L=4, o_min=2); "
          "8 complete edges; "
          f"spelled={sorted(spell_images)} K_truth={K(truth)}; "
          f"integer-flow defeater={defeat} K={K(defeat)} > {K(truth)}")


if __name__ == "__main__":
    verify()
