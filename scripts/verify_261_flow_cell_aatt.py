#!/usr/bin/env python3
"""Exact small-instance verifier: a second RC support with spelled-vs-flow gap.

Mirrors the finite MB09 §6.2 overlap graph, signed incidence, vertex throughput,
zero-terminal balance and circuit spelling definitions. Candidate flows are
integer edge multiplicities on the complete graph; the spelled comparison class
is circular maximal-overlap circuits visiting both observed molecule classes.
The objective is the fixed-external-N product-binomial core on those two classes;
all arithmetic is integral.
"""
from collections import Counter
from itertools import product
from math import prod

COMP = {0: 3, 3: 0, 1: 2, 2: 1}


def rc(w):
    return tuple(COMP[x] for x in reversed(w))


def verify():
    # Two distinct, non-palindromic DNA RC classes: ACA<->TGT and CAC<->GTG.
    a, b = (0, 1, 0), (1, 0, 1)
    strands = list(dict.fromkeys((a, b, rc(a), rc(b))))
    assert rc(a) == (3, 2, 3) and rc(b) == (2, 3, 2)
    assert all(rc(rc(w)) == w for w in strands)
    rep = {s: min(s, rc(s)) for s in strands}
    verts = (a, b)
    L, omin = 3, 1

    def overlap(x, y, n):
        return x[L - n:] == y[:n]

    # Edge tuple: (source strand, target strand, overlap, source sign, target sign).
    edges = [(x, y, n, 1 if x == rep[x] else -1,
              -1 if y == rep[y] else 1)
             for n in range(omin, L) for x in strands for y in strands
             if overlap(x, y, n)]
    assert len(edges) == 8 and sum(e[2] == 2 for e in edges) == 4

    def throughput(f, v):
        return sum(f[i] for i, e in enumerate(edges) if rep[e[0]] == v)

    def balance(f, v):
        return (sum(f[i] * e[3] for i, e in enumerate(edges) if rep[e[0]] == v)
                + sum(f[i] * e[4] for i, e in enumerate(edges) if rep[e[1]] == v))

    def feasible(f):
        return all(throughput(f, v) >= 1 and balance(f, v) == 0 for v in verts)

    # Enumerate every simple (0/1 edge) flow on this graph as a fully checkable
    # bounded search; the concrete witness below itself is independently checked.
    flow_images = set()
    for f in product(range(2), repeat=len(edges)):
        if feasible(f):
            flow_images.add(tuple(throughput(f, v) for v in verts))

    # Enumerate circular sequences through all strands, retaining maximal overlaps
    # and the MB09 opposite-incidence condition at every cyclic vertex.
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

    # The spelled spectra through length 4 are enumerated exactly below.
    truth = (2, 2)
    assert spell_images == {(1, 1), truth}, spell_images

    # Truth flow is the two maximal-overlap edges ACA->CAC->ACA.
    f_truth = tuple(int((e[0], e[1], e[2]) in {
        (a, b, 2), (b, a, 2), (rc(a), rc(b), 2), (rc(b), rc(a), 2)})
                     for e in edges)
    assert feasible(f_truth)
    assert tuple(throughput(f_truth, v) for v in verts) == truth

    # Strict flow defeater: the complete balanced multiplicity vector is searched
    # from the 0/1 edge cube, then re-certified below against the explicit flow.
    f_def = next(f for f in product(range(2), repeat=len(edges))
                 if feasible(f)
                 and tuple(throughput(f, v) for v in verts) == (1, 2))
    assert feasible(f_def)
    defeat = tuple(throughput(f_def, v) for v in verts)
    assert defeat == (1, 2) and defeat in flow_images
    assert defeat not in spell_images

    # Fixed N=4, n=3, x=(1,2), so K(d;x)=prod d_i^xi (N-d_i)^(3-xi).
    N, x = 4, (1, 2)
    def K(d):
        assert all(0 <= c <= N for c in d)
        return prod(c ** xi * (N-c) ** (sum(x)-xi) for c, xi in zip(d, x))

    assert K(truth) == 64 and K(defeat) == 72 and K(defeat) > K(truth)
    assert all(K(d) <= K(truth) for d in spell_images)
    print("PASS: support ACA/CAC (RC-completed); 8 complete edges; "
          f"spelled={sorted(spell_images)} K_truth={K(truth)}; "
          f"integer-flow defeater={defeat} K={K(defeat)} > {K(truth)}")


if __name__ == "__main__":
    verify()
