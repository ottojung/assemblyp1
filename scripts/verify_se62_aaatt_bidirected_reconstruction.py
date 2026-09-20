#!/usr/bin/env python3
"""
Independent reconstruction of the Medvedev-Brudno (2009) section 6.2
transitively reduced bidirected overlap graph for the PR #39 witness
`AAATT -> AAAATT`, with observed read vertices {AAA, AAT, TAA}.

This script is deliberately self-contained and does not import or reuse the
branch's `Feasible` / `SeqSupportLB` predicate or its graph helpers.  It builds
the bidirected graph straight from the primary-source definitions:

  * section 3.1  a read is a DNA molecule = an unordered reverse-complement
                 strand pair; a k-molecule is represented once;
  * section 3.2  a bidirected edge carries a positive/negative incidence at
                 each endpoint; a (x1,xk)-walk has e_{i-1}, e_i of *opposite*
                 orientation at every interior vertex x_i; a loop that is twice
                 positive/negative-incident has incidence +2 / -2;
  * section 3.3  the four strand-overlap cases that make a bidirected overlap,
                 with the incidence sign convention stated there;
  * section 3.4  flow balance: sum_e I(v,e) f(e) = b(v);
  * section 6.2  vertices are the reads; edges are *all* bidirected overlaps of
                 length at least o_min; transitive edge reduction removes an
                 overlap spelled by two shorter overlaps; every read vertex has
                 lower bound 1, all other lower bounds 0, all upper bounds
                 infinity; supersource/sink edges carry prohibitive cost;
  * Observation 7  the number of times a walk visits a read equals the number of
                 times that read occurs as a submolecule of the spelled
                 molecule;
  * section 6.1  the separable product-of-binomial-marginals objective with the
                 external genome size N.

All arithmetic is exact (fractions.Fraction).  The script exits non-zero if any
assertion fails.
"""
from __future__ import annotations

import sys
from collections import Counter
from fractions import Fraction
from itertools import product

# ---------------------------------------------------------------------------
# Alphabet and reverse complement
# ---------------------------------------------------------------------------

A, T = 0, 1
COMP = {A: T, T: A}
L = 3  # read length
N = 5  # external genome size (true |S|)


def rc(s):
    return tuple(COMP[c] for c in reversed(s))


def mol(s):
    """Molecule class representative: lexicographically smaller strand."""
    s = tuple(s)
    r = rc(s)
    return min(s, r)


def word(s):
    return "".join("AT"[c] for c in s)


# ---------------------------------------------------------------------------
# Bidirected overlap graph (MB09 section 3.3)
# ---------------------------------------------------------------------------

class Edge:
    __slots__ = ("x", "y", "sx", "sy", "l", "ix", "iy")

    def __init__(self, x, y, sx, sy, l, ix, iy):
        self.x, self.y = x, y          # endpoint molecules (positive reps)
        self.sx, self.sy = sx, sy      # strands realizing the overlap
        self.l = l                     # underlying string-overlap length
        self.ix, self.iy = ix, iy      # incidences at x and at y

    def key(self):
        return (self.x, self.y, self.sx, self.sy, self.l)


def overlaps(a, b):
    """All suffix/prefix overlap lengths of a and b (proper, i.e. < len(a))."""
    out = []
    for l in range(1, len(a) + 1):
        if a[len(a) - l:] == b[:l]:
            out.append(l)
    return out


def build_graph(vertices, omin):
    """All bidirected overlaps of length in [omin, L), by section 3.3.

    For molecules x, y with strand choices sx in {p(x), n(x)} and
    sy in {p(y), n(y)}, the four cases are:
        sx=p(x), sy=p(y)  ->  (+, -)     (case 1)
        sx=p(x), sy=n(y)  ->  (+, +)     (case 2)
        sx=n(x), sy=p(y)  ->  (-, -)     (case 3)
        sx=n(x), sy=n(y)  ->  (-, +)     (case 4)
    """
    edges = []
    for x, y in product(vertices, repeat=2):
        px, nx = x, rc(x)
        py, ny = y, rc(y)
        for sx, sy in ((px, py), (px, ny), (nx, py), (nx, ny)):
            ix = +1 if sx == px else -1
            iy = +1 if sy == ny else -1
            for l in overlaps(sx, sy):
                if omin <= l < L:
                    edges.append(Edge(x, y, sx, sy, l, ix, iy))
    return edges


def is_reducible_literal(e, vertices):
    """MB09 section 6.2: removable iff spelled by two *shorter* overlaps.

    An x-y overlap of length l realized by strands (sx, sy) is spelled through
    an intermediate molecule z with strand sz when sx overlaps sz in l1 and sz
    overlaps sy in l2, both in [omin, l), and the composition has outer overlap
    l1 + l2 - L = l.
    """
    for z in vertices:
        for sz in (z, rc(z)):
            l1s = overlaps(e.sx, sz)
            l2s = overlaps(sz, e.sy)
            for l1 in l1s:
                for l2 in l2s:
                    if l1 < e.l and l2 < e.l and (l1 + l2 - L) == e.l:
                        return True, (z, sz, l1, l2)
    return False, None


# ---------------------------------------------------------------------------
# Cyclic window walk of a molecule, as a bidirected walk
# ---------------------------------------------------------------------------

def window_strands(seq):
    G = len(seq)
    return [tuple(seq[(i + j) % G] for j in range(L)) for i in range(G)]


def walk(seq, edges_by_key):
    """Return (steps, visits); assert each step is a real graph edge."""
    strands = window_strands(seq)
    G = len(seq)
    visits = [mol(s) for s in strands]
    steps = []
    for i in range(G):
        sx, sy = strands[i], strands[(i + 1) % G]
        assert sx[1:] == sy[:-1], ("windows do not overlap by L-1", sx, sy)
        key = (mol(sx), mol(sy), sx, sy, L - 1)
        assert key in edges_by_key, ("no graph edge for step", i, word(sx), word(sy))
        steps.append(edges_by_key[key])
    return steps, visits


def check_bidirected(seq, edges_by_key):
    steps, visits = walk(seq, edges_by_key)
    G = len(seq)
    # walk condition at every visit: arriving orientation is opposite to
    # departing orientation (section 3.2); the wrap-around vertex included.
    for i in range(G):
        prev = steps[(i - 1) % G]
        cur = steps[i]
        assert prev.y == visits[i] and cur.x == visits[i]
        assert prev.iy == -cur.ix, ("orientation mismatch at visit", i, visits[i])
    return steps, visits


def vertex_throughput(visits):
    return Counter(visits)


def balance(steps, vertices):
    b = {v: 0 for v in vertices}
    for e in steps:
        b[e.x] += e.ix
        b[e.y] += e.iy
    return b


# ---------------------------------------------------------------------------
# Section 6.1 separable binomial objective
# ---------------------------------------------------------------------------

def log_lik_factor(d, x, n, N):
    """One type's binomial marginal (without the x-independent coefficient)."""
    return Fraction(d, N) ** x * Fraction(N - d, N) ** (n - x)


def objective(spectrum, obs, n, N, universe):
    r = Fraction(1)
    for w in universe:
        r *= log_lik_factor(spectrum.get(w, 0), obs.get(w, 0), n, N)
    return r


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    truth = (A, A, A, T, T)          # AAATT, G = 5
    competitor = (A, A, A, A, T, T)  # AAAATT, G = 6
    starts = (0, 1, 4)
    n = len(starts)
    assert N == len(truth)

    truth_windows = window_strands(truth)
    comp_windows = window_strands(competitor)
    obs_list = [mol(truth_windows[r]) for r in starts]
    vertices = sorted(set(mol(w) for w in truth_windows))
    assert vertices == [mol((A, A, A)), mol((A, A, T)), mol((T, A, A))]

    print("observed read molecules :", sorted(word(v) for v in obs_list))
    print("truth windows (classes):",
          [word(mol(w)) for w in truth_windows])
    print("competitor windows     :",
          [word(mol(w)) for w in comp_windows])
    print()

    # (1) Graph at the strictest threshold o_min = L-1 = 2.
    g2 = build_graph(vertices, 2)
    print(f"(G) bidirected overlaps at o_min=2: {len(g2)}")
    for e in g2:
        case = {(1, -1): "p/p (+,-)", (1, 1): "p/n (+,+)",
                (-1, -1): "n/p (-,-)", (-1, 1): "n/n (-,+)"}[(e.ix, e.iy)]
        print(f"    {word(e.x):>3} -- {word(e.y):<3}  len={e.l}  {case}"
              f"   strands {word(e.sx)}/{word(e.sy)}")
    print()
    assert len(g2) == 10

    # (2) Transitive reduction under the literal MB09 rule.  With L=3 and
    # o_min=2 there are no shorter admissible overlaps, so nothing is removed.
    reducible = [e for e in g2 if is_reducible_literal(e, vertices)[0]]
    print(f"(R) edges removable as 'spelled by two shorter overlaps': "
          f"{len(reducible)}")
    assert not reducible

    # The same at o_min = 1: the graph gains length-1 edges, but the employed
    # length-(L-1) edges must remain irreducible.
    g1 = build_graph(vertices, 1)
    print(f"(R) bidirected overlaps at o_min=1: {len(g1)}")
    print()

    # (3) Build lookup tables and check both molecules as bidirected circuits.
    by_key_2 = {e.key(): e for e in g2}
    by_key_1 = {e.key(): e for e in g1}
    results = {}
    for name, seq in (("truth AAATT", truth), ("competitor AAAATT", competitor)):
        steps, visits = check_bidirected(seq, by_key_2)
        d = vertex_throughput(visits)
        bal = balance(steps, vertices)
        # Also confirm the walk is present at o_min=1.
        for e in steps:
            assert e.key() in by_key_1, ("missing at o_min=1", e.key())
        # Observation 7: visit counts = submolecule occurrence counts.
        spec = Counter(mol(w) for w in window_strands(seq))
        assert d == spec, (d, spec)
        assert all(b == 0 for b in bal.values()), bal
        assert all(d[v] >= 1 for v in vertices)
        results[name] = (steps, d, bal)
        print(f"(W) {name}: valid bidirected circuit")
        print(f"    visit/throughput d = "
              f"{ {word(k): v for k, v in sorted(d.items())} }")
        print(f"    vertex balance b(v) = "
              f"{ {word(k): v for k, v in sorted(bal.items())} }  "
              f"(edge LB 0, vertex LB 1, no supersource/sink)")
    print()

    # (4) Section 6.1 objective, external N, observed counts x.
    obs = Counter(obs_list)
    dS = results["truth AAATT"][1]
    dD = results["competitor AAAATT"][1]
    universe = set(vertices)  # ATA has d=0 in both, factor 1
    LS = objective(dS, obs, n, N, universe)
    LD = objective(dD, obs, n, N, universe)
    ratio = LD / LS
    print(f"(L) observed x = { {word(k): v for k, v in sorted(obs.items())} }, "
          f"n = {n}, N = {N}")
    print(f"    d_S = { {word(k): v for k, v in sorted(dS.items())} }")
    print(f"    d_D = { {word(k): v for k, v in sorted(dD.items())} }")
    print(f"    L_6.1(D)/L_6.1(S) = {ratio}  (expected 9/8)")
    assert ratio == Fraction(9, 8) and ratio > 1

    print()
    print("ALL CHECKS PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
