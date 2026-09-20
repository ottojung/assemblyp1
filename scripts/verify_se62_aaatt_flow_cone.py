#!/usr/bin/env python3
"""Independent characterization of the MB09 §6.2 copy-count cone for the
reads ``AAA, AAT, TAA`` (the ``AAATT`` instance), and adjudication of the
spectra ``2,2,1`` and ``2,2,2``.

Object (see docs/section62-aaatt-reduced-flow-cone-and-spectra.md):

* reads are DNA molecules = unordered reverse-complement pairs; on the binary
  alphabet ``A=0, T=1`` the involution is ``0 <-> 1`` and a read type is the
  class ``min(w, rc(w))``;
* the read-overlap graph is bidirected: vertices are the observed read
  molecules, and an overlap edge exists when a suffix of one strand of ``X``
  equals a prefix of one strand of ``Y`` in a fixed orientation convention
  (ports), of length >= o_min and proper (< L);
* it is transitively reduced as in Myers (2005), which MB09 §6.2 names as the
  procedure: an overlap is removed when it is spelled by a two-step path with
  strictly longer proper overlaps;
* every read vertex has lower bound 1, every edge lower bound 0, upper bounds
  infinity; a flow is a collection of walks, and (Observation 7) the flow
  through vertex ``v`` is the number of occurrences of ``v`` in the spelled
  molecules.

The script checks, with exact integer arithmetic:

1. The window/class spectra of ``AAATT`` (= 1,2,2) and ``AAAATT`` (= 2,2,2),
   and the literal §6.1 binomial ratio 9/8.
2. The 10 proper length-2 port edges and the 18 length-1 port edges.
3. Myers reduction: for L = 3 only length-1 overlaps can be transitive
   (composition l = l1 + l2 - L with l1,l2 <= L-1 forces l <= L-2 = 1).  A
   length-1 edge is reducible iff the middle window of its spelled 5-mer is an
   observed read.  Exactly the two directions of ``AAT.p1 -- TAA.p0`` survive.
4. The circulation (closed-walk) cone of the reduced graph has all generators
   with ``d_AAT = d_TAA``; the generators are ``(1,0,0)`` and ``(0,1,1)``, so
   the feasible integer copy counts are exactly ``{(a,k,k)}``.
5. Hence in the ordering ``(AAA, AAT, TAA)``:
      (1,2,2) = truth   FEASIBLE
      (2,2,2) = AAAATT  FEASIBLE
      (2,2,1)           NOT feasible (closed §6.2 flow)
   while (2,2,1) becomes feasible only if the reducible length-1 edges are
   retained (the literal "two shorter overlaps" wording) or if open
   source/sink paths are allowed.
6. Single-molecule (sequence-level) spectra: every circular binary molecule
   whose length-3 window classes lie in {AAA,AAT,TAA} has all runs of length
   >= 2 and class counts ``(G-4k, 2k, 2k)``; in particular ``AAT = TAA`` and
   ``(2,2,1)`` never occurs.

Exits non-zero on any failed assertion.
"""

from collections import defaultdict
from itertools import product

A, T = 0, 1


def revcomp(w):
    return tuple(1 - b for b in reversed(w))


def sb(w):
    return "".join("A" if b == 0 else "T" for b in w)


def mol_class(w):
    return min(w, revcomp(w))


# observed read molecules with fixed canonical representatives
CANON = {"AAA": (A, A, A), "AAT": (A, A, T), "TAA": (T, A, A)}
OBS = set(CANON.values())
KEYS = ["AAA", "AAT", "TAA"]


def strand_entry(name, q):
    """Strand traversed when a molecule is entered at port ``q`` (q=0 is the
    5' end of the canonical representative, q=1 the 5' end of its rc)."""
    w = CANON[name]
    return w if q == 0 else revcomp(w)


def directed_port_edges(length):
    """All directed port edges ``X.p -> Y.q`` of the given proper overlap
    length: exit port ``p`` of ``X`` and entry port ``q`` of ``Y``."""
    out = []
    for X in CANON:
        for Y in CANON:
            for p in (0, 1):
                for q in (0, 1):
                    su = strand_entry(X, 1 - p)
                    sv = strand_entry(Y, q)
                    if su[3 - length:] == sv[:length]:
                        out.append((X, p, Y, q))
    return out


def reducible(edge, length):
    """Myers-transitive.  For a proper overlap of length ``length`` to be
    spelled by two proper overlaps ``l1, l2 <= L-1`` we need
    ``length = l1 + l2 - L <= L - 2``; with L = 3 only ``length = 1`` can
    qualify.  A length-1 edge is reducible iff the middle window of its
    spelled 5-mer is an observed read."""
    if length > 1:
        return False
    X, p, Y, q = edge
    su = strand_entry(X, 1 - p)
    sv = strand_entry(Y, q)
    mol = su + sv[1:]
    return mol_class(tuple(mol[1:4])) in OBS


def build_walk_graph(edges):
    """State = (molecule, exit port).  Traversing an edge X.p -> Y.q enters Y
    at q and leaves at the other port, so the successor state is (Y, 1-q)."""
    adj = defaultdict(list)
    for (X, p, Y, q) in edges:
        adj[(X, p)].append(((Y, 1 - q), Y))
    return adj


def elementary_circuit_vectors(adj, maxlen=12):
    states = sorted(adj)
    idx = {s: i for i, s in enumerate(states)}
    seen = set()
    for start in states:
        def dfs(cur, vis, path):
            for (nxt, Y) in adj[cur]:
                if nxt == start:
                    tr = tuple((states.index(c), Y) for (c, Y) in path + [(cur, Y)])
                    if min(t[0] for t in tr) == idx[start]:
                        seen.add(tr)
                elif nxt not in vis and len(path) < maxlen:
                    dfs(nxt, vis + [nxt], path + [(cur, Y)])
        dfs(start, [start], [])
    vecs = set()
    for tr in seen:
        c = defaultdict(int)
        for (_, Y) in tr:
            c[Y] += 1
        vecs.add(tuple(c.get(k, 0) for k in KEYS))
    return vecs, seen


def monoid(gens, bound):
    reach = {(0, 0, 0)}
    changed = True
    while changed:
        changed = False
        for v in list(reach):
            for g in gens:
                w = tuple(a + b for a, b in zip(v, g))
                if sum(w) <= bound and w not in reach:
                    reach.add(w)
                    changed = True
    return reach


def class_spectrum(seq):
    g = len(seq)
    counts = defaultdict(int)
    for i in range(g):
        w = tuple(seq[(i + j) % g] for j in range(3))
        counts[mol_class(w)] += 1
    return tuple(counts.get(CANON[k], 0) for k in KEYS)


def all_single_molecule_spectra(maxlen=12):
    """Class spectra of all circular binary molecules up to length maxlen whose
    length-3 windows all have an observed class."""
    out = {}
    for g in range(1, maxlen + 1):
        for seq in product((A, T), repeat=g):
            spec = class_spectrum(seq)
            if all(c == 0 for c in spec):  # cannot happen, keep total
                continue
            # support check: every window class is observed
            ok = True
            for i in range(g):
                w = tuple(seq[(i + j) % g] for j in range(3))
                if mol_class(w) not in OBS:
                    ok = False
                    break
            if ok:
                out.setdefault(spec, sb(seq))
    return out


def main():
    # ---- 1. the instances -------------------------------------------------
    S = (A, A, A, T, T)          # AAATT
    D = (A, A, A, A, T, T)       # AAAATT
    assert class_spectrum(S) == (1, 2, 2), class_spectrum(S)
    assert class_spectrum(D) == (2, 2, 2), class_spectrum(D)

    # literal §6.1 product of binomials over the three observed classes,
    # external N = 5, n = 3, every x_w = 1
    from fractions import Fraction
    def lik(spec):
        out = Fraction(1)
        for x, d in zip((1, 1, 1), spec):
            out *= Fraction(d, 5) * (1 - Fraction(d, 5)) ** (3 - x)
        return out
    ratio = lik((2, 2, 2)) / lik((1, 2, 2))
    assert ratio == Fraction(9, 8), ratio

    # ---- 2. the port edges ------------------------------------------------
    e2 = directed_port_edges(2)
    e1 = directed_port_edges(1)
    assert len(e2) == 10, len(e2)
    assert len(e1) == 18, len(e1)

    # ---- 3. Myers transitive reduction ------------------------------------
    kept1 = [e for e in e1 if not reducible(e, 1)]
    assert len(kept1) == 2, kept1
    assert set(kept1) == {("AAT", 1, "TAA", 0), ("TAA", 0, "AAT", 1)}, kept1
    # no length-2 edge is reducible
    for e in e2:
        assert not reducible(e, 2), e

    reduced_edges = e2 + kept1
    unreduced_edges = e2 + e1

    # ---- 4./5. circulation cones -----------------------------------------
    adj_red = build_walk_graph(reduced_edges)
    cyc_red, _ = elementary_circuit_vectors(adj_red)
    assert all(v[1] == v[2] for v in cyc_red), cyc_red
    assert (1, 0, 0) in cyc_red and (0, 1, 1) in cyc_red, cyc_red
    M_red = monoid(cyc_red, 8)
    for a in range(0, 5):
        for k in range(0, 5):
            if a + 2 * k <= 8:
                assert (a, k, k) in M_red, (a, k, k)
    assert (2, 2, 1) not in M_red
    assert (1, 2, 2) in M_red and (2, 2, 2) in M_red

    adj_unred = build_walk_graph(unreduced_edges)
    cyc_unred, _ = elementary_circuit_vectors(adj_unred)
    M_unred = monoid(cyc_unred, 8)
    assert (2, 2, 1) in M_unred

    # ---- 6. sequence-level (single molecule) spectra ----------------------
    seqspecs = all_single_molecule_spectra(12)
    assert all(v[1] == v[2] for v in seqspecs), seqspecs
    assert (2, 2, 1) not in seqspecs
    assert (1, 2, 2) in seqspecs and (2, 2, 2) in seqspecs

    print("PASS: source §6.2 reduced-flow cone for reads {AAA,AAT,TAA}")
    print(f"  proper length-2 port edges      : {len(e2)}")
    print(f"  length-1 port edges             : {len(e1)}  (kept after reduction: {len(kept1)})")
    print(f"  survived edge                   : AAT.p1 -- TAA.p0")
    print(f"  reduced circulation generators  : (1,0,0), (0,1,1)  =>  d_AAT = d_TAA")
    print(f"  truth  (AAA,AAT,TAA) = (1,2,2)  : FEASIBLE")
    print(f"  rival  (AAA,AAT,TAA) = (2,2,2)  : FEASIBLE  (AAAATT)")
    print(f"  probe  (AAA,AAT,TAA) = (2,2,1)  : NOT feasible as a closed flow")
    print(f"        (feasible only if reducible length-1 edges are retained)")
    print(f"  §6.1 binomial ratio L(D)/L(S)   : {ratio}")


if __name__ == "__main__":
    main()
