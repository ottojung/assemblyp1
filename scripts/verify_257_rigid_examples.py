#!/usr/bin/env python3
"""Issue #257: kernel-criterion cross-check with one non-rigid and one
rigid-repetitive L-mer example, plus exhaustive agreement scan over short
binary circular genomes.

Exact criterion (Theorem 1 in docs/source-notes/issue-257-rigid-read-graphs.md):
  A is RIGID  <=>  no nonzero integral delta with M*delta = 0 (incidence
  kernel / flow conservation at every (L-1)-mer vertex), sum(delta) = 0
  (same total length G), and A + delta >= 1 on every support edge
  (the alternative circulation stays strictly positive on the support).

  A is NON-RIGID <=> such a delta witness exists.

Example 1 (NON-RIGID): S = AATATT, L = 2.
  Circular 2-mer counts: A = {AA:1, AT:2, TA:2, TT:1}, G = 6.
  Support vertices (1-mers): {A, T}. Loops AA, TT are conservation-neutral.
  Witness delta = (AA:+1, AT:-1, TA:-1, TT:+1):
    vertex A: in(TA) - out(AT) = -1 - (-1) = 0
    vertex T: in(AT) - out(TA) = -1 - (-1) = 0
    sum(delta) = 0,  A + delta = (2,1,1,2) >= 1 everywhere.
  Hence B = (2,1,1,2) is a second positive circulation of total 6:
  NON-RIGID.

Example 2 (RIGID REPETITIVE): S = ATATAT, L = 3.
  Circular 3-mer counts: A = {ATA:3, TAT:3}, G = 6.
  Support: vertices {AT, TA}, edges ATA: AT->TA, TAT: TA->AT (directed 2-cycle).
  ker(M) = span((1,1)); any delta = (t,t) has sum 2t = 0 forcing t = 0.
  Hence RIGID, even though both (L-1)-mers AT and TA occur 3x each.
  This refutes necessity of the "no length-(L-1) triple" hypothesis:
  that repeat bound is sufficient but NOT necessary.

FAILED SIMPLER HYPOTHESIS (recorded as required by #257):
  H: "A is rigid IFF no length-(L-1) word occurs >= 3 times."
  H is FALSE as an iff: Example 2 is rigid with two distinct triples.
  (Sufficiency direction is not disputed here.)

CANDIDATE GRAPH-THEORETIC CERTIFICATE -- STATUS: CONJECTURE (not proved):
  (C1) Chord-parametrized box feasibility: fix a spanning forest of the
  support; every circulation delta is determined by its values on the
  c = |E|-|V|+components chord edges; rigidity is equivalent to
  infeasibility of the box-constrained integer system on chords
  (M*delta = 0 rewritten in chord coordinates, sum = 0, 1-A <= delta).
  Whether this admits a polynomial min-cut/max-flow closed form for
  arbitrary explicitly represented supports is OPEN; the direct rational/LP
  relaxation is already known unsound (merged coin/LP no-go). C1 is an
  exact restatement of Theorem 1, NOT a proved graph-structural simplification.

LEAN LEMMA STATEMENT (for later Lean work, not formalized here):
  lemma rigid_iff_no_admissible_delta (M : Matrix V E Z) (A : E -> N)
    (hA : forall e in support, A e >= 1) :
    Rigid M A  <->  ~(exists delta : E -> Z,
      (forall v, sum_e M v e * delta e = 0) /\
      (sum_e delta e = 0) /\ delta != 0 /\
      (forall e in support, (A e : Z) + delta e >= 1)).
  Non-rigidity witness: provides delta above for Example 1.
  Rigid instance: Example 2 with M = !![1,-1;-1,1], A = ![3,3].
"""
from collections import Counter
from itertools import product

ALPH = "AT"


def circ_counts(S, L):
    n = len(S)
    return Counter("".join(S[(i + k) % n] for k in range(L)) for i in range(n))


def support_graph(counts, L):
    edges = sorted(counts.keys())
    verts = sorted({e[: L - 1] for e in edges} | {e[1:] for e in edges})
    return verts, edges


def balanced(vec, verts, edges, L):
    bal = {v: 0 for v in verts}
    for e in edges:
        u, w = e[: L - 1], e[1:]
        if u == w:
            continue  # loop: conservation-neutral
        bal[u] -= vec[e]
        bal[w] += vec[e]
    return all(v == 0 for v in bal.values())


def positive_circulations(verts, edges, L, G):
    """All B in [1,G]^E with sum G that are balanced."""
    out = []
    for tup in product(range(1, G + 1), repeat=len(edges)):
        if sum(tup) != G:
            continue
        vec = dict(zip(edges, tup))
        if balanced(vec, verts, edges, L):
            out.append(vec)
    return out


def rigidity_bruteforce(counts, L):
    verts, edges = support_graph(counts, L)
    A = {e: counts[e] for e in edges}
    G = sum(A.values())
    circs = positive_circulations(verts, edges, L, G)
    assert any(all(c[e] == A[e] for e in edges) for c in circs), "A must be a circulation"
    others = [c for c in circs if any(c[e] != A[e] for e in edges)]
    return (len(others) == 0, A, G, verts, edges, others)


def kernel_witness_search(counts, L):
    """Search nonzero delta in ker(M), sum 0, A+delta >= 1. Returns witness or None."""
    verts, edges = support_graph(counts, L)
    A = {e: counts[e] for e in edges}
    G = sum(A.values())
    lo = {e: 1 - A[e] for e in edges}
    ranges = [range(lo[e], G) for e in edges]
    for tup in product(*ranges):
        d = dict(zip(edges, tup))
        if all(v == 0 for v in tup):
            continue
        if sum(tup) != 0:
            continue
        if not balanced(d, verts, edges, L):
            continue
        return d
    return None


def check_example(S, L, expect_rigid):
    counts = circ_counts(S, L)
    rigid, A, G, verts, edges, others = rigidity_bruteforce(counts, L)
    wit = kernel_witness_search(counts, L)
    assert rigid == expect_rigid, f"{S}: bruteforce rigid={rigid}, expected {expect_rigid}"
    assert (wit is None) == expect_rigid, f"{S}: witness/rigidity disagree"
    return counts, A, G, verts, edges, others, wit


def main():
    # Worked examples from the docstring.
    c1, A1, G1, v1, e1, o1, w1 = check_example("AATATT", 2, False)
    print(f"Ex1 S=AATATT L=2: A={dict(sorted(A1.items()))} G={G1} NON-RIGID")
    print(f"  witness delta={dict(sorted(w1.items()))}")
    print(f"  alternative B={dict(sorted(o1[0].items()))} total={sum(o1[0].values())}")
    assert dict(sorted(c1.items())) == {"AA": 1, "AT": 2, "TA": 2, "TT": 1}
    # Canonical witness from the docstring, checked directly (the search may
    # return a different valid witness first, e.g. (0,-1,-1,2)).
    canon = {"AA": 1, "AT": -1, "TA": -1, "TT": 1}
    assert sum(canon.values()) == 0 and balanced(canon, v1, e1, 2)
    assert all(A1[e] + canon[e] >= 1 for e in e1)

    c2, A2, G2, v2, e2, o2, w2 = check_example("ATATAT", 3, True)
    print(f"Ex2 S=ATATAT L=3: A={dict(sorted(A2.items()))} G={G2} RIGID")
    trips = {w: c for w, c in circ_counts("ATATAT", 2).items() if c >= 3}
    print(f"  (L-1)-mer counts with >=3 occurrences: {dict(sorted(trips.items()))} (necessity refuted)")
    assert dict(sorted(c2.items())) == {"ATA": 3, "TAT": 3}
    assert trips == {"AT": 3, "TA": 3}

    # Exhaustive agreement: brute-force rigidity vs kernel-witness search,
    # all binary circular genomes of length 2..6, L in {2, 3}.
    total = rigid_n = triple_rigid_n = 0
    mism = 0
    for n in range(2, 7):
        for tup in product(ALPH, repeat=n):
            S = "".join(tup)
            for L in (2, 3):
                if L > n:
                    continue
                counts = circ_counts(S, L)
                rigid, *_ = rigidity_bruteforce(counts, L)
                wit = kernel_witness_search(counts, L)
                total += 1
                rigid_n += rigid
                if rigid != (wit is None):
                    mism += 1
                    print(f"  MISMATCH S={S} L={L}")
                if rigid:
                    sub = circ_counts(S, L - 1)
                    if any(c >= 3 for c in sub.values()):
                        triple_rigid_n += 1
    print(f"exhaustive: {total} (S,L) cases, {rigid_n} rigid, {mism} mismatches")
    print(f"  rigid cases WITH an (L-1)-mer triple: {triple_rigid_n} (further necessity-refuting instances)")
    assert mism == 0, "criterion/witness-search disagreement"
    assert triple_rigid_n >= 1
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
