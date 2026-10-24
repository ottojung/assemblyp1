#!/usr/bin/env python3
"""Exhaustive genome-derived rigidity sweep for issue #257.

Theorem 1 (ExactRigidityCriterion, kernel-checked): a positive integer
circulation A of total G on an oriented support (n nodes, m edges) is
non-rigid iff there is a nonzero integer delta with K*delta = 0
(K = incidence M stacked with the all-ones zero-sum row) and
A + delta >= 1 on every edge.

This script reimplements the incidence-kernel decider from scratch
(exact QQ-RREF, free-coordinate search over (2C+1)^d with C = G - m)
and cross-checks it against direct positive-circulation enumeration on
genome-derived instances: every circular word over {A, T} of length
1..9 and every circular word over {A, C, T} of length 1..7, for L = 2
and L = 3.  It additionally records:

  * rigid repetitive examples with an (L-1)-mer occurring >= 3 times
    (refuting necessity of the repeat-triple bound; the ATATAT/L=3
    directed-cycle instance is the smallest, and the (AT)^k family
    extends it);
  * a one-line sufficient condition (directed simple-cycle support is
    rigid) together with an explicit counterexample to its necessity
    (AATT/L=2 is rigid on a 4-edge support that is not a simple
    directed cycle);
  * a mutation-red control (shrinking the free-coordinate box to C-1
    misses a genuine witness).

Run: python3 scripts/verify_257_kernel_genome_sweep.py
Stdlib only, exact rational arithmetic, deterministic.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import product


def incidence_stacked(n, arcs):
    m = len(arcs)
    K = [[Fraction(0)] * m for _ in range(n + 1)]
    for j, (u, v) in enumerate(arcs):
        if u != v:
            K[u][j] += 1
            K[v][j] -= 1
    for j in range(m):
        K[n][j] = Fraction(1)
    return K


def rref_pivots(K):
    R = [row[:] for row in K]
    nrows, ncols = len(R), len(R[0]) if R else 0
    pivots = []
    r = 0
    for c in range(ncols):
        piv = None
        for i in range(r, nrows):
            if R[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        R[r], R[piv] = R[piv], R[r]
        inv = R[r][c]
        R[r] = [x / inv for x in R[r]]
        for i in range(nrows):
            if i != r and R[i][c] != 0:
                factor = R[i][c]
                R[i] = [a - factor * b for a, b in zip(R[i], R[r])]
        pivots.append(c)
        r += 1
        if r == nrows:
            break
    return R, pivots


def kernel_decider(n, arcs, A):
    """Return (rigid, witness_or_None) via the free-coordinate search."""
    m = len(arcs)
    G = sum(A)
    C = G - m
    K = incidence_stacked(n, arcs)
    R, pivots = rref_pivots(K)
    pset = set(pivots)
    free = [c for c in range(m) if c not in pset]
    prow = {p: k for k, p in enumerate(pivots)}
    for assign in product(range(-C, C + 1), repeat=len(free)):
        if not any(assign):
            continue
        delta = [Fraction(0)] * m
        for fcol, val in zip(free, assign):
            delta[fcol] = Fraction(val)
        for p, k in prow.items():
            delta[p] = -sum(R[k][f] * delta[f] for f in free)
        if any(x.denominator != 1 for x in delta):
            continue
        d = [int(x) for x in delta]
        if any(A[i] + d[i] < 1 for i in range(m)):
            continue
        return (False, tuple(d))
    return (True, None)


def compositions(G, m):
    """All m-tuples of positive ints summing to G (stars and bars)."""
    from itertools import combinations
    if m == 1:
        yield (G,)
        return
    for cuts in combinations(range(1, G), m - 1):
        prev, out = 0, []
        for c in cuts:
            out.append(c - prev)
            prev = c
        out.append(G - prev)
        yield tuple(out)


def circulations(n, arcs, G):
    """All positive integer circulations of total G (exact)."""
    m = len(arcs)
    out = [[] for _ in range(n)]
    inn = [[] for _ in range(n)]
    for j, (u, v) in enumerate(arcs):
        out[u].append(j)
        inn[v].append(j)
    res = []
    for B in compositions(G, m):
        if all(sum(B[j] for j in out[v]) == sum(B[j] for j in inn[v])
               for v in range(n)):
            res.append(B)
    return res


def direct_rigid(n, arcs, A):
    for B in circulations(n, arcs, sum(A)):
        if tuple(B) != tuple(A):
            return (False, tuple(B))
    return (True, None)


def genome_support(genome, L):
    G = len(genome)
    cyc = genome + genome[: L - 1]
    windows = [cyc[i: i + L] for i in range(G)]
    edges = sorted(set(windows))
    nodes = sorted(set(w[: L - 1] for w in edges) | set(w[1:] for w in edges))
    idx = {x: i for i, x in enumerate(nodes)}
    arcs = [(idx[w[: L - 1]], idx[w[1:]]) for w in edges]
    A = tuple(windows.count(w) for w in edges)
    return len(nodes), arcs, A, edges, windows


def is_simple_directed_cycle(n, arcs):
    m = len(arcs)
    if m != n:
        return False
    return all(sum(1 for (u, v) in arcs if u == x) == 1
               and sum(1 for (u, v) in arcs if v == x) == 1 for x in range(n))


def main():
    tested = rigid = nonrigid = mismatch = 0
    triple_rigid = []   # rigid despite an (L-1)-mer occurring >= 3 times
    witnesses = []      # (genome, L, A, delta) non-rigid examples
    seen_supports = set()
    words = []
    seen_words = set()
    for alpha in ("AT", "ACT"):
        maxlen = 9 if alpha == "AT" else 7
        for length in range(1, maxlen + 1):
            for w in product(alpha, repeat=length):
                s = "".join(w)
                # canonical rotation: circular genomes differing by
                # rotation give the same instance up to edge permutation
                canon = min(s[i:] + s[:i] for i in range(length))
                if canon not in seen_words:
                    seen_words.add(canon)
                    words.append(s)
    for genome in words:
        for L in (2, 3):
            if L > len(genome) and len(genome) < 3:
                pass  # genome_support handles wrap-around regardless
            n, arcs, A, edges, windows = genome_support(genome, L)
            m = len(arcs)
            G = sum(A)
            assert G == len(genome)
            key = (tuple(sorted(arcs)), A, n)
            r1, _ = direct_rigid(n, arcs, A)
            r2, w2 = kernel_decider(n, arcs, A)
            tested += 1
            rigid += r1
            nonrigid += (not r1)
            if r1 != r2:
                mismatch += 1
                print("  MISMATCH", genome, L, edges, A, r1, r2)
            if r2 and w2 is not None:
                raise AssertionError("kernel decider returned witness "
                                     "but claims rigid")
            if not r2 and w2 is not None:
                assert any(w2) and sum(w2) == 0
                assert all(A[i] + w2[i] >= 1 for i in range(m))
            if r1 and key not in seen_supports:
                seen_supports.add(key)
                # count (L-1)-mer occurrences along the circular genome
                cyc = genome + genome[: L - 1]
                kmers = [cyc[i: i + L - 1] for i in range(len(genome))]
                if any(kmers.count(k) >= 3 for k in set(kmers)):
                    triple_rigid.append((genome, L, A, edges))
            if (not r1) and len(witnesses) < 8 and key not in seen_supports:
                seen_supports.add(key)
                witnesses.append((genome, L, A, w2))
    print(f"genome sweep: words={len(words)} tested={tested} rigid={rigid} "
          f"nonrigid={nonrigid} mismatches={mismatch}")
    assert mismatch == 0 and tested > 0

    # The rigid-repetitive family: (AT)^k with L=3 is a directed 2-cycle.
    for k in (3, 4, 5, 6):
        genome = "AT" * k
        n, arcs, A, edges, _ = genome_support(genome, 3)
        r, _ = kernel_decider(n, arcs, A)
        rd, _ = direct_rigid(n, arcs, A)
        cyc = genome + genome[:2]
        kmers = [cyc[i: i + 2] for i in range(len(genome))]
        rep = max(kmers.count(x) for x in set(kmers))
        print(f"(AT)^{k} L=3: A={A} rigid={r}/{rd} max-2mer-count={rep}")
        assert r and rd and rep >= 3

    # Sufficient-but-not-necessary: directed simple-cycle support => rigid.
    n, arcs, A, edges, _ = genome_support("ATATAT", 3)
    assert is_simple_directed_cycle(n, arcs)
    r, _ = kernel_decider(n, arcs, A)
    assert r
    # Necessity fails: AATT/L=2 is rigid but not a simple directed cycle.
    n0, arcs0, A0, edges0, _ = genome_support("AATT", 2)
    assert not is_simple_directed_cycle(n0, arcs0), edges0
    r0, _ = kernel_decider(n0, arcs0, A0)
    rd0, _ = direct_rigid(n0, arcs0, A0)
    print(f"AATT L=2: edges={edges0} A={A0} rigid={r0}/{rd0} "
          f"simple-cycle={is_simple_directed_cycle(n0, arcs0)}")
    assert r0 and rd0

    print(f"rigid-with-triple-repeat instances: {len(triple_rigid)} "
          f"(e.g. {triple_rigid[:3]})")
    assert len(triple_rigid) > 0
    for genome, L, A, w2 in witnesses:
        print(f"non-rigid witness: {genome} L={L} A={A} delta={w2}")

    # Mutation-red control: C-1 box misses a genuine witness.
    es = ((0, 0), (1, 1))
    A3 = (2, 1)
    r3, _ = kernel_decider(2, es, A3)
    assert not r3
    K = incidence_stacked(2, es)
    R, piv = rref_pivots(K)
    free = [c for c in range(2) if c not in set(piv)]
    found = any(any(a) for a in product(range(0, 1), repeat=len(free)))
    assert not found, "C-1 box should admit no nonzero assignment here"
    print("mutation control: C-1 coefficient box misses figure-eight "
          "witness (detected)")


if __name__ == "__main__":
    main()
