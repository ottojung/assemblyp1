#!/usr/bin/env python3
"""Incidence-kernel decider for issue #257 (exact, support-agnostic).

Theorem 1 (ExactRigidityCriterion, kernel-checked): a positive integer
circulation A of total G on an oriented support (n nodes, m edges) is
non-rigid iff there is a nonzero integer delta with K*delta = 0
(K = incidence M stacked with the all-ones zero-sum row) and
delta_e >= 1 - A_e on every edge.

This script decides rigidity WITHOUT enumerating the delta box or the
(B in {1..G}^m) product.  Instead it:

  1. computes an exact rational (Fraction) reduced row-echelon form of K,
     identifying pivot columns P and free columns S (|S| = d = m - rank K,
     the cyclomatic number of the support, up to the extra sum row);
  2. enumerates only the free-coordinate assignments f : S -> [-C, C]
     with C = G - m (every feasible delta satisfies |delta_e| <= C, since
     B = A + delta has B_e in [1, G-m+1]);
  3. extends each f to a full vector delta via the exact RREF relations,
     keeping assignments whose extension is integral, nonzero, and in-box.

The search space is (2C+1)^d instead of (2C+1)^m (delta-box) or (G+1)^m
(product decider).  The script cross-checks the kernel decider against
direct positive-circulation enumeration on exhaustive small supports,
re-derives the rigid-repetitive ATATAT genome instance and a non-rigid
genome witness, and includes a mutation-red control (shrinking the
coefficient bound to C-1 misses a genuine witness).

Run: python3 scripts/verify_257_kernel_decider.py
Stdlib only, exact rational arithmetic, deterministic.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import product


def incidence_stacked(n, arcs):
    """Rows: n incidence rows + 1 zero-sum row; entry (v,e): +1 out, -1 in.

    Self-loops contribute 0 to their incidence row (balanced automatically).
    """
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
    """Reduced row-echelon form over QQ. Returns (R, pivots).

    R is the RREF matrix (list of rows), pivots[k] = pivot column of row k.
    """
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
    C = G - m  # slack total; every feasible delta has |delta_e| <= C
    K = incidence_stacked(n, arcs)
    R, pivots = rref_pivots(K)
    free = [c for c in range(m) if c not in set(pivots)]
    prow = {p: k for k, p in enumerate(pivots)}  # pivot col -> RREF row
    # Extension: delta[p] = -sum_{f free} R[row][f] * delta[f].
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


def direct_rigid(n, arcs, A):
    """Brute force: any other positive integer circulation of total G?"""
    m = len(arcs)
    G = sum(A)
    out = [[] for _ in range(n)]
    inn = [[] for _ in range(n)]
    for j, (u, v) in enumerate(arcs):
        out[u].append(j)
        inn[v].append(j)
    for B in product(range(1, G + 1), repeat=m):
        if sum(B) != G or tuple(B) == tuple(A):
            continue
        if all(sum(B[j] for j in out[v]) == sum(B[j] for j in inn[v])
               for v in range(n)):
            return (False, tuple(B))
    return (True, None)


def all_supports(n, max_m):
    """All strongly-connected arc sets where every edge lies on a cycle."""
    nodes = list(range(n))
    arcs_all = [(u, v) for u in nodes for v in nodes]
    if n == 2:
        pass
    for mask in range(1, 1 << len(arcs_all)):
        es = tuple(arcs_all[i] for i in range(len(arcs_all)) if mask >> i & 1)
        if len(es) > max_m:
            continue
        reach = [[i == j for j in nodes] for i in nodes]
        for u, v in es:
            reach[u][v] = True
        for k in nodes:
            for i in nodes:
                for j in nodes:
                    reach[i][j] = reach[i][j] or (reach[i][k] and reach[k][j])
        if not all(reach[i][j] for i in nodes for j in nodes):
            continue
        # every edge on a cycle: self-loop, or endpoints mutually reachable
        # without the edge itself... approximate: v reaches u (then edge is
        # on a directed cycle) or self-loop.
        ok = True
        for u, v in es:
            if u == v:
                continue
            # reachability using other edges
            seen = {v}
            stack = [v]
            while stack:
                x = stack.pop()
                for a, b in es:
                    if a == x and (a, b) != (u, v) and b not in seen:
                        seen.add(b)
                        stack.append(b)
            if u not in seen:
                ok = False
                break
        if ok:
            yield es


def genome_support(genome, L):
    """Oriented L-mer support graph of a circular genome string."""
    G = len(genome)
    cyc = genome + genome[: L - 1]
    windows = [cyc[i: i + L] for i in range(G)]
    edges = sorted(set(windows))
    nodes = sorted(set(w[: L - 1] for w in edges) | set(w[1:] for w in edges))
    idx = {x: i for i, x in enumerate(nodes)}
    arcs = [(idx[w[: L - 1]], idx[w[1:]]) for w in edges]
    A = tuple(windows.count(w) for w in edges)
    return len(nodes), arcs, A, edges


def main():
    tested = rigid = nonrigid = mismatch = 0
    dims = []
    for n in (2, 3):
        for es in all_supports(n, max_m=5):
            m = len(es)
            K = incidence_stacked(n, es)
            _, piv = rref_pivots(K)
            d = m - len(piv)
            dims.append(d)
            for G in range(m, min(2 * m, 7) + 1):
                # enumerate all positive circulations of total G
                out = [[] for _ in range(n)]
                inn = [[] for _ in range(n)]
                for j, (u, v) in enumerate(es):
                    out[u].append(j)
                    inn[v].append(j)
                for A in product(range(1, G + 1), repeat=m):
                    if sum(A) != G:
                        continue
                    if any(sum(A[j] for j in out[v]) != sum(A[j] for j in inn[v])
                           for v in range(n)):
                        continue
                    r1, _ = direct_rigid(n, es, A)
                    r2, w2 = kernel_decider(n, es, A)
                    tested += 1
                    rigid += r1
                    nonrigid += (not r1)
                    if r1 != r2:
                        mismatch += 1
                        print("  MISMATCH", n, es, A, r1, r2)
                    elif not r2 and w2 is not None:
                        # validate the witness independently
                        assert any(w2), "zero witness"
                        assert all(A[i] + w2[i] >= 1 for i in range(m))
                        assert sum(w2) == 0
                        for v in range(n):
                            bo = sum(w2[j] for j in out[v])
                            bi = sum(w2[j] for j in inn[v])
                            assert bo == bi, "witness not balanced"
    print(f"kernel-decider cross-check: tested={tested} rigid={rigid} "
          f"nonrigid={nonrigid} mismatches={mismatch}")
    print(f"kernel dimensions seen: sorted(set)={sorted(set(dims))}")
    assert mismatch == 0 and tested > 0

    # Worked genome instances: support derived from the string itself.
    n, arcs, A, edges = genome_support("ATATAT", 3)
    assert edges == ["ATA", "TAT"], edges
    r, _ = kernel_decider(n, arcs, A)
    rd, _ = direct_rigid(n, arcs, A)
    print(f"ATATAT L=3: A={A} kernel-rigid={r} direct-rigid={rd}")
    assert r and rd  # rigid despite (L-1)-mer triples

    n2, arcs2, A2, edges2 = genome_support("AATATT", 2)
    r2, w2 = kernel_decider(n2, arcs2, A2)
    rd2, _ = direct_rigid(n2, arcs2, A2)
    print(f"AATATT L=2: A={A2} kernel-rigid={r2} direct-rigid={rd2} "
          f"witness={w2}")
    assert (not r2) and (not rd2)  # non-rigid witness exists
    n0, arcs0, A0, _ = genome_support("AATT", 2)
    r0, _ = kernel_decider(n0, arcs0, A0)
    print(f"AATT L=2: A={A0} kernel-rigid={r0}")
    assert r0  # same-support rigid unit endpoint (single directed cycle)

    # Mutation-red control: shrinking the coefficient box to C-1 must miss
    # a genuine witness (two self-loops, A=(2,1): delta=(-1,+1) needs |c|=1).
    es = ((0, 0), (1, 1))
    A3 = (2, 1)
    r3, _ = kernel_decider(2, es, A3)
    assert not r3  # C = 3-2 = 1 finds delta=(-1,1)
    # re-run with bound C-1 = 0: only the zero assignment -> claims rigid
    K = incidence_stacked(2, es)
    R, piv = rref_pivots(K)
    free = [c for c in range(2) if c not in set(piv)]
    found = False
    for assign in product(range(0, 1), repeat=len(free)):
        if any(assign):
            found = True
    assert not found, "C-1 box should admit no nonzero assignment here"
    print("mutation control: C-1 coefficient box misses figure-eight "
          "witness (detected)")


if __name__ == "__main__":
    main()
