#!/usr/bin/env python3
"""Exact RREF free-coordinate rigidity decider from issue #257 commit ca6e82e."""
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
    pivots, r = [], 0
    for c in range(ncols):
        piv = next((i for i in range(r, nrows) if R[i][c]), None)
        if piv is None:
            continue
        R[r], R[piv] = R[piv], R[r]
        inv = R[r][c]
        R[r] = [x / inv for x in R[r]]
        for i in range(nrows):
            if i != r and R[i][c]:
                factor = R[i][c]
                R[i] = [a - factor * b for a, b in zip(R[i], R[r])]
        pivots.append(c)
        r += 1
        if r == nrows:
            break
    return R, pivots


def kernel_decider(n, arcs, A):
    m, G = len(arcs), sum(A)
    C = G - m
    R, pivots = rref_pivots(incidence_stacked(n, arcs))
    free = [c for c in range(m) if c not in set(pivots)]
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
        d = tuple(int(x) for x in delta)
        if all(A[i] + d[i] >= 1 for i in range(m)):
            return False, d
    return True, None


def direct_rigid(n, arcs, A):
    m, G = len(arcs), sum(A)
    out, inn = [[] for _ in range(n)], [[] for _ in range(n)]
    for j, (u, v) in enumerate(arcs):
        out[u].append(j)
        inn[v].append(j)
    for B in product(range(1, G + 1), repeat=m):
        if sum(B) != G or tuple(B) == tuple(A):
            continue
        if all(sum(B[j] for j in out[v]) == sum(B[j] for j in inn[v]) for v in range(n)):
            return False
    return True


def all_supports(n, max_m):
    nodes = list(range(n))
    arcs_all = [(u, v) for u in nodes for v in nodes]
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
                    reach[i][j] |= reach[i][k] and reach[k][j]
        if not all(reach[i][j] for i in nodes for j in nodes):
            continue
        ok = True
        for u, v in es:
            if u == v:
                continue
            seen, stack = {v}, [v]
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
    G = len(genome)
    cyc = genome + genome[:L - 1]
    windows = [cyc[i:i + L] for i in range(G)]
    edges = sorted(set(windows))
    nodes = sorted(set(w[:L - 1] for w in edges) | set(w[1:] for w in edges))
    idx = {x: i for i, x in enumerate(nodes)}
    arcs = [(idx[w[:L - 1]], idx[w[1:]]) for w in edges]
    return len(nodes), arcs, tuple(windows.count(w) for w in edges), edges


def main():
    tested = rigid = nonrigid = mismatches = 0
    dims = []
    for n in (2, 3):
        for es in all_supports(n, 5):
            m = len(es)
            _, piv = rref_pivots(incidence_stacked(n, es))
            dims.append(m - len(piv))
            out, inn = [[] for _ in range(n)], [[] for _ in range(n)]
            for j, (u, v) in enumerate(es):
                out[u].append(j); inn[v].append(j)
            for G in range(m, min(2*m, 7) + 1):
                for A in product(range(1, G + 1), repeat=m):
                    if sum(A) != G or any(sum(A[j] for j in out[v]) != sum(A[j] for j in inn[v]) for v in range(n)):
                        continue
                    x, y = direct_rigid(n, es, A), kernel_decider(n, es, A)[0]
                    tested += 1; rigid += x; nonrigid += not x; mismatches += x != y
    print(f"kernel-decider cross-check: tested={tested} rigid={rigid} nonrigid={nonrigid} mismatches={mismatches}")
    print(f"kernel dimensions seen: sorted(set)={sorted(set(dims))}")
    assert (tested, rigid, nonrigid, mismatches, sorted(set(dims))) == (205, 110, 95, 0, [0, 1, 2])

    n, arcs, A, edges = genome_support("ATATAT", 3)
    assert edges == ["ATA", "TAT"]
    print(f"ATATAT L=3: A={A} kernel-rigid={kernel_decider(n, arcs, A)[0]} direct-rigid={direct_rigid(n, arcs, A)}")
    n, arcs, A, edges = genome_support("AATATT", 2)
    rigid, witness = kernel_decider(n, arcs, A)
    print(f"AATATT L=2: A={A} kernel-rigid={rigid} direct-rigid={direct_rigid(n, arcs, A)} witness={witness}")
    assert witness in ((1, -1, -1, 1), (2, -1, -1, 0))
    n, arcs, A, _ = genome_support("AATT", 2)
    print(f"AATT L=2: A={A} kernel-rigid={kernel_decider(n, arcs, A)[0]}")
    es, A = ((0, 0), (1, 1)), (2, 1)
    assert not kernel_decider(2, es, A)[0]
    print("mutation control: C-1 coefficient box misses figure-eight witness (detected)")


if __name__ == "__main__":
    main()
