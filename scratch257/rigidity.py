"""Brute-force rigidity checker for positive circulations on directed graphs.

A directed graph D = (V, E) with a positive integer circulation A (total G).
Rigid  <=>  A is the UNIQUE positive integer circulation of total G on D.

Equivalent (exact):  NOT rigid  <=>  exists d in Z^E, d != 0, with
    M d = 0  (balanced),  sum(d) = 0,  d >= 1 - A  (componentwise).

We enumerate positive circulations B of total G directly by backtracking,
using the balance equations as pruning constraints.
"""
from itertools import product


def edges_of(n, arcs):
    """arcs: list of (u, v) with 0 <= u,v < n. Returns list of (u,v)."""
    return list(arcs)


def out_in(n, arcs):
    out = [[] for _ in range(n)]
    inn = [[] for _ in range(n)]
    for i, (u, v) in enumerate(arcs):
        out[u].append(i)
        inn[v].append(i)
    return out, inn


def enum_positive_circulations(n, arcs, G, cap=60):
    """Enumerate all B: E -> Z, B >= 1, balanced, sum = G. Yields tuples."""
    out, inn = out_in(n, arcs)
    m = len(arcs)
    B = [0] * m

    # order edges; backtrack with pruning on vertex balance
    # feasible remaining range per edge given current partial assignment
    def rec(i, remaining):
        if i == m:
            # check all balances exactly
            for v in range(n):
                if sum(B[e] for e in out[v]) != sum(B[e] for e in inn[v]):
                    return
            if remaining == 0:
                yield tuple(B)
            return
        # pruning: remaining edges must be able to satisfy balance
        lo = 1
        hi = remaining - (m - i - 1)  # each later edge needs >= 1
        if hi < lo:
            return
        hi = min(hi, cap)
        for val in range(lo, hi + 1):
            B[i] = val
            yield from rec(i + 1, remaining - val)
        B[i] = 0

    yield from rec(0, G)


def is_rigid(n, arcs, A):
    """A: list of positive ints (the circulation). Returns (rigid, witnesses)."""
    G = sum(A)
    wit = []
    for B in enum_positive_circulations(n, arcs, G):
        if tuple(A) != B:
            wit.append(B)
            if len(wit) >= 3:
                break
    return (len(wit) == 0), wit


def kernel_zero_sum_search(n, arcs, A):
    """Directly search for nonzero d with M d = 0, sum d = 0, d >= 1 - A.
    Uses bound |d(e)| <= G - |E|. Returns a witness d or None."""
    m = len(arcs)
    G = sum(A)
    bound = G - m
    if bound < 0:
        return None
    out, inn = out_in(n, arcs)
    # ranges
    ranges = [range(1 - A[e], bound + 1) for e in range(m)]
    for d in product(*ranges):
        if all(x == 0 for x in d):
            continue
        if sum(d) != 0:
            continue
        ok = True
        for v in range(n):
            if sum(d[e] for e in out[v]) != sum(d[e] for e in inn[v]):
                ok = False
                break
        if ok:
            return d
    return None


if __name__ == "__main__":
    # sanity: 3-cycle, A = (2,2,2), G=6 -> rigid
    arcs = [(0, 1), (1, 2), (2, 0)]
    A = [2, 2, 2]
    rigid, wit = is_rigid(3, arcs, A)
    print("3-cycle A=(2,2,2): rigid =", rigid, "witnesses:", wit)
    # A = (1,1,1), G=3 -> rigid (only B=(1,1,1))
    rigid2, wit2 = is_rigid(3, arcs, [1, 1, 1])
    print("3-cycle A=(1,1,1): rigid =", rigid2, "witnesses:", wit2)
    # two disjoint 3-cycles, A = (1,1,1,1,1,1): move flow -> non-rigid
    arcs2 = [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)]
    rigid3, wit3 = is_rigid(6, arcs2, [1, 1, 1, 1, 1, 1])
    print("two 3-cycles A=all1: rigid =", rigid3, "witnesses:", wit3)
    # ATATAT: 2 vertices, edges ATA (0->1), TAT (1->0); A=(3,3) G=6 -> rigid
    rigid4, wit4 = is_rigid(2, [(0, 1), (1, 0)], [3, 3])
    print("ATATAT 2-cycle A=(3,3): rigid =", rigid4, "witnesses:", wit4)
