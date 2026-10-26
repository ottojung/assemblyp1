#!/usr/bin/env python3
"""Exhaustively check the support-agnostic slack bound for issue #257.

For positive integer circulations A,B on m edges with equal total G, every
coordinate of delta=B-A lies in [-(G-m), G-m]. Compare direct alternative-
circulation enumeration with bounded-delta enumeration on small supports.
"""
from itertools import product


def supports(n):
    arcs = [(u, v) for u in range(n) for v in range(n) if u != v]
    for mask in range(1, 1 << len(arcs)):
        es = tuple(arcs[i] for i in range(len(arcs)) if mask >> i & 1)
        r = [[i == j for j in range(n)] for i in range(n)]
        for u, v in es:
            r[u][v] = True
        for k in range(n):
            for i in range(n):
                for j in range(n):
                    r[i][j] |= r[i][k] and r[k][j]
        if all(r[i][j] for i in range(n) for j in range(n)):
            yield es


def circulations(n, es, G):
    for a in product(range(1, G + 1), repeat=len(es)):
        if sum(a) == G and all(
            sum(a[i] for i, e in enumerate(es) if e[0] == v)
            == sum(a[i] for i, e in enumerate(es) if e[1] == v)
            for v in range(n)
        ):
            yield a


def deltas(n, es, A, bound):
    for d in product(range(-bound, bound + 1), repeat=len(es)):
        if not any(d) or sum(d) or any(A[i] + d[i] < 1 for i in range(len(es))):
            continue
        if all(
            sum(d[i] for i, e in enumerate(es) if e[0] == v)
            == sum(d[i] for i, e in enumerate(es) if e[1] == v)
            for v in range(n)
        ):
            yield d


def main():
    tested = 0
    for n in (2, 3):
        for es in supports(n):
            m = len(es)
            if m > 5:
                continue
            for G in range(m, min(2 * m, 8) + 1):
                for A in circulations(n, es, G):
                    direct = any(B != A for B in circulations(n, es, G))
                    bounded = any(deltas(n, es, A, G - m))
                    assert direct == bounded, (n, es, G, A, direct, bounded)
                    tested += 1
    # Mutation: reducing C to C-1 incorrectly rejects this valid transfer.
    # Two self-loops have A=(2,1), G=3, m=2, hence C=1; B=(1,2).
    es, A = ((0, 0), (1, 1)), (2, 1)
    assert any(deltas(2, es, A, 1)) and not any(deltas(2, es, A, 0))
    print(f"slack-bound: {tested} instances, 0 mismatches")
    print("mutation control: C-1 misses figure-eight witness (detected)")


if __name__ == "__main__":
    main()
