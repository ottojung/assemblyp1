#!/usr/bin/env python3
"""Exact incidence-matrix perturbation witnesses for Issue #257.

All arithmetic is integral. The checker verifies balance, zero total, the
lower box bound delta >= 1-A, and that the resulting circulation differs.
It also cross-checks the same examples by exhaustive feasible-flow counting.
"""

from itertools import product


def check(edges, A, delta):
    vertices = sorted({v for edge in edges for v in edge})
    assert len(edges) == len(A) == len(delta)
    divergence = {v: 0 for v in vertices}
    for (u, v), a, d in zip(edges, A, delta):
        divergence[u] += d
        divergence[v] -= d
        assert a + d >= 1, (a, d)
    assert all(x == 0 for x in divergence.values()), divergence
    assert sum(delta) == 0
    assert any(delta)
    B = tuple(a + d for a, d in zip(A, delta))
    assert sum(B) == sum(A)
    return B


def candidates(edges, A):
    vertices = sorted({v for e in edges for v in e})
    answer = []
    for B in product(range(1, sum(A) + 1), repeat=len(edges)):
        if sum(B) != sum(A):
            continue
        div = {v: 0 for v in vertices}
        for (u, v), b in zip(edges, B):
            div[u] += b
            div[v] -= b
        if all(x == 0 for x in div.values()):
            answer.append(B)
    return answer


def main():
    # Same directed figure-eight support, two different multiplicity vectors.
    fig8 = [(0, 1), (1, 0), (0, 2), (2, 0)]
    A = (2, 2, 1, 1)
    delta = (-1, -1, 1, 1)
    B = check(fig8, A, delta)
    assert B == (1, 1, 2, 2)
    assert len(candidates(fig8, (1, 1, 1, 1))) == 1
    assert len(candidates(fig8, A)) > 1
    print(f"figure-eight witness: A={A}, delta={delta}, B={B}; same support rigid at unit flow, non-rigid at A")

    # Genuine repetitive genome with multi-cycle support: AATT, L=2. Edge
    # order AA, AT, TT, TA. At unit multiplicity, total=|E| forces uniqueness.
    # Verify the alternative multiplicity vector has an explicit signed trade.
    aatt = [("A", "A"), ("A", "T"), ("T", "T"), ("T", "A")]
    # Increase the two loops, then transfer one unit from each loop to the
    # corresponding cross-edge, preserving both vertex balances and total.
    A2 = (2, 1, 2, 1)
    delta2 = (-1, 1, -1, 1)
    B2 = check(aatt, A2, delta2)
    assert B2 == (1, 2, 1, 2)
    assert len(candidates(aatt, A2)) > 1
    print(f"AATT L=2 witness: A={A2}, delta={delta2}, B={B2}")

    # Rigid repetitive example with genuine multi-cycle support.
    assert len(candidates(aatt, (1, 1, 1, 1))) == 1
    print("AATT L=2 rigid repetitive control: all four distinct 2-mers occur once")
    print("RESULT: exact incidence witnesses and exhaustive checks passed")


if __name__ == "__main__":
    main()
