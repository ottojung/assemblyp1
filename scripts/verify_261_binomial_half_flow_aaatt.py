#!/usr/bin/env python3
"""Exact small-instance check of the fixed-N binomial half-flow gap (#261).

This reconstructs the two integral AAATT flow maximizers and their midpoint in
the four used edges of the stated o_min=1 flow witness.  It checks edgewise
nonnegativity, signed incidence balance, vertex lower bounds, the induced
throughputs, and the full product-binomial ratio using rational arithmetic.
The midpoint is a feasible *flow*, not merely a feasible throughput vector.

The graph/reduction remains the explicitly stated project witness model; this
script does not establish source-faithful transitive-reduction equivalence.
"""
from fractions import Fraction as Q


# Edge order: AAA->AAA self-loop, AAA->AAT, AAT->TAA (overlap 1),
# TAA->AAA.  Incidence signs in this project representation are (+1,-1).
EDGES = ((0, 0), (0, 1), (1, 2), (2, 0))
SIGNS = ((1, -1), (1, -1), (1, -1), (1, -1))
VERTICES = (0, 1, 2)  # AAA, AAT, TAA
OBS = {0: 2, 1: 1, 2: 1}
EXTERNAL_N = 5


def throughput(flow):
    d = {v: Q(0) for v in VERTICES}
    for (sx, _), value in zip(EDGES, flow):
        d[sx] += value
    return d


def balance(flow):
    b = {v: Q(0) for v in VERTICES}
    for ((sx, sy), (gx, gy), value) in zip(EDGES, SIGNS, flow):
        b[sx] += gx * value
        b[sy] += gy * value
    return b


def feasible(flow):
    d = throughput(flow)
    return all(z >= 0 for z in flow) and all(z == 0 for z in balance(flow).values()) \
        and all(d[v] >= 1 for v in VERTICES)


def binomial_score(d):
    # Binomial coefficients and N**(-n) are candidate-independent.  Keep all
    # observed coordinates and their (N-d) complement factors exactly.
    n = sum(OBS.values())
    score = Q(1)
    for v in VERTICES:
        x = OBS[v]
        score *= d[v] ** x * (EXTERNAL_N - d[v]) ** (n - x)
    return score


def main():
    # f2 and f3 are the documented integral optima (AAA throughput 2 and 3).
    f2 = (Q(1), Q(1), Q(1), Q(1))
    f3 = (Q(2), Q(1), Q(1), Q(1))
    half = tuple((a + b) / 2 for a, b in zip(f2, f3))

    assert feasible(f2) and feasible(f3) and feasible(half)
    assert throughput(f2) == {0: Q(2), 1: Q(1), 2: Q(1)}
    assert throughput(f3) == {0: Q(3), 1: Q(1), 2: Q(1)}
    assert throughput(half) == {0: Q(5, 2), 1: Q(1), 2: Q(1)}
    assert balance(f2) == balance(f3) == balance(half) == {0: 0, 1: 0, 2: 0}
    assert sum(throughput(half).values()) <= EXTERNAL_N

    # The integer truth-domain maximizers are f2/f3 in this instance; the AAA
    # coordinate's factor d^2(5-d)^2 is 36 at either endpoint and 625/16 at
    # the feasible midpoint.  Other coordinates agree and cancel.
    ratio = binomial_score(throughput(half)) / binomial_score(throughput(f2))
    assert ratio == Q(625, 576) > 1
    assert binomial_score(throughput(f2)) == binomial_score(throughput(f3))
    print("AAATT integral endpoint flows: feasible; throughputs (2,1,1), (3,1,1)")
    print("their half-integral midpoint: feasible; throughput (5/2,1,1)")
    print(f"fixed-N=5 binomial score ratio midpoint/endpoint: {ratio} > 1")
    print("ALL CHECKS PASS (bounded project flow model; reduction fidelity open)")


if __name__ == "__main__":
    main()
