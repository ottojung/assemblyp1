#!/usr/bin/env python3
"""Exact-rational audit of the finite real-flow relaxation witness in #261."""

from fractions import Fraction as Q

# Coordinates are (AAA loop, AAA->AAT, AAT->TAA, TAA->AAA). The latter
# three edges form a balanced cycle; the loop contributes zero net balance.
integer_a = (Q(1), Q(1), Q(1), Q(1))
integer_b = (Q(2), Q(1), Q(1), Q(1))
fractional = tuple((a + b) / 2 for a, b in zip(integer_a, integer_b))
assert fractional == (Q(3, 2), Q(1), Q(1), Q(1))


def throughput(flow):
    # Loop and outgoing cycle edge count at AAA; the next edges depart AAT/TAA.
    return (flow[0] + flow[1], flow[2], flow[3])


def balances(flow):
    # A signed + departure / - arrival convention. The self-loop cancels.
    return (flow[1] - flow[3], -flow[1] + flow[2], -flow[2] + flow[3])


for flow in (integer_a, integer_b, fractional):
    assert all(value >= 0 for value in flow)
    assert balances(flow) == (0, 0, 0)
    assert min(throughput(flow)) >= 1
assert throughput(integer_a) == (2, 1, 1)
assert throughput(integer_b) == (3, 1, 1)
assert throughput(fractional) == (Q(5, 2), 1, 1)
assert all(0 <= d <= 5 for d in throughput(fractional))


def marginal(d, observed):
    # Binomial coefficients cancel in the candidate ratio; include them anyway.
    from math import comb

    n, N = 4, 5
    return Q(comb(n, observed)) * (d / N) ** observed * (1 - d / N) ** (n - observed)


ratio = marginal(Q(5, 2), 2) / marginal(Q(2), 2)
assert ratio == Q(625, 576) and ratio > 1

def active_score(d):
    return marginal(d[0], 2) * marginal(d[1], 1) * marginal(d[2], 1)


integer_score_a = active_score(tuple(map(Q, throughput(integer_a))))
integer_score_b = active_score(tuple(map(Q, throughput(integer_b))))
real_score = active_score(throughput(fractional))
assert integer_score_a == integer_score_b
assert real_score / integer_score_a == ratio

print("real-flow midpoint feasible on the four active edges: PASS")
print("throughput (5/2,1,1), external N=5 probability bounds: PASS")
print(f"AAA binomial marginal ratio over either integral optimum: {ratio} > 1")
