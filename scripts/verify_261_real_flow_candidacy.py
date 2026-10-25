#!/usr/bin/env python3
"""Exact-rational candidacy classification of the #261 real-flow midpoint.

Companion to docs/issue261-real-flow-candidacy.md. Uses only the full
o_min=1 overlap graph (graph1); no transitive-reduction convention is
invoked, so issue #284's graph-model blocker does not apply.

Candidate classes distinguished:
  (F)  nonnegative real edge flows satisfying signed-incidence balance and
       vertex throughput lower bound 1 (the real relaxation of Feasible62);
  (I)  integer flows (Lean BdFlow is N-valued; Feasible62 endpoints live here);
  (C)  spelled single-circuit traversals (closed walks induce N-valued edge
       multiplicity vectors);
  (G)  circular genome spectra (per-class window counts are N-valued and sum
       to the genome length).

The midpoint of the kernel-checked integer feasible flows starFlow21 and
starFlow31 is in (F) but in none of (I), (C), (G), yet strictly beats the
entire integer optimum under the fixed-N=5 product-binomial score.
"""

from fractions import Fraction as Q
from math import comb

# Coordinates: (AAA loop, AAA->AAT, AAT->TAA overlap 1, TAA->AAA).
integer_a = (Q(1), Q(1), Q(1), Q(1))
integer_b = (Q(2), Q(1), Q(1), Q(1))
fractional = tuple((a + b) / 2 for a, b in zip(integer_a, integer_b))
assert fractional == (Q(3, 2), Q(1), Q(1), Q(1))


def throughput(flow):
    return (flow[0] + flow[1], flow[2], flow[3])


def balances(flow):
    return (flow[1] - flow[3], -flow[1] + flow[2], -flow[2] + flow[3])


def is_integer(q):
    return q.denominator == 1


# (F): real-flow feasibility by convexity of every constraint.
for flow in (integer_a, integer_b, fractional):
    assert all(v >= 0 for v in flow)
    assert balances(flow) == (0, 0, 0)
    assert min(throughput(flow)) >= 1
assert throughput(fractional) == (Q(5, 2), 1, 1)
assert all(0 <= d <= 5 for d in throughput(fractional))

# (I): the midpoint is not an integer flow (AAA loop is 3/2).
assert not all(is_integer(v) for v in fractional)
assert fractional[0] == Q(3, 2) and not is_integer(fractional[0])

# (C): not a spelled single-circuit traversal. Any closed walk traverses each
# edge an integer number of times, so its edge-multiplicity vector is N-valued.
# The midpoint's 3/2 loop value cannot arise from any closed walk.
assert not is_integer(fractional[0]), "fractional loop excludes circuit traversal"

# (G): not a circular genome spectrum. A length-G circular genome contributes
# exactly one length-L window per start, so every per-class count is a natural
# number and the class counts sum to G (a natural number). The midpoint
# throughput (5/2, 1, 1) has a fractional coordinate and fractional total 9/2.
mid_tp = throughput(fractional)
assert not is_integer(mid_tp[0])
total = sum(mid_tp)
assert total == Q(9, 2) and not is_integer(total)

# Score gap (fixed external N=5 product-binomial, n=4, x=(2,1,1)).


def marginal(d, observed):
    n, N = 4, 5
    return Q(comb(n, observed)) * (d / N) ** observed * (1 - d / N) ** (n - observed)


def active_score(d):
    return marginal(d[0], 2) * marginal(d[1], 1) * marginal(d[2], 1)


score_a = active_score(tuple(map(Q, throughput(integer_a))))
score_b = active_score(tuple(map(Q, throughput(integer_b))))
score_real = active_score(throughput(fractional))
assert score_a == score_b  # both integer optima agree (cf. Lean star_argmax)
ratio = score_real / score_a
assert ratio == Q(625, 576) and ratio > 1

print("real-flow midpoint feasible in (F): PASS")
print("midpoint outside integer flows (I): PASS (AAA loop 3/2)")
print("midpoint outside spelled circuits (C): PASS (fractional edge count)")
print("midpoint outside genome spectra (G): PASS (throughput (5/2,1,1), mass 9/2)")
print(f"binomial score ratio over either integer optimum: {ratio} > 1")
