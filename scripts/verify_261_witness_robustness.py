#!/usr/bin/env python3
"""Robustness axes of the #261 real-flow midpoint witness (issue #261).

Companion to docs/issue261-witness-robustness.md. Exact-rational checks only;
uses the full o_min=1 graph (graph1); no transitive-reduction convention is
invoked, so issue #284's graph-model blocker does not apply.

Three bounded claims:
  (O) o_min sensitivity: the witness support needs the overlap-1 edge
      AAT->TAA, so it is infeasible at o_min=2. No upward transfer.
  (V) vertex-bound tightness: lower bound 1 is tight at AAT/TAA, slack at AAA.
  (L) likelihood-choice sensitivity: under the fixed-N=5 product-binomial the
      two integer endpoints tie, while under the exact candidate-intrinsic-N
      multinomial endpoint A beats endpoint B by exactly 625/576.
"""

from fractions import Fraction as Q
from math import comb, factorial

# Edge coordinates: (AAA loop, AAA->AAT, AAT->TAA, TAA->AAA).
integer_a = (Q(1), Q(1), Q(1), Q(1))
integer_b = (Q(2), Q(1), Q(1), Q(1))
fractional = tuple((a + b) / 2 for a, b in zip(integer_a, integer_b))

# (O): proper-overlap lengths of the four graph1 edges. The loop is the
# full-length self overlap (length L=3); the cross edges spell AAA->AAT
# (overlap 2, "AA"), AAT->TAA (overlap 1, "T"), TAA->AAA (overlap 2, "AA").
overlap_lengths = (3, 2, 1, 2)
o_min_used = 1
assert all(o >= o_min_used for o in overlap_lengths)
# At o_min=2 the overlap-1 edge (index 2) is absent from the graph, but every
# witness flow puts strictly positive flow (1) on it -> infeasible there.
o_min_raised = 2
assert overlap_lengths[2] < o_min_raised
assert all(f[2] > 0 for f in (integer_a, integer_b, fractional))
print("(O) witness needs overlap-1 edge; infeasible at o_min=2: PASS")


def throughput(flow):
    return (flow[0] + flow[1], flow[2], flow[3])


# (V): vertex lower bound 1 tightness per vertex (AAA, AAT, TAA).
for name, flow in (("A", integer_a), ("B", integer_b), ("mid", fractional)):
    tp = throughput(flow)
    slack = tuple(t - 1 for t in tp)
    assert min(tp) >= 1
    # AAT and TAA throughputs are exactly 1 (tight); AAA is slack.
    assert tp[1] == 1 and tp[2] == 1 and tp[0] > 1, (name, tp)
    print(f"(V) vertex bound tightness {name}: throughput {tuple(map(str, tp))}, "
          f"slack {tuple(map(str, slack))}: PASS")


# (L): likelihood-choice sensitivity. Reads: n=4, x=(2,1,1); external N=5.
def fixed_n_binomial(d):
    n, N = 4, 5
    s = Q(1)
    for di, xi in zip(d, (2, 1, 1)):
        s *= Q(comb(n, xi)) * (Q(di) / N) ** xi * (1 - Q(di) / N) ** (n - xi)
    return s


def exact_intrinsic_multinomial(d):
    # Exact global read-count multinomial up to the common multinomial
    # coefficient n!/x! (identical for both endpoints, cancels in the ratio):
    # score ~ prod_i (d_i / N(D))^{x_i} with N(D) = sum(d).
    N = sum(d)
    s = Q(1)
    for di, xi in zip(d, (2, 1, 1)):
        s *= (Q(di) / N) ** xi
    return s


tp_a = tuple(map(Q, throughput(integer_a)))  # (2,1,1), intrinsic N=4
tp_b = tuple(map(Q, throughput(integer_b)))  # (3,1,1), intrinsic N=5
assert sum(tp_a) == 4 and sum(tp_b) == 5

assert fixed_n_binomial(tp_a) == fixed_n_binomial(tp_b)  # tie (cf. star_argmax)
exact_a = exact_intrinsic_multinomial(tp_a)
exact_b = exact_intrinsic_multinomial(tp_b)
assert exact_a == Q(1, 64), exact_a
assert exact_b == Q(9, 625), exact_b
assert exact_a / exact_b == Q(625, 576)
assert exact_a > exact_b
print(f"(L) fixed-N binomial: tie {fixed_n_binomial(tp_a)}: PASS")
print(f"(L) exact intrinsic-N multinomial: A={exact_a} > B={exact_b}, "
      f"ratio 625/576: PASS")

# The real midpoint throughput (5/2,1,1) is inadmissible under the exact
# multinomial (fractional counts and fractional intrinsic length 9/2).
mid_tp = throughput(fractional)
assert mid_tp == (Q(5, 2), Q(1), Q(1)) and sum(mid_tp) == Q(9, 2)
assert sum(mid_tp).denominator != 1
print("(L) midpoint inadmissible under exact multinomial (mass 9/2): PASS")
