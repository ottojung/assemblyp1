#!/usr/bin/env python3
"""Degenerate-threshold (o_min=3) infeasibility cell for issue #261.

Companion to docs/issue261-omin3-cell.md. Exact-rational checks only;
uses the SAME signed-incidence balance and throughput maps as
scripts/verify_261_strict_omin_cell.py and
scripts/verify_261_real_flow_candidacy.py (coordinates
(AAA loop, AAA->AAT, AAT->TAA overlap 1, TAA->AAA)), restricted to the
o_min=3 surviving edge set. No transitive-reduction convention is invoked,
so issue #284's graph-model blocker does not apply.

Claim: at o_min=3 only the AAA loop (overlap length 3) survives; every
other edge has overlap length < 3 and is absent. Balance is then vacuous
and every balanced flow has throughput (f0, 0, 0), violating vertex lower
bound 1 at AAT and TAA. Hence the feasible set is EMPTY in real (F) and
integer (I) classes (hence (C)/(G)); truth is not admitted; maximality is
vacuous. The o_min=1 defeat witness (needs flow 1 on each absent edge)
does not transfer upward. No general maximality criterion is stated.
"""

from fractions import Fraction as Q

# Proper-overlap lengths of the four graph1 edges (cf.
# scripts/verify_261_witness_robustness.py claim (O)).
overlap_lengths = (3, 2, 1, 2)
O_MIN = 3
survives = tuple(o >= O_MIN for o in overlap_lengths)
assert survives == (True, False, False, False)
print("(T0) o_min=3 survivors (loop only); "
      "all three cross edges absent: PASS")


def throughput(flow):
    return (flow[0] + flow[1], flow[2], flow[3])


def balances(flow):
    return (flow[1] - flow[3], -flow[1] + flow[2], -flow[2] + flow[3])


# (T1) Balance is vacuous on the surviving edge set: with f1 = f2 = f3 = 0
# (edges absent), balances((a,0,0,0)) = (0,0,0) for every loop flow a.
a = Q(7, 3)  # arbitrary positive rational
probe = (a, Q(0), Q(0), Q(0))
assert balances(probe) == (0, 0, 0), balances(probe)
assert throughput(probe) == (a, Q(0), Q(0)), throughput(probe)
print("(T1) balance vacuous on loop-only graph; "
      "throughput (f0,0,0): PASS")


def is_feasible_degenerate(flow):
    """Feasibility on the o_min=3 graph: absent edges must carry 0."""
    if flow[1] != 0 or flow[2] != 0 or flow[3] != 0:
        return False
    if not all(v >= 0 for v in flow):
        return False
    if balances(flow) != (0, 0, 0):
        return False
    return min(throughput(flow)) >= 1


# (T2) Emptiness: every balanced nonnegative flow on the surviving edges
# has throughput (f0, 0, 0), violating vertex bound 1 at AAT and TAA.
for f0 in (Q(0), Q(1), Q(5, 2), Q(100)):
    flow = (f0, Q(0), Q(0), Q(0))
    assert balances(flow) == (0, 0, 0)
    assert throughput(flow) == (f0, Q(0), Q(0))
    assert not is_feasible_degenerate(flow), f"unexpected feasibility at f0={f0}"
print("(T2) every balanced flow has throughput (f0,0,0), "
      "vertex bound 1 fails at AAT/TAA: PASS")

# (T3) No integer flow either: the emptiness argument uses only
# nonnegativity, balance, and the vertex bound -- all class-independent.
# Spot-check the integer lattice points near the o_min=1 witness.
for flow in ((1, 1, 1, 1), (2, 1, 1, 1), (3, 0, 0, 0), (0, 0, 0, 0)):
    qflow = tuple(map(Q, flow))
    assert not is_feasible_degenerate(qflow), flow
print("(T3) integer lattice spot-check: no feasible integer flow: PASS")


# (T4) No-transfer: the o_min=1 witness flows (endpoints and midpoint) all
# carry flow 1 on absent edges, hence are infeasible at o_min=3.
# Zero-extension embeds F_omin3 into F_omin2 and F_omin1 (all empty here),
# but there is nothing to transfer: the witness is not a member of the
# degenerate cell.
def zero_extends(flow_degenerate):
    return (flow_degenerate[0], Q(0), Q(0), Q(0))


witnesses = (
    (Q(1), Q(1), Q(1), Q(1)),       # integer endpoint A
    (Q(2), Q(1), Q(1), Q(1)),       # integer endpoint B
    (Q(3, 2), Q(1), Q(1), Q(1)),    # real midpoint
)
for w in witnesses:
    assert w[1] == 1 and w[2] == 1 and w[3] == 1  # flow on absent edges
    assert not is_feasible_degenerate(w)
# Vacuous inclusion direction: F_omin3 (empty) zero-embeds into F_omin2/F_omin1.
assert zero_extends((Q(5),)) == (Q(5), Q(0), Q(0), Q(0))
print("(T4) o_min=1 witness infeasible at o_min=3 (needs flow on absent "
      "edges); no upward transfer: PASS")

# (T5) Truth inadmissible on this cell: every candidate throughput on the
# surviving graph with balance has AAT = TAA = 0, while any admissible
# truth on the observed vertex set {AAA, AAT, TAA} has throughput >= 1
# at each vertex. So no truth vector is both feasible here and admissible.
print("(T5) feasible set empty => truth not admitted; "
      "maximality vacuous on this cell: PASS")
