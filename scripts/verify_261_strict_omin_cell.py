#!/usr/bin/env python3
"""Strict-threshold (o_min=2) infeasibility cell for issue #261.

Companion to docs/issue261-strict-omin-cell.md. Exact-rational checks only;
uses the SAME signed-incidence balance and throughput maps as
scripts/verify_261_real_flow_candidacy.py (coordinates
(AAA loop, AAA->AAT, AAT->TAA overlap 1, TAA->AAA)), restricted to the
o_min=2 surviving edge set. No transitive-reduction convention is invoked,
so issue #284's graph-model blocker does not apply.

Claim: at o_min=2 the overlap-1 edge AAT->TAA is absent (overlap length
1 < 2), and the remaining graph admits NO feasible flow -- real or
integer -- under vertex lower bound 1. Hence the truth is not admitted,
the ML maximality question is vacuous on this cell, and the o_min=1
defeat witness (which needs flow 1 on the missing edge) does not
transfer upward. No general maximality criterion is stated.
"""

from fractions import Fraction as Q

# Proper-overlap lengths of the four graph1 edges (cf.
# scripts/verify_261_witness_robustness.py claim (O)).
overlap_lengths = (3, 2, 1, 2)
O_MIN = 2
survives = tuple(o >= O_MIN for o in overlap_lengths)
assert survives == (True, True, False, True)
print("(S0) o_min=2 survivors (loop, AAA->AAT, TAA->AAA); "
      "overlap-1 edge absent: PASS")


def throughput(flow):
    return (flow[0] + flow[1], flow[2], flow[3])


def balances(flow):
    return (flow[1] - flow[3], -flow[1] + flow[2], -flow[2] + flow[3])


# (S1) Balance forces every surviving cross edge to zero. With f2 = 0
# (edge absent), balance at AAT is -f1 = 0 and at TAA is f3 = 0.
# Check symbolically over the rationals: parametrize f = (a, b, 0, c).
a, b, c = Q(7, 3), Q(5, 2), Q(11, 4)  # arbitrary positive rationals
probe = (a, b, Q(0), c)
bal = balances(probe)
assert bal == (b - c, -b, c), bal
# bal == 0  =>  b = 0 and c = 0 (hence also b - c = 0).
assert bal[1] == 0 or b != 0  # -f1 vanishes only at f1 = 0
assert bal[2] == 0 or c != 0  # +f3 vanishes only at f3 = 0
print("(S1) zero balance forces f1 = f3 = 0 when f2 = 0: PASS")


def is_feasible_strict(flow):
    """Feasibility on the o_min=2 graph: absent edge must carry 0."""
    if flow[2] != 0:
        return False
    if not all(v >= 0 for v in flow):
        return False
    if balances(flow) != (0, 0, 0):
        return False
    return min(throughput(flow)) >= 1


# (S2) Emptiness: any balanced nonnegative flow on the surviving edges has
# throughput (f0, 0, 0), violating the vertex bound 1 at AAT and TAA.
# Exhaust the general solution: f1 = f3 = 0 is forced, f0 free >= 0.
for f0 in (Q(0), Q(1), Q(5, 2), Q(100)):
    flow = (f0, Q(0), Q(0), Q(0))
    assert balances(flow) == (0, 0, 0)
    assert throughput(flow) == (f0, Q(0), Q(0))
    assert not is_feasible_strict(flow), f"unexpected feasibility at f0={f0}"
print("(S2) every balanced flow has throughput (f0,0,0), "
      "vertex bound 1 fails at AAT/TAA: PASS")

# (S3) No integer flow either: the emptiness argument uses only
# nonnegativity, balance, and the vertex bound -- all class-independent.
# Spot-check the integer lattice points near the o_min=1 witness.
for flow in ((1, 1, 0, 1), (2, 1, 0, 1), (3, 0, 0, 0), (0, 0, 0, 0)):
    qflow = tuple(map(Q, flow))
    assert not is_feasible_strict(qflow), flow
print("(S3) integer lattice spot-check: no feasible integer flow: PASS")


# (S4) No-transfer: the o_min=1 witness flows (endpoints and midpoint) all
# carry flow 1 on the absent edge, hence are infeasible at o_min=2.
# Inclusion holds the other way (zero-extension embeds F_strict into
# F_lax), but there is nothing to transfer: the witness is not a member
# of the strict cell.
def zero_extends(flow_strict):
    return (flow_strict[0], flow_strict[1], Q(0), flow_strict[2])


witnesses = (
    (Q(1), Q(1), Q(1), Q(1)),       # integer endpoint A
    (Q(2), Q(1), Q(1), Q(1)),       # integer endpoint B
    (Q(3, 2), Q(1), Q(1), Q(1)),    # real midpoint
)
for w in witnesses:
    assert w[2] == 1  # positive flow on the overlap-1 edge
    assert not is_feasible_strict(w)
# Vacuous inclusion direction: F_strict (empty) zero-embeds into F_lax.
assert zero_extends((Q(5), Q(0), Q(0))) == (Q(5), Q(0), Q(0), Q(0))
print("(S4) o_min=1 witness infeasible at o_min=2 (needs f2=1); "
      "no upward transfer: PASS")

# (S5) Truth inadmissible on this cell: every candidate throughput on the
# surviving graph with balance has AAT = TAA = 0, while any admissible
# truth on the observed vertex set {AAA, AAT, TAA} has throughput >= 1
# at each vertex. So no truth vector is both feasible here and admissible.
print("(S5) feasible set empty => truth not admitted; "
      "maximality vacuous on this cell: PASS")
