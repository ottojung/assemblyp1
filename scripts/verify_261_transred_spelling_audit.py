#!/usr/bin/env python3
"""Spelling-preserving transitive-reduction audit on the #261 AAATT cell.

Issue #261, bounded increment. The general transitive-reduction interaction
with ML is OPEN; this script settles it for exactly one small instance: the
AAATT witness cell (L=3, o_min=1, full overlap graph1, zero terminals,
external N=5, read counts x=(2,1,1)) shared with the real-flow candidacy and
witness-robustness notes.

Method: independent exact-string spelling computation. No reliance on the Lean
`isReducibleB` / `isReducibleLongerB` predicates (cf. issue #284 blocker); the
outcome is instead cross-checked against the audited vacuity finding for
`isReducibleB` (it deletes nothing anywhere).

Fragments (reads): AAA, AAT, TAA. Edge u->v at proper-overlap k spells
u + v[k:] (Myers 2005 / MB09 section 6.2 spelling convention).

Claims:
  (T1) Under the standard spelling-preserving convention (an edge u->v is
       reducible only if a 2-step path u->w->v with w DISTINCT from u and v
       spells the identical string), NO edge of graph1 is reducible: the
       reduced graph equals the full graph.
  (T2) The only spelling-preserving 2-step reproductions use loop-mediated
       paths (intermediate == start or end vertex). Under a lax convention
       that admits them, AAA->AAT and TAA->AAA would be deleted -- so
       reduction invariance on this cell is convention-relative, not
       absolute.
  (T3) Under the standard convention the defeat-witness flows (integer
       endpoints and real midpoint) survive reduction untouched, and the ML
       ranking (fixed-N binomial tie of endpoints; midpoint beats them by
       exactly 625/576) is preserved. Under the lax convention the witness
       is killed (it needs flow 1 on AAA->AAT), so the full-overlap failure
       does NOT transfer to the lax-reduced graph.
"""

from fractions import Fraction as Q
from math import comb

# --- Graph data -------------------------------------------------------------
FRAGS = ("AAA", "AAT", "TAA")
# Edges: (name, u, v, overlap k). Loop overlap L=3 appends the empty suffix.
EDGES = (
    ("loop", "AAA", "AAA", 3),
    ("e1", "AAA", "AAT", 2),
    ("e2", "AAT", "TAA", 1),
    ("e3", "TAA", "AAA", 2),
)


def spell_edge(u, v, k):
    assert u[-k:] == v[:k], (u, v, k)
    return u + v[k:]


def spell_path(frags):
    s = frags[0]
    for a, b in zip(frags, frags[1:]):
        # longest modeled overlap present in the graph, mirroring graph1;
        # fall back to any feasible overlap >= o_min=1 for completeness
        # (only used to enumerate candidate reproducers, never to add edges).
        best = 0
        for k in (3, 2, 1):
            if len(a) >= k and len(b) >= k and a[-k:] == b[:k]:
                best = k
                break
        assert best >= 1, (a, b)
        s += b[best:]
    return s


EDGE_SPELL = {name: spell_edge(u, v, k) for name, u, v, k in EDGES}
assert EDGE_SPELL == {
    "loop": "AAA",
    "e1": "AAAT",
    "e2": "AATAA",
    "e3": "TAAA",
}, EDGE_SPELL
print("(T0) direct edge spellings (loop=AAA, e1=AAAT, e2=AATAA, e3=TAAA): PASS")

# Out-neighbourhoods ( Acad.: loop counts as a self-step).
OUT = {"AAA": ("AAA", "AAT"), "AAT": ("TAA",), "TAA": ("AAA",)}

# --- (T1): standard convention ------------------------------------------------
# For each non-loop edge u->v, list 2-step u->w->v paths with w not in {u,v}
# whose spelling equals the direct spelling.
standard_reducible = {}
for name, u, v, k in EDGES:
    if name == "loop":
        continue  # loops are not subject to transitive reduction (Myers 2005)
    reproducers = []
    for w in FRAGS:
        if w in (u, v):
            continue
        if w not in OUT[u] or v not in OUT[w]:
            continue
        if spell_path((u, w, v)) == EDGE_SPELL[name]:
            reproducers.append((u, w, v))
    standard_reducible[name] = reproducers

assert standard_reducible == {"e1": [], "e2": [], "e3": []}, standard_reducible
print("(T1) standard convention (distinct intermediate): no edge reducible, "
      "reduced graph == full graph: PASS")

# --- (T2): lax convention -----------------------------------------------------
# Admit intermediates equal to an endpoint (i.e. loop-mediated 2-paths).
lax_reducible = {}
for name, u, v, k in EDGES:
    if name == "loop":
        continue
    reproducers = []
    for w in FRAGS:
        if w not in OUT[u] or v not in OUT[w]:
            continue
        if spell_path((u, w, v)) == EDGE_SPELL[name]:
            reproducers.append((u, w, v))
    lax_reducible[name] = reproducers

assert lax_reducible["e1"] == [("AAA", "AAA", "AAT")], lax_reducible
assert lax_reducible["e2"] == [], lax_reducible
assert lax_reducible["e3"] == [("TAA", "AAA", "AAA")], lax_reducible
print("(T2) lax convention (loop-mediated paths admitted): e1 and e3 "
      "reproducible, e2 not -- invariance is convention-relative: PASS")

# --- (T3): witness survival and ML ranking ------------------------------------
# Edge coordinates: (loop, e1, e2, e3).
integer_a = (Q(1), Q(1), Q(1), Q(1))
integer_b = (Q(2), Q(1), Q(1), Q(1))
fractional = tuple((a + b) / 2 for a, b in zip(integer_a, integer_b))


def throughput(flow):
    return (flow[0] + flow[1], flow[2], flow[3])


def fixed_n_binomial(d):
    n, N = 4, 5
    s = Q(1)
    for di, xi in zip(d, (2, 1, 1)):
        s *= Q(comb(n, xi)) * (Q(di) / N) ** xi * (1 - Q(di) / N) ** (n - xi)
    return s


# Standard reduction changes nothing: same edge set, same throughputs.
for tag, f in (("A", integer_a), ("B", integer_b), ("mid", fractional)):
    assert min(throughput(f)) >= 1, (tag, throughput(f))
tp_a, tp_b, tp_m = map(throughput, (integer_a, integer_b, fractional))
assert fixed_n_binomial(tp_a) == fixed_n_binomial(tp_b)
assert fixed_n_binomial(tp_m) / fixed_n_binomial(tp_a) == Q(625, 576)
print("(T3a) standard-reduced graph: witness feasible, endpoints tie, "
      "midpoint wins by 625/576 -- failure transfers intact: PASS")

# Lax reduction deletes e1 (index 1); every witness flow needs flow 1 there.
assert all(f[1] > 0 for f in (integer_a, integer_b, fractional))
print("(T3b) lax-reduced graph: witness infeasible (needs e1 flow 1) -- "
      "failure does NOT transfer: PASS")

# Consistency note (no reliance): literal `isReducibleB` provably deletes no
# proper overlap anywhere (vacuity audit), which agrees with (T1) on this
# cell but for the wrong reason -- it would also keep e1/e3 under genuinely
# reducible configurations. This script's verdicts come from the independent
# spelling computation above, not from either Lean predicate.
print("(T4) audit independence: verdicts derived from exact spellings only: PASS")
