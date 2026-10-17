#!/usr/bin/env python3
"""Exhaustive bounded sanity checks for the bidirected signed double cover.

Two abstract physical EDGE IDs each produce two lifted directed ARC IDs.
These identities are incidence-level only. They do not imply any
spelled-genome realization or descent from 2f projected uses to f.
"""
from itertools import product

def cover(e):
    (u, v, a, b) = e
    return (((u, a), (v, -b)), ((v, b), (u, -a)))

def outgoing(e, state):
    return sum(arc[0] == state for arc in cover(e))

def incoming(e, state):
    return sum(arc[1] == state for arc in cover(e))

def incidence(e, w, sign):
    (u, v, a, b) = e
    return int(u == w and a == sign) + int(v == w and b == sign)

cases = 0
for u, v, a, b, f in product((0, 1), (0, 1), (-1, 1), (-1, 1), (0, 1, 2)):
    e = u, v, a, b
    for w in (0, 1):
        for s in (-1, 1):
            assert outgoing(e, (w,s)) * f == incidence(e,w,s) * f
            assert incoming(e, (w,s)) * f == incidence(e,w,-s) * f
    assert len(cover(e)) == 2
    assert f + f == 2*f
    cases += 1
# Mixed-sign loop has one positive and negative incidence, not zero visits.
assert incidence((0,0,1,-1),0,1) == 1
assert incidence((0,0,1,-1),0,-1) == 1
# ++ loop has two distinct arcs, both leaving the positive signed state.
assert outgoing((0,0,1,1),(0,1)) == 2
# Parallel physical IDs remain distinct even if their endpoint data coincide.
physical_edges = {0:(0,0,1,-1), 1:(0,0,1,-1)}
arc_ids = [(i, orientation) for i in physical_edges for orientation in (0,1)]
assert len(arc_ids) == len(set(arc_ids)) == 4
print(f"PASS: {cases} signed edge/weight cases; two signed state balances per vertex")
print("PASS: mixed and ++ loops, parallel physical IDs, projection uses 2f")
