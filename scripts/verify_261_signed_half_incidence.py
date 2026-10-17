#!/usr/bin/env python3
"""Independent finite check of representation-invariant signed half-incidences.

Edges are signed ordered oriented-strand overlap representations:
(sx, sy, signX, signY), where sx/sy are (class, orientation).
Reversal swaps the two endpoints and signs and toggles orientations.
All four combinations of two classes/orientations and all signed
incidences are checked. Physical equivalence does NOT quotient
parallel edge identities: the Lean module proves only per-edge equations.
"""
from itertools import product

strands = list(product((False, True), repeat=2))
signs = (-1, 1)

def rev(e):
    sx, sy, a, b = e
    return ((sy[0], not sy[1]), (sx[0], not sx[1]), b, a)

def count(e, v, sign):
    sx, sy, a, b = e
    return int(sx[0] == v and a == sign) + int(sy[0] == v and b == sign)

def dep(e, v):
    return int(e[0][0] == v)

n = 0
for sx, sy, a, b in product(strands, strands, signs, signs):
    e = (sx, sy, a, b)
    assert rev(rev(e)) == e
    for v in (False, True):
        assert count(e, v, 1) == count(rev(e), v, 1)
        assert count(e, v, -1) == count(rev(e), v, -1)
        net = int(sx[0] == v) * a + int(sy[0] == v) * b
        assert count(e, v, 1) - count(e, v, -1) == net
    n += 1

a = ((False, False), (True, False), 1, -1)
assert dep(a, False) == 1 and dep(rev(a), False) == 0
mixed_loop = ((False, False), (False, False), 1, -1)
assert (count(mixed_loop, False, 1), count(mixed_loop, False, -1)) == (1, 1)
positive_loop = ((False, False), (False, True), 1, 1)
assert (count(positive_loop, False, 1), count(positive_loop, False, -1)) == (2, 0)
print(f"PASS: {n} signed oriented endpoint instances, both molecule classes; half-incidences invariant")
print("PASS: mixed loop (1+,1-), ++ loop (2+,0-), departure-count reversal counterexample")
