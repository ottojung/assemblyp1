#!/usr/bin/env python3
"""Independent exact validation of the #261 physical edge-orbit quotient.

Scope: the ATAT witness of `AssemblyP1/Section62PhysicalEdgeOrbit.lean`
(issue #261).  That module forms the reversal setoid on tagged signed edges,
quotients it to the physical edge type, lifts the representation-invariant
positive/negative half-incidences of merged PR #300 to the quotient, and shows
that the inherited departure-based `throughput` is *not* the physical visit
count once orbit weights are normalized.

This script recomputes the witness from scratch with exact integer arithmetic
and no trust in the Lean output.  A tagged strand is `(word, bit)`; the class
representative is `(word, False)`, reversal toggles the bit; an edge is
`(sx, sy, len, sgnX, sgnY)` with `sgnX = +1` iff the departure strand is its own
class representative, `sgnY = -1` iff the arrival strand is its own class
representative (the `sgnRep`/`sgnTgt` convention of
`AssemblyP1.Section62BidirectedFlow` at `rep = cls`).

Checked:
  * reversal is an involution and preserves the overlap length;
  * the four ATAT tagged orientations fall into exactly THREE unordered orbits
    `{E1,E4}`, `{E2}`, `{E3}`;
  * the mixed-sign loop orbit has one positive and one negative half-incidence,
    the `++` loop two positive, the `--` loop two negative;
  * the unit mixed-sign orbit flow is physically balanced with visit count one;
  * the induced oriented flow's inherited departure `throughput` is two, so it
    differs from the physical visit count;
  * two edges with different overlap length are never in the same orbit.

The script is deterministic, exits non-zero on any failed assertion, and shares
no code with the Lean module.
"""

PAL = "ATAT"


def cls(s):
    return (s[0], False)


def flip(s):
    return (s[0], not s[1])


def bd_edge(sx, sy, length):
    return (sx, sy, length,
            (1 if sx == cls(sx) else -1),
            (-1 if sy == cls(sy) else 1))


def reverse_edge(e):
    sx, sy, length, a, b = e
    return (flip(sy), flip(sx), length, b, a)


def pos_half(e, v):
    sx, sy, _length, a, b = e
    return int(cls(sx) == v and a == 1) + int(cls(sy) == v and b == 1)


def neg_half(e, v):
    sx, sy, _length, a, b = e
    return int(cls(sx) == v and a == -1) + int(cls(sy) == v and b == -1)


def orbit(e):
    return frozenset((e, reverse_edge(e)))


def departure_count(e, v):
    return int(cls(e[0]) == v)


def main():
    v0 = (PAL, False)
    E1 = bd_edge((PAL, False), (PAL, False), 2)
    E2 = bd_edge((PAL, False), (PAL, True), 2)
    E3 = bd_edge((PAL, True), (PAL, False), 2)
    E4 = bd_edge((PAL, True), (PAL, True), 2)
    edges = [E1, E2, E3, E4]

    # Reversal is an involution and preserves overlap length.
    for e in edges:
        assert reverse_edge(reverse_edge(e)) == e
        assert reverse_edge(e)[2] == e[2]

    assert reverse_edge(E1) == E4 and reverse_edge(E4) == E1
    assert reverse_edge(E2) == E2 and reverse_edge(E3) == E3

    # Exactly three unordered orbits.
    orbits = set(orbit(e) for e in edges)
    assert len(orbits) == 3, orbits
    assert orbit(E1) == orbit(E4) == frozenset((E1, E4))

    # Half-incidences at the observed class.
    assert (pos_half(E1, v0), neg_half(E1, v0)) == (1, 1)
    assert (pos_half(E2, v0), neg_half(E2, v0)) == (2, 0)
    assert (pos_half(E3, v0), neg_half(E3, v0)) == (0, 2)
    assert (pos_half(E4, v0), neg_half(E4, v0)) == (1, 1)

    # Unit mixed-sign orbit flow is balanced with physical visit count one.
    reps = [E1, E2, E3]
    weights = [1, 0, 0]
    pos_total = sum(w * pos_half(r, v0) for r, w in zip(reps, weights))
    neg_total = sum(w * neg_half(r, v0) for r, w in zip(reps, weights))
    assert (pos_total, neg_total) == (1, 1)

    # The induced oriented flow copies the orbit weight onto both representatives.
    def induced_flow(e):
        return 1 if e in (E1, E4) else 0

    inherited = sum(induced_flow(e) for e in edges if cls(e[0]) == v0)
    assert inherited == 2
    assert inherited != pos_total

    # Distinct parallel overlaps are never identified.
    longer = bd_edge((PAL, False), (PAL, False), 3)
    assert reverse_edge(longer)[2] == 3
    assert longer not in orbit(E1)

    # The orbit quotient is well defined: reversal-equivalent edges agree on
    # both half-incidences.
    for e in edges:
        for v in (v0, (PAL, True)):
            assert pos_half(e, v) == pos_half(reverse_edge(e), v)
            assert neg_half(e, v) == neg_half(reverse_edge(e), v)

    print("PASS: 4 ATAT tagged orientations -> 3 unordered reversal orbits")
    print("PASS: mixed loop (1+,1-), ++ loop (2+,0-), -- loop (0+,2-)")
    print("PASS: unit mixed-sign orbit flow balanced with physical visit count 1")
    print("PASS: inherited departure throughput = 2 != physical visit count 1")
    print("PASS: distinct parallel overlap lengths are not identified")


if __name__ == "__main__":
    main()
