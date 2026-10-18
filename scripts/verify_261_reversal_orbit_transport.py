#!/usr/bin/env python3
"""Independent exact validation of the #255/#261 reversal-orbit transport result.

Scope: `AssemblyP1/Section62ReversalOrbitTransport.lean`.  That module shows
that the *first* disjunct of the pinned L2 flow-transport discipline
(`docs/section62-reversal-orbit-correspondence-gap-255.md`), namely requiring
`f e = f (reverseEdge e)` on tagged edge values, does **not** leave the physical
feasible set unchanged: for a self-loop orbit the inherited departure
`throughput` is always even, while the physical visit count of a unit
mixed-sign loop is one.

This script recomputes the witness from scratch with exact integer arithmetic
and no trust in the Lean output.  A tagged strand is `(word, bit)`; the class
representative is `(word, False)`; reversal toggles the bit; an edge is
`(sx, sy, len, sgnX, sgnY)` with `sgnX = +1` iff the departure strand is its own
class representative and `sgnY = -1` iff the arrival strand is its own class
representative (the `sgnRep`/`sgnTgt` convention at `rep = cls`).

Checked:
  * `reverseEdge` is an involution and maps the mixed-sign loop to a *distinct*
    tagged edge in the same physical reversal orbit;
  * the mixed-sign loop is a self-loop (both endpoints in class `(False, False)`);
  * its physical positive half-incidence at the class is one;
  * for the two-element edge list `[mixedLoop, reverseEdge mixedLoop]` the
    inherited departure `throughput` equals `f e + f (reverseEdge e)`;
  * consequently, for every reversal-symmetric flow the inherited departure
    throughput is even, and no reversal-symmetric flow realizes the physical
    visit count one.

The script is deterministic, exits non-zero on any failed assertion, and shares
no code with the Lean module.
"""

from itertools import product


def cls(s):
    return (s[0], False)


def flip(s):
    return (s[0], not s[1])


def reverse_edge(e):
    sx, sy, length, a, b = e
    return (flip(sy), flip(sx), length, b, a)


def pos_half(e, v):
    sx, sy, _length, a, b = e
    return int(cls(sx) == v and a == 1) + int(cls(sy) == v and b == 1)


def neg_half(e, v):
    sx, sy, _length, a, b = e
    return int(cls(sx) == v and a == -1) + int(cls(sy) == v and b == -1)


def throughput(f, edges, v):
    return sum(f[e] for e in edges if cls(e[0]) == v)


# The length-1 mixed-sign self-loop over the two-symbol alphabet (False, True),
# exactly as `AssemblyP1.Section62PhysicalHalfIncidence.mixedLoop`.
MIXED = ((False, False), (False, False), 1, 1, -1)
V0 = (False, False)


def main() -> int:
    checks = 0

    mixed_rev = reverse_edge(MIXED)
    assert mixed_rev != MIXED, "reverseEdge mixedLoop must be a distinct tagged edge"
    checks += 1
    assert reverse_edge(mixed_rev) == MIXED, "reverseEdge must be an involution"
    checks += 1
    # Same physical orbit: reversal forgets the orientation bit at both ends.
    assert (cls(mixed_rev[0]), cls(mixed_rev[1])) == (cls(MIXED[0]), cls(MIXED[1])), \
        "both representations must lie in one physical orbit"
    checks += 1

    # The mixed-sign loop is a self-loop in class V0.
    assert cls(MIXED[0]) == cls(MIXED[1]) == V0, "mixedLoop must be a self-loop at V0"
    checks += 1

    # Physical positive half-incidence one, negative half-incidence one.
    assert pos_half(MIXED, V0) == 1, "posHalf of the mixed-sign loop must be 1"
    assert neg_half(MIXED, V0) == 1, "negHalf of the mixed-sign loop must be 1"
    checks += 2
    assert pos_half(mixed_rev, V0) == 1, "posHalf must be reversal-invariant"
    assert neg_half(mixed_rev, V0) == 1, "negHalf must be reversal-invariant"
    checks += 2

    edges = [MIXED, mixed_rev]

    # General pair identity: throughput = f e + f (reverseEdge e).
    for a, b in product(range(6), repeat=2):
        f = {MIXED: a, mixed_rev: b}
        assert throughput(f, edges, V0) == a + b, "pair transport identity failed"
        checks += 1

    # Reversal-symmetric flows: even inherited throughput, never one.
    for k in range(0, 20):
        f = {MIXED: k, mixed_rev: k}
        t = throughput(f, edges, V0)
        assert t == 2 * k, "symmetric flow must give even throughput"
        assert t != 1, "no symmetric flow may realize physical visit count one"
        checks += 2

    # Exhaustive small symmetric-flow sweep: the only value attained is even.
    attained = {throughput({MIXED: k, mixed_rev: k}, edges, V0) for k in range(0, 8)}
    assert attained == {0, 2, 4, 6, 8, 10, 12, 14}, f"unexpected symmetric image {attained}"
    assert 1 not in attained, "physical visit count one is unreachable by a symmetric flow"
    checks += 2

    print(f"reversal-orbit transport checks passed ({checks} assertions)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
