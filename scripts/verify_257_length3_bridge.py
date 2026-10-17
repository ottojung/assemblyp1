#!/usr/bin/env python3
"""Exhaustive small-case cross-check for the LENGTH-3 ANTIPARALLEL BRIDGE
rigidity criterion of Antonina board issue #257 (AssemblyP1,
``github.com/ottojung/assemblyp1``), scope §8.1.

Claim (proved and kernel-checked in ``AssemblyP1/RigidityLength3Bridge.lean``,
theorems ``length3Bridge_nonrigid_iff`` and ``length3Bridge_rigid_iff``):

    The length-3 bridge has vertices ``v=0, x=1, a2=2, y=3, b2=4`` and eight
    arcs
      ``0: v->x``,  ``1: x->a2``,  ``2: a2->v``,
      ``3: v->y``,  ``4: y->b2``,  ``5: b2->v``,
      ``6: x->y``,  ``7: y->x``.
    With multiplicities ``m1, m2, f >= 1`` (``m1`` on arcs 0,1,2; ``m2`` on
    arcs 3,4,5; ``f`` on arcs 6,7), the base circulation ``A`` is NOT rigid iff
    there are integers ``a, c, u, w``, not all zero, with
      ``3a + 3c + u + w = 0``                       (zero total mass)
      ``a >= 1 - m1``, ``a - u + w >= 1 - m1``,     (C1 box)
      ``c >= 1 - m2``, ``c - w + u >= 1 - m2``,     (C2 box)
      ``u >= 1 - f``,  ``w >= 1 - f``.              (bridge box)
    Equivalently (``length3Bridge_rigid_iff``) ``A`` is rigid iff
    ``m1 = 1`` and ``m2 = 1`` and ``f <= 2``.

    This REFUTES the naive generalisation of the merged 2-cycle bridge
    classification (``RigidityBridge.bridgeA_rigid_iff_trivial``, rigid iff all
    multiplicities are 1): the length-3 bridge with ``(m1, m2, f) = (1, 1, 2)``
    is a rigid *repetitive* support.

The script is self-contained (no repository import), uses exact integer
arithmetic, and is deterministic. Parts:

* ``bruteforce``: for every ``(m1, m2, f)`` in a small exhaustive scope,
  compute rigidity from scratch by enumerating *all* positive integer
  circulations of total ``G`` on the eight-arc graph, and compare with the
  four-variable criterion and with the classification. Exit non-zero on any
  mismatch.
* ``witnesses``: re-derive the kernel-checked non-rigidity witnesses for the
  three non-trivial families and the rigid repetitive instance.

Exit code is non-zero if any check fails.
"""
from __future__ import annotations

import sys

# length-3 bridge graph
ARCS = [(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 0), (1, 3), (3, 1)]
NV = 5
OUT = [[] for _ in range(NV)]
INN = [[] for _ in range(NV)]
for _i, (_u, _w) in enumerate(ARCS):
    OUT[_u].append(_i)
    INN[_w].append(_i)
M = len(ARCS)


def base(m1, m2, f):
    return [m1, m1, m1, m2, m2, m2, f, f]


def balanced(B):
    return all(sum(B[e] for e in OUT[v]) == sum(B[e] for e in INN[v])
               for v in range(NV))


def enum_positive_circulations(G):
    B = [0] * M

    def rec(i, remaining):
        if i == M:
            if balanced(B) and remaining == 0:
                yield tuple(B)
            return
        lo = 1
        hi = remaining - (M - i - 1)
        if hi < lo:
            return
        for val in range(lo, hi + 1):
            B[i] = val
            yield from rec(i + 1, remaining - val)
        B[i] = 0

    yield from rec(0, G)


def is_rigid_bruteforce(m1, m2, f):
    A = base(m1, m2, f)
    G = sum(A)
    for B in enum_positive_circulations(G):
        if B != tuple(A):
            return False
    return True


def nonrigid_criterion(m1, m2, f, bound=24):
    """Brute-force the four-variable criterion. Returns a witness or None."""
    lo_a, lo_c, lo_u, lo_w = 1 - m1, 1 - m2, 1 - f, 1 - f
    for a in range(lo_a, bound + 1):
        for c in range(lo_c, bound + 1):
            for u in range(lo_u, bound + 1):
                w = -3 * a - 3 * c - u
                if w < lo_w or w > bound:
                    continue
                if a == 0 and c == 0 and u == 0 and w == 0:
                    continue
                if a - u + w < lo_a or c - w + u < lo_c:
                    continue
                return (a, c, u, w)
    return None


def phi(a, c, u, w):
    return [a, a - u + w, a - u + w, c, c - w + u, c - w + u, u, w]


def check_bruteforce(gmax=40):
    tested = bad = 0
    for m1 in range(1, 7):
        for m2 in range(1, 7):
            for f in range(1, 9):
                G = 3 * (m1 + m2) + 2 * f
                if G > gmax:
                    continue
                rigid_bf = is_rigid_bruteforce(m1, m2, f)
                w = nonrigid_criterion(m1, m2, f, bound=G)
                nonrigid_crit = w is not None
                classified = (m1 == 1 and m2 == 1 and f <= 2)
                tested += 1
                if rigid_bf != (not nonrigid_crit) or rigid_bf != classified:
                    bad += 1
                    print(f"MISMATCH m1={m1} m2={m2} f={f} rigid_bf={rigid_bf} "
                          f"crit_nonrigid={nonrigid_crit} classified_rigid={classified} "
                          f"witness={w}")
    print(f"[bruteforce] tested {tested} length-3 bridges, mismatches {bad}")
    return bad == 0


def check_witnesses():
    ok = True
    cases = [
        # (m1, m2, f, (a, c, u, w), expected delta, expected_nonrigid)
        (2, 1, 1, (-1, 1, 0, 0), [-1, -1, -1, 1, 1, 1, 0, 0], True),
        (1, 2, 1, (1, -1, 0, 0), [1, 1, 1, -1, -1, -1, 0, 0], True),
        (1, 1, 3, (1, 0, -1, -2), [1, 0, 0, 0, 1, 1, -1, -2], True),
        (1, 1, 2, None, None, False),  # rigid repetitive
    ]
    for m1, m2, f, acuw, delta, expect_nonrigid in cases:
        A = base(m1, m2, f)
        if acuw is None:
            # rigid repetitive: no nonzero criterion witness with 3a+3c+u+w=0
            w = nonrigid_criterion(m1, m2, f)
            rigid_bf = is_rigid_bruteforce(m1, m2, f)
            this = (w is None) and rigid_bf
            print(f"[witness] m1={m1} m2={m2} f={f} RIGID repetitive "
                  f"criterion_witness={w} rigid_bruteforce={rigid_bf} ok={this}")
            ok = ok and this
            continue
        a, c, u, w = acuw
        d = phi(a, c, u, w)
        zero_sum = sum(d) == 0
        box = all(A[e] + d[e] >= 1 for e in range(M))
        bal = balanced(d)
        nonzero = any(v != 0 for v in d)
        this = zero_sum and box and bal and nonzero and d == delta
        print(f"[witness] m1={m1} m2={m2} f={f} delta={tuple(d)} "
              f"zero_sum={zero_sum} box={box} balanced={bal} nonzero={nonzero} "
              f"ok={this}")
        ok = ok and this
    return ok


def main():
    results = [check_bruteforce(), check_witnesses()]
    if all(results):
        print("ALL CHECKS PASSED")
        return 0
    print("FAILURES DETECTED")
    return 1


if __name__ == "__main__":
    sys.exit(main())
