#!/usr/bin/env python3
"""Exhaustive small-case cross-check for the ANTIPARALLEL-BRIDGE rigidity
criterion of Antonina board issue #257 (AssemblyP1,
``github.com/ottojung/assemblyp1``), scope §8.1.

Claim (proved and kernel-checked in ``AssemblyP1/RigidityBridge.lean``,
theorem ``bridge_nonrigid_iff`` and ``bridgeA_rigid_iff_trivial``):

    The bridge graph has vertices ``v, x, y`` and six arcs
      ``0: v->x``, ``1: x->v``, ``2: v->y``, ``3: y->v``, ``4: x->y``,
      ``5: y->x``.
    With multiplicities ``m1, m2, f >= 1`` (``m1`` on arcs 0,1; ``m2`` on arcs
    2,3; ``f`` on arcs 4,5), the base circulation ``A`` is NOT rigid iff there
    are integers ``a, c, p, q``, not all zero, with
      ``2a + 2c + p + q = 0``                       (zero total mass)
      ``a >= 1 - m1``, ``a + q - p >= 1 - m1``,     (x-cycle box)
      ``c >= 1 - m2``, ``c + p - q >= 1 - m2``,     (y-cycle box)
      ``p >= 1 - f``,  ``q >= 1 - f``.              (bridge box)
    Equivalently (``bridgeA_rigid_iff_trivial``) ``A`` is rigid iff
    ``m1 = m2 = f = 1``.

The script is self-contained (no repository import), uses exact integer
arithmetic, and is deterministic. Parts:

* ``bruteforce``: for every ``(m1, m2, f)`` in a small exhaustive scope,
  compute rigidity from scratch by enumerating *all* positive integer
  circulations of total ``G`` on the bridge graph, and compare with the
  four-variable criterion and with the trivial-rigidity classification. Exit
  non-zero on any mismatch.
* ``witnesses``: re-derive the kernel-checked non-rigidity witnesses for the
  three non-trivial families.

Exit code is non-zero if any check fails.
"""
from __future__ import annotations

import sys
from itertools import product

# bridge graph
ARCS = [(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1)]
NV = 3
OUT = [[] for _ in range(NV)]
INN = [[] for _ in range(NV)]
for _i, (_u, _w) in enumerate(ARCS):
    OUT[_u].append(_i)
    INN[_w].append(_i)
M = len(ARCS)


def base(m1, m2, f):
    return [m1, m1, m2, m2, f, f]


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


def nonrigid_criterion(m1, m2, f, bound=14):
    """Brute-force the four-variable criterion. Returns a witness or None."""
    lo_a, lo_c, lo_p, lo_q = 1 - m1, 1 - m2, 1 - f, 1 - f
    for a in range(lo_a, bound + 1):
        for c in range(lo_c, bound + 1):
            for p in range(lo_p, bound + 1):
                q = -2 * a - 2 * c - p
                if q < lo_q or q > bound:
                    continue
                if a == 0 and c == 0 and p == 0 and q == 0:
                    continue
                # δ = (a, a+q-p, c, c+p-q, p, q)
                if a + q - p < lo_a or c + p - q < lo_c:
                    continue
                return (a, c, p, q)
    return None


def check_bruteforce(mmax=10):
    tested = bad = 0
    for m1 in range(1, mmax + 1):
        for m2 in range(1, mmax + 1):
            for f in range(1, mmax + 1):
                G = 2 * (m1 + m2 + f)
                if G > 44:
                    continue
                rigid_bf = is_rigid_bruteforce(m1, m2, f)
                w = nonrigid_criterion(m1, m2, f)
                nonrigid_crit = w is not None
                trivial = (m1 == 1 and m2 == 1 and f == 1)
                tested += 1
                if rigid_bf != (not nonrigid_crit) or rigid_bf != trivial:
                    bad += 1
                    print(f"MISMATCH m1={m1} m2={m2} f={f} rigid_bf={rigid_bf} "
                          f"crit_nonrigid={nonrigid_crit} trivial_rigid={trivial} "
                          f"witness={w}")
    print(f"[bruteforce] tested {tested} bridges, mismatches {bad}")
    return bad == 0


def check_witnesses():
    ok = True
    cases = [
        (2, 1, 1, (-1, 0, 1, 1), (-1, -1, 0, 0, 1, 1)),
        (1, 2, 1, (0, -1, 1, 1), (0, 0, -1, -1, 1, 1)),
        (1, 1, 2, (0, 1, -1, -1), (0, 0, 1, 1, -1, -1)),
    ]
    for m1, m2, f, (a, c, p, q), delta in cases:
        A = base(m1, m2, f)
        d = [a, a + q - p, c, c + p - q, p, q]
        zero_sum = sum(d) == 0
        box = all(A[e] + d[e] >= 1 for e in range(M))
        bal = balanced(d)
        nonzero = any(v != 0 for v in d)
        this = zero_sum and box and bal and nonzero and tuple(d) == delta
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
