#!/usr/bin/env python3
"""Exhaustive small-case cross-check for the GENERAL p,q LONG-BRIDGE rigidity
criterion of Antonina board issue #257 (AssemblyP1,
``github.com/ottojung/assemblyp1``), scope §8.1.

Claim (proved and kernel-checked in ``AssemblyP1/RigidityGeneralBridge.lean``,
theorem ``generalBridge_nonrigid_iff``):

    The general long bridge has a hub ``v=0``, a ``p``-cycle
      ``C1: v -> x -> a2 -> ... -> v``   (arcs ``0..p-1``)
    and a ``q``-cycle
      ``C2: v -> y -> b2 -> ... -> v``   (arcs ``p..p+q-1``)
    joined by the antiparallel bridge ``x -> y``, ``y -> x``
    (arcs ``p+q``, ``p+q+1``).
    With multiplicities ``m1`` on each ``C1`` arc, ``m2`` on each ``C2`` arc and
    ``f`` on each bridge arc, the base circulation ``A`` is NOT rigid iff there
    are integers ``a, c, u, w``, not all zero, with
      ``p*a + q*c + (q-p+1)*u + (p-q+1)*w = 0``        (zero total mass)
      ``a >= 1 - m1``, ``a - u + w >= 1 - m1``,        (C1 box)
      ``c >= 1 - m2``, ``c - w + u >= 1 - m2``,        (C2 box)
      ``u >= 1 - f``,  ``w >= 1 - f``.                 (bridge box)

    At ``p = q = 2`` this is the merged bridge criterion
    (``RigidityBridge.bridge_nonrigid_iff``, coefficients ``2,2,1,1``); at
    ``p = q = 3`` it is the length-3 bridge criterion
    (``RigidityLength3Bridge.length3Bridge_nonrigid_iff``, coefficients
    ``3,3,1,1``). Unlike either, the general criterion is genuinely
    ``p,q``-dependent: the instance ``(p,q,m1,m2,f) = (3,4,2,1,1)`` is rigid
    although the first cycle is traversed twice.

The script is self-contained (no repository import), uses exact integer
arithmetic, and is deterministic. Parts:

* ``bruteforce``: for every ``(p,q,m1,m2,f)`` in a small exhaustive scope,
  compute rigidity from scratch by enumerating *all* positive integer
  circulations of total ``G`` on the ``p+q+2`` arcs, and compare with the
  four-variable criterion. Exit non-zero on any mismatch.
* ``witnesses``: re-derive the kernel-checked non-rigidity witnesses and the
  ``p,q``-dependent rigid repetitive instance.

Exit code is non-zero if any check fails.
"""
from __future__ import annotations

import sys


def build(p, q):
    """Return (OUT, INN, M) for the general p,q long bridge."""
    n = p + q - 1
    arcs = []
    for i in range(p):
        arcs.append((i, i + 1 if i + 1 < p else 0))
    arcs.append((0, p))
    for j in range(p, p + q - 1):
        arcs.append((j, j + 1 if j + 1 < p + q - 1 else 0))
    arcs.append((1, p))
    arcs.append((p, 1))
    out = [[] for _ in range(n)]
    inn = [[] for _ in range(n)]
    for idx, (u, w) in enumerate(arcs):
        out[u].append(idx)
        inn[w].append(idx)
    return out, inn, len(arcs)


def base(p, q, m1, m2, f):
    return [m1] * p + [m2] * q + [f, f]


def balanced(out, inn, B):
    return all(sum(B[e] for e in out[v]) == sum(B[e] for e in inn[v])
               for v in range(len(out)))


def enum_positive_circulations(out, inn, M, G):
    B = [0] * M

    def rec(i, remaining):
        if i == M:
            if remaining == 0 and balanced(out, inn, B):
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


def is_rigid_bruteforce(p, q, m1, m2, f):
    out, inn, M = build(p, q)
    A = base(p, q, m1, m2, f)
    G = sum(A)
    for B in enum_positive_circulations(out, inn, M, G):
        if B != tuple(A):
            return False
    return True


def nonrigid_criterion(p, q, m1, m2, f, bound):
    """Brute-force the four-variable criterion. Returns a witness or None.

    Iterates ``a, c, u`` in the box and solves the zero-sum equation for ``w``
    exactly (the coefficient of ``w`` is ``p-q+1``)."""
    lo_a, lo_c, lo_u, lo_w = 1 - m1, 1 - m2, 1 - f, 1 - f
    beta = p - q + 1
    for a in range(lo_a, bound + 1):
        for c in range(lo_c, bound + 1):
            for u in range(lo_u, bound + 1):
                rhs = -(p * a + q * c + (q - p + 1) * u)
                if beta == 0:
                    if rhs != 0:
                        continue
                    for w in range(lo_w, bound + 1):
                        if (a, c, u, w) == (0, 0, 0, 0):
                            continue
                        if a - u + w < lo_a or c - w + u < lo_c:
                            continue
                        return (a, c, u, w)
                    continue
                if rhs % beta != 0:
                    continue
                w = rhs // beta
                if w < lo_w or w > bound:
                    continue
                if (a, c, u, w) == (0, 0, 0, 0):
                    continue
                if a - u + w < lo_a or c - w + u < lo_c:
                    continue
                return (a, c, u, w)
    return None


def phi(p, q, a, c, u, w):
    d = [a] * p + [c] * q
    d = [a] + [a - u + w] * (p - 1) + [c] + [c - w + u] * (q - 1) + [u, w]
    return d


def check_bruteforce(pmax=4, qmax=4, mmax=4, fmax=5, gmax=22):
    tested = bad = 0
    for p in range(2, pmax + 1):
        for q in range(2, qmax + 1):
            for m1 in range(1, mmax + 1):
                for m2 in range(1, mmax + 1):
                    for f in range(1, fmax + 1):
                        G = p * m1 + q * m2 + 2 * f
                        if G > gmax:
                            continue
                        rigid_bf = is_rigid_bruteforce(p, q, m1, m2, f)
                        wit = nonrigid_criterion(p, q, m1, m2, f, bound=G)
                        nonrigid_crit = wit is not None
                        tested += 1
                        if rigid_bf == nonrigid_crit:
                            bad += 1
                            print(f"MISMATCH p={p} q={q} m1={m1} m2={m2} f={f} "
                                  f"rigid_bf={rigid_bf} crit_nonrigid={nonrigid_crit} "
                                  f"witness={wit}")
    print(f"[bruteforce] tested {tested} general bridges "
          f"(2<=p,q<={pmax}, 1<=m1,m2<={mmax}, 1<=f<={fmax}, G<={gmax}), "
          f"mismatches {bad}")
    return bad == 0


def check_witness(p, q, m1, m2, f, acuw, label):
    a, c, u, w = acuw
    d = phi(p, q, a, c, u, w)
    A = base(p, q, m1, m2, f)
    zero_sum = sum(d) == 0
    box = all(A[e] + d[e] >= 1 for e in range(len(A)))
    out, inn, _ = build(p, q)
    bal = balanced(out, inn, d)
    nonzero = any(v != 0 for v in d)
    ok = zero_sum and box and bal and nonzero
    print(f"[witness] {label} (p,q,m1,m2,f)=({p},{q},{m1},{m2},{f}) "
          f"(a,c,u,w)={acuw} delta={tuple(d)} zero_sum={zero_sum} box={box} "
          f"balanced={bal} nonzero={nonzero} ok={ok}")
    return ok


def check_witnesses():
    ok = True
    # general p,q witnesses
    ok &= check_witness(5, 3, 1, 6, 2, (3, -5, 0, 0), "m2>=p+1 (q,-p,0,0)")
    ok &= check_witness(3, 5, 6, 1, 2, (-5, 3, 0, 0), "m1>=q+1 (-q,p,0,0)")
    # p = q witnesses
    ok &= check_witness(4, 4, 2, 1, 1, (-1, 1, 0, 0), "p=q, m1>=2")
    ok &= check_witness(4, 4, 1, 2, 1, (1, -1, 0, 0), "p=q, m2>=2")
    # q = 3 bridge repetition, arbitrary p
    ok &= check_witness(5, 3, 1, 1, 3, (1, 0, -1, -2), "q=3, f>=3")
    ok &= check_witness(3, 3, 1, 1, 3, (1, 0, -1, -2), "q=3 (p=3), f>=3")
    # p = q = 2 and p = q = 3 specialisations of the merged criteria
    ok &= check_witness(2, 2, 2, 1, 1, (-1, 1, 0, 0), "merged 2-cycle, m1>=2")
    ok &= check_witness(3, 3, 1, 1, 3, (1, 0, -1, -2), "length-3, f>=3")
    return ok


def check_rigid_repetitive():
    p, q, m1, m2, f = 3, 4, 2, 1, 1
    rigid_bf = is_rigid_bruteforce(p, q, m1, m2, f)
    G = p * m1 + q * m2 + 2 * f
    wit = nonrigid_criterion(p, q, m1, m2, f, bound=G)
    ok = rigid_bf and (wit is None)
    print(f"[rigid] p,q,m1,m2,f=({p},{q},{m1},{m2},{f}) "
          f"rigid_bruteforce={rigid_bf} criterion_witness={wit} ok={ok}")
    return ok


def main():
    results = [check_bruteforce(), check_witnesses(), check_rigid_repetitive()]
    if all(results):
        print("ALL CHECKS PASSED")
        return 0
    print("FAILURES DETECTED")
    return 1


if __name__ == "__main__":
    sys.exit(main())
