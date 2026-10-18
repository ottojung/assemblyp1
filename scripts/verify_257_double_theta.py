#!/usr/bin/env python3
"""Exhaustive small-case cross-check for the DOUBLE-THETA rigidity criterion of
Antonina board issue #257 (AssemblyP1, ``github.com/ottojung/assemblyp1``),
scope §8.1.

Claim (proved and kernel-checked in ``AssemblyP1/RigidityDoubleTheta.lean``,
theorem ``doubleTheta_nonrigid_iff``):

    The double-theta graph has hubs ``u=0`` and ``v=1`` and two degree-2
    vertices ``w=2``, ``z=3``, joined by two arcs/paths in each direction::

        e0: u -> v          (P1, length 1)
        e1: u -> w -> v     (P2, length 2, arcs e1,e2)
        e3: v -> u          (Q1, length 1)
        e4: v -> z -> u     (Q2, length 2, arcs e4,e5)

    With multiplicities ``m1`` on ``P1``, ``m2`` on each ``P2`` arc, ``n1`` on
    ``Q1`` and ``n2`` on each ``Q2`` arc (and balance ``m1 + m2 = n1 + n2``),
    the base circulation ``A`` is NOT rigid iff there are integers
    ``a, b, c, d``, not all zero, with

        ``a + b = c + d``                       (hub balance -- the coupling)
        ``a + 2*b + c + 2*d = 0``               (zero total mass)
        ``a >= 1 - m1``, ``b >= 1 - m2``,       (P1, P2 boxes)
        ``c >= 1 - n1``, ``d >= 1 - n2``.       (Q1, Q2 boxes)

    The hub-balance equation is *not* implied by the box constraints: the
    instance ``(m1,m2,n1,n2) = (2,1,2,1)`` is rigid although the *relaxed*
    predicate obtained by dropping ``a + b = c + d`` is satisfied.

The script is self-contained (no repository import), uses exact integer
arithmetic, and is deterministic. Parts:

* ``bruteforce``: for every ``(m1,m2,n1,n2)`` in a small exhaustive scope with
  ``m1 + m2 = n1 + n2``, compute rigidity from scratch by enumerating *all*
  positive integer circulations of total ``G`` on the six arcs, and compare with
  the four-variable criterion. Exit non-zero on any mismatch.
* ``witnesses``: re-derive the kernel-checked non-rigidity witness and the rigid
  repetitive instance.
* ``relaxed``: confirm that the relaxed (coupling-dropped) predicate is satisfied
  at the rigid instance ``(2,1,2,1)``, so the coupling equation is essential.
* ``rank2``: sanity check that every rank-2 theta graph (two cycles sharing a
  directed path) agrees with the *bouquet* criterion (the shared path value is
  the sum of the private path values, so no coupling), substantiating that
  coupling begins at rank 3.

Exit code is non-zero if any check fails.
"""
from __future__ import annotations

import sys

# Edges (tail, head) of the double-theta graph.
EDGES = [(0, 1), (0, 2), (2, 1), (1, 0), (1, 3), (3, 0)]
NVERT = 4


def base(m1, m2, n1, n2):
    return [m1, m2, m2, n1, n2, n2]


def balanced(B):
    for v in range(NVERT):
        out = sum(B[i] for i, (t, h) in enumerate(EDGES) if t == v)
        inn = sum(B[i] for i, (t, h) in enumerate(EDGES) if h == v)
        if out != inn:
            return False
    return True


def enum_positive_circulations(G):
    M = len(EDGES)
    B = [0] * M

    def rec(i, remaining):
        if i == M:
            if remaining == 0 and balanced(B):
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


def is_rigid_bruteforce(m1, m2, n1, n2):
    A = base(m1, m2, n1, n2)
    G = sum(A)
    for B in enum_positive_circulations(G):
        if B != tuple(A):
            return False
    return True


def nonrigid_criterion(m1, m2, n1, n2, bound):
    """Brute-force the four-variable criterion. Returns a witness or None.

    Iterates ``a, b, c`` in the box and solves the zero-sum equation for ``d``
    exactly (the coefficient of ``d`` is 2)."""
    lo_a, lo_b, lo_c, lo_d = 1 - m1, 1 - m2, 1 - n1, 1 - n2
    for a in range(lo_a, bound + 1):
        for b in range(lo_b, bound + 1):
            for c in range(lo_c, bound + 1):
                rhs = -(a + 2 * b + c)
                if rhs % 2 != 0:
                    continue
                d = rhs // 2
                if d < lo_d or d > bound:
                    continue
                if (a, b, c, d) == (0, 0, 0, 0):
                    continue
                if a + b != c + d:
                    continue
                return (a, b, c, d)
    return None


def relaxed_witness(m1, m2, n1, n2, bound):
    """Witness of the *relaxed* predicate (hub balance dropped), or None."""
    lo_a, lo_b, lo_c, lo_d = 1 - m1, 1 - m2, 1 - n1, 1 - n2
    for a in range(lo_a, bound + 1):
        for b in range(lo_b, bound + 1):
            for c in range(lo_c, bound + 1):
                rhs = -(a + 2 * b + c)
                if rhs % 2 != 0:
                    continue
                d = rhs // 2
                if d < lo_d or d > bound:
                    continue
                if (a, b, c, d) == (0, 0, 0, 0):
                    continue
                return (a, b, c, d)
    return None


def check_bruteforce(mmax=5, gmax=16):
    tested = bad = 0
    for m1 in range(1, mmax + 1):
        for m2 in range(1, mmax + 1):
            for n1 in range(1, mmax + 1):
                for n2 in range(1, mmax + 1):
                    if m1 + m2 != n1 + n2:
                        continue
                    G = m1 + 2 * m2 + n1 + 2 * n2
                    if G > gmax:
                        continue
                    rigid_bf = is_rigid_bruteforce(m1, m2, n1, n2)
                    wit = nonrigid_criterion(m1, m2, n1, n2, bound=G)
                    nonrigid_crit = wit is not None
                    tested += 1
                    if rigid_bf == nonrigid_crit:
                        bad += 1
                        print(f"MISMATCH m1={m1} m2={m2} n1={n1} n2={n2} "
                              f"rigid_bf={rigid_bf} crit_nonrigid={nonrigid_crit} "
                              f"witness={wit}")
    print(f"[bruteforce] tested {tested} double thetas "
          f"(1<=m1,m2,n1,n2<={mmax}, m1+m2=n1+n2, G<={gmax}), mismatches {bad}")
    return bad == 0


def check_witnesses():
    ok = True

    def witness(m1, m2, n1, n2, abcd, label):
        nonlocal ok
        a, b, c, d = abcd
        delta = [a, b, b, c, d, d]
        A = base(m1, m2, n1, n2)
        zero_sum = sum(delta) == 0
        box = all(A[e] + delta[e] >= 1 for e in range(len(A)))
        bal = balanced(delta)
        nonzero = any(v != 0 for v in delta)
        hub = a + b == c + d
        good = zero_sum and box and bal and nonzero and hub
        ok &= good
        print(f"[witness] {label} (m1,m2,n1,n2)=({m1},{m2},{n1},{n2}) "
              f"(a,b,c,d)={abcd} delta={tuple(delta)} zero_sum={zero_sum} "
              f"box={box} balanced={bal} hub_balance={hub} nonzero={nonzero} "
              f"ok={good}")
        return good

    ok &= witness(1, 2, 1, 2, (2, -1, 2, -1), "kernel witness (1,2,1,2)")
    ok &= witness(2, 3, 4, 1, (-1, 0, -3, 2), "family m1>=2,n1>=4")
    ok &= witness(4, 1, 2, 3, (-3, 2, -1, 0), "family m1>=4,n1>=2")
    return ok


def check_rigid_repetitive():
    m1, m2, n1, n2 = 2, 1, 2, 1
    rigid_bf = is_rigid_bruteforce(m1, m2, n1, n2)
    G = m1 + 2 * m2 + n1 + 2 * n2
    wit = nonrigid_criterion(m1, m2, n1, n2, bound=G)
    ok = rigid_bf and (wit is None)
    print(f"[rigid] (m1,m2,n1,n2)=({m1},{m2},{n1},{n2}) "
          f"rigid_bruteforce={rigid_bf} criterion_witness={wit} ok={ok}")
    return ok


def check_relaxed():
    m1, m2, n1, n2 = 2, 1, 2, 1
    G = m1 + 2 * m2 + n1 + 2 * n2
    rw = relaxed_witness(m1, m2, n1, n2, bound=G)
    rigid_bf = is_rigid_bruteforce(m1, m2, n1, n2)
    crit = nonrigid_criterion(m1, m2, n1, n2, bound=G)
    ok = (rw is not None) and rigid_bf and (crit is None)
    print(f"[relaxed] (m1,m2,n1,n2)=({m1},{m2},{n1},{n2}) relaxed_witness={rw} "
          f"true_rigid={rigid_bf} exact_criterion_witness={crit} ok={ok}")
    return ok


def theta_graph(p, q1, q2):
    """The rank-2 theta graph: shared path P (u=0 -> v=1, p edges), return
    paths Q1 (v -> u, q1 edges) and Q2 (v -> u, q2 edges). Returns (edges, nv)."""
    edges = []
    nv = 2

    def add_path(a, b, length):
        nonlocal nv
        prev = a
        for i in range(length):
            if i == length - 1:
                head = b
            else:
                head = nv
                nv += 1
            edges.append((prev, head))
            prev = head

    add_path(0, 1, p)
    add_path(1, 0, q1)
    add_path(1, 0, q2)
    return edges, nv


def is_rigid_generic(edges, nv, A):
    """Brute-force rigidity on an arbitrary graph (edges, nv vertices)."""
    M = len(edges)
    G = sum(A)

    def balanced(B):
        for v in range(nv):
            out = sum(B[i] for i, (t, h) in enumerate(edges) if t == v)
            inn = sum(B[i] for i, (t, h) in enumerate(edges) if h == v)
            if out != inn:
                return False
        return True

    B = [0] * M

    def rec(i, remaining):
        if i == M:
            if remaining == 0 and balanced(B) and tuple(B) != tuple(A):
                return False
            return True
        lo = 1
        hi = remaining - (M - i - 1)
        if hi < lo:
            return True
        for val in range(lo, hi + 1):
            B[i] = val
            if not rec(i + 1, remaining - val):
                return False
        B[i] = 0
        return True

    return rec(0, G)


def bouquet_witness(L1, L2, m1, m2, bound):
    """Witness of the bouquet criterion on two cycles of lengths L1, L2 and
    multiplicities m1, m2, or None."""
    lo_x, lo_y = 1 - m1, 1 - m2
    for x in range(lo_x, bound + 1):
        for y in range(lo_y, bound + 1):
            if x == 0 and y == 0:
                continue
            if L1 * x + L2 * y == 0:
                return (x, y)
    return None


def check_rank2_theta(pmax=3, qmax=3, mmax=3, gmax=12):
    """Rank-2 sanity: every theta graph (two cycles sharing a directed path)
    satisfies the *bouquet* criterion (no coupling), because the shared path
    value is the sum of the two private path values."""
    tested = bad = 0
    for p in range(1, pmax + 1):
        for q1 in range(1, qmax + 1):
            for q2 in range(1, qmax + 1):
                edges, nv = theta_graph(p, q1, q2)
                for m1 in range(1, mmax + 1):
                    for m2 in range(1, mmax + 1):
                        mP = m1 + m2
                        A = [mP] * p + [m1] * q1 + [m2] * q2
                        G = sum(A)
                        if G > gmax:
                            continue
                        rigid_bf = is_rigid_generic(edges, nv, A)
                        L1, L2 = p + q1, p + q2
                        wit = bouquet_witness(L1, L2, m1, m2, bound=G)
                        nonrigid_crit = wit is not None
                        tested += 1
                        if rigid_bf == nonrigid_crit:
                            bad += 1
                            print(f"RANK2 MISMATCH p={p} q1={q1} q2={q2} "
                                  f"m1={m1} m2={m2} rigid_bf={rigid_bf} "
                                  f"bouquet_nonrigid={nonrigid_crit}")
    print(f"[rank2] tested {tested} theta graphs "
          f"(1<=p,q1,q2<={max(pmax, qmax)}, 1<=m1,m2<={mmax}, G<={gmax}), "
          f"mismatches {bad}")
    return bad == 0


def main():
    results = [check_bruteforce(), check_witnesses(), check_rigid_repetitive(),
               check_relaxed(), check_rank2_theta()]
    if all(results):
        print("ALL CHECKS PASSED")
        return 0
    print("FAILURES DETECTED")
    return 1


if __name__ == "__main__":
    sys.exit(main())
