#!/usr/bin/env python3
"""Exhaustive small-case cross-check for the MULTI-HUB rigidity criterion of
Antonina board issue #257 (AssemblyP1, ``github.com/ottojung/assemblyp1``),
scope §8.1/§8.2.

Claim (proved and kernel-checked in ``AssemblyP1/RigidityMultiHub.lean``,
theorem ``multiHub_nonrigid_iff``):

    The *multi-hub* family joins two hubs ``u = 0`` and ``v = 1`` by ``k``
    internally vertex-disjoint ``u -> v`` paths and ``l`` internally
    vertex-disjoint ``v -> u`` paths, of arbitrary lengths ``L_i, M_j >= 1``.
    Its cycle rank is ``k + l - 1`` (unbounded).  Every circulation is constant
    on each path; writing ``alpha`` for the path value on each path, the two
    hubs give the single hub-balance equation

        ``sum_{u->v} alpha = sum_{v->u} alpha``,

    and the total mass is ``sum length * alpha``.  With multiplicities
    ``m >= 1`` with ``sum m(u->v) = sum m(v->u)``, the base circulation is NOT
    rigid iff there is a nonzero integer path-perturbation ``alpha`` with

        ``sum_{u->v} alpha = sum_{v->u} alpha``   (hub balance -- the coupling)
        ``sum length * alpha = 0``                (zero total mass)
        ``alpha_s >= 1 - m_s``                    (boxes)

    The hub-balance equation is *not* implied by the boxes: the instance
    ``p2``/``m2`` (lengths ``(1,3)`` each way, multiplicities ``(2,1)``) is
    rigid although the *relaxed* predicate obtained by dropping the hub balance
    is satisfied.

§8.2: because the path lengths are encoded in unary (explicit support), the
criterion is a two-equation nonnegative-integer uniqueness problem and is
decidable by a polynomial dynamic program in the input size.  This script
implements that DP (counting solutions up to 2) and cross-checks it against the
criterion and against from-scratch enumeration.

The script is self-contained (no repository import), uses exact integer
arithmetic, and is deterministic.  Exit code is non-zero on any failure.
"""
from __future__ import annotations

import sys
from itertools import product


# --------------------------------------------------------------------------
# graph construction
# --------------------------------------------------------------------------
def build_multi_hub(k, l, Ls, Ms):
    """Return (tail, head, nv, path_edges).  Hubs u=0, v=1.

    ``path_edges`` lists, for each path (first the ``k`` u->v paths, then the
    ``l`` v->u paths), the indices of its arcs.
    """
    tail, head = [], []
    nv = 2

    def add_path(a, b, length):
        nonlocal nv
        prev = a
        edges = []
        for t in range(length):
            h = b if t == length - 1 else nv
            if t != length - 1:
                nv += 1
            edges.append(len(tail))
            tail.append(prev)
            head.append(h)
            prev = h
        return edges

    path_edges = [add_path(0, 1, Li) for Li in Ls]
    path_edges += [add_path(1, 0, Mj) for Mj in Ms]
    return tail, head, nv, path_edges


def base_circulation(tail, head, path_edges, ms, ns):
    B = [0] * len(tail)
    for i, pe in enumerate(path_edges):
        val = ms[i] if i < len(ms) else ns[i - len(ms)]
        for e in pe:
            B[e] = val
    return tuple(B)


# --------------------------------------------------------------------------
# from-scratch brute force
# --------------------------------------------------------------------------
def is_balanced(tail, head, nv, B):
    for v in range(nv):
        out = sum(B[e] for e in range(len(tail)) if tail[e] == v)
        inn = sum(B[e] for e in range(len(head)) if head[e] == v)
        if out != inn:
            return False
    return True


def enum_positive_circulations(tail, head, nv, G, limit=2):
    """Yield up to ``limit`` positive integer circulations of total ``G``."""
    M = len(tail)
    B = [0] * M
    found = 0
    inc_of = [[e for e in range(M) if tail[e] == v or head[e] == v] for v in range(nv)]

    def balanced_partial(upto):
        for v in range(nv):
            inc = inc_of[v]
            if inc and max(inc) < upto:
                out = sum(B[e] for e in inc if tail[e] == v)
                inn = sum(B[e] for e in inc if head[e] == v)
                if out != inn:
                    return False
        return True

    def rec(i, remaining):
        nonlocal found
        if found >= limit:
            return
        if i == M:
            if remaining == 0 and is_balanced(tail, head, nv, B):
                yield tuple(B)
                found += 1
            return
        lo = 1
        hi = remaining - (M - i - 1)
        for val in range(lo, hi + 1):
            B[i] = val
            if balanced_partial(i + 1):
                yield from rec(i + 1, remaining - val)
        B[i] = 0

    yield from rec(0, G)


def is_rigid_bruteforce(tail, head, nv, A, G):
    cnt = 0
    for B in enum_positive_circulations(tail, head, nv, G, limit=2):
        cnt += 1
        if B != A:
            return False
    return cnt == 1


# --------------------------------------------------------------------------
# the criterion (direct search) and the polynomial DP decision
# --------------------------------------------------------------------------
def count_decompositions(gens, cap_count, cap_mass):
    """DP: (count, mass) -> number of nonneg combos of ``gens`` (capped at 2)."""
    cur = {(0, 0): 1}
    for (dc, dm) in gens:
        nxt = {}
        for (c, m), ways in cur.items():
            t = 0
            while c + t * dc <= cap_count and m + t * dm <= cap_mass:
                key = (c + t * dc, m + t * dm)
                nxt[key] = min(2, nxt.get(key, 0) + ways)
                t += 1
        cur = nxt
    return cur


def criterion_nonrigid(k, l, Ls, Ms, ms, ns):
    """Return (nonrigid?, nsolutions) for the two-equation criterion.

    Uses the same DP as the polynomial decision: the number of solution pairs
    ``(u, v)`` of ``sum u - sum v = l - k`` and ``sum L u + sum M v = C`` with
    ``u, v >= 0``.  The base solution is one of them, so non-rigid iff >= 2.
    """
    G = sum(Ls[i] * ms[i] for i in range(k)) + sum(Ms[j] * ns[j] for j in range(l))
    E = sum(Ls) + sum(Ms)
    C = G - E
    if C < 0:
        return False, 0
    U = count_decompositions([(1, Ls[i]) for i in range(k)], C, C)
    V = count_decompositions([(1, Ms[j]) for j in range(l)], C, C)
    target_dc = l - k
    total = 0
    for (pu, qu), wu in U.items():
        pv = pu - target_dc
        qv = C - qu
        if qv < 0:
            continue
        wv = V.get((pv, qv), 0)
        total = min(2, total + wu * wv)
    return total >= 2, total


def relaxed_nonrigid(k, l, Ls, Ms, ms, ns):
    """The coupling-dropped (bouquet-style) relaxation: exists nonzero alpha
    with zero total mass and boxes, ignoring hub balance."""
    G = sum(Ls[i] * ms[i] for i in range(k)) + sum(Ms[j] * ns[j] for j in range(l))
    E = sum(Ls) + sum(Ms)
    C = G - E
    # search over bounded alpha
    bound = C + 2
    for alpha in product(range(-bound, bound + 1), repeat=k + l):
        if all(a == 0 for a in alpha):
            continue
        mass = sum((Ls[i] if i < k else Ms[i - k]) * alpha[i] for i in range(k + l))
        if mass != 0:
            continue
        ok = True
        for i in range(k + l):
            m = ms[i] if i < k else ns[i - k]
            if alpha[i] < 1 - m:
                ok = False
                break
        if ok:
            return True
    return False


# --------------------------------------------------------------------------
# checks
# --------------------------------------------------------------------------
def check_scope(k, l, Ls, Ms, mmax, gmax, results):
    tail, head, nv, pe = build_multi_hub(k, l, Ls, Ms)
    tested = 0
    mism = 0
    nonrigid = 0
    for ms in product(range(1, mmax + 1), repeat=k):
        for ns in product(range(1, mmax + 1), repeat=l):
            if sum(ms) != sum(ns):
                continue
            A = base_circulation(tail, head, pe, list(ms), list(ns))
            G = sum(A)
            if G > gmax:
                continue
            tested += 1
            bf = not is_rigid_bruteforce(tail, head, nv, A, G)
            crit, _ = criterion_nonrigid(k, l, Ls, Ms, list(ms), list(ns))
            if bf != crit:
                mism += 1
                print(f"  MISMATCH k={k} l={l} L={Ls} M={Ms} m={ms} n={ns} G={G} "
                      f"bruteforce_nonrigid={bf} criterion_nonrigid={crit}")
            if bf:
                nonrigid += 1
    results.append(mism == 0)
    print(f"[bruteforce] k={k} l={l} L={Ls} M={Ms}: tested={tested} "
          f"nonrigid={nonrigid} mismatches={mism}")
    return tested


def check_rigid_repetitive():
    """p2/m2: lengths (1,3) each way, multiplicities (2,1) -> rigid, despite the
    length-1 path being traversed twice."""
    k = l = 2
    Ls = Ms = [1, 3]
    ms = ns = [2, 1]
    tail, head, nv, pe = build_multi_hub(k, l, Ls, Ms)
    A = base_circulation(tail, head, pe, ms, ns)
    G = sum(A)
    bf_rigid = is_rigid_bruteforce(tail, head, nv, A, G)
    crit, nsol = criterion_nonrigid(k, l, Ls, Ms, ms, ns)
    ok = bf_rigid and not crit and nsol == 1
    print(f"[rigid-repetitive] L={Ls} M={Ms} m={ms} n={ns} G={G}: "
          f"bruteforce_rigid={bf_rigid} criterion_nonrigid={crit} nsolutions={nsol} "
          f"-> {'OK' if ok else 'FAIL'}")
    return ok


def check_relaxed_not_sound():
    """At p2/m2 the relaxed predicate holds while the instance is rigid."""
    k = l = 2
    Ls = Ms = [1, 3]
    ms = ns = [2, 1]
    tail, head, nv, pe = build_multi_hub(k, l, Ls, Ms)
    A = base_circulation(tail, head, pe, ms, ns)
    G = sum(A)
    bf_rigid = is_rigid_bruteforce(tail, head, nv, A, G)
    relaxed = relaxed_nonrigid(k, l, Ls, Ms, ms, ns)
    ok = bf_rigid and relaxed
    print(f"[relaxed] L={Ls} M={Ms} m={ms} n={ns}: rigid={bf_rigid} "
          f"relaxed_nonrigid={relaxed} -> {'OK' if ok else 'FAIL'}")
    return ok


def check_all_one_rigid():
    """All multiplicities 1 is rigid (boxes force alpha >= 0; positive lengths
    force alpha = 0)."""
    k = l = 2
    Ls, Ms = [1, 2], [2, 3]
    ms = ns = [1, 1]
    tail, head, nv, pe = build_multi_hub(k, l, Ls, Ms)
    A = base_circulation(tail, head, pe, ms, ns)
    G = sum(A)
    bf_rigid = is_rigid_bruteforce(tail, head, nv, A, G)
    crit, nsol = criterion_nonrigid(k, l, Ls, Ms, ms, ns)
    ok = bf_rigid and not crit
    print(f"[all-one] L={Ls} M={Ms} m={ms} n={ns}: rigid={bf_rigid} "
          f"criterion_nonrigid={crit} nsolutions={nsol} -> {'OK' if ok else 'FAIL'}")
    return ok


def main():
    results = []

    # Exhaustive small scopes (unbounded cycle rank k + l - 1).
    check_scope(1, 1, [1], [2], 4, 12, results)          # bouquet-like
    check_scope(2, 2, [1, 2], [1, 2], 4, 14, results)    # double theta / two-hub
    check_scope(2, 2, [1, 3], [1, 3], 4, 16, results)    # p2/m2 scope
    check_scope(3, 3, [1, 2, 3], [1, 2, 3], 3, 16, results)
    check_scope(3, 2, [1, 2, 2], [1, 3], 3, 15, results)
    check_scope(4, 4, [1, 1, 2, 2], [1, 2, 3, 1], 2, 16, results)
    check_scope(2, 3, [1, 2], [1, 1, 3], 3, 14, results)

    results.append(check_rigid_repetitive())
    results.append(check_relaxed_not_sound())
    results.append(check_all_one_rigid())

    print()
    if all(results):
        print("ALL CHECKS PASSED")
        return 0
    print("FAILURES DETECTED")
    return 1


if __name__ == "__main__":
    sys.exit(main())
