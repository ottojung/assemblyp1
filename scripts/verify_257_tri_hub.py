#!/usr/bin/env python3
"""Exhaustive small-case cross-check for the TRIANGULAR MULTI-HUB rigidity
criterion of Antonina board issue #257 (AssemblyP1), scope §8.1/§8.2.

Claim (proved and kernel-checked in ``AssemblyP1/RigidityTriHub.lean``, theorem
``triHub_nonrigid_iff``):

    The *triangular multi-hub* family joins three hubs ``u=0, v=1, w=2`` in a
    directed cycle: ``a`` internally vertex-disjoint ``u -> v`` paths, ``b``
    ``v -> w`` paths and ``c`` ``w -> u`` paths, of arbitrary lengths
    ``plen >= 1``; cycle rank ``a + b + c - 2`` (unbounded).  Every circulation
    is constant on each path; with path values ``alpha, beta, gamma`` the hubs
    give two independent balance equations
        ``sum_{u->v} alpha = sum_{v->w} beta`` and
        ``sum_{v->w} beta  = sum_{w->u} gamma``,
    and total mass ``sum length*alpha + sum length*beta + sum length*gamma``.
    With multiplicities ``m >= 1`` and ``sum m(u->v) = sum m(v->w) = sum m(w->u)``
    the base circulation is NOT rigid iff there is a nonzero integer
    perturbation ``(alpha, beta, gamma)`` with hub balance, zero mass, and the
    boxes ``alpha_s >= 1 - m_s``.

The script is self-contained (no repository import), uses exact integer
arithmetic, and is deterministic.  Exit code is non-zero on any failure.
"""
from __future__ import annotations

import sys
from itertools import product


def build_tri_hub(a, b, c, Ls, Ms, Ns):
    """Return (tail, head, nv, path_edges).  Hubs u=0, v=1, w=2."""
    tail, head = [], []
    nv = 3

    def add_path(p, q, length):
        nonlocal nv
        prev = p
        edges = []
        for t in range(length):
            h = q if t == length - 1 else nv
            if t != length - 1:
                nv += 1
            edges.append(len(tail))
            tail.append(prev)
            head.append(h)
            prev = h
        return edges

    path_edges = [add_path(0, 1, Li) for Li in Ls]
    path_edges += [add_path(1, 2, Mj) for Mj in Ms]
    path_edges += [add_path(2, 0, Nk) for Nk in Ns]
    return tail, head, nv, path_edges


def base_circulation(tail, path_edges, ms, ns, ps):
    B = [0] * len(tail)
    vals = list(ms) + list(ns) + list(ps)
    for i, pe in enumerate(path_edges):
        for e in pe:
            B[e] = vals[i]
    return tuple(B)


def is_balanced(tail, head, nv, B):
    for v in range(nv):
        out = sum(B[e] for e in range(len(tail)) if tail[e] == v)
        inn = sum(B[e] for e in range(len(head)) if head[e] == v)
        if out != inn:
            return False
    return True


def enum_positive_circulations(tail, head, nv, G, limit=2):
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
        hi = remaining - (M - i - 1)
        for val in range(1, hi + 1):
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


def criterion_nonrigid(a, b, c, Ls, Ms, Ns, ms, ns, ps):
    """Direct bounded search over perturbations; returns (nonrigid?, witness)."""
    G = (sum(Ls[i] * ms[i] for i in range(a))
         + sum(Ms[j] * ns[j] for j in range(b))
         + sum(Ns[k] * ps[k] for k in range(c)))
    lo_a = [1 - ms[i] for i in range(a)]
    lo_b = [1 - ns[j] for j in range(b)]
    lo_c = [1 - ps[k] for k in range(c)]
    for al in product(*[range(lo_a[i], G + 1) for i in range(a)]):
        sa = sum(al)
        for be in product(*[range(lo_b[j], G + 1) for j in range(b)]):
            if sum(be) != sa:
                continue
            rem = -(sum(Ls[i] * al[i] for i in range(a))
                    + sum(Ms[j] * be[j] for j in range(b)))
            for ga in product(*[range(lo_c[k], G + 1) for k in range(c)]):
                if sum(ga) != sa:
                    continue
                if sum(Ns[k] * ga[k] for k in range(c)) != rem:
                    continue
                if all(v == 0 for v in al) and all(v == 0 for v in be) \
                        and all(v == 0 for v in ga):
                    continue
                return True, (al, be, ga)
    return False, None


def dp_nonrigid(a, b, c, Ls, Ms, Ns, ms, ns, ps):
    """Polynomial DP counting (up to 2) nonnegative solutions of the shifted
    system; base solution is one, so non-rigid iff count >= 2."""
    Kab = sum(ms[i] - 1 for i in range(a)) - sum(ns[j] - 1 for j in range(b))
    Kbc = sum(ns[j] - 1 for j in range(b)) - sum(ps[k] - 1 for k in range(c))
    Kmass = (sum(Ls[i] * (ms[i] - 1) for i in range(a))
             + sum(Ms[j] * (ns[j] - 1) for j in range(b))
             + sum(Ns[k] * (ps[k] - 1) for k in range(c)))
    if Kmass < 0:
        return False
    cur = {(0, 0, 0): 1}
    for (w, count, tag) in ((Ls, a, "a"), (Ms, b, "b"), (Ns, c, "c")):
        for i in range(count):
            L = w[i]
            nxt = {}
            for (d1, d2, m), ways in cur.items():
                t = 0
                while m + t * L <= Kmass:
                    nd1 = d1 + (t if tag == "a" else (-t if tag == "b" else 0))
                    nd2 = d2 + (t if tag == "b" else (-t if tag == "c" else 0))
                    key = (nd1, nd2, m + t * L)
                    nxt[key] = min(2, nxt.get(key, 0) + ways)
                    t += 1
            cur = nxt
    return cur.get((Kab, Kbc, Kmass), 0) >= 2


def relaxed_nonrigid(a, b, c, Ls, Ms, Ns, ms, ns, ps):
    G = (sum(Ls[i] * ms[i] for i in range(a))
         + sum(Ms[j] * ns[j] for j in range(b))
         + sum(Ns[k] * ps[k] for k in range(c)))
    bound = G + 2
    lens = list(Ls) + list(Ms) + list(Ns)
    lows = [1 - ms[i] for i in range(a)] + [1 - ns[j] for j in range(b)] \
        + [1 - ps[k] for k in range(c)]
    for vals in product(*[range(lows[i], bound + 1) for i in range(len(lens))]):
        if all(v == 0 for v in vals):
            continue
        if sum(lens[i] * vals[i] for i in range(len(lens))) == 0:
            return True
    return False


def check_scope(a, b, c, Ls, Ms, Ns, mmax, gmax, results, use_criterion=False):
    tail, head, nv, pe = build_tri_hub(a, b, c, Ls, Ms, Ns)
    tested = mism = nonrigid = 0
    for ms in product(range(1, mmax + 1), repeat=a):
        for ns in product(range(1, mmax + 1), repeat=b):
            for ps in product(range(1, mmax + 1), repeat=c):
                if not (sum(ms) == sum(ns) == sum(ps)):
                    continue
                A = base_circulation(tail, pe, list(ms), list(ns), list(ps))
                G = sum(A)
                if G > gmax:
                    continue
                tested += 1
                bf = not is_rigid_bruteforce(tail, head, nv, A, G)
                dp = dp_nonrigid(a, b, c, Ls, Ms, Ns, list(ms), list(ns), list(ps))
                crit = dp
                if use_criterion:
                    crit, _ = criterion_nonrigid(a, b, c, Ls, Ms, Ns,
                                                 list(ms), list(ns), list(ps))
                if bf != dp or bf != crit:
                    mism += 1
                    print(f"  MISMATCH a={a} b={b} c={c} L={Ls} M={Ms} N={Ns} "
                          f"m={ms} n={ns} p={ps} G={G} brute={bf} dp={dp} crit={crit}")
                if bf:
                    nonrigid += 1
    results.append(mism == 0)
    print(f"[bruteforce] a={a} b={b} c={c} L={Ls} M={Ms} N={Ns}: tested={tested} "
          f"nonrigid={nonrigid} mismatches={mism}")
    return tested


def check_rigid_repetitive():
    a = b = c = 2
    Ls = Ms = Ns = [1, 3]
    ms = ns = ps = [2, 1]
    tail, head, nv, pe = build_tri_hub(a, b, c, Ls, Ms, Ns)
    A = base_circulation(tail, pe, ms, ns, ps)
    G = sum(A)
    bf_rigid = is_rigid_bruteforce(tail, head, nv, A, G)
    crit, _ = criterion_nonrigid(a, b, c, Ls, Ms, Ns, ms, ns, ps)
    dp = dp_nonrigid(a, b, c, Ls, Ms, Ns, ms, ns, ps)
    ok = bf_rigid and not crit and not dp
    print(f"[rigid-repetitive] L={Ls} M={Ms} N={Ns} m={ms} n={ns} p={ps} G={G}: "
          f"bruteforce_rigid={bf_rigid} criterion_nonrigid={crit} dp_nonrigid={dp} "
          f"-> {'OK' if ok else 'FAIL'}")
    return ok


def check_nonrigid_witness():
    a = b = c = 2
    Ls = Ms = Ns = [1, 1]
    ms = ns = ps = [2, 2]
    tail, head, nv, pe = build_tri_hub(a, b, c, Ls, Ms, Ns)
    A = base_circulation(tail, pe, ms, ns, ps)
    G = sum(A)
    bf_rigid = is_rigid_bruteforce(tail, head, nv, A, G)
    crit, wit = criterion_nonrigid(a, b, c, Ls, Ms, Ns, ms, ns, ps)
    ok = (not bf_rigid) and crit and wit is not None
    if ok:
        al, be, ga = wit
        mass = (sum(Ls[i] * al[i] for i in range(a))
                + sum(Ms[j] * be[j] for j in range(b))
                + sum(Ns[k] * ga[k] for k in range(c)))
        boxes = (all(al[i] >= 1 - ms[i] for i in range(a))
                 and all(be[j] >= 1 - ns[j] for j in range(b))
                 and all(ga[k] >= 1 - ps[k] for k in range(c)))
        nonzero = any(v != 0 for v in al + be + ga)
        ok = (sum(al) == sum(be) == sum(ga)) and mass == 0 and boxes and nonzero
    print(f"[nonrigid-witness] L={Ls} M={Ms} N={Ns} m={ms} n={ns} p={ps} G={G}: "
          f"bruteforce_nonrigid={not bf_rigid} criterion_nonrigid={crit} "
          f"witness={wit} -> {'OK' if ok else 'FAIL'}")
    return ok


def check_relaxed_not_sound():
    a = b = c = 2
    Ls = Ms = Ns = [1, 3]
    ms = ns = ps = [2, 1]
    tail, head, nv, pe = build_tri_hub(a, b, c, Ls, Ms, Ns)
    A = base_circulation(tail, pe, ms, ns, ps)
    G = sum(A)
    bf_rigid = is_rigid_bruteforce(tail, head, nv, A, G)
    relaxed = relaxed_nonrigid(a, b, c, Ls, Ms, Ns, ms, ns, ps)
    ok = bf_rigid and relaxed
    print(f"[relaxed] L={Ls} M={Ms} N={Ns} m={ms} n={ns} p={ps}: rigid={bf_rigid} "
          f"relaxed_nonrigid={relaxed} -> {'OK' if ok else 'FAIL'}")
    return ok


def check_all_one_rigid():
    a = b = c = 2
    Ls, Ms, Ns = [1, 2], [2, 3], [1, 3]
    ms = ns = ps = [1, 1]
    tail, head, nv, pe = build_tri_hub(a, b, c, Ls, Ms, Ns)
    A = base_circulation(tail, pe, ms, ns, ps)
    G = sum(A)
    bf_rigid = is_rigid_bruteforce(tail, head, nv, A, G)
    crit, _ = criterion_nonrigid(a, b, c, Ls, Ms, Ns, ms, ns, ps)
    dp = dp_nonrigid(a, b, c, Ls, Ms, Ns, ms, ns, ps)
    ok = bf_rigid and not crit and not dp
    print(f"[all-one] L={Ls} M={Ms} N={Ns} m={ms} n={ns} p={ps}: rigid={bf_rigid} "
          f"criterion_nonrigid={crit} dp_nonrigid={dp} -> {'OK' if ok else 'FAIL'}")
    return ok


def check_mutation_red():
    """Mutation control (must turn RED): replace the exact criterion by the
    coupling-dropped relaxation (drop both hub-balance equations).  The mutated
    decision must disagree with the from-scratch brute force on at least one
    instance of the p3/m3 scope, otherwise the harness has no discriminating
    power and we fail."""
    a = b = c = 2
    Ls = Ms = Ns = [1, 3]
    mism = 0
    for ms in product(range(1, 4), repeat=a):
        for ns in product(range(1, 4), repeat=b):
            for ps in product(range(1, 4), repeat=c):
                if not (sum(ms) == sum(ns) == sum(ps)):
                    continue
                tail, head, nv, pe = build_tri_hub(a, b, c, Ls, Ms, Ns)
                A = base_circulation(tail, pe, list(ms), list(ns), list(ps))
                G = sum(A)
                if G > 16:
                    continue
                bf = not is_rigid_bruteforce(tail, head, nv, A, G)
                mutated = relaxed_nonrigid(a, b, c, Ls, Ms, Ns,
                                           list(ms), list(ns), list(ps))
                if bf != mutated:
                    mism += 1
    ok = mism > 0
    print(f"[mutation-red] coupling-dropped relaxation disagrees with brute force "
          f"on {mism} instance(s) -> {'OK (red)' if ok else 'FAIL (no discriminating power)'}")
    return ok


def main():
    results = []
    check_scope(1, 1, 1, [1], [1], [1], 4, 10, results, use_criterion=True)
    check_scope(2, 2, 2, [1, 1], [1, 1], [1, 1], 4, 14, results, use_criterion=True)
    check_scope(2, 2, 2, [1, 2], [1, 2], [1, 2], 3, 14, results, use_criterion=True)
    check_scope(2, 2, 2, [1, 3], [1, 3], [1, 3], 3, 16, results)
    check_scope(3, 3, 3, [1, 1, 1], [1, 1, 1], [1, 1, 1], 2, 16, results)
    check_scope(2, 3, 2, [1, 1], [1, 1, 1], [1, 1], 3, 14, results)
    check_scope(3, 2, 3, [1, 1, 1], [1, 1], [1, 1, 1], 2, 14, results)
    check_scope(2, 2, 3, [1, 2], [1, 1], [1, 1, 1], 2, 14, results)

    results.append(check_rigid_repetitive())
    results.append(check_nonrigid_witness())
    results.append(check_relaxed_not_sound())
    results.append(check_all_one_rigid())
    results.append(check_mutation_red())

    print()
    if all(results):
        print("ALL CHECKS PASSED")
        return 0
    print("FAILURES DETECTED")
    return 1


if __name__ == "__main__":
    sys.exit(main())
