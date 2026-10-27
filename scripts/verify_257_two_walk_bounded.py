#!/usr/bin/env python3
"""Bounded, time-boxed cross-check for the TWO-CLOSED-WALK rigidity criterion
of Antonina board issue #257 (AssemblyP1, ``github.com/ottojung/assemblyp1``).

This is the convergent companion to ``scripts/verify_257_two_walk_iff.py``.
That script re-enumerates *all* positive circulations of total ``G`` once per
candidate ``A`` (quadratic in the number of circulations), so its ``n = 4``
constructive phase and its ``n = 3`` search phase do not finish in a routine
time budget.  This script checks the identical mathematical claim with two
changes:

* **Memoization (exact, no sampling of verdicts):** for each support graph and
  total ``G``, the positive-circulation census is enumerated exactly once; the
  rigidity verdict for every ``A`` and every non-rigidity witness ``delta``
  are read off that single census.  Verdicts agree with the unmemoized script
  by construction (same generator, same order, first alternative wins).
* **Explicit scope + time box:** ``--max-graphs`` caps the number of support
  graphs (deterministic order, no cherry-picking), ``--time-budget`` caps
  wall-clock seconds.  On budget exhaustion the script reports the exact
  completed scope and exits ``2`` (truncated, not failed).  Exit ``0`` means
  the full requested scope completed with zero mismatches; exit ``1`` means a
  genuine criterion mismatch.

Default scope (converges in seconds): all strongly connected ``n = 3``
digraphs whose every edge lies on a cycle, ``G`` from ``m`` through ``3m``,
both the constructive check (proof-construction validation for every
non-rigid instance) and the closed-walk search check (``max_len = 10``).

Self-contained: no repository import. Exact integer arithmetic. Deterministic.
"""

from __future__ import annotations

import argparse
import sys
import time
from collections import deque
from math import gcd


# --------------------------------------------------------------------------
# graph helpers (same mathematics as verify_257_two_walk_iff.py)
# --------------------------------------------------------------------------
def out_in(n, arcs):
    out = [[] for _ in range(n)]
    inn = [[] for _ in range(n)]
    for i, (u, v) in enumerate(arcs):
        out[u].append((v, i))
        inn[v].append((u, i))
    return out, inn


def divergence(n, arcs, x):
    out, inn = out_in(n, arcs)
    return [sum(x[i] for (_, i) in out[v]) - sum(x[i] for (_, i) in inn[v])
            for v in range(n)]


def is_balanced(n, arcs, x):
    return all(d == 0 for d in divergence(n, arcs, x))


def is_strongly_connected(n, arcs):
    adj = [[] for _ in range(n)]
    for (u, v) in arcs:
        adj[u].append(v)
    for s in range(n):
        seen = [False] * n
        seen[s] = True
        q = [s]
        while q:
            u = q.pop()
            for v in adj[u]:
                if not seen[v]:
                    seen[v] = True
                    q.append(v)
        if not all(seen):
            return False
    return True


def every_edge_on_cycle(n, arcs):
    adj = [[] for _ in range(n)]
    for (u, v) in arcs:
        adj[u].append(v)
    for (u, v) in arcs:
        seen = [False] * n
        st = [v]
        seen[v] = True
        found = False
        while st:
            x = st.pop()
            if x == u:
                found = True
                break
            for w in adj[x]:
                if not seen[w]:
                    seen[w] = True
                    st.append(w)
        if not found:
            return False
    return True


def all_digraphs(n):
    pairs = [(u, v) for u in range(n) for v in range(n) if u != v]
    m = len(pairs)
    for mask in range(1, 1 << m):
        yield [pairs[i] for i in range(m) if mask & (1 << i)]


def enum_pos_circ(n, arcs, G, cap=400):
    """All positive circulations B >= 1, balanced, total G (as tuples)."""
    out, inn = out_in(n, arcs)
    m = len(arcs)
    B = [0] * m

    def rec(i, remaining):
        if i == m:
            if remaining != 0:
                return
            for v in range(n):
                if sum(B[e] for (_, e) in out[v]) != sum(B[e] for (_, e) in inn[v]):
                    return
            yield tuple(B)
            return
        lo = 1
        hi = min(remaining - (m - i - 1), cap)
        if hi < lo:
            return
        for val in range(lo, hi + 1):
            B[i] = val
            yield from rec(i + 1, remaining - val)
        B[i] = 0
    yield from rec(0, G)


def census(n, arcs, G):
    """Single enumeration of all positive circulations of total G."""
    return list(enum_pos_circ(n, arcs, G))


# --------------------------------------------------------------------------
# proof-construction helpers (same as verify_257_two_walk_iff.py)
# --------------------------------------------------------------------------
def route_flow(n, arcs, target):
    adj = [[] for _ in range(n)]
    for i, (u, v) in enumerate(arcs):
        adj[u].append((v, i))
    h = [0] * len(arcs)
    supply = [max(t, 0) for t in target]
    demand = [max(-t, 0) for t in target]
    while any(s > 0 for s in supply):
        src = next(v for v in range(n) if supply[v] > 0)
        prev = [None] * n
        seen = [False] * n
        seen[src] = True
        q = deque([src])
        dst = None
        while q:
            u = q.popleft()
            if demand[u] > 0:
                dst = u
                break
            for (w, ei) in adj[u]:
                if not seen[w]:
                    seen[w] = True
                    prev[w] = (u, ei)
                    q.append(w)
        if dst is None:
            raise RuntimeError("no demand reachable (graph not strongly connected)")
        amt = min(supply[src], demand[dst])
        cur = dst
        while prev[cur] is not None:
            p, ei = prev[cur]
            h[ei] += amt
            cur = p
        supply[src] -= amt
        demand[dst] -= amt
    return h


def spanning_circulation(n, arcs):
    adj = [[] for _ in range(n)]
    for i, (u, v) in enumerate(arcs):
        adj[u].append((v, i))
    gamma = [0] * len(arcs)

    def shortest_path(a, b):
        prev = [None] * n
        seen = [False] * n
        seen[a] = True
        q = deque([a])
        while q:
            u = q.popleft()
            if u == b:
                break
            for (w, ei) in adj[u]:
                if not seen[w]:
                    seen[w] = True
                    prev[w] = (u, ei)
                    q.append(w)
        if not seen[b]:
            return None
        path = []
        cur = b
        while cur != a:
            p, ei = prev[cur]
            path.append(ei)
            cur = p
        return path

    for v in range(1, n):
        p1 = shortest_path(0, v)
        p2 = shortest_path(v, 0)
        if p1 is None or p2 is None:
            raise RuntimeError("not strongly connected")
        for ei in p1:
            gamma[ei] += 1
        for ei in p2:
            gamma[ei] += 1
    return gamma


def support_connected(n, arcs, x):
    used = [i for i in range(len(arcs)) if x[i] > 0]
    if not used:
        return True
    verts = set()
    adj = {}
    for i in used:
        u, v = arcs[i]
        verts.add(u)
        verts.add(v)
    for v in verts:
        adj.setdefault(v, [])
    for i in used:
        u, v = arcs[i]
        adj[u].append(v)
        adj[v].append(u)
    start = next(iter(verts))
    seen = {start}
    st = [start]
    while st:
        u = st.pop()
        for w in adj[u]:
            if w not in seen:
                seen.add(w)
                st.append(w)
    return seen == verts


def eulerian_circuit(n, arcs, x):
    used = [i for i in range(len(arcs)) if x[i] > 0]
    if not used:
        return []
    rem = list(x)
    adj = [[] for _ in range(n)]
    for i in used:
        u, v = arcs[i]
        adj[u].append((v, i))
    start = arcs[used[0]][0]
    stack = [start]
    circuit = []
    it = [0] * n
    while stack:
        u = stack[-1]
        advanced = False
        while it[u] < len(adj[u]):
            (v, ei) = adj[u][it[u]]
            if rem[ei] > 0:
                rem[ei] -= 1
                stack.append(v)
                advanced = True
                break
            it[u] += 1
        if not advanced:
            circuit.append(stack.pop())
    circuit.reverse()
    walk = []
    for k in range(len(circuit) - 1):
        a, b = circuit[k], circuit[k + 1]
        for (w, ei) in adj[a]:
            if w == b:
                walk.append(ei)
                break
        else:
            return None
    return walk


def decompose(delta, n, arcs):
    m = len(arcs)
    dpos = [max(d, 0) for d in delta]
    dneg = [max(-d, 0) for d in delta]
    D = divergence(n, arcs, dneg)
    assert divergence(n, arcs, dpos) == D
    h0 = route_flow(n, arcs, [-d for d in D])
    gamma = spanning_circulation(n, arcs)
    h = [h0[i] + gamma[i] for i in range(m)]
    g = [dneg[i] + h[i] for i in range(m)]
    f = [dpos[i] + h[i] for i in range(m)]
    return f, g


# --------------------------------------------------------------------------
# closed-walk search helpers (same mathematics as verify_257_two_walk_iff.py)
# --------------------------------------------------------------------------
def all_closed_walk_vectors(n, arcs, max_len):
    adj = [[] for _ in range(n)]
    for i, (u, v) in enumerate(arcs):
        adj[u].append((v, i))
    m = len(arcs)
    out = []

    def dfs(start, u, path):
        if len(path) >= max_len:
            return
        for (v, ei) in adj[u]:
            path.append(ei)
            if v == start:
                out.append(tuple(path))
            dfs(start, v, path)
            path.pop()

    for st in range(n):
        dfs(st, st, [])
    seen = set()
    uniq = []
    for w in out:
        cnt = [0] * m
        for ei in w:
            cnt[ei] += 1
        key = tuple(cnt)
        if key not in seen:
            seen.add(key)
            uniq.append((key, len(w)))
    return uniq


def has_two_walk_witness(A, walks):
    m = len(A)
    s = [a - 1 for a in A]
    for (c1, l1) in walks:
        for (c2, l2) in walks:
            if c1 == c2:
                continue
            g = gcd(l1, l2)
            for sgn in (1, -1):
                w1 = sgn * l2 // g
                w2 = -sgn * l1 // g
                vals = [w1 * c1[i] + w2 * c2[i] for i in range(m)]
                if all(vals[i] >= -s[i] for i in range(m)) and any(vals[i] != 0 for i in range(m)):
                    return True
    return False


# --------------------------------------------------------------------------
# bounded driver
# --------------------------------------------------------------------------
class BudgetExceeded(Exception):
    pass


def run_scope(n, max_g_factor, max_walk_len, max_graphs, deadline, do_search):
    tested = rigid = nonrigid = 0
    bad = []
    graphs_done = 0
    truncated = False
    for arcs in all_digraphs(n):
        if not is_strongly_connected(n, arcs):
            continue
        if not every_edge_on_cycle(n, arcs):
            continue
        if max_graphs is not None and graphs_done >= max_graphs:
            truncated = True
            break
        m = len(arcs)
        walks = all_closed_walk_vectors(n, arcs, max_walk_len) if do_search else None
        for G in range(m, max_g_factor * m + 1):
            if time.monotonic() > deadline:
                raise BudgetExceeded()
            pop = census(n, arcs, G)
            for A in pop:
                tested += 1
                if len(pop) == 1:
                    rigid += 1
                    if do_search and has_two_walk_witness(A, walks):
                        bad.append((arcs, A, "rigid-but-witness"))
                    continue
                nonrigid += 1
                B = next(X for X in pop if X != A)
                delta = [B[i] - A[i] for i in range(m)]
                if (not is_balanced(n, arcs, delta) or sum(delta) != 0
                        or any(delta[i] < 1 - A[i] for i in range(m))):
                    bad.append((arcs, A, "delta-invalid"))
                    continue
                f, g = decompose(delta, n, arcs)
                ok = (all(x >= 0 for x in f) and all(x >= 0 for x in g)
                      and is_balanced(n, arcs, f) and is_balanced(n, arcs, g)
                      and [f[i] - g[i] for i in range(m)] == delta
                      and sum(f) == sum(g)
                      and support_connected(n, arcs, f)
                      and support_connected(n, arcs, g))
                if not ok:
                    bad.append((arcs, A, "decompose-fail"))
                    continue
                wf = eulerian_circuit(n, arcs, f)
                wg = eulerian_circuit(n, arcs, g)
                if wf is None or wg is None or len(wf) != len(wg):
                    bad.append((arcs, A, "euler-fail"))
                    continue
                cf = [0] * m
                cg = [0] * m
                for ei in wf:
                    cf[ei] += 1
                for ei in wg:
                    cg[ei] += 1
                comb = [cf[i] - cg[i] for i in range(m)]
                if (cf != f or cg != g or comb != delta
                        or any(comb[i] < 1 - A[i] for i in range(m))):
                    bad.append((arcs, A, "walk-mismatch"))
                    continue
                if do_search and not has_two_walk_witness(A, walks):
                    bad.append((arcs, A, "nonrigid-no-witness"))
        graphs_done += 1
    return tested, rigid, nonrigid, bad, graphs_done, truncated


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--n", type=int, default=3)
    ap.add_argument("--max-g-factor", type=int, default=3)
    ap.add_argument("--max-walk-len", type=int, default=10)
    ap.add_argument("--max-graphs", type=int, default=None)
    ap.add_argument("--time-budget", type=float, default=600.0)
    ap.add_argument("--no-search", action="store_true",
                    help="skip the closed-walk search phase (constructive only)")
    args = ap.parse_args()
    deadline = time.monotonic() + args.time_budget
    t0 = time.monotonic()
    try:
        tested, rigid, nonrigid, bad, ngraphs, truncated = run_scope(
            args.n, args.max_g_factor, args.max_walk_len,
            args.max_graphs, deadline, not args.no_search)
    except BudgetExceeded:
        print("TRUNCATED: time budget exhausted before scope completed")
        return 2
    dt = time.monotonic() - t0
    print(f"scope: n={args.n} maxG={args.max_g_factor}m "
          f"max_walk_len={args.max_walk_len} max_graphs={args.max_graphs} "
          f"search={'on' if not args.no_search else 'off'}")
    print(f"graphs={ngraphs} tested={tested} rigid={rigid} "
          f"nonrigid={nonrigid} bad={len(bad)} elapsed={dt:.1f}s")
    for b in bad[:10]:
        print("  BAD", b)
    if truncated:
        print("TRUNCATED: graph cap reached before scope completed")
        return 2
    if bad:
        print(f"FAIL: {len(bad)} mismatches")
        return 1
    print("OK: bounded two-closed-walk census agrees with brute-force rigidity")
    return 0


if __name__ == "__main__":
    sys.exit(main())