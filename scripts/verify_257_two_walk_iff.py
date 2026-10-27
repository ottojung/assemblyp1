#!/usr/bin/env python3
"""Exhaustive small-case cross-check for the TWO-CLOSED-WALK rigidity criterion
of Antonina board issue #257 (AssemblyP1, ``github.com/ottojung/assemblyp1``).

Claim checked (now proved in ``docs/source-notes/issue-257-rigid-read-graphs.md``
section 12): for a strongly connected support graph ``D`` and a positive
circulation ``A`` of total ``G`` (slack ``s = A - 1``), ``A`` is **not** rigid
iff there exist two closed walks ``W1, W2`` and integers ``w1, w2``, not both
zero, with

    w1 * |W1| + w2 * |W2| = 0            (zero-sum)
    w1 * chi_W1 + w2 * chi_W2 >= -s      (inside the box)
    w1 * chi_W1 + w2 * chi_W2 != 0       (nonzero)

The script has two independent halves:

* ``constructive``: given the exact brute-force rigidity answer, for every
  NON-rigid instance it follows the proof's construction --- complete the
  positive/negative parts of the witness ``delta`` to non-negative integer
  circulations ``f, g`` with connected support, extract Eulerian circuits, and
  verify that the two resulting closed walks are of equal length, differ by
  ``delta``, and lie in the box. This validates the constructive direction of
  the theorem on every instance in scope.

* ``search``: an independent enumeration of all closed walks up to a length
  bound, deduplicated by count vector, checking that the two-walk box predicate
  agrees with brute-force rigidity.

Self-contained: no repository import. Exact integer arithmetic. Deterministic.
Exit code is non-zero if any instance fails either check.
"""
from __future__ import annotations

import sys
from collections import deque
from itertools import product
from math import gcd


# --------------------------------------------------------------------------
# graph helpers
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


def brute_rigid(n, arcs, A):
    """(rigid?, alternative B or None) via exhaustive enumeration."""
    G = sum(A)
    for B in enum_pos_circ(n, arcs, G):
        if B != tuple(A):
            return (False, B)
    return (True, None)


# --------------------------------------------------------------------------
# construction (validates the proof's constructive direction)
# --------------------------------------------------------------------------
def route_flow(n, arcs, target):
    """Non-negative h with divergence h = target (requires sum target = 0 and
    strong connectivity). Greedy shortest-path routing."""
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
    """Non-negative circulation whose support is connected and spans all n
    vertices: sum over v of a 0->v path plus a v->0 path."""
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
    """Closed walk (edge-index list) whose count vector is x; requires x to be a
    non-negative circulation with connected support."""
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
    """f, g non-negative circulations with connected support and f - g = delta."""
    m = len(arcs)
    dpos = [max(d, 0) for d in delta]
    dneg = [max(-d, 0) for d in delta]
    D = divergence(n, arcs, dneg)
    assert divergence(n, arcs, dpos) == D, "positive/negative parts differ in divergence"
    h0 = route_flow(n, arcs, [-d for d in D])
    gamma = spanning_circulation(n, arcs)
    h = [h0[i] + gamma[i] for i in range(m)]
    g = [dneg[i] + h[i] for i in range(m)]
    f = [dpos[i] + h[i] for i in range(m)]
    return f, g


def check_constructive(n, maxG_factor):
    tested = rigid = nonrigid = 0
    bad = []
    for arcs in all_digraphs(n):
        if not is_strongly_connected(n, arcs):
            continue
        if not every_edge_on_cycle(n, arcs):
            continue
        m = len(arcs)
        for G in range(m, maxG_factor * m + 1):
            for A in enum_pos_circ(n, arcs, G):
                tested += 1
                rigidA, B = brute_rigid(n, arcs, A)
                if rigidA:
                    rigid += 1
                    continue
                nonrigid += 1
                delta = [B[i] - A[i] for i in range(m)]
                if (not is_balanced(n, arcs, delta) or sum(delta) != 0
                        or any(delta[i] < 1 - A[i] for i in range(m))
                        or all(d == 0 for d in delta)):
                    bad.append((arcs, A, "delta-invalid", delta))
                    continue
                f, g = decompose(delta, n, arcs)
                ok = (all(x >= 0 for x in f) and all(x >= 0 for x in g)
                      and is_balanced(n, arcs, f) and is_balanced(n, arcs, g)
                      and [f[i] - g[i] for i in range(m)] == delta
                      and sum(f) == sum(g)
                      and support_connected(n, arcs, f)
                      and support_connected(n, arcs, g))
                if not ok:
                    bad.append((arcs, A, "decompose-fail", delta, f, g))
                    continue
                wf = eulerian_circuit(n, arcs, f)
                wg = eulerian_circuit(n, arcs, g)
                if wf is None or wg is None or len(wf) != len(wg):
                    bad.append((arcs, A, "euler-fail", delta))
                    continue
                cf = [0] * m
                cg = [0] * m
                for ei in wf:
                    cf[ei] += 1
                for ei in wg:
                    cg[ei] += 1
                comb = [cf[i] - cg[i] for i in range(m)]
                if (cf != f or cg != g or comb != delta
                        or any(comb[i] < 1 - A[i] for i in range(m))
                        or all(c == 0 for c in comb)):
                    bad.append((arcs, A, "walk-mismatch", delta, wf, wg))
    print(f"constructive n={n} maxG={maxG_factor}m: tested={tested} "
          f"rigid={rigid} nonrigid={nonrigid} bad={len(bad)}")
    for b in bad[:10]:
        print("  BAD", b)
    return len(bad)


# --------------------------------------------------------------------------
# exhaustive closed-walk search (independent criterion check)
# --------------------------------------------------------------------------
def all_closed_walk_vectors(n, arcs, max_len):
    """All count vectors of closed walks of length <= max_len, deduplicated."""
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
                    return (c1, c2, w1, w2)
    return None


def check_search(n, max_len, maxG_factor):
    tested = rigid = nonrigid = 0
    bad = []
    for arcs in all_digraphs(n):
        if not is_strongly_connected(n, arcs):
            continue
        if not every_edge_on_cycle(n, arcs):
            continue
        walks = all_closed_walk_vectors(n, arcs, max_len)
        m = len(arcs)
        for G in range(m, maxG_factor * m + 1):
            for A in enum_pos_circ(n, arcs, G):
                tested += 1
                rigidA, _ = brute_rigid(n, arcs, A)
                wit = has_two_walk_witness(A, walks)
                if rigidA:
                    rigid += 1
                    if wit is not None:
                        bad.append((arcs, A, "rigid-but-witness", wit))
                else:
                    nonrigid += 1
                    if wit is None:
                        bad.append((arcs, A, "nonrigid-no-witness"))
    print(f"search n={n} maxlen={max_len} maxG={maxG_factor}m: tested={tested} "
          f"rigid={rigid} nonrigid={nonrigid} bad={len(bad)}")
    for b in bad[:10]:
        print("  BAD", b)
    return len(bad)


def main(argv=None):
    import argparse
    ap = argparse.ArgumentParser(description="two-closed-walk rigidity cross-check")
    ap.add_argument("--extended", action="store_true",
                    help="also run constructive n=4 maxG=2m (slow, >100s)")
    args = ap.parse_args(argv)
    failures = 0
    failures += check_constructive(3, 3)
    failures += check_search(3, 10, 3)
    if args.extended:
        failures += check_constructive(4, 2)
    if failures:
        print(f"FAIL: {failures} bad instances")
        return 1
    scope = "constructive n=3 maxG=3m (447 instances) + search n=3 maxlen=10 maxG=3m"
    if args.extended:
        scope += " + constructive n=4 maxG=2m"
    print("OK: two-closed-walk criterion agrees with brute-force rigidity "
          f"({scope})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
