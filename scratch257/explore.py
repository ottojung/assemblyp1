"""Enumerate strongly connected digraphs, positive circulations, classify rigidity.

For each (graph, A) we compute:
  - rigid? (exactly, via brute force)
  - a non-rigidity witness delta (zero-sum circulation, delta >= 1-A)
  - the cycle structure of the witness (is it supported on <= 2 directed cycles?)
  - test candidate graph-theoretic characterizations
"""
from itertools import product, combinations
from rigidity import enum_positive_circulations, is_rigid, kernel_zero_sum_search
import sys


def is_strongly_connected(n, arcs):
    if not arcs:
        return n <= 1
    adj = [[] for _ in range(n)]
    for (u, v) in arcs:
        adj[u].append(v)
    # reachability from 0
    for start in range(n):
        seen = [False] * n
        stack = [start]
        seen[start] = True
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if not seen[v]:
                    seen[v] = True
                    stack.append(v)
        if not all(seen):
            return False
    return True


def every_edge_on_cycle(n, arcs):
    """Every edge lies on some directed cycle (necessary for positive circulation)."""
    m = len(arcs)
    adj = [[] for _ in range(n)]
    for (u, v) in arcs:
        adj[u].append(v)
    for (u, v) in arcs:
        # is v reachable from u? then edge u->v is on a cycle
        seen = [False] * n
        stack = [v]
        seen[v] = True
        found = False
        while stack:
            x = stack.pop()
            if x == u:
                found = True
                break
            for w in adj[x]:
                if not seen[w]:
                    seen[w] = True
                    stack.append(w)
        if not found:
            return False
    return True


def all_directed_graphs(n):
    """All digraphs on n vertices (no self loops for now), as edge lists."""
    pairs = [(u, v) for u in range(n) for v in range(n) if u != v]
    m = len(pairs)
    for mask in range(1, 1 << m):
        arcs = [pairs[i] for i in range(m) if mask & (1 << i)]
        yield arcs


def find_witness_cycles(n, arcs, delta):
    """Given a zero-sum circulation delta, try to write it using <= 2 directed cycles.
    Returns (C1, C2, w1, w2) with delta = w1*chi_C1 + w2*chi_C2, or None."""
    # find directed cycles
    adj = [[] for _ in range(n)]
    for i, (u, v) in enumerate(arcs):
        if delta[i] != 0:
            adj[u].append((v, i))
    # enumerate simple directed cycles up to some length
    cycles = []
    def dfs(start, u, path, used):
        if len(path) > 8:
            return
        for (v, ei) in adj[u]:
            if v == start and len(path) >= 1:
                cycles.append(list(path))
            elif v not in used:
                used.add(v)
                path.append(ei)
                dfs(start, v, path, used)
                path.pop()
                used.discard(v)
    for s in range(n):
        dfs(s, s, [], {s})
    # dedup cycles by edge set
    seen = set()
    uniq = []
    for c in cycles:
        key = frozenset(c)
        if key not in seen:
            seen.add(key)
            uniq.append(c)
    # try single cycle
    for c in uniq:
        chi = [0] * len(arcs)
        for ei in c:
            chi[ei] += 1
        if all(chi[i] == delta[i] for i in range(len(arcs))):
            return (c, [], 1, 0)
    # try pairs w1*chi_C1 + w2*chi_C2 = delta
    for c1 in uniq:
        chi1 = [0] * len(arcs)
        for ei in c1:
            chi1[ei] += 1
        for c2 in uniq:
            if c1 == c2:
                continue
            chi2 = [0] * len(arcs)
            for ei in c2:
                chi2[ei] += 1
            # solve w1*chi1 + w2*chi2 = delta
            # find w1, w2 from entries where only one is nonzero
            only1 = [i for i in range(len(arcs)) if chi1[i] != 0 and chi2[i] == 0]
            only2 = [i for i in range(len(arcs)) if chi2[i] != 0 and chi1[i] == 0]
            both = [i for i in range(len(arcs)) if chi1[i] != 0 and chi2[i] != 0]
            w1 = w2 = None
            ok = True
            for i in only1:
                if delta[i] % chi1[i] != 0:
                    ok = False
                    break
                cand = delta[i] // chi1[i]
                if w1 is None:
                    w1 = cand
                elif w1 != cand:
                    ok = False
                    break
            if not ok:
                continue
            for i in only2:
                if delta[i] % chi2[i] != 0:
                    ok = False
                    break
                cand = delta[i] // chi2[i]
                if w2 is None:
                    w2 = cand
                elif w2 != cand:
                    ok = False
                    break
            if not ok:
                continue
            # entries in both: delta[i] = w1*chi1[i] + w2*chi2[i] = w1 + w2
            for i in both:
                if w1 is not None and w2 is not None:
                    if w1 + w2 != delta[i]:
                        ok = False
                        break
                elif w1 is not None:
                    w2 = delta[i] - w1
                elif w2 is not None:
                    w1 = delta[i] - w2
                else:
                    ok = False
                    break
            if not ok or w1 is None or w2 is None:
                continue
            if w1 == 0 and w2 == 0:
                continue
            # verify
            if all(w1 * chi1[i] + w2 * chi2[i] == delta[i] for i in range(len(arcs))):
                return (c1, c2, w1, w2)
    return None


def main():
    n = 3
    results = []
    for arcs in all_directed_graphs(n):
        if not is_strongly_connected(n, arcs):
            continue
        if not every_edge_on_cycle(n, arcs):
            continue
        m = len(arcs)
        # enumerate positive circulations with small total
        for G in range(m, 4 * m + 1):
            for A in enum_positive_circulations(n, arcs, G):
                rigid, wit = is_rigid(n, arcs, A)
                results.append((arcs, A, rigid))
    # stats
    total = len(results)
    rigid_count = sum(1 for _, _, r in results if r)
    print(f"n={n}: {total} (graph,A) pairs, {rigid_count} rigid, {total-rigid_count} non-rigid")
    # for non-rigid ones, check witness cycle structure
    two_cycle = 0
    more = 0
    for arcs, A, rigid in results:
        if rigid:
            continue
        d = kernel_zero_sum_search(n, arcs, A)
        if d is None:
            print("ERROR: non-rigid but no kernel witness found", arcs, A)
            continue
        fc = find_witness_cycles(n, arcs, d)
        if fc is not None:
            two_cycle += 1
        else:
            more += 1
            print("witness needs >2 cycles:", arcs, "A=", A, "d=", d)
    print(f"non-rigid witnesses expressible with <=2 cycles: {two_cycle}, needing more: {more}")


if __name__ == "__main__":
    main()
