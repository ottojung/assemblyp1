"""Test: is non-rigidity equivalent to a TWO-CYCLE obstruction?

Two-cycle obstruction: directed cycles C1, C2 and integers w1,w2 (not both 0)
  with w1*|C1| + w2*|C2| = 0 (zero-sum) and w1*chi_C1 + w2*chi_C2 >= -s.

We search over all simple directed cycles and all (w1,w2) arising from the
zero-sum condition, and compare with brute-force rigidity.
"""
from itertools import product
from rigidity import enum_positive_circulations, is_rigid
from explore import is_strongly_connected, every_edge_on_cycle, all_directed_graphs
from math import gcd


def directed_cycles(n, arcs, max_len=8):
    """All simple directed cycles as lists of edge indices."""
    adj = [[] for _ in range(n)]
    for i, (u, v) in enumerate(arcs):
        adj[u].append((v, i))
    cycles = []
    def dfs(start, u, path, used):
        if len(path) > max_len:
            return
        for (v, ei) in adj[u]:
            if v == start and len(path) >= 1:
                cycles.append(tuple(path + [ei]))
            elif v not in used:
                used.add(v)
                path.append(ei)
                dfs(start, v, path, used)
                path.pop()
                used.discard(v)
    for st in range(n):
        dfs(st, st, [], {st})
    # dedup by edge-set
    seen = set()
    uniq = []
    for c in cycles:
        k = frozenset(c)
        if k not in seen:
            seen.add(k)
            uniq.append(c)
    return uniq


def two_cycle_obstruction(n, arcs, A):
    """Return a two-cycle witness (C1,C2,w1,w2) if one exists, else None."""
    m = len(arcs)
    s = [a - 1 for a in A]
    cyc = directed_cycles(n, arcs)
    lens = [len(c) for c in cyc]
    for i1 in range(len(cyc)):
        for i2 in range(len(cyc)):
            if i1 == i2:
                continue
            C1, C2 = cyc[i1], cyc[i2]
            L1, L2 = lens[i1], lens[i2]
            g = gcd(L1, L2)
            # w1*C1 + w2*C2 = 0  =>  w1 = a*L2/g, w2 = -a*L1/g
            for a in (1, -1):
                w1 = a * L2 // g
                w2 = -a * L1 // g
                ok = True
                for e in range(m):
                    val = 0
                    if e in C1:
                        val += w1
                    if e in C2:
                        val += w2
                    if val < -s[e]:
                        ok = False
                        break
                if ok:
                    return (C1, C2, w1, w2)
    return None


def main():
    n = 3
    match = 0
    mismatch = []
    total_nr = 0
    for arcs in all_directed_graphs(n):
        if not is_strongly_connected(n, arcs):
            continue
        if not every_edge_on_cycle(n, arcs):
            continue
        m = len(arcs)
        for G in range(m, 3 * m + 1):
            for A in enum_positive_circulations(n, arcs, G):
                rigid, _ = is_rigid(n, arcs, A)
                obs = two_cycle_obstruction(n, arcs, A)
                if not rigid:
                    total_nr += 1
                    if obs is None:
                        mismatch.append((arcs, A))
                    else:
                        match += 1
                else:
                    if obs is not None:
                        mismatch.append((arcs, A))
    print(f"non-rigid total: {total_nr}")
    print(f"two-cycle obstruction matches non-rigidity: {match}")
    print(f"mismatches: {len(mismatch)}")
    for mm in mismatch[:15]:
        print("  MISMATCH arcs=", mm[0], "A=", mm[1])


if __name__ == "__main__":
    main()
