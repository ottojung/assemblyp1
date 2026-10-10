"""Robust verification of the two-cycle counterexample + closed-walk refinement test."""
from itertools import product
from math import gcd
from rigidity import is_rigid
from two_cycle import two_cycle_obstruction, directed_cycles

# The counterexample graph and spectra
ARCS = [(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)]
A = (1,3,1,1,1,1,2,1,2)
B = (3,1,1,2,1,1,1,1,2)
n = 4


def check_circulation(arcs, f):
    out, inn = {}, {}
    for v in range(n):
        out[v] = [i for i,(u,w) in enumerate(arcs) if u == v]
        inn[v] = [i for i,(u,w) in enumerate(arcs) if w == v]
    return all(sum(f[e] for e in out[v]) == sum(f[e] for e in inn[v]) for v in range(n))


def closed_walks(n, arcs, max_len=8):
    """All closed walks (edge-index tuples) up to max_len, as multisets."""
    adj = [[] for _ in range(n)]
    for i,(u,v) in enumerate(arcs):
        adj[u].append((v,i))
    walks = []
    def dfs(start, u, path):
        if len(path) > max_len:
            return
        for (v, ei) in adj[u]:
            if v == start and len(path) >= 1:
                walks.append(tuple(path + [ei]))
            elif len(path) + 1 <= max_len:
                dfs(start, v, path + [ei])
    for st in range(n):
        dfs(st, st, [])
    # dedup by sorted edge multiset
    seen = set()
    uniq = []
    for w in walks:
        k = tuple(sorted(w))
        if k not in seen:
            seen.add(k)
            uniq.append(w)
    return uniq


def walk_obstruction(n, arcs, A, walks):
    """Search for two closed walks W1,W2 giving an obstruction."""
    m = len(arcs)
    s = [a-1 for a in A]
    lens = [len(w) for w in walks]
    for i1 in range(len(walks)):
        for i2 in range(len(walks)):
            if i1 == i2:
                continue
            W1, W2 = walks[i1], walks[i2]
            L1, L2 = lens[i1], lens[i2]
            g = gcd(L1, L2)
            for a in (1, -1):
                w1 = a * L2 // g
                w2 = -a * L1 // g
                ok = True
                for e in range(m):
                    val = w1 * W1.count(e) + w2 * W2.count(e)
                    if val < -s[e]:
                        ok = False
                        break
                if ok:
                    return (W1, W2, w1, w2)
    return None


print("=== Counterexample verification ===")
print("A is circulation:", check_circulation(ARCS, A))
print("B is circulation:", check_circulation(ARCS, B))
print("sum A =", sum(A), " sum B =", sum(B), " A != B:", A != B)
print("A >= 1:", all(a >= 1 for a in A), " B >= 1:", all(b >= 1 for b in B))
print("is_rigid (brute force):", is_rigid(n, ARCS, A))
print("two-simple-cycle obstruction:", two_cycle_obstruction(n, ARCS, list(A)))
walks = closed_walks(n, ARCS, max_len=6)
print("num closed walks (len<=6):", len(walks))
print("two-closed-walk obstruction (len<=6):", walk_obstruction(n, ARCS, list(A), walks))
