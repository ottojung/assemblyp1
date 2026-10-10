"""Optimized rigidity check via backtracking delta-search, and n=4 two-cycle test."""
from itertools import product
from math import gcd
from two_cycle import directed_cycles, two_cycle_obstruction
from explore import is_strongly_connected, every_edge_on_cycle


def find_delta(n, arcs, A, time_limit_nodes=2_000_000):
    """Backtracking search for nonzero d with M d=0, sum d=0, d >= 1-A.
    Returns first witness or None. Uses pruning on partial balance."""
    m = len(arcs)
    G = sum(A)
    bound = G - m
    if bound < 0:
        return None
    out, inn = [], []
    for v in range(n):
        o = [i for i, (u, w) in enumerate(arcs) if u == v]
        i_ = [i for i, (u, w) in enumerate(arcs) if w == v]
        out.append(o)
        inn.append(i_)
    d = [0] * m
    nodes = [0]
    # order edges to improve pruning: process edges sharing vertices together
    order = list(range(m))
    lo = [1 - A[e] for e in range(m)]
    hi = [bound] * m

    def rec(k, remaining):
        nodes[0] += 1
        if nodes[0] > time_limit_nodes:
            raise TimeoutError
        if k == m:
            if remaining != 0:
                return None
            for v in range(n):
                if sum(d[e] for e in out[v]) != sum(d[e] for e in inn[v]):
                    return None
            return list(d) if any(x != 0 for x in d) else None
        e = order[k]
        for val in range(lo[e], hi[e] + 1):
            d[e] = val
            # prune: remaining sum must be achievable
            rem_after = remaining - val
            if rem_after < 0:
                continue
            res = rec(k + 1, rem_after)
            if res is not None:
                return res
            if nodes[0] > time_limit_nodes:
                raise TimeoutError
        d[e] = 0
        return None

    try:
        return rec(0, 0)
    except TimeoutError:
        return "TIMEOUT"


def rigidity_via_delta(n, arcs, A):
    """rigid iff no delta witness. Returns (rigid, witness)."""
    r = find_delta(n, arcs, A)
    if r == "TIMEOUT":
        return ("TIMEOUT", None)
    return (r is None, r)


def all_digraphs_n(n):
    pairs = [(u, v) for u in range(n) for v in range(n) if u != v]
    m = len(pairs)
    for mask in range(1, 1 << m):
        arcs = [pairs[i] for i in range(m) if mask & (1 << i)]
        yield arcs


def enum_pos_circ_fast(n, arcs, G, cap=40):
    out, inn = [], []
    for v in range(n):
        out.append([i for i, (u, w) in enumerate(arcs) if u == v])
        inn.append([i for i, (u, w) in enumerate(arcs) if w == v])
    m = len(arcs)
    B = [0] * m
    def rec(i, remaining):
        if i == m:
            if remaining != 0:
                return
            for v in range(n):
                if sum(B[e] for e in out[v]) != sum(B[e] for e in inn[v]):
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
    G = sum(A)
    for Bb in enum_pos_circ_fast(n, arcs, G):
        if Bb != tuple(A):
            return (False, Bb)
    return (True, None)


def main():
    import sys
    n = 4
    mode = sys.argv[1] if len(sys.argv) > 1 else "twocycle"
    tested = 0
    mismatch = []
    nonrigid = 0
    rigid = 0
    for arcs in all_digraphs_n(n):
        if not is_strongly_connected(n, arcs):
            continue
        if not every_edge_on_cycle(n, arcs):
            continue
        m = len(arcs)
        for G in range(m, 2 * m + 1):
            for A in enum_pos_circ_fast(n, arcs, G):
                if mode == "twocycle":
                    obs = two_cycle_obstruction(n, arcs, A)
                    predicted_rigid = (obs is None)
                else:
                    predicted_rigid = None
                rigid_bf, wit = brute_rigid(n, arcs, A)
                tested += 1
                if rigid_bf:
                    rigid += 1
                else:
                    nonrigid += 1
                if mode == "twocycle":
                    if predicted_rigid != rigid_bf:
                        mismatch.append((arcs, A, rigid_bf, obs))
                if tested % 200 == 0:
                    print(f"  ...tested {tested}, rigid={rigid}, nonrigid={nonrigid}, mismatch={len(mismatch)}", flush=True)
    print(f"n={n} mode={mode}: tested={tested} rigid={rigid} nonrigid={nonrigid} mismatch={len(mismatch)}")
    for mm in mismatch[:20]:
        print("  MISMATCH", mm)


if __name__ == "__main__":
    main()
