#!/usr/bin/env python3
"""Exact MB09 Section 6.2 reconstruction for the *smallest* bridging,
flow-feasible witnesses.

Question
========
Fix the Medvedev-Brudno (2009) Section 6.2 object: vertices are observed read
DNA molecules, edges are bidirected overlaps of length >= o_min on the
transitively reduced graph, every read vertex has lower bound 1, and the
candidate is an integral flow scored by the Section 6.1 separable binomial with
the external true genome length N.  A truth S is *admissible* iff its window
spectrum d_S is a feasible flow.  Does I_s (strict bridging, Shomorony et al.)
plus this admissibility force d_S to be maximum-likelihood optimal?

Determination (this script)
===========================
No.  The smallest counterexample appears at G = 4:

    S   = AAAT (0001),  G = 4,  L = 3,  N = 4,  o_min in {1,2}
    reads at starts (0,0,1,2,3)  ->  x = {AAA:2, AAT:1, ATA:1, TAA:1}, n = 5
    d_S = {AAA:1, AAT:1, ATA:1, TAA:1}          (admissible)
    d*  = {AAA:2, AAT:1, ATA:1, TAA:1}          (admissible; spelled by TAAAA)
    L(d*)/L(d_S) = 32/27 > 1.

Two facts make the determination complete rather than a bounded search:

  * the coordinate-wise integer maximiser of the objective with
    (N, n, x) = (4, 5, (2,1,1,1)) is exactly d* = (2,1,1,1) on [1,N]^4, so no
    admissible flow whatsoever can beat d*; and
  * d* is realised by the spelled molecule TAAAA, so it lies in the smallest
    (sequence-induced) candidate class.

The witness needs a repeated read start (n = 5 > G = 4), i.e. sampling with
replacement, which is the source model.  With distinct starts (n <= G) the
smallest witness is G = 5 (AAATT, ratio 9/8; AATAT, ratio 243/128).  G = 3 has
no witness (proved below).

Epistemic status
================
Source facts are the Section 6.2/6.1 definitions (MB09 PMC3154397).  The
reconstruction and the conservation/objective arguments are mathematical
derivation.  All finite enumerations are exact integer/`Fraction` computation
and are complete only in the stated boxes; the script exits non-zero on any
failed assertion.
"""

from fractions import Fraction
from itertools import combinations, combinations_with_replacement


# ---------------------------------------------------------------------------
# molecules, circular windows, spectra  (MB09 section 3.1)
# ---------------------------------------------------------------------------

def revcomp(w):
    return tuple(1 - b for b in reversed(w))


def mol(w):
    """Canonical positive strand of the molecule {w, rc(w)}."""
    return min(w, revcomp(w))


def circ(seq, start, length):
    g = len(seq)
    return tuple(seq[(start + i) % g] for i in range(length))


def spectrum(seq, L):
    counts = {}
    for s in range(len(seq)):
        w = mol(circ(seq, s, L))
        counts[w] = counts.get(w, 0) + 1
    return counts


def observed(seq, starts, L):
    counts = {}
    for s in starts:
        w = mol(circ(seq, s, L))
        counts[w] = counts.get(w, 0) + 1
    return counts


def s_of(bits):
    return "".join("T" if b else "A" for b in bits)


# ---------------------------------------------------------------------------
# Section 3.3 bidirected overlap graph (folded: some orientation of each
# molecule overlaps some orientation of the other at length >= o_min)
# ---------------------------------------------------------------------------

class Edge:
    __slots__ = ("u", "su", "v", "sv", "length")

    def __init__(self, u, su, v, sv, length):
        self.u, self.su, self.v, self.sv, self.length = u, su, v, sv, length

    def pos_inc(self, w):
        return (1 if (self.u == w and self.su == +1) else 0) + \
               (1 if (self.v == w and self.sv == +1) else 0)

    def neg_inc(self, w):
        return (1 if (self.u == w and self.su == -1) else 0) + \
               (1 if (self.v == w and self.sv == -1) else 0)


def strand(m, orient):
    return m if orient == +1 else revcomp(m)


def max_overlap(a, b):
    best = 0
    for l in range(1, len(a)):
        if a[len(a) - l:] == b[:l]:
            best = l
    return best


def build_graph(molecules, L, o_min):
    ids = {m: i for i, m in enumerate(molecules)}
    edges, seen = [], set()
    for i, x in enumerate(molecules):
        for j, y in enumerate(molecules):
            if j < i:
                continue
            for ox in (+1, -1):
                for oy in (+1, -1):
                    l = max_overlap(strand(x, ox), strand(y, oy))
                    if l >= o_min:
                        sx = +1 if ox == +1 else -1
                        sy = +1 if oy == -1 else -1
                        key = (i, sx, j, sy, l)
                        if key in seen:
                            continue
                        seen.add(key)
                        edges.append(Edge(i, sx, j, sy, l))
    return ids, edges


# ---------------------------------------------------------------------------
# exact feasible throughput set  (integral circulations, balance 0, d in [1,N])
# ---------------------------------------------------------------------------

def feasible_throughputs(molecules, kept, x, N):
    """Every integer circulation f >= 0 with balance 0 at each read vertex,
    vertex throughput d_w in [1, N], and support exactly x.

    Complete: any admissible flow has f_e <= N (each edge has an incidence at
    some vertex whose throughput bounds it) and sum_e f_e <= V*N (each
    bidirected edge has exactly two incidences and pos = neg = d_w).  The DFS
    is pruned by the reachable balance interval, so the caps are exact.
    """
    V, E = len(molecules), len(kept)
    coeff = [[kept[e].pos_inc(v) - kept[e].neg_inc(v) for e in range(E)]
             for v in range(V)]
    cap_edge, cap_total = N, V * N
    smin = [[0] * (E + 1) for _ in range(V)]
    smax = [[0] * (E + 1) for _ in range(V)]
    for v in range(V):
        for e in range(E - 1, -1, -1):
            c = coeff[v][e]
            smin[v][e] = smin[v][e + 1] + min(0, c * cap_edge)
            smax[v][e] = smax[v][e + 1] + max(0, c * cap_edge)
    out, flow = {}, [0] * E

    def rec(e, bal, tot):
        if tot > cap_total:
            return
        for v in range(V):
            if bal[v] + smin[v][e] > 0 or bal[v] + smax[v][e] < 0:
                return
        if e == E:
            if any(b != 0 for b in bal):
                return
            d = {}
            for v in range(V):
                p = sum(kept[j].pos_inc(v) * flow[j] for j in range(E))
                if not (1 <= p <= N):
                    return
                d[molecules[v]] = p
            if set(d) != set(x):
                return
            out[tuple(sorted(d.items()))] = dict(d)
            return
        for val in range(0, min(cap_edge, cap_total - tot) + 1):
            for v in range(V):
                bal[v] += coeff[v][e] * val
            flow[e] = val
            rec(e + 1, bal, tot + val)
            for v in range(V):
                bal[v] -= coeff[v][e] * val
        flow[e] = 0

    rec(0, [0] * V, 0)
    return list(out.values())


def spellable(molecules, kept, d, L, maxlen=16):
    """A binary molecule whose window spectrum is d and whose window walk is a
    valid bidirected walk on `kept`, or None."""
    tot = sum(d.values())
    ids = {m: i for i, m in enumerate(molecules)}
    if tot == 0 or tot > maxlen:
        return None
    for bits in range(1 << tot):
        D = [(bits >> i) & 1 for i in range(tot)]
        if spectrum(D, L) != d:
            continue
        if sequence_walk(D, L, ids, kept) is not None:
            return D
    return None


def sequence_walk(seq, L, ids, edges):
    """Edge indices realizing the cyclic window walk, or None."""
    g = len(seq)
    used = []
    for s in range(g):
        A, B = circ(seq, s, L), circ(seq, (s + 1) % g, L)
        x, y = mol(A), mol(B)
        if x not in ids or y not in ids:
            return None
        ox = +1 if A == strand(x, +1) else -1
        oy = +1 if B == strand(y, +1) else -1
        ix, iy = ids[x], ids[y]
        out_x = +1 if ox == +1 else -1
        in_y = +1 if oy == -1 else -1
        found = None
        for ei, e in enumerate(edges):
            if e.u == ix and e.v == iy:
                tail, head = e.su, e.sv
            elif e.u == iy and e.v == ix:
                tail, head = e.sv, e.su
            else:
                continue
            if tail == out_x and head == in_y:
                found = (ei, tail, head)
                break
        if found is None:
            return None
        used.append(found)
    for k in range(1, g):
        if used[k - 1][2] == used[k][1]:
            return None
    if used[-1][2] == used[0][1]:
        return None
    return [u[0] for u in used]


# ---------------------------------------------------------------------------
# strict bridging I_s  (Shomorony et al. Eq. (1); repository normalization)
# ---------------------------------------------------------------------------

def bridges_copy(seq, starts, L, t, ell):
    g = len(seq)
    for r in starts:
        for k in (-2, -1, 0, 1, 2):
            rr = r + k * g
            if rr < t and t + ell < rr + L:
                return True
    return False


def maximal_repeat_pairs(seq, ell):
    g = len(seq)
    out = []
    for t1, t2 in combinations(range(g), 2):
        if circ(seq, t1, ell) != circ(seq, t2, ell):
            continue
        if seq[(t1 - 1) % g] == seq[(t2 - 1) % g]:
            continue
        if seq[(t1 + ell) % g] == seq[(t2 + ell) % g]:
            continue
        out.append((t1, t2))
    return out


def maximal_triple_repeats(seq, ell):
    g = len(seq)
    out = []
    for t1, t2, t3 in combinations(range(g), 3):
        if not (circ(seq, t1, ell) == circ(seq, t2, ell) == circ(seq, t3, ell)):
            continue
        if len({seq[(t - 1) % g] for t in (t1, t2, t3)}) == 1:
            continue
        if len({seq[(t + ell) % g] for t in (t1, t2, t3)}) == 1:
            continue
        out.append((t1, t2, t3))
    return out


def cyclically_interleaved(a, b, c, d, g):
    if len({a % g, b % g, c % g, d % g}) < 4:
        return False

    def between(x, lo, hi):
        return 0 < (x - lo) % g < (hi - lo) % g

    return between(c, a, b) != between(d, a, b)


def check_I_s(seq, starts, L):
    g = len(seq)
    failures = []
    covered = {(r + i) % g for r in starts for i in range(L)}
    if covered != set(range(g)):
        failures.append("coverage")
    for ell in range(1, g + 1):
        for triple in maximal_triple_repeats(seq, ell):
            for t in triple:
                if not bridges_copy(seq, starts, L, t, ell):
                    failures.append(("triple", ell, t))
    for ell1 in range(1, g + 1):
        for ell2 in range(1, g + 1):
            for (a, b) in maximal_repeat_pairs(seq, ell1):
                for (c, d) in maximal_repeat_pairs(seq, ell2):
                    if (a, b, c, d) == (c, d, a, b):
                        continue
                    if not cyclically_interleaved(a, b, c, d, g):
                        continue
                    if not any(bridges_copy(seq, starts, L, t, e)
                               for (t, e) in ((a, ell1), (b, ell1),
                                              (c, ell2), (d, ell2))):
                        failures.append(("interleaved", ell1, a, b, ell2, c, d))
    return (not failures), failures


# ---------------------------------------------------------------------------
# Section 6.1 objective and the exact optimum
# ---------------------------------------------------------------------------

def factor(dw, xw, n, N):
    if not (0 <= dw <= N):
        return Fraction(0)
    return Fraction(dw, N) ** xw * (1 - Fraction(dw, N)) ** (n - xw)


def likelihood(x, d, n, N):
    p = Fraction(1)
    for w, xw in x.items():
        p *= factor(d[w], xw, n, N)
    return p


def best_ratio(x, dS, flows, n, N):
    Ls = likelihood(x, dS, n, N)
    best, arg = None, None
    for d in flows:
        r = likelihood(x, d, n, N) / Ls
        if best is None or r > best:
            best, arg = r, d
    return best, arg


def graph_of(S, starts, L, o_min):
    x = observed(S, starts, L)
    dS = spectrum(S, L)
    molecules = sorted(set(x) | set(dS))
    _, edges = build_graph(molecules, L, o_min)
    return x, dS, molecules, edges


def all_witnesses(Gmax, n_extra, o_min):
    """Exhaustive hits over G in [3, Gmax], all start multisets with
    n <= G + n_extra, truths required I_s and truth-flow-feasible."""
    L, hits = 3, []
    for G in range(3, Gmax + 1):
        for bits in range(1 << G):
            S = [(bits >> i) & 1 for i in range(G)]
            if min(tuple(S[i:] + S[:i]) for i in range(G)) != tuple(S):
                continue
            for n in range(1, G + n_extra + 1):
                for starts in combinations_with_replacement(range(G), n):
                    ok, _ = check_I_s(S, list(starts), L)
                    if not ok:
                        continue
                    x, dS, molecules, edges = graph_of(S, list(starts), L, o_min)
                    if set(x) != set(dS) or any(v > G for v in dS.values()):
                        continue
                    flows = feasible_throughputs(molecules, edges, x, G)
                    if tuple(sorted(dS.items())) not in \
                            {tuple(sorted(f.items())) for f in flows}:
                        continue
                    r, arg = best_ratio(x, dS, flows, n, G)
                    if r is not None and r > 1:
                        hits.append((G, S, tuple(starts), x, dS, r, arg, flows))
    return hits


# ---------------------------------------------------------------------------
# verification
# ---------------------------------------------------------------------------

def verify_g3():
    """G = 3 has no witness: the only non-homopolymer molecule class has
    feasible flows (k,k,k), (1,3,1), (3,1,3) with d_AAT = d_TAA; the last two
    and (3,3,3) have zero likelihood on any sample observing all three types,
    and (2,2,2) has ratio 2**(-n) < 1."""
    L = 3
    for S in ([0, 0, 1], [0, 1, 1]):
        x, dS, molecules, edges = graph_of(S, [0, 1, 2], L, 2)
        flows = feasible_throughputs(molecules, edges, x, 3)
        shape = sorted(tuple(sorted(f.items())) for f in flows)
        for n in range(3, 9):
            for starts in combinations_with_replacement(range(3), n):
                ox = observed(S, list(starts), L)
                if set(ox) != set(dS):
                    continue
                r, _ = best_ratio(ox, dS, flows, n, 3)
                assert r is None or r <= 1, (S, n, starts, r)
    # count check the printed flow forms
    assert len(shape) == 5
    print("  G=3: no witness for n<=8 (feasible cone verified)")


def verify_g4_witness():
    """The G = 4 smallest witness and the exact optimum over *all* flows."""
    L, G = 3, 4
    S, starts = [0, 0, 0, 1], [0, 0, 1, 2, 3]
    assert len(starts) == 5 > G, "witness needs a repeated read start"
    x, dS, molecules, edges = graph_of(S, starts, L, 2)
    ok, fails = check_I_s(S, starts, L)
    assert ok, fails
    assert set(x) == set(dS)
    flows = feasible_throughputs(molecules, edges, x, G)
    assert tuple(sorted(dS.items())) in {tuple(sorted(f.items()))
                                         for f in flows}, "truth not feasible"
    r, arg = best_ratio(x, dS, flows, 5, G)
    assert r == Fraction(32, 27), r
    # d* is the coordinate-wise integer maximiser on [1,N]^4 (so no flow
    # whatsoever can beat it, for any o_min and any feasible set), and it is
    # spelled by TAAAA.
    expected = {mol((0, 0, 0)): 2, mol((0, 0, 1)): 1,
                mol((0, 1, 0)): 1, mol((1, 0, 0)): 1}
    assert arg == expected, (arg, expected)
    # exact global upper bound: d* is the componentwise integer maximiser of
    # the objective on [1,N], so no feasible flow can beat it (any o_min).
    for w, xw in x.items():
        assert all(factor(arg[w], xw, 5, G) >= factor(d, xw, 5, G)
                   for d in range(1, G + 1)), w
    assert likelihood(x, arg, 5, G) == likelihood(x, dS, 5, G) * Fraction(32, 27)
    # Feasibility at o_min = 1 also holds: the competitor's window edges have
    # length 2 >= 1, so the same spelled molecule lies in the o_min = 1 graph.
    _, edges1 = build_graph(molecules, L, 1)
    D = spellable(molecules, edges1, arg, L)
    assert D is not None and spectrum(D, L) == arg
    assert mol(tuple(D)) == mol((1, 0, 0, 0, 0))
    print("  G=4: AAAT / starts (0,0,1,2,3) is a witness, ratio 32/27, "
          "competitor spelled by TAAAA (feasible at o_min=1,2)")


def verify_g5_witnesses():
    L, G = 3, 5
    for S, starts in (([0, 0, 0, 1, 1], [0, 1, 4]),
                      ([0, 0, 1, 0, 1], [0, 2, 4])):
        x, dS, molecules, edges = graph_of(S, starts, L, 2)
        ok, fails = check_I_s(S, starts, L)
        assert ok, fails
        flows = feasible_throughputs(molecules, edges, x, G)
        assert tuple(sorted(dS.items())) in {tuple(sorted(f.items()))
                                             for f in flows}
        r, arg = best_ratio(x, dS, flows, len(starts), G)
        assert r > 1
        assert spellable(molecules, edges, arg, L) is not None
    # reconciliation: the unmerged "smallest non-spellable" witness uses
    # d = (AAT:1, ATA:2, TAA:1) for S = AATAT at o_min = 1 on the UNREDUCED
    # folded relation.  On the maximal-overlap (o_min = 2) transitively reduced
    # graph it is not a feasible flow, so it does not lower the smallest
    # source-faithful witness below G = 5.
    S, starts = [0, 0, 1, 0, 1], [0, 2, 4]
    x, dS, molecules, edges = graph_of(S, starts, L, 2)
    flows = feasible_throughputs(molecules, edges, x, G)
    target = {mol((0, 0, 1)): 1, mol((0, 1, 0)): 2, mol((1, 0, 0)): 1}
    assert tuple(sorted(target.items())) not in \
        {tuple(sorted(f.items())) for f in flows}
    print("  G=5: AAATT (9/8) and AATAT (243/128) reproduced; best flows "
          "spellable (unmerged non-spellable (1,2,1) is infeasible at o_min=2)")


def verify_minimality():
    # exhaustive: no G<=3 witness, no G=4 witness with distinct starts
    n34 = all_witnesses(4, 0, 2)
    assert n34 == [], [h[:3] for h in n34]
    # exhaustive G=4 with repeated starts (n up to 6): hits exist, first at n=5
    n4 = all_witnesses(4, 2, 2)
    assert n4, "expected G=4 repeated-start witnesses"
    assert all(len(h[2]) == 5 or len(h[2]) == 6 for h in n4)
    assert all(h[0] == 4 for h in n4)
    print(f"  minimality: no witness with n<=G for G<=4; "
          f"{len(n4)} G=4 repeated-start hits (n in 5..6)")


def main():
    print("MB09 Section 6.2 smallest flow-feasible witness (exact)")
    print("=" * 58)
    verify_g3()
    verify_g4_witness()
    verify_g5_witnesses()
    verify_minimality()
    print()
    print("All assertions passed.")


if __name__ == "__main__":
    main()
