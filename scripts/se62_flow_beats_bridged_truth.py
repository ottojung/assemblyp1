#!/usr/bin/env python3
"""
Independent bounded search (issue #36): a bridged, Medvedev-Brudno Section 6.2
feasible truth beaten by another feasible Section 6.2 flow.

This is a from-scratch reconstruction; it imports no other repository search
module.  It records:

  * the exact model (below) and the two reversals it does not conflate:
    a *flow* (a non-contiguous assembly) and a *spellable molecule* (a single
    circular sequence whose window spectrum is the flow);
  * two witnessed counterexamples, re-derived here;
  * exhaustive bounded scopes with exact fraction arithmetic.

Model (source: Medvedev-Brudno 2009, J. Comput. Biol. 16(8), Sec. 6.1-6.2,
PMC3154397)
--------------------------------------------------------------------------
Section 6.2 builds the transitively reduced bidirected read-overlap graph:

  * a read is a DNA molecule, i.e. an unordered reverse-complement pair;
  * the vertices are the observed read molecule classes;
  * every read vertex has lower bound 1; all other lower bounds 0 and all
    upper bounds infinity;
  * a feasible object is an integer circulation (a collection of walks, a
    "(non-contiguous) assembly"); d_w is the throughput (visit count) at
    vertex w;
  * the objective is the Section 6.1 separable binomial with the externally
    known genome length N = G and n = sum(x) trials,
        L(d) = prod_w C(n,x_w) (d_w/N)^{x_w} (1 - d_w/N)^{n-x_w}.

Bridging (I_s) is the Shomorony et al. condition: coverage, every triple
repeat all-bridged, every interleaved pair bridged on at least one copy.

A truth S is an admissible Section 6.2 candidate iff its own window spectrum
d_S is a feasible flow on the observed vertices.  Because every observed read
is a window of S, this forces support(d_S) = support(x); d_S itself is always
realizable by S's cyclic window walk.  The source lower bound is 1, so the
literal reading imposes no extra condition.  The repository's Observation-7
argument additionally gives a per-occurrence lower bound d_S >= x; both are
searched (--per-occurrence).

The competitor class is all feasible flows with d_w >= 1 and d_w <= N.

Run:  python3 scripts/se62_flow_beats_bridged_truth.py [--quick]
Exact fractions.Fraction; exits non-zero on any failed assertion.
"""
import argparse
import sys
import time
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product

# ---------------------------------------------------------------------------
# I_s (bridging)
# ---------------------------------------------------------------------------


def covers_all(S, starts, L):
    G = len(S)
    cov = set()
    for r in starts:
        for o in range(L):
            cov.add((r + o) % G)
    return len(cov) == G


def maximal_repeat_pairs(S):
    G = len(S)
    out, seen = [], set()
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for _, pos in groups.items():
            if len(pos) < 2:
                continue
            for p in combinations(pos, 2):
                t1, t2 = p
                if (S[(t1 - 1) % G] != S[(t2 - 1) % G]
                        and S[(t1 + ell) % G] != S[(t2 + ell) % G]):
                    if p not in seen:
                        seen.add(p)
                        out.append((ell, p))
    return out


def triple_repeats(S):
    G = len(S)
    out, seen = [], set()
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for _, pos in groups.items():
            if len(pos) < 3:
                continue
            for tri in combinations(pos, 3):
                pre = {S[(t - 1) % G] for t in tri}
                post = {S[(t + ell) % G] for t in tri}
                if len(pre) > 1 and len(post) > 1:
                    key = tuple(sorted(tri))
                    if key not in seen:
                        seen.add(key)
                        out.append((ell, key))
    return out


def interleaved_pairs(S):
    reps = maximal_repeat_pairs(S)
    out, seen = [], set()
    for i in range(len(reps)):
        e1, p1 = reps[i]
        for j in range(i + 1, len(reps)):
            e2, p2 = reps[j]
            four = sorted(set(list(p1) + list(p2)))
            if len(four) != 4:
                continue
            lab = {}
            for p in p1:
                lab[p] = 0
            for p in p2:
                lab[p] = 1
            seq = [lab[p] for p in four]
            if seq in ([0, 1, 0, 1], [1, 0, 1, 0]):
                key = (e1, tuple(sorted(p1)), e2, tuple(sorted(p2)))
                if key not in seen:
                    seen.add(key)
                    out.append(((e1, tuple(sorted(p1))),
                                (e2, tuple(sorted(p2)))))
    return out


def copy_bridged(S, t, ell, starts, L):
    G = len(S)
    for r in starts:
        rp = {(r + o) % G for o in range(L)}
        if (t - 1) % G in rp and (t + ell) % G in rp:
            return True
    return False


def check_I_s(S, starts, L, trips, inter):
    if not covers_all(S, starts, L):
        return False
    for ell, pos in trips:
        for t in pos:
            if not copy_bridged(S, t, ell, starts, L):
                return False
    for (e1, p1), (e2, p2) in inter:
        b1 = any(copy_bridged(S, t, e1, starts, L) for t in p1)
        b2 = any(copy_bridged(S, t, e2, starts, L) for t in p2)
        if not (b1 or b2):
            return False
    return True


# ---------------------------------------------------------------------------
# Molecules and window spectra
# ---------------------------------------------------------------------------


def make_comp(sigma):
    c = {}
    for i in range(0, sigma - 1, 2):
        c[i] = i + 1
        c[i + 1] = i
    if sigma % 2:
        c[sigma - 1] = sigma - 1
    return c


def reverse_complement(s, comp):
    return tuple(comp[c] for c in reversed(tuple(s)))


def mol(s, comp):
    if comp is None:
        return tuple(s)
    return min(tuple(s), reverse_complement(s, comp))


def spec_mol(seq, L, comp):
    G = len(seq)
    return Counter(mol(tuple(seq[(i + j) % G] for j in range(L)), comp)
                   for i in range(G))


def observed(S, starts, L, comp):
    G = len(S)
    x = Counter()
    for r in starts:
        x[mol(tuple(S[(r + j) % G] for j in range(L)), comp)] += 1
    return x


# ---------------------------------------------------------------------------
# Overlap graph and exact circulation feasibility
# ---------------------------------------------------------------------------


def ov(u, v, L):
    best = 0
    for k in range(1, L):
        if tuple(u[-k:]) == tuple(v[:k]):
            best = k
    return best


def graph_reduced(types, L, omin, comp):
    """Repository-consistent model: directed overlap on molecule-class
    representatives (rep = min of the revcomp pair), then the
    junction-containment transitive reduction.  This is the convention used by
    the unmerged Section 6.2 feasibility notes; it is a strict sub-relation of
    the orientation-folded bidirected graph below."""
    E = {(u, v) for u in types for v in types if ov(u, v, L) >= omin}
    rem = set()
    for (u, v) in E:
        thr = L + ov(u, v, L)
        for w in types:
            if (u, w) in E and (w, v) in E \
                    and (u, w) != (u, v) and (w, v) != (u, v):
                if ov(u, w, L) + ov(w, v, L) >= thr:
                    rem.add((u, v))
                    break
    return E - rem


def graph_folded(types, L, omin, comp):
    """Faithful orientation-folded bidirected relation: U ~ V iff some
    orientation of U overlaps some orientation of V by at least o_min.  The
    relation is symmetric (reverse-complement the overlap equation), so both
    directions are added; the directed-circulation test is then the standard
    conservative orientation of the underlying undirected bidirected graph.
    No transitive reduction is applied here because the reduction convention
    for a bidirected graph is a separate source ambiguity."""
    E = set()
    for U in types:
        for V in types:
            best = 0
            for u in _orients(U, comp):
                for v in _orients(V, comp):
                    best = max(best, ov(u, v, L))
            if best >= omin:
                E.add((U, V))
                E.add((V, U))
    return E


def _orients(t, comp):
    if comp is None:
        return [tuple(t)]
    r = reverse_complement(t, comp)
    return [tuple(t)] if r == tuple(t) else [tuple(t), r]


class Dinic:
    def __init__(self, n):
        self.n = n
        self.g = [[] for _ in range(n)]

    def add(self, u, v, c):
        self.g[u].append([v, c, len(self.g[v])])
        self.g[v].append([u, 0, len(self.g[u]) - 1])

    def bfs(self, s, t):
        self.level = [-1] * self.n
        self.level[s] = 0
        q = [s]
        while q:
            nq = []
            for u in q:
                for e in self.g[u]:
                    if e[1] > 0 and self.level[e[0]] < 0:
                        self.level[e[0]] = self.level[u] + 1
                        nq.append(e[0])
            q = nq
        return self.level[t] >= 0

    def dfs(self, u, t, f):
        if u == t:
            return f
        while self.it[u] < len(self.g[u]):
            e = self.g[u][self.it[u]]
            if e[1] > 0 and self.level[e[0]] == self.level[u] + 1:
                d = self.dfs(e[0], t, min(f, e[1]))
                if d > 0:
                    e[1] -= d
                    self.g[e[0]][e[2]][1] += d
                    return d
            self.it[u] += 1
        return 0

    def maxflow(self, s, t):
        flow = 0
        while self.bfs(s, t):
            self.it = [0] * self.n
            while True:
                f = self.dfs(s, t, 10 ** 9)
                if f == 0:
                    break
                flow += f
        return flow


def flow_feasible(d, types, E):
    """Exact feasibility of throughput vector d as a nonnegative integer
    circulation, by a lower-bound max-flow on the vertex-split graph."""
    n = len(types)
    idx = {t: i for i, t in enumerate(types)}
    S, T = 2 * n, 2 * n + 1
    din = Dinic(2 * n + 2)
    demand = [0] * (2 * n + 2)
    for t in types:
        i = idx[t]
        dv = d.get(t, 0)
        demand[i] -= dv
        demand[n + i] += dv
    for (u, v) in E:
        din.add(n + idx[u], idx[v], 10 ** 9)
    need = 0
    for i in range(2 * n):
        if demand[i] > 0:
            din.add(S, i, demand[i])
            need += demand[i]
        elif demand[i] < 0:
            din.add(i, T, -demand[i])
    return din.maxflow(S, T) == need


# ---------------------------------------------------------------------------
# Objective and spellability
# ---------------------------------------------------------------------------


def binom_ratio(d, dS, x, N):
    """L(d)/L(dS) for the literal Section 6.1 binomial; None if out of domain."""
    n = sum(x.values())
    r = Fraction(1)
    for w, xw in x.items():
        dd, ds = d.get(w, 0), dS.get(w, 0)
        if not (0 <= dd <= N) or not (0 <= ds <= N):
            return None
        num = Fraction(dd, N) ** xw * Fraction(N - dd, N) ** (n - xw)
        den = Fraction(ds, N) ** xw * Fraction(N - ds, N) ** (n - xw)
        if den == 0:
            return None
        r *= num / den
    return r


def spellable_spectrum(d, L, comp, sigma):
    """A molecule with window spectrum d, or None.  Any such molecule has length
    sum(d), so this enumeration over Sigma^sum(d) is complete."""
    m = sum(d.values())
    if m == 0:
        return None
    for D in product(range(sigma), repeat=m):
        if spec_mol(D, L, comp) == d:
            return D
    return None


def lit(seq):
    return "".join(map(str, seq))


# ---------------------------------------------------------------------------
# Witnesses
# ---------------------------------------------------------------------------

# W1: the strongest new witness.  Non-vacuous triple repeats (length-1), the
# truth is per-occurrence feasible (d_S >= x), and the beating flow is not the
# window spectrum of any single molecule.
W1 = dict(S=(0, 0, 0, 1, 0, 1), L=3, starts=(0, 1, 3, 5),
          d={(0, 0, 0): 1, (0, 0, 1): 1, (0, 1, 0): 2, (1, 0, 0): 1})

# W2: the unmerged branch witness (G=6, L=4), re-derived independently.
W2 = dict(S=(0, 0, 0, 1, 1, 1), L=4, starts=(0, 1, 3, 4),
          d={(0, 0, 0, 1): 2, (0, 0, 1, 1): 2, (1, 0, 0, 0): 2, (1, 1, 0, 0): 2})

W2MIN = dict(S=(0, 0, 1, 0, 1), L=3, starts=(0, 2, 4),
             d={(0, 0, 1): 1, (0, 1, 0): 2, (1, 0, 0): 1})

EXPECT_RATIO = {"W1": Fraction(128, 81), "W2": Fraction(16384, 15625),
                "W2MIN": Fraction(3, 2)}


def report_witness(name, W, comp, sigma):
    S, L, starts, d = W["S"], W["L"], W["starts"], W["d"]
    G = len(S)
    trips, inter = triple_repeats(S), interleaved_pairs(S)
    dS = spec_mol(S, L, comp)
    x = observed(S, starts, L, comp)
    types = sorted(dS)
    print("=" * 78)
    print(f"{name}: S = {lit(S)}  G = {G}  L = {L}  starts = {starts}  "
          f"n = {sum(x.values())} < G")
    print(f"  I_s holds (and {len(trips)} triple-repeat classes) : "
          f"{check_I_s(S, starts, L, trips, inter)}")
    print(f"  d_S = { {lit(k): v for k, v in sorted(dS.items())} }")
    print(f"  x   = { {lit(k): v for k, v in sorted(x.items())} }")
    print(f"  d   = { {lit(k): v for k, v in sorted(d.items())} }")
    assert check_I_s(S, starts, L, trips, inter)
    assert set(x) == set(dS), "support equality (truth is a candidate)"
    assert all(dS.get(w, 0) >= x[w] for w in x), "per-occurrence truth feasible"
    # truth feasible on both graph readings
    for gname, E in [("reduced(rep)", graph_reduced(types, L, 1, comp)),
                     ("folded(o_min=1)", graph_folded(types, L, 1, comp))]:
        assert flow_feasible(dict(dS), types, E), f"d_S not feasible on {gname}"
    # competitor feasible, beats, non-spellable on the reduced-representative
    # graph (the repository's convention); folded sensitivity below
    E = graph_reduced(types, L, 1, comp)
    assert flow_feasible(d, types, E), "d not feasible"
    r = binom_ratio(d, dS, x, G)
    print(f"  binomial ratio L(d)/L(d_S)   : {r} = {float(r):.6f} > 1")
    assert r == EXPECT_RATIO[name]
    sp = spellable_spectrum(d, L, comp, sigma)
    print(f"  molecule with spectrum d      : {lit(sp) if sp else None} "
          f"(sum(d) = {sum(d.values())})")
    assert sp is None, "winner must be a genuinely non-spellable flow"
    return dS, x, types


def sensitivity(comp):
    """o_min sensitivity of the witnessed beats on the two graph readings."""
    print()
    print("o_min sensitivity (feasible + ratio > 1 on both sides)")
    for name in ("W1", "W2", "W2MIN"):
        W = {"W1": W1, "W2": W2, "W2MIN": W2MIN}[name]
        S, L, starts, d = W["S"], W["L"], W["starts"], W["d"]
        G = len(S)
        dS, x = spec_mol(S, L, comp), observed(S, starts, L, comp)
        types = sorted(dS)
        cells = []
        for omin in range(1, L):
            def ok(E):
                return (flow_feasible(dict(dS), types, E)
                        and flow_feasible(d, types, E)
                        and (binom_ratio(d, dS, x, G) or 0) > 1)
            cells.append(
                f"o_min={omin}: rep-reduced={ok(graph_reduced(types, L, omin, comp))}"
                f" folded={ok(graph_folded(types, L, omin, comp))}")
        print(f"  {name} ({lit(S)}, G={G}, L={L}): " + "; ".join(cells))
    return None


# ---------------------------------------------------------------------------
# Exhaustive bounded scope
# ---------------------------------------------------------------------------


def search_scope(G, L, sigma, comp, omin, graph, per_occurrence, nmax=None,
                 boxcap=3_000_000):
    """Exhaustive over S, start multisets, and competitor throughput vectors.

    Returns (instances, spellable_beats, nonspellable_beats) for I_s- and
    truth-feasible instances under the chosen lower-bound reading.
    """
    compd = make_comp(sigma) if comp else None
    n_inst = spell = nonspell = nonvac = 0
    if nmax is None:
        nmax = G
    for S in product(range(sigma), repeat=G):
        trips, inter = triple_repeats(S), interleaved_pairs(S)
        dS = spec_mol(S, L, compd)
        suppS = set(dS)
        types = sorted(suppS)
        E = graph(types, L, omin, compd)
        if not flow_feasible(dict(dS), types, E):
            # ill-posed graph: the truth is not a candidate under this reading
            continue
        for n in range(max(1, (G + L - 1) // L), nmax + 1):
            for starts in combinations_with_replacement(range(G), n):
                if not check_I_s(S, starts, L, trips, inter):
                    continue
                x = observed(S, starts, L, compd)
                if set(x) != suppS:
                    continue
                if per_occurrence and any(dS[w] < x[w] for w in x):
                    continue
                box = 1
                for w in types:
                    box *= G
                if box > boxcap:
                    raise AssertionError(f"box too large {lit(S)} {starts}")
                n_inst += 1
                for combo in product(*[range(1, G + 1) for _ in types]):
                    d = dict(zip(types, combo))
                    if all(d[t] == dS[t] for t in types):
                        continue
                    if not flow_feasible(d, types, E):
                        continue
                    r = binom_ratio(d, dS, x, G)
                    if r is None or r <= 1:
                        continue
                    if spellable_spectrum(d, L, compd, sigma) is None:
                        nonspell += 1
                        if trips:
                            nonvac += 1
                    else:
                        spell += 1
    return n_inst, spell, nonspell, nonvac


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    a = ap.parse_args()
    sigma, comp = 2, make_comp(2)

    for name, W in (("W1", W1), ("W2", W2), ("W2MIN", W2MIN)):
        report_witness(name, W, comp, sigma)
    sensitivity(comp)

    print()
    print("=" * 78)
    print("Exhaustive scopes: bidirected (revcomp 0<->1), binary, "
          "truth feasible under both readings")
    print("=" * 78)
    # (G, L, o_min, graph, per_occurrence) -> (instances, spell, nonspell, nonvac)
    plans = [
        (5, 3, 1, graph_reduced, True),
        (5, 3, 2, graph_reduced, True),
        (6, 3, 1, graph_reduced, True),
        (6, 3, 2, graph_reduced, True),
        (5, 3, 1, graph_folded, True),
        (5, 3, 2, graph_folded, True),
        (6, 3, 1, graph_folded, True),
        (6, 3, 2, graph_folded, True),
        (5, 3, 1, graph_reduced, False),
        (6, 3, 1, graph_reduced, False),
        (5, 3, 1, graph_folded, False),
        (6, 3, 1, graph_folded, False),
    ]
    if not a.quick:
        plans += [
            (5, 4, 1, graph_folded, True),
        ]
    for (G, L, omin, graph, po) in plans:
        t0 = time.time()
        got = search_scope(G, L, sigma, comp, omin, graph, po)
        gname = "rep-reduced" if graph is graph_reduced else "folded"
        print(f"  G={G} L={L} o_min={omin} {gname:11s} per_occ={po}: "
              f"instances={got[0]:>6} spell_cex={got[1]:>4} "
              f"nonspell_cex={got[2]:>4} (of which triple-repeat truths "
              f"{got[3]:>4}) ({time.time()-t0:.1f}s)")
    print("\nALL ASSERTIONS PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
