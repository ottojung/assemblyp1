#!/usr/bin/env python3
"""
Can a truth-feasible bridged genome be beaten by a Medvedev-Brudno Section 6.2
*feasible flow* that is not a single spelled molecule?

Motivation (issue #36 residue)
------------------------------
docs/section62-bidirected-flow-feasibility.md Sec. 6 records as the remaining
open gap:

    "A *spellable* truth can be beaten by a Section 6.2 flow that is not
     any single molecule  --  open."

The repository's earlier searches enumerated only candidates D that are single
circular molecules (spelled by one closed walk).  Section 6.2, however,
optimizes over *flows*, and a flow decomposes into a collection of walks, i.e.
a "(non-contiguous) assembly of the genome" (PMC3154397 Sec. 6.2).  This script
enumerates the full cycle-cone of the read-overlap graph, so it includes
non-spellable flows, and asks whether one of them strictly improves the
Section 6.1 separable binomial on a truth-feasible bridging instance.

Model (explicit assumptions)
----------------------------
* true circular genome S, length G; read length L; alphabet size sigma;
* observed read multiset R with type counts x; n = sum(x);
* Truth is sequence-level Section 6.2-feasible (per-occurrence reading): every
  length-L window of S is an observed read type and d_S(w) >= x_w.  Such an
  instance automatically has n <= G, because sum_w x_w <= sum_w d_S(w) = G.
  The search over n is therefore complete for the per-occurrence reading.
* Feasible flows = integer cycle-cone of the directed overlap graph on observed
  read types: edge u -> v iff u and v have a proper overlap of length >= o_min
  (overlap length L is excluded).  A throughput vector d is feasible iff an
  integer circulation has in = out = d_v at every vertex; checked exactly by a
  lower-bound max-flow on the vertex-split graph.
* Objective = literal Section 6.1 separable binomial with external denominator
  N = G and n trials,
      L(d) = prod_w C(n,x_w) (d_w/N)^{x_w} (1 - d_w/N)^{n-x_w},
  domain d_w <= N; exact fractions.Fraction arithmetic.

Two graph readings are compared, because the source says the graph is
*transitively reduced* but reduction conventions differ:
* "full": the raw overlap graph with threshold o_min, no reduction;
* "string": a source-defensible transitive reduction that preserves spelled
  molecules -- remove edge u->v when some read w spans the u-v junction, i.e.
  overlap(u,w) + overlap(w,v) >= L + overlap(u,v).  This is order-independent,
  yields a subgraph of the full graph, and never removes the overlap-(L-1)
  edges of a spelled molecule's own circuit, so the truth stays a candidate.
  (A reachability or "any 2-hop path" reduction is stricter and can remove the
  truth's own circuit; it is not used here.)

Results (reproduced and asserted below)
---------------------------------------
1. FULL graph, o_min = 1, per-occurrence: non-spellable counterexamples exist.
   Recorded smallest witness:
       S = 01011 (G = 5, L = 3), starts (0,1,2,3)
       d_S   = {010:1, 101:2, 011:1, 110:1}
       x     = {010:1, 101:1, 011:1, 110:1}
       flow  d = x, realized by the circulation
           010 -> 101 -> 011 -> 110 -> 010
       whose last step has overlap 1 < L-1 = 2.  Section 6.1 binomial ratio
       32/27 > 1.  No circular molecule has window spectrum d, so d is
       genuinely non-spellable.
   The winning edge 110->010 is, however, transitively reducible: the read 101
   spans its junction (overlap(110,101) + overlap(101,010) = 2 + 2 >= 3 = L).
2. STRING-reduced graph, per-occurrence, G = 5,6,7, L = 3, o_min = 1,2:
   zero counterexamples.  So the answer is reduction-dependent: the only
   recorded non-spellable per-occurrence witness uses an edge the source's
   transitive reduction removes.
3. Per-type lower bound (d_w >= 1 for every observed molecule), STRING graph,
   o_min = 2: counterexamples persist (G = 6: 48 instances).  The smallest is
   the *spellable* molecule 0000101, so it is not a new non-spellable
   phenomenon and it lies outside the per-occurrence statement.

Run:  python3 scripts/se62_nonspellable_flow_search.py [--quick]
Exact arithmetic; exits non-zero if any recorded assertion fails.
"""
import argparse
import time
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product

# --------------------------------------------------------------------------
# Bridging machinery (I_s)
# --------------------------------------------------------------------------


def covers_all(S, starts, L):
    G = len(S)
    cov = set()
    for r in starts:
        for o in range(L):
            cov.add((r + o) % G)
    return len(cov) == G


def maximal_repeat_pairs(S):
    G = len(S)
    out, seen_pos = [], set()
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for kmer, pos in groups.items():
            if len(pos) < 2:
                continue
            for pair in combinations(pos, 2):
                t1, t2 = pair
                if (S[(t1 - 1) % G] != S[(t2 - 1) % G]
                        and S[(t1 + ell) % G] != S[(t2 + ell) % G]):
                    if pair not in seen_pos:
                        seen_pos.add(pair)
                        out.append((ell, pair, kmer))
    return out


def triple_repeats(S):
    G = len(S)
    out, seen = [], set()
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for kmer, pos in groups.items():
            if len(pos) < 3:
                continue
            for tri in combinations(pos, 3):
                pre = {S[(t - 1) % G] for t in tri}
                post = {S[(t + ell) % G] for t in tri}
                if len(pre) > 1 and len(post) > 1:
                    key = tuple(sorted(tri))
                    if key not in seen:
                        seen.add(key)
                        out.append((ell, key, kmer))
    return out


def interleaved_pairs(S):
    reps = maximal_repeat_pairs(S)
    out, seen = [], set()
    for i in range(len(reps)):
        e1, p1, _ = reps[i]
        for j in range(i + 1, len(reps)):
            e2, p2, _ = reps[j]
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
    for ell, pos, _ in trips:
        for t in pos:
            if not copy_bridged(S, t, ell, starts, L):
                return False
    for (e1, p1), (e2, p2) in inter:
        b1 = any(copy_bridged(S, t, e1, starts, L) for t in p1)
        b2 = any(copy_bridged(S, t, e2, starts, L) for t in p2)
        if not (b1 or b2):
            return False
    return True


# --------------------------------------------------------------------------
# Reads / spectra
# --------------------------------------------------------------------------


def make_comp(sigma):
    c = {}
    for i in range(0, sigma - 1, 2):
        c[i] = i + 1
        c[i + 1] = i
    if sigma % 2:
        c[sigma - 1] = sigma - 1
    return c


def mol(s, comp):
    if comp is None:
        return tuple(s)
    r = tuple(comp[c] for c in reversed(s))
    return min(tuple(s), r)


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


# --------------------------------------------------------------------------
# Overlap graph and exact cycle-cone feasibility
# --------------------------------------------------------------------------


def overlap_length(u, v, L):
    best = 0
    for k in range(1, L):
        if u[-k:] == v[:k]:
            best = k
    return best


def full_edges(types, L, omin):
    return {(u, v) for u in types for v in types
            if overlap_length(u, v, L) >= omin}


def string_reduce(types, L, omin):
    """String-graph reduction preserving spelled molecules.

    Drop u->v when some read w lies inside the spelled u-v junction: with
    ov = overlap(u,v), a length-L read w that starts s positions into the
    junction has overlap(u,w) = L-s and overlap(w,v) = s+ov, so
    overlap(u,w) + overlap(w,v) = L + ov.  The condition
    overlap(u,w) + overlap(w,v) >= L + overlap(u,v) therefore says exactly
    that w spans the junction, and it never removes the overlap-(L-1) edges of
    a spelled molecule's own circuit.
    """
    E = full_edges(types, L, omin)
    ov = overlap_length
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
    """Exact: is d the vertex-throughput vector of an integer circulation?"""
    n = len(types)
    idx = {t: i for i, t in enumerate(types)}
    S, T = 2 * n, 2 * n + 1
    din = Dinic(2 * n + 2)
    demand = [0] * (2 * n + 2)
    for t in types:
        i = idx[t]
        dv = d.get(t, 0)
        demand[i] -= dv          # v_in -> ... 
        demand[n + i] += dv      # ... -> v_out, fixed throughput dv
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


def binomial_ratio(d, dS, x, N):
    """L_binom(d)/L_binom(dS) with external denominator N and n = sum(x)."""
    n = sum(x.values())
    r = Fraction(1)
    for w, xw in x.items():
        dd, ds = d.get(w, 0), dS[w]
        if dd > N or ds > N:
            return None
        num = Fraction(dd, N) ** xw * Fraction(N - dd, N) ** (n - xw)
        den = Fraction(ds, N) ** xw * Fraction(N - ds, N) ** (n - xw)
        r *= num / den
    return r


def molecule_with_spectrum(d):
    """A circular molecule with window spectrum d, or None.

    Any such molecule has length sum(d), so this search is complete.
    """
    if not d:
        return None
    m = sum(d.values())
    L = len(next(iter(d)))
    alpha = max(max(t) for t in d) + 1
    for word in product(range(alpha), repeat=m):
        if spec_mol(word, L, None) == d:
            return word
    return None


# --------------------------------------------------------------------------
# Search
# --------------------------------------------------------------------------


def search(G, L, sigma, comp, per_occ, omin, mode, nmax=None, cap=None):
    """Exhaustive over S, start multisets, and throughput vectors d.

    per_occ=True : lower bound d_w >= x_w (truth feasibility forces n <= G, so
                   nmax=G makes the n-search complete).
    per_occ=False: lower bound d_w >= 1 for every observed molecule.
    mode         : "full" | "string".
    """
    N = G
    out = []
    inst = 0
    truth_not_in_cone = 0
    if nmax is None:
        nmax = G
    for S in product(range(sigma), repeat=G):
        trips = triple_repeats(S)
        inter = interleaved_pairs(S)
        spS = spec_mol(S, L, comp)
        suppS = set(spS)
        for n in range(max(1, (G + L - 1) // L), nmax + 1):
            for starts in combinations_with_replacement(range(G), n):
                if not check_I_s(S, starts, L, trips, inter):
                    continue
                x = observed(S, starts, L, comp)
                if set(x) != suppS:
                    continue
                if per_occ and any(spS.get(w, 0) < c for w, c in x.items()):
                    continue
                inst += 1
                types = sorted(suppS)
                E = full_edges(types, L, omin)
                if mode == "string":
                    E = string_reduce(types, L, omin)
                # The truth must itself be a feasible flow, otherwise the
                # comparison is ill-posed.  (Always true on the full graph;
                # checked on the reduced graph too.)
                if not flow_feasible(dict(spS), types, E):
                    truth_not_in_cone += 1
                lo = {w: (x[w] if per_occ else 1) for w in types}
                for combo in product(*[range(lo[w], N + 1) for w in types]):
                    d = dict(zip(types, combo))
                    if all(combo[i] == spS[types[i]]
                           for i in range(len(types))):
                        continue
                    if not flow_feasible(d, types, E):
                        continue
                    r = binomial_ratio(d, spS, x, N)
                    if r is not None and r > 1:
                        out.append((S, starts, n, x, spS, d, r, frozenset(E)))
                        if cap is not None and len(out) >= cap:
                            return inst, out
    if truth_not_in_cone:
        raise AssertionError(
            f"{truth_not_in_cone}/{inst} truth-feasible instances had d_S "
            "outside the cycle cone of the searched graph")
    return inst, out


def lit(seq):
    return "".join(map(str, seq))


# --------------------------------------------------------------------------
# Witness and recorded scopes
# --------------------------------------------------------------------------

WITNESS = ((0, 1, 0, 1, 1), 3, (0, 1, 2, 3))   # S=01011, L=3, starts


def witness_report():
    print("=" * 78)
    print("Non-spellable Section 6.2 flow beating a truth-feasible genome")
    print("=" * 78)
    S, L, starts = WITNESS
    G = len(S)
    trips = triple_repeats(S)
    inter = interleaved_pairs(S)
    spS = spec_mol(S, L, None)
    x = observed(S, starts, L, None)
    types = sorted(spS)
    d = {t: 1 for t in types}            # the observed spectrum, each once
    E_full = full_edges(types, L, 1)
    E_str = string_reduce(types, L, 1)
    print(f"  truth S = {lit(S)}  (G={G}, L={L}), starts = {starts}")
    print(f"  I_s holds                    : "
          f"{check_I_s(S, starts, L, trips, inter)}")
    print(f"  observed support = spec(S)   : {set(x) == set(spS)}")
    print(f"  d_S   = {{ {', '.join(f'{lit(k)}:{v}' for k, v in sorted(spS.items()))} }}")
    print(f"  x     = {{ {', '.join(f'{lit(k)}:{v}' for k, v in sorted(x.items()))} }}")
    print(f"  per-occurrence truth feasible: "
          f"{all(spS.get(w, 0) >= c for w, c in x.items())}")
    print(f"  d = x = {{ {', '.join(f'{lit(k)}:{v}' for k, v in sorted(d.items()))} }}")
    print(f"  d feasible on FULL  o_min=1  : {flow_feasible(d, types, E_full)}")
    print(f"  d feasible on STRING graph   : {flow_feasible(d, types, E_str)}")
    print("  circulation cycle            : 010 -> 101 -> 011 -> 110 -> 010")
    cyc = [(0, 1, 0), (1, 0, 1), (0, 1, 1), (1, 1, 0)]
    ols = [overlap_length(cyc[i], cyc[(i + 1) % 4], L) for i in range(4)]
    print(f"  step overlaps                : {ols}  (L-1 = {L-1})")
    molD = molecule_with_spectrum(d)
    print(f"  molecule with spectrum d     : {lit(molD) if molD else None}")
    print("                                 => non-spellable: "
          f"{molD is None}")
    r = binomial_ratio(d, spS, x, G)
    print(f"  Section 6.1 binomial ratio   : {r} = {float(r):.6f} > 1")
    assert check_I_s(S, starts, L, trips, inter)
    assert set(x) == set(spS)
    assert all(spS.get(w, 0) >= c for w, c in x.items())
    assert flow_feasible(d, types, E_full)
    assert not flow_feasible(d, types, E_str)
    assert min(ols) == 1 and max(ols) == L - 1
    assert molD is None
    assert r > 1
    return r


# Recorded counts asserted by the script.  `None` is a scope that is only
# printed, not asserted (kept small to avoid brittle large literals).
RECORDED = {
    # (G, L, "occ"/"type", "full"/"string", o_min) -> cex count
    (5, 3, "occ", "string", 1): 0,
    (5, 3, "occ", "string", 2): 0,
    (6, 3, "occ", "string", 1): 0,
    (6, 3, "occ", "string", 2): 0,
    (7, 3, "occ", "string", 1): 0,
    (7, 3, "occ", "string", 2): 0,
    (6, 3, "type", "string", 1): 48,
    (6, 3, "type", "string", 2): 48,
    (5, 3, "occ", "full", 1): 20,
    (5, 3, "occ", "full", 2): 0,
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true",
                    help="smaller G scope for the exhaustive tables")
    a = ap.parse_args()
    witness_report()
    # The full (unreduced) graph is only needed at G <= 6 to exhibit the
    # contrast; the string-reduced graph is searched through G = 7.
    plans = [
        ("occ", True, [5] if a.quick else [5, 6], [5] if a.quick else [5, 6, 7]),
        ("type", False, [5] if a.quick else [5, 6], [5] if a.quick else [5, 6]),
    ]
    for reading, per_occ, full_scopes, string_scopes in plans:
        print()
        print("=" * 78)
        print(f"Exhaustive searches, {reading} lower bound"
              + (" (n <= G is complete)" if per_occ else ""))
        print("=" * 78)
        for mode, scopes in [("full", full_scopes), ("string", string_scopes)]:
            for G in scopes:
                for omin in [1, 2]:
                    t0 = time.time()
                    inst, out = search(G, 3, 2, None, per_occ, omin, mode)
                    key = (G, 3, reading, mode, omin)
                    exp = RECORDED.get(key)
                    mark = "" if exp is None else f" (expected {exp})"
                    print(f"  G={G} L=3 o_min={omin} {mode:6s} "
                          f"instances={inst:>6} cex={len(out):>4}{mark} "
                          f"({time.time()-t0:.1f}s)")
                    if exp is not None:
                        assert len(out) == exp, \
                            f"{key}: got {len(out)} != {exp}"
                    if out and reading == "type" and mode == "string" \
                            and omin == 2:
                        S, starts, n, x, spS, d, r, E = out[0]
                        md = molecule_with_spectrum(d)
                        print(f"      e.g. S={lit(S)} ratio={r} "
                              f"spellable={md is not None}"
                              + (f" ({lit(md)})" if md else ""))
    print()
    print("  Contrast: the non-spellable per-occurrence witness exists only")
    print("  on the FULL graph; on the STRING (transitively reduced) graph")
    print("  no per-occurrence counterexample was found in scope.")
    print("\nALL ASSERTIONS PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
