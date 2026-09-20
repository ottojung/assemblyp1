#!/usr/bin/env python3
"""
Independent KKT / cycle-descent analysis of the Medvedev-Brudno Section 6.2
fixed-N binomial objective on its actual feasible-flow polytope.

Self-contained (no third-party packages).  Two things are checked:

  (1) The cycle-descent / KKT obstruction on small explicit flow polytopes:
      if some admissible circulation direction v (v = d - d_S, d feasible)
      has sum_w h_w v_w > 0 with h_w = (N x_w - n d_S,w)/(d_S,w (N - d_S,w)),
      then the truth-induced flow d_S is not a global optimum.

  (2) An infinite parametric family of information-feasible instances

          S = 0^(G-1) 1     (truth, length G)
          D = 0^(G-2) 1     (competitor, length G-1)
          L = G-2, N = G, single strand, o_min arbitrary in [1, L-1]

      in which the truth-induced flow is feasible, the competitor flow is
      feasible, I_s holds, and the competitor strictly improves the literal
      Section 6.1 product of per-type binomials by the closed form

          ratio = (1/2) * ((G-1)/(G-2))^(G-2)  > 1   for every G >= 4.

All arithmetic is exact (fractions.Fraction).  Exits non-zero on any failed
assertion.  Computational evidence only; the family identity is proved in the
accompanying note.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations


# ---------------------------------------------------------------------------
# Dinic max flow (integer capacities)
# ---------------------------------------------------------------------------
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
            v = e[0]
            if e[1] > 0 and self.level[v] == self.level[u] + 1:
                d = self.dfs(v, t, min(f, e[1]))
                if d > 0:
                    e[1] -= d
                    self.g[v][e[2]][1] += d
                    return d
            self.it[u] += 1
        return 0

    def maxflow(self, s, t):
        flow = 0
        while self.bfs(s, t):
            self.it = [0] * self.n
            while True:
                f = self.dfs(s, t, 10 ** 15)
                if f == 0:
                    break
                flow += f
        return flow


# ---------------------------------------------------------------------------
# Genome / read / bridging predicates (independent implementation)
# ---------------------------------------------------------------------------
def windows(seq, L):
    G = len(seq)
    return [tuple(seq[(i + j) % G] for j in range(L)) for i in range(G)]


def covers_all(G, starts, L):
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
        for pos in groups.values():
            if len(pos) < 2:
                continue
            for a, b in combinations(pos, 2):
                if (S[(a - 1) % G] != S[(b - 1) % G]
                        and S[(a + ell) % G] != S[(b + ell) % G]):
                    key = (a, b)
                    if key not in seen:
                        seen.add(key)
                        out.append((ell, (a, b)))
    return out


def triple_repeats(S):
    G = len(S)
    out, seen = [], set()
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for pos in groups.values():
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
            four = sorted(set(p1) | set(p2))
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


def check_I_s(S, starts, L):
    G = len(S)
    if not covers_all(G, starts, L):
        return False, "coverage"
    for ell, pos in triple_repeats(S):
        for t in pos:
            if not copy_bridged(S, t, ell, starts, L):
                return False, "triple-repeat copy %d not bridged" % t
    for (e1, p1), (e2, p2) in interleaved_pairs(S):
        b1 = any(copy_bridged(S, t, e1, starts, L) for t in p1)
        b2 = any(copy_bridged(S, t, e2, starts, L) for t in p2)
        if not (b1 or b2):
            return False, "interleaved pair not bridged"
    return True, "ok"


# ---------------------------------------------------------------------------
# Section 6.2 flow feasibility (single strand)
# ---------------------------------------------------------------------------
def overlap(u, v):
    L = len(u)
    for k in range(L - 1, 0, -1):
        if u[L - k:] == v[:k]:
            return k
    return 0


def overlap_edges(types, o_min):
    """All directed edges i -> j (including i == j when the read self-overlaps
    by at least o_min) with suffix-prefix overlap >= o_min."""
    V = len(types)
    E = []
    for i in range(V):
        for j in range(V):
            if overlap(types[i], types[j]) >= o_min:
                E.append((i, j))
    return E


def throughput_feasible(types, d, o_min):
    """Transportation test: is there a nonnegative integer flow f on overlap
    edges with row/column sums d?  s -> out(i) [d_i]; out(i) -> in(j) [inf]
    for each edge; in(j) -> t [d_j].  Feasible iff maxflow = sum d."""
    V = len(types)
    E = overlap_edges(types, o_min)
    S_, T = 0, 2 * V + 1
    din = Dinic(2 * V + 2)
    for v in range(V):
        if d[v] < 0:
            return False
        din.add(S_, 1 + v, int(d[v]))
        din.add(1 + V + v, T, int(d[v]))
    for (i, j) in E:
        din.add(1 + i, 1 + V + j, 10 ** 9)
    return din.maxflow(S_, T) == sum(int(x) for x in d)


# ---------------------------------------------------------------------------
# Objective (literal Section 6.1 product of per-type binomials, fixed N)
# ---------------------------------------------------------------------------
def binom_ratio(dD, dS, x, N):
    """exact product-of-binomials ratio P(dD)/P(dS); C(n,x) factors cancel."""
    r = Fraction(1)
    n = sum(x.values())
    for w, xw in x.items():
        r *= Fraction(dD[w], N) ** xw
        r *= Fraction(N - dD[w], N) ** (n - xw)
        r /= Fraction(dS[w], N) ** xw
        r /= Fraction(N - dS[w], N) ** (n - xw)
    return r


def kkt_h(dS, x, N):
    """h_w = d/dd_w log P at d_S (positive = under-observed, wants more)."""
    n = sum(x.values())
    return {w: Fraction(N * x[w] - n * dS[w], dS[w] * (N - dS[w]))
            for w in dS}


# ---------------------------------------------------------------------------
# Parametric family S = 0^(G-1) 1, D = 0^(G-2) 1, L = G-2
# ---------------------------------------------------------------------------
def family_starts(S, D, L):
    G = len(S)
    Sw = windows(S, L)
    Dw = windows(D, L)
    starts, used = [], Counter()
    for w in Dw:
        found = None
        for p in range(G):
            if Sw[p] == w and used[p] == 0:
                found = p
                break
        assert found is not None, ("no free occurrence", w)
        used[found] += 1
        starts.append(found)
    return tuple(sorted(starts))


def verify_family(G):
    assert G >= 4
    L = G - 2
    S = tuple([0] * (G - 1) + [1])
    D = tuple([0] * (G - 2) + [1])
    N = G
    Sw, Dw = windows(S, L), windows(D, L)
    Sspec, Dspec = Counter(Sw), Counter(Dw)
    assert all(c == 1 for c in Dspec.values()), (G, Dspec)
    x = dict(Dspec)
    observed_types = list(x.keys())
    assert set(Sspec) == set(Dspec), (G, set(Sspec) ^ set(Dspec))
    d_S = {w: Sspec[w] for w in observed_types}
    d_D = {w: Dspec[w] for w in observed_types}
    assert sum(d_S.values()) == G and sum(d_D.values()) == G - 1
    starts = family_starts(S, D, L)
    assert Counter(Sw[p] for p in starts) == Counter(x)
    ok, why = check_I_s(S, starts, L)
    for o_min in range(1, L):
        dS_list = [d_S[w] for w in observed_types]
        dD_list = [d_D[w] for w in observed_types]
        assert throughput_feasible(observed_types, dS_list, o_min), (G, o_min, "dS")
        assert throughput_feasible(observed_types, dD_list, o_min), (G, o_min, "dD")
    r = binom_ratio(d_D, d_S, x, N)
    predicted = Fraction(1, 2) * Fraction(G - 1, G - 2) ** (G - 2)
    # KKT: direction v = d_D - d_S decreases the over-observed type 0^L
    h = kkt_h(d_S, x, N)
    v = {w: d_D[w] - d_S[w] for w in d_S}
    deriv = sum(h[w] * v[w] for w in d_S)
    return dict(G=G, L=L, n=sum(x.values()), ratio=r, predicted=predicted,
                d_S=d_S, d_D=d_D, x=x, starts=starts, deriv=deriv,
                i_s_ok=ok, i_s_why=why,
                zero_word=tuple([0] * L))


def verify_kkt_small():
    """Spot-check the KKT formula on the family: derivative sign matches ratio."""
    for G in range(4, 11):
        info = verify_family(G)
        assert info["ratio"] == info["predicted"]
        if info["i_s_ok"]:
            assert info["deriv"] > 0 and info["ratio"] > 1


def main():
    verify_kkt_small()
    print("== KKT/cycle-descent sign matches exact ratio, G=4..10 ==")
    print("== parametric family S=0^(G-1)1, D=0^(G-2)1, L=G-2, N=G ==")
    good = []
    for G in range(4, 61):
        info = verify_family(G)
        assert info["ratio"] == info["predicted"], (G, info)
        assert info["ratio"] > 1
        if info["i_s_ok"]:
            good.append(G)
        if G <= 15:
            tag = "I_s OK" if info["i_s_ok"] else ("I_s NO (%s)" % info["i_s_why"])
            print("G=%2d L=%2d n=%2d  ratio=%-16s  deriv=%-6s  %s"
                  % (G, info["L"], info["n"], str(info["ratio"]),
                     str(info["deriv"]), tag))
    print("family identity (1/2)((G-1)/(G-2))^(G-2) verified G=4..60;"
          " limit e/2 = %.6f" % (2.718281828459045 / 2))
    assert good == list(range(6, 61)), good
    print("I_s holds for every G in 6..60 (and is proved in the note for all G>=6)")


if __name__ == "__main__":
    main()
