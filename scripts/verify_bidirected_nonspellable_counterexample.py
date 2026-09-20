#!/usr/bin/env python3
"""
Self-contained exact verification of a *non-spellable* Medvedev-Brudno Section
6.2 flow counterexample under the source-faithful bidirected (orientation-
resolved) reading.  Companion to
`docs/section62-bidirected-nonspellable-flow-counterexample.md`.

Model (source: Medvedev-Brudno 2009, J. Comput. Biol. 16(8), Sec. 6.1-6.2,
PMC3154397)
--------------------------------------------------------------------------
* A read is a DNA molecule = unordered reverse-complement pair; the molecule
  class of a word is the smaller of the word and its reverse complement.
* The Section 6.2 graph is the *oriented* read-overlap graph: two nodes per
  observed molecule class (one per strand), a directed edge a -> b iff the
  longest proper suffix-prefix overlap ov(a,b) >= o_min, then Myers transitive
  reduction (drop a -> b if some node c with c != a,b satisfies
  ov(a,c) >= ov(a,b)+1 and ov(a,c)+ov(c,b) >= ov(a,b)+L).
* A candidate is an integer circulation of the reduced oriented graph.  Its
  molecule throughput d_m is the number of visits to either strand of m.
* Lower bound: d_m >= 1 (per-type, the source's reading) or d_m >= x_m
  (per-occurrence).  Objective: literal Section 6.1 separable binomial over the
  observed vertices with the external genome length N = G.
* A circular molecule D is *traceable* on the observed set V iff, walking D's
  length-L windows and stopping at the observed ones, every cyclic gap between
  consecutive observed windows is <= L - o_min and the corresponding reduced
  edge exists.  Its throughput is spec_L(D)|_V (Observation 7).  A traceable
  molecule is a special (single-circuit) Section 6.2 candidate.

The witness (non-spellable, per-type, o_min = L-2)
--------------------------------------------------
    S = 001011 (G = 6), L = 4, starts (0,1,3,3,3,4), N = 6
    x = {0010:1, 0101:1, 0110:3, 1100:1}
    d_S = {0010:2, 0101:1, 0110:2, 1100:1}
    d  = x  (a feasible circulation, not any molecule's window spectrum)
    L(d)/L(d_S) = 2278125/1048576 ~ 2.1726

Every assertion below is exact (fractions.Fraction); the script is
deterministic and exits non-zero on failure.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product

COMP = {0: 1, 1: 0}


# --------------------------------------------------------------------------
# strings and bridging
# --------------------------------------------------------------------------
def windows(seq, L):
    G = len(seq)
    return [tuple(seq[(i + j) % G] for j in range(L)) for i in range(G)]


def rc(w, comp=COMP):
    return tuple(comp[c] for c in reversed(tuple(w)))


def mol(w, comp=COMP):
    w = tuple(w)
    return min(w, rc(w, comp))


def spec(seq, L, comp=COMP):
    return Counter(mol(w, comp) for w in windows(seq, L))


def observed(S, starts, L, comp=COMP):
    ws = windows(S, L)
    return Counter(mol(ws[r], comp) for r in starts)


def overlap(a, b):
    m = min(len(a), len(b)) - 1
    for k in range(m, 0, -1):
        if tuple(a[len(a) - k:]) == tuple(b[:k]):
            return k
    return 0


def lit(w):
    return "".join(map(str, w))


def covers(S, starts, L):
    G = len(S)
    seen = set()
    for r in starts:
        for o in range(L):
            seen.add((r + o) % G)
    return len(seen) == G


def triple_repeats(S):
    G = len(S)
    out = []
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for _, pos in groups.items():
            for tri in combinations(pos, 3):
                pre = {S[(t - 1) % G] for t in tri}
                post = {S[(t + ell) % G] for t in tri}
                if len(pre) > 1 and len(post) > 1:
                    out.append((ell, tuple(sorted(tri))))
    return out


def maximal_pairs(S):
    G = len(S)
    out = []
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for _, pos in groups.items():
            for a, b in combinations(pos, 2):
                if (S[(a - 1) % G] != S[(b - 1) % G]
                        and S[(a + ell) % G] != S[(b + ell) % G]):
                    out.append((ell, (a, b)))
    return out


def interleaved_pairs(S):
    reps = maximal_pairs(S)
    out = []
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
            if [lab[p] for p in four] in ([0, 1, 0, 1], [1, 0, 1, 0]):
                out.append(((e1, p1), (e2, p2)))
    return out


def copy_bridged(S, t, ell, starts, L):
    G = len(S)
    for r in starts:
        rp = {(r + o) % G for o in range(L)}
        if (t - 1) % G in rp and (t + ell) % G in rp:
            return True
    return False


def check_I_s(S, starts, L):
    if not covers(S, starts, L):
        return False
    for ell, pos in triple_repeats(S):
        if not all(copy_bridged(S, t, ell, starts, L) for t in pos):
            return False
    for (e1, p1), (e2, p2) in interleaved_pairs(S):
        if not (any(copy_bridged(S, t, e1, starts, L) for t in p1)
                or any(copy_bridged(S, t, e2, starts, L) for t in p2)):
            return False
    return True


# --------------------------------------------------------------------------
# oriented graph, circulation, traceability
# --------------------------------------------------------------------------
class Dinic:
    def __init__(self, n):
        self.n = n
        self.g = [[] for _ in range(n)]

    def add(self, u, v, c):
        self.g[u].append([v, c, len(self.g[v])])
        self.g[v].append([u, 0, len(self.g[u]) - 1])

    def _bfs(self, s, t):
        self.lvl = [-1] * self.n
        self.lvl[s] = 0
        q = [s]
        for u in q:
            for v, c, _ in self.g[u]:
                if c > 0 and self.lvl[v] < 0:
                    self.lvl[v] = self.lvl[u] + 1
                    q.append(v)
        return self.lvl[t] >= 0

    def _dfs(self, u, t, f):
        if u == t:
            return f
        while self.it[u] < len(self.g[u]):
            e = self.g[u][self.it[u]]
            if e[1] > 0 and self.lvl[e[0]] == self.lvl[u] + 1:
                d = self._dfs(e[0], t, min(f, e[1]))
                if d > 0:
                    e[1] -= d
                    self.g[e[0]][e[2]][1] += d
                    return d
            self.it[u] += 1
        return 0

    def maxflow(self, s, t):
        f = 0
        while self._bfs(s, t):
            self.it = [0] * self.n
            while True:
                d = self._dfs(s, t, 1 << 60)
                if d == 0:
                    break
                f += d
        return f


def orientation_nodes(V, comp=COMP):
    On = set()
    for m in V:
        m = tuple(m)
        On.add(m)
        On.add(rc(m, comp))
    return sorted(On)


def build_edges(On, L, o_min):
    return {(a, b) for a in On for b in On if overlap(a, b) >= o_min}


def transitive_reduce(On, E, L):
    keep = set()
    for (a, b) in E:
        k = overlap(a, b)
        red = False
        if k <= L - 2:
            for c in On:
                if c == a or c == b:
                    continue
                l1 = overlap(a, c)
                if l1 >= k + 1 and l1 + overlap(c, b) >= k + L:
                    red = True
                    break
        if not red:
            keep.add((a, b))
    return keep


def circulation_ok(thr, On, E):
    idx = {a: i for i, a in enumerate(On)}
    n = len(On)
    S, T = 2 * n, 2 * n + 1
    din = Dinic(2 * n + 2)
    total = 0
    for a in On:
        dv = thr.get(a, 0)
        if dv < 0:
            return False
        total += dv
        din.add(S, idx[a], dv)
        din.add(n + idx[a], T, dv)
    for (a, b) in E:
        din.add(idx[a], n + idx[b], max(total, 1))
    return din.maxflow(S, T) == total


def molecule_feasible(d, V, On, E, comp=COMP):
    groups = defaultdict(list)
    for a in On:
        groups[mol(a, comp)].append(a)
    choices = []
    for m in sorted(V):
        ns = groups.get(tuple(m), [])
        dv = d.get(m, 0)
        if len(ns) == 1:
            choices.append([{tuple(ns[0]): dv}])
        elif len(ns) == 2:
            choices.append([{tuple(ns[0]): k, tuple(ns[1]): dv - k}
                            for k in range(dv + 1)])
        else:
            return False
    for combo in product(*choices):
        thr = Counter()
        for c in combo:
            thr.update(c)
        if circulation_ok(thr, On, E):
            return True
    return False


def explicit_circulation(d, V, On, E, comp=COMP):
    """Return (orientation throughput, edge flow Counter) or None."""
    groups = defaultdict(list)
    for a in On:
        groups[mol(a, comp)].append(a)
    choices = []
    for m in sorted(V):
        ns = groups.get(tuple(m), [])
        dv = d.get(m, 0)
        choices.append([{tuple(ns[0]): k, tuple(ns[1]): dv - k}
                        for k in range(dv + 1)] if len(ns) == 2
                       else [{tuple(ns[0]): dv}])
    for combo in product(*choices):
        thr = Counter()
        for c in combo:
            thr.update(c)
        idx = {a: i for i, a in enumerate(On)}
        n = len(On)
        S, T = 2 * n, 2 * n + 1
        din = Dinic(2 * n + 2)
        total = sum(thr.values())
        for a in On:
            din.add(S, idx[a], thr.get(a, 0))
            din.add(n + idx[a], T, thr.get(a, 0))
        refs = []
        for (a, b) in E:
            din.add(idx[a], n + idx[b], max(total, 1))
            refs.append(((a, b), len(din.g[idx[a]]) - 1))
        if din.maxflow(S, T) != total:
            continue
        eu = Counter()
        for (a, b), pos in refs:
            f = max(total, 1) - din.g[idx[a]][pos][1]
            if f > 0:
                eu[(a, b)] = f
        out = Counter()
        inn = Counter()
        for (a, b), f in eu.items():
            out[a] += f
            inn[b] += f
        if all(out[a] == thr.get(a, 0) for a in On) and \
           all(inn[a] == thr.get(a, 0) for a in On):
            return thr, eu
    return None


def traceable(seq, V, L, o_min, E, comp=COMP):
    """Throughput Counter over V if seq is spelled by a closed walk on V."""
    m = len(seq)
    if m == 0:
        return None
    Vset = set(V)
    pos, nodes, classes = [], [], []
    for i in range(m):
        w = tuple(seq[(i + j) % m] for j in range(L))
        c = mol(w, comp)
        if c in Vset:
            pos.append(i)
            nodes.append(w)
            classes.append(c)
    if not pos:
        return None
    for t in range(len(pos)):
        a = pos[t]
        b = pos[(t + 1) % len(pos)] + (m if t + 1 == len(pos) else 0)
        if b - a > L - o_min:
            return None
        if a != b and (nodes[t], nodes[(t + 1) % len(nodes)]) not in E:
            return None
    thr = Counter(classes)
    if any(thr.get(w, 0) < 1 for w in V):
        return None
    return thr


def binom_obj(thr, x, N):
    n = sum(x.values())
    v = Fraction(1)
    for w, xw in x.items():
        dw = thr.get(w, 0)
        v *= Fraction(dw, N) ** xw * Fraction(N - dw, N) ** (n - xw)
    return v


# --------------------------------------------------------------------------
# checks
# --------------------------------------------------------------------------
CHECKS = []


def check(name, cond):
    CHECKS.append((name, bool(cond)))
    print(f"[{'PASS' if cond else 'FAIL'}] {name}")
    return cond


def main():
    # ---- witness instance -------------------------------------------------
    S = (0, 0, 1, 0, 1, 1)
    starts = (0, 1, 3, 3, 3, 4)
    L, o_min, N = 4, 2, 6
    x = observed(S, starts, L)
    V = sorted(x)
    dS_full = spec(S, L)
    check("S=001011: I_s holds", check_I_s(S, starts, L))
    check("S=001011: II_s triple repeats non-vacuous",
          len(triple_repeats(S)) >= 1)
    check("S=001011: interleaving conjunct non-vacuous",
          len(interleaved_pairs(S)) >= 1)
    check("observed x = {0010:1,0101:1,0110:3,1100:1}",
          x == {(0, 0, 1, 0): 1, (0, 1, 0, 1): 1, (0, 1, 1, 0): 3, (1, 1, 0, 0): 1})

    On = orientation_nodes(V)
    E = transitive_reduce(On, build_edges(On, L, o_min), L)
    thrS = traceable(S, V, L, o_min, E)
    check("truth spectrum d_S = {0010:2,0101:1,0110:2,1100:1}",
          thrS == {(0, 0, 1, 0): 2, (0, 1, 0, 1): 1,
                   (0, 1, 1, 0): 2, (1, 1, 0, 0): 1})
    d = {w: x[w] for w in V}
    check("d = x is a feasible circulation on the reduced graph",
          molecule_feasible(d, V, On, E))
    circ = explicit_circulation(d, V, On, E)
    check("explicit circulation certificate exists", circ is not None)
    if circ:
        thr, eu = circ
        print("    orientation throughput:",
              {lit(k): v for k, v in sorted(thr.items())})
        for (a, b), f in sorted(eu.items()):
            print(f"      {lit(a)} -> {lit(b)}  f={f}  ov={overlap(a, b)}")
    vS = binom_obj(thrS, x, N)
    vd = binom_obj(d, x, N)
    check("exact ratio L(d)/L(d_S) = 2278125/1048576",
          vd / vS == Fraction(2278125, 1048576))
    print(f"    ratio = {vd / vS} ~ {float(vd / vS):.4f}")

    # complete non-spellability --------------------------------------------
    # Any spelled molecule beating d_S has throughput thr in [1,N]^V with
    # binom_obj(thr) > vS.  Enumerate those and their total visit count.
    beating = []
    for combo in product(range(1, N + 1), repeat=len(V)):
        t = dict(zip(V, combo))
        if binom_obj(t, x, N) > vS:
            beating.append((sum(combo), t))
    maxsum = max(s for s, _ in beating)
    check("every throughput beating d_S has total visits <= 7", maxsum <= 7)
    # A traceable molecule has length <= (1 + (L - o_min - 1)) * sum(thr)
    # = 2 * sum(thr) <= 14, so length-14 enumeration is complete.
    maxlen = 2 * maxsum
    best = Fraction(0)
    bestD = None
    for mlen in range(1, maxlen + 1):
        for D in product(range(2), repeat=mlen):
            thr = traceable(D, V, L, o_min, E)
            if thr is None:
                continue
            if any(thr.get(w, 0) > N for w in V):
                continue
            b = binom_obj(thr, x, N)
            if b > best:
                best, bestD = b, D
    check("no molecule of length <= 14 beats d_S (max ratio = 1)",
          best == vS)
    print("    best spelled molecule:", lit(bestD) if bestD else None)

    # ---- why the earlier "non-spellable" witnesses are not genuine -------
    def instance(name, S2, st2, L2, d2, o_min2):
        x2 = observed(S2, st2, L2)
        V2 = sorted(set(x2) | set(d2))
        On2 = orientation_nodes(V2)
        Eraw = build_edges(On2, L2, o_min2)
        Ered = transitive_reduce(On2, Eraw, L2)
        raw = molecule_feasible(d2, V2, On2, Eraw)
        red = molecule_feasible(d2, V2, On2, Ered)
        print(f"    {name}: o_min={o_min2} raw-feasible={raw} "
              f"reduced-feasible={red}")
        return raw, red

    print("  failure analysis of the folded-model witnesses:")
    # W1 / W2MIN rely on a molecule self-loop / overlap-1 edge removed by
    # Myers reduction, and are not feasible at o_min = L-1.
    raw1a, red1a = instance("W1", (0, 0, 0, 1, 0, 1), (0, 1, 3, 5), 3,
                            {(0, 0, 0): 1, (0, 0, 1): 1, (0, 1, 0): 2,
                             (1, 0, 0): 1}, 1)
    raw1b, red1b = instance("W1", (0, 0, 0, 1, 0, 1), (0, 1, 3, 5), 3,
                            {(0, 0, 0): 1, (0, 0, 1): 1, (0, 1, 0): 2,
                             (1, 0, 0): 1}, 2)
    check("W1 feasible only raw at o_min=1 (dies under reduction)", raw1a and not red1a)
    check("W1 not feasible at o_min=2", not raw1b and not red1b)
    raw2a, red2a = instance("W2MIN", (0, 0, 1, 0, 1), (0, 2, 4), 3,
                            {(0, 0, 1): 1, (0, 1, 0): 2, (1, 0, 0): 1}, 1)
    check("W2MIN feasible only raw at o_min=1 (dies under reduction)",
          raw2a and not red2a)
    # W2 survives reduction but is realizable by a spelled molecule.
    W2_S = (0, 0, 0, 1, 1, 1)
    W2_st = (0, 1, 3, 4)
    W2_d = {(0, 0, 0, 1): 2, (0, 0, 1, 1): 2,
            (1, 0, 0, 0): 2, (1, 1, 0, 0): 2}
    raw3, red3 = instance("W2", W2_S, W2_st, 4, W2_d, 2)
    xW2 = observed(W2_S, W2_st, 4)
    VW2 = sorted(xW2)
    OnW2 = orientation_nodes(VW2)
    EW2 = transitive_reduce(OnW2, build_edges(OnW2, 4, 2), 4)
    dstar = {(0, 0, 0, 1): 2, (0, 0, 1, 1): 2, (1, 0, 0, 0): 2, (1, 1, 0, 0): 2}
    padded = traceable((0, 0, 0, 1, 1, 0, 0, 0, 1, 1), VW2, 4, 2, EW2)
    check("W2 winner is realizable by a spelled molecule (padding)",
          raw3 and red3 and padded is not None
          and dict(padded) == dict(dstar))

    # ---- comparison: the proof-level KKT spelled family (G=6) ------------
    KKT_S = (0, 0, 0, 0, 0, 1)
    KKT_D = (0, 0, 0, 0, 1)
    KKT_starts = (0, 2, 3, 4, 5)
    xk = observed(KKT_S, KKT_starts, 4)
    Vk = sorted(xk)
    Onk = orientation_nodes(Vk)
    Ek = transitive_reduce(Onk, build_edges(Onk, 4, 1), 4)
    dSk = traceable(KKT_S, Vk, 4, 1, Ek)
    dDk = traceable(KKT_D, Vk, 4, 1, Ek)
    KKT_ok = (dSk is not None and dDk is not None
              and binom_obj(dDk, xk, 6) > binom_obj(dSk, xk, 6))
    check("KKT family G=6: both spelled and competitor beats truth", KKT_ok)

    print()
    failed = [n for n, ok in CHECKS if not ok]
    if failed:
        print("SOME CHECKS FAILED:", failed)
        return 1
    print("ALL CHECKS PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
