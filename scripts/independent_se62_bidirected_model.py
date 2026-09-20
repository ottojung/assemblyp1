#!/usr/bin/env python3
"""Independent exact model of the Medvedev-Brudno (2009) Section 6.2
bidirected-flow constraint, and its use against the AAATT -> AAAATT witness.

This file is deliberately written from the primary source (MB09 sections 3.1,
3.2, 3.3, 3.4, 5.2, 6.1, 6.2; PMC3154397) and *not* from the repository's
existing support/lower-bound predicate.  The distinction matters: the existing
`Feasible` / `SeqSupportLB` predicate is a finite support certificate, whereas
Section 6.2 asks for an integral bidirected flow with read-vertex lower bound 1
on a transitively reduced bidirected overlap graph, whose vertex throughput is
the number of visits of a spelled walk (Observation 7).

What is modeled here
====================

Alphabet.  Binary {0,1} (A=0, T=1) with reverse-complement involution
rc(w) = complement(reverse(w)).  A DNA molecule is the unordered pair
{w, rc(w)}; its canonical positive strand is p = min(w, rc(w)) and its
negative strand is n = rc(p).  (MB09 section 3.1.)

Bidirected overlap graph.  Vertices are the observed read molecule types.
For molecules x,y and orientation choices (ox,oy) in {P,N}^2 put
A = p(x) if ox=P else n(x), B = p(y) if oy=P else n(y).  If a nonempty proper
suffix of A equals a prefix of B of length l with 1 <= l <= L-1, add a
bidirected edge with

    sign at x = +1 if ox=P else -1
    sign at y = +1 if oy=N else -1      (MB09 section 3.3, four cases)

and overlap length l = the maximal such length.  Loops (x=y) take incidence
+2 when (P,N), -2 when (N,P), and 0 when (P,P) or (N,N) (MB09 section 3.2).

Walk.  A walk is a sequence of edges in which the head incidence of an
incoming edge is opposite to the tail incidence of the outgoing edge at every
interior vertex (MB09 section 3.2).  A spelled molecule is exactly such a walk;
its throughput d(v) = pos(f)(v) = neg(f)(v) by Observation 7.

Flow / admissibility.  An integral flow f >= 0 on the (transitively reduced)
graph is admissible with read-vertex lower bound 1 when the signed-incidence
balance pos(f)(v) - neg(f)(v) = 0 at every read vertex and d(v) = pos(f)(v) >= 1
for every observed read vertex.  (The source's supersource/sink allows nonzero
balance; a single spelled molecule is the special case with zero balance and no
source/sink usage.  A spelled competitor is therefore an admissible flow a
fortiori.)

Objective.  The Section 6.1 separable binomial with external N = true genome
length,

    L(d) = prod_w (d_w/N)^{x_w} (1 - d_w/N)^{n - x_w},   0 <= d_w <= N.

Bridging.  I_s is the Shomorony et al. Eq. (1) / Bresler et al. predicate:
coverage, every maximal triple repeat all-bridged, every maximal interleaved
repeat pair bridged, with the strict copy-bridging normalization
    read [r,r+L) bridges copy [t,t+ell)  iff  r < t and t+ell < r+L.

Scope / epistemic status
========================
Everything computed here is finite exact computation (fractions.Fraction),
i.e. EVIDENCE, not proof.  The only mathematical claims are the explicitly
proved lemmas in the accompanying note.  The bounded neighbourhood search is
exhaustive only for the stated finite box.

Exits non-zero on a failed assertion.
"""

from fractions import Fraction
from itertools import combinations


# ---------------------------------------------------------------------------
# molecules, circular windows, spectra
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
        m = mol(circ(seq, s, L))
        counts[m] = counts.get(m, 0) + 1
    return counts


def observed(seq, starts, L):
    counts = {}
    for s in starts:
        m = mol(circ(seq, s, L))
        counts[m] = counts.get(m, 0) + 1
    return counts


# ---------------------------------------------------------------------------
# Section 3.3 bidirected overlap graph
# ---------------------------------------------------------------------------

class Edge:
    """An undirected bidirected edge with a fixed incidence at each endpoint.

    u, v are molecule-class indices (u <= v).  su, sv in {+1,-1} are the
    incidence signs at u and v; for a loop (u == v) the effective loop
    incidence is su + sv when su == sv and 0 otherwise, matching section 3.2.
    length is the underlying strand-overlap length.
    """

    __slots__ = ("u", "su", "v", "sv", "length")

    def __init__(self, u, su, v, sv, length):
        self.u, self.su, self.v, self.sv, self.length = u, su, v, sv, length

    def pos_inc(self, w):
        """Number of positive-incident ends of this edge at vertex w."""
        return (1 if (self.u == w and self.su == +1) else 0) + \
               (1 if (self.v == w and self.sv == +1) else 0)

    def neg_inc(self, w):
        """Number of negative-incident ends of this edge at vertex w."""
        return (1 if (self.u == w and self.su == -1) else 0) + \
               (1 if (self.v == w and self.sv == -1) else 0)

    def as_tuple(self):
        return (self.u, self.su, self.v, self.sv, self.length)

    def __repr__(self):
        return f"Edge({self.u},{self.su:+d},{self.v},{self.sv:+d},len={self.length})"


def strand(m, orient):
    return m if orient == +1 else revcomp(m)


def max_overlap(a, b):
    """Maximal nonempty proper overlap: suffix of a == prefix of b, < len(a)."""
    best = 0
    for l in range(1, len(a)):
        if a[len(a) - l:] == b[:l]:
            best = l
    return best


def build_graph(molecules, L, o_min):
    """Return (ids, edges) for the bidirected overlap graph on molecule types."""
    ids = {m: i for i, m in enumerate(molecules)}
    edges = []
    seen = set()
    for i, x in enumerate(molecules):
        for j, y in enumerate(molecules):
            if j < i:
                continue
            for ox in (+1, -1):
                for oy in (+1, -1):
                    A = strand(x, ox)
                    B = strand(y, oy)
                    l = max_overlap(A, B)
                    if l >= o_min:
                        # sign at x: +1 iff positive strand used
                        sx = +1 if ox == +1 else -1
                        # sign at y: +1 iff NEGATIVE strand used (section 3.3)
                        sy = +1 if oy == -1 else -1
                        key = (i, sx, j, sy, l)
                        if key in seen:
                            continue
                        seen.add(key)
                        edges.append(Edge(i, sx, j, sy, l))
    return ids, edges


def transitive_reduction(edges, molecules, L, verbose=False):
    """Literal reading: remove an overlap spelled by two strictly shorter ones.

    An edge (x,l,y) is reducible if there is a molecule z and edges (x,l1,z),
    (z,l2,y) with l1,l2 < l, orientation-consistent at z (opposite incidences),
    and l = l1 + l2 - L (composition of equal-length read overlaps).
    """
    kept = []
    removed = []
    for e in edges:
        red = False
        for z in range(len(molecules)):
            for e1 in edges:
                if e1 is e:
                    continue
                if not ({e1.u, e1.v} <= {e.u, z}):
                    continue
                # orient e1 from x to z
                if e1.u == e.u and e1.v == z:
                    a, sa, b, sb = e1.u, e1.su, e1.v, e1.sv
                elif e1.v == e.u and e1.u == z:
                    a, sa, b, sb = e1.v, e1.sv, e1.u, e1.su
                else:
                    continue
                for e2 in edges:
                    if e2 is e or e2 is e1:
                        continue
                    # orient e2 from z to y
                    if e2.u == z and e2.v == e.v:
                        c, sc, d, sd = e2.u, e2.su, e2.v, e2.sv
                    elif e2.v == z and e2.u == e.v:
                        c, sc, d, sd = e2.v, e2.sv, e2.u, e2.su
                    else:
                        continue
                    if sb != -sc:
                        continue
                    if e1.length < e.length and e2.length < e.length \
                            and e1.length + e2.length - L == e.length:
                        red = True
                        break
                if red:
                    break
            if red:
                break
        (removed if red else kept).append(e)
    if verbose:
        print(f"    transitive reduction: {len(removed)} removed, "
              f"{len(kept)} kept")
    return kept, removed


# ---------------------------------------------------------------------------
# spelled-molecule verification and throughput
# ---------------------------------------------------------------------------

def sequence_walk(seq, L, ids, edges):
    """Return the list of edge indices realizing the cyclic window walk, or None.

    Also returns the sign sequence at each vertex to check the walk condition.
    """
    g = len(seq)
    n = g  # one transition per start
    used = []
    positions = []
    for s in range(n):
        A = circ(seq, s, L)
        B = circ(seq, (s + 1) % g, L)
        x, y = mol(A), mol(B)
        if x not in ids or y not in ids:
            return None
        ox = +1 if A == strand(x, +1) else -1
        oy = +1 if B == strand(y, +1) else -1
        ix, iy = ids[x], ids[y]
        # required departure sign at x and arrival sign at y (section 3.3)
        out_x = +1 if ox == +1 else -1
        in_y = +1 if oy == -1 else -1
        found = None
        for ei, e in enumerate(edges):
            if e.u == ix and e.v == iy:
                tail_sig, head_sig = e.su, e.sv
            elif e.u == iy and e.v == ix:
                tail_sig, head_sig = e.sv, e.su
            else:
                continue
            if tail_sig == out_x and head_sig == in_y:
                found = (ei, tail_sig, head_sig)
                break
        if found is None:
            return None
        used.append(found)
        positions.append((s, ix, iy))
    # walk condition: opposite head/tail orientations at interior vertices
    for k in range(1, n):
        if used[k - 1][2] == used[k][1]:
            return None
    # closing condition at the origin vertex
    if used[-1][2] == used[0][1]:
        return None
    return [u[0] for u in used]


def throughput(seq, L, ids):
    d = {}
    for s in range(len(seq)):
        m = mol(circ(seq, s, L))
        d[m] = d.get(m, 0) + 1
    return d


# ---------------------------------------------------------------------------
# Section 6.1 separable binomial objective
# ---------------------------------------------------------------------------

def loglik_ratio(x, dS, dD, n, N):
    def prod(d):
        out = Fraction(1)
        for w, xw in x.items():
            dw = d.get(w, 0)
            if not (0 <= dw <= N):
                return None
            base = Fraction(dw, N)
            out *= base ** xw * (1 - base) ** (n - xw)
        return out
    a, b = prod(dS), prod(dD)
    if a is None or b is None:
        return None
    return b / a


# ---------------------------------------------------------------------------
# I_s (strict bridging), independent implementation
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
        pre = {seq[(t - 1) % g] for t in (t1, t2, t3)}
        post = {seq[(t + ell) % g] for t in (t1, t2, t3)}
        if len(pre) == 1 or len(post) == 1:
            continue
        out.append((t1, t2, t3))
    return out


def cyclically_interleaved(a, b, c, d, g):
    if len({a % g, b % g, c % g, d % g}) < 4:
        return False

    def between(x, lo, hi):
        return 0 < (x - lo) % g < (hi - lo) % g

    # labels alternate iff exactly one of c,d lies on the arc a->b
    return between(c, a, b) != between(d, a, b)


def check_I_s(seq, starts, L):
    g = len(seq)
    failures = []
    covered = set()
    for r in starts:
        for i in range(L):
            covered.add((r + i) % g)
    if covered != set(range(g)):
        failures.append(("coverage", sorted(set(range(g)) - covered)))
    for ell in range(1, g + 1):
        for triple in maximal_triple_repeats(seq, ell):
            for t in triple:
                if not bridges_copy(seq, starts, L, t, ell):
                    failures.append(("triple", ell, t))
    for ell1 in range(1, g + 1):
        p1 = maximal_repeat_pairs(seq, ell1)
        for ell2 in range(1, g + 1):
            p2 = maximal_repeat_pairs(seq, ell2)
            for (a, b) in p1:
                for (c, d) in p2:
                    if (a, b, c, d) == (c, d, a, b):
                        continue
                    if not cyclically_interleaved(a, b, c, d, g):
                        continue
                    bridged = any(
                        bridges_copy(seq, starts, L, t, ell)
                        for (t, ell) in ((a, ell1), (b, ell1),
                                         (c, ell2), (d, ell2)))
                    if not bridged:
                        failures.append(("interleaved", ell1, a, b, ell2, c, d))
    return (not failures), failures


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

def s_of(bits):
    return "".join("T" if b else "A" for b in bits)


def primary_test(words=True, o_min=2):
    S = [0, 0, 0, 1, 1]          # AAATT
    starts = [0, 1, 4]
    L = 3
    N = len(S)
    x = observed(S, starts, L)
    dS = spectrum(S, L)
    ok, fails = check_I_s(S, starts, L)
    assert ok, f"I_s failed: {fails}"

    molecules = sorted(set(x) | set(dS))
    ids, edges = build_graph(molecules, L, o_min=o_min)
    kept, removed = transitive_reduction(edges, molecules, L)

    # no edge of the employed witnesses is reducible (max proper overlap L-1)
    assert all(e.length <= L - 1 for e in kept)
    assert not any(e.length == L - 1 for e in removed), \
        "a maximal-overlap edge was removed by the reduction"

    walkS = sequence_walk(S, L, ids, kept)
    assert walkS is not None, "truth AAATT is not a valid bidirected walk"

    D = [0, 0, 0, 0, 1, 1]       # AAAATT
    dD = spectrum(D, L)
    assert set(dD) <= set(dS), "competitor uses an unobserved read type"
    assert set(dD) == set(dS), "competitor drops an observed read vertex"
    walkD = sequence_walk(D, L, ids, kept)
    assert walkD is not None, "competitor AAAATT is not a valid bidirected walk"

    n = sum(x.values())
    ratio = loglik_ratio(x, dS, dD, n, N)
    assert ratio is not None and ratio > 1, f"ratio not > 1: {ratio}"

    if words:
        print("MB09 Section 6.2 independent bidirected-flow test")
        print("=" * 56)
        print(f"  truth      S = {s_of(S)}  (G={len(S)}, L={L}, N={N})")
        print(f"  reads      starts {starts}, x = "
              f"{ {s_of(k): v for k, v in sorted(x.items())} }")
        print(f"  molecules  {[s_of(m) for m in molecules]}")
        print(f"  edges      {len(edges)} (o_min={o_min}); after reduction "
              f"{len(kept)}; removed {len(removed)}")
        print(f"  truth walk {[kept[i].as_tuple() for i in walkS]}")
        print(f"  d_S        { {s_of(k): v for k, v in sorted(dS.items())} }")
        print(f"  competitor D = {s_of(D)}  (|D|={len(D)})")
        print(f"  d_D        { {s_of(k): v for k, v in sorted(dD.items())} }")
        print(f"  L(D)/L(S)  = {ratio} = {float(ratio):.6f} > 1")
    return {
        "S": S, "starts": starts, "L": L, "N": N, "x": x, "dS": dS,
        "D": D, "dD": dD, "ratio": ratio, "molecules": molecules,
        "ids": ids, "edges": edges, "kept": kept,
    }


def enumerate_admissible_flows(molecules, ids, kept, x, totals_cap, edge_cap, N):
    """Enumerate integral circulations with balance 0 at read vertices.

    Bounded exact enumeration over edge multiplicities 0..edge_cap with
    sum f_e <= totals_cap.  Returns the list of distinct throughput vectors d
    with d_w >= 1 on all observed vertices and d_w <= N (binomial domain).
    """
    V = len(molecules)
    E = len(kept)
    pos = [[kept[e].pos_inc(v) for e in range(E)] for v in range(V)]
    neg = [[kept[e].neg_inc(v) for e in range(E)] for v in range(V)]
    results = {}

    def rec(e, f, bal, tot):
        if e == E:
            if any(b != 0 for b in bal):
                return
            d = {}
            for v, m in enumerate(molecules):
                p = sum(pos[v][j] * f[j] for j in range(E))
                if p < 1 or p > N:
                    return
                d[m] = p
            if set(d) != set(x):
                return
            results[tuple(sorted(d.items()))] = d
            return
        for val in range(0, min(edge_cap, totals_cap - tot) + 1):
            nb = [bal[v] + (pos[v][e] - neg[v][e]) * val for v in range(V)]
            rec(e + 1, f + [val], nb, tot + val)

    rec(0, [], [0] * V, 0)
    return list(results.values())


def enumerate_spelled_competitors(molecules, ids, kept, x, N, L, max_len):
    """All single spelled molecules D with |D| <= max_len whose every L-window
    is an observed read type, whose support equals the observed support, whose
    bidirected window walk is valid, and with d_w <= N.  Exact within the bound.
    """
    seen = set()
    out = []
    for GD in range(L, max_len + 1):
        for bits in range(1 << GD):
            D = [(bits >> i) & 1 for i in range(GD)]
            dD = spectrum(D, L)
            if set(dD) != set(x):
                continue
            if any(v > N for v in dD.values()):
                continue
            if sequence_walk(D, L, ids, kept) is None:
                continue
            key = tuple(sorted(dD.items()))
            if key not in seen:
                seen.add(key)
                out.append(dD)
    return out


def bounded_search():
    """Exhaustive finite search for a bridging truth beaten by a spelled
    competitor, over a tightly bounded box.  EVIDENCE ONLY."""
    hits = []
    L = 3
    for G in (4, 5, 6):
        for bits in range(1 << G):
            S = [(bits >> i) & 1 for i in range(G)]
            # fix the rotation so each circular class is visited once
            if min((tuple(S[i:] + S[:i]) for i in range(G))) != tuple(S):
                continue
            for n in (2, 3, 4):
                for starts in combinations(range(G), n):
                    ok, _ = check_I_s(S, starts, L)
                    if not ok:
                        continue
                    x = observed(S, starts, L)
                    dS = spectrum(S, L)
                    if set(x) != set(dS):
                        continue
                    N = G
                    if any(v > N for v in dS.values()):
                        continue
                    molecules = sorted(set(x) | set(dS))
                    ids, edges = build_graph(molecules, L, o_min=2)
                    kept, _ = transitive_reduction(edges, molecules, L)
                    for dD in enumerate_spelled_competitors(
                            molecules, ids, kept, x, N, L, max_len=N + 2):
                        r = loglik_ratio(x, dS, dD, sum(x.values()), N)
                        if r is not None and r > 1:
                            # reconstruct *some* spelling string for the report
                            hits.append((S, starts, dD, r))
    return hits


def main():
    info = primary_test()

    # robustness: the witness uses only length-(L-1) overlaps, which cannot be
    # removed by the transitive reduction for any o_min, and o_min in {1,2} are
    # the only values at L=3.  Re-run the whole certificate at o_min=1.
    alt = primary_test(words=False, o_min=1)
    assert alt["ratio"] == info["ratio"], "o_min changed the ratio"
    print(f"  [robustness] identical certificate at o_min=1 "
          f"({len(alt['edges'])} edges, ratio {alt['ratio']})")

    print()
    print("Bounded exhaustive flow check for the primary instance")
    print("-" * 56)
    molecules = info["molecules"]
    ids = info["ids"]
    x = info["x"]
    dS = info["dS"]
    N = info["N"]
    n = sum(x.values())
    flows = enumerate_admissible_flows(molecules, ids, info["kept"], x,
                                       totals_cap=3 * N, edge_cap=N, N=N)

    def lik(d):
        out = Fraction(1)
        for w, xw in x.items():
            dw = d.get(w, 0)
            out *= Fraction(dw, N) ** xw * (1 - Fraction(dw, N)) ** (n - xw)
        return out

    best = max(flows, key=lik)
    print(f"  admissible circulations with d_w <= N (sum f_e <= {3*N}, "
          f"f_e <= {N}): {len(flows)}")
    print(f"  best throughput d* = "
          f"{ {s_of(k): v for k, v in sorted(best.items())} }")
    print(f"  L(d*)/L(d_S) = {lik(best) / lik(dS)}")
    print(f"  truth d_S = { {s_of(k): v for k, v in sorted(dS.items())} }")
    # note: d* need not be a single circuit; a single spelled competitor is
    # enumerated separately below and is the first-tier (no source/sink) object.
    spelled = enumerate_spelled_competitors(
        molecules, ids, info["kept"], x, N, info["L"], max_len=N + 2)
    if spelled:
        dbest = max(spelled, key=lik)
        print(f"  best single spelled competitor (|D| <= {N+2}): "
              f"{ {s_of(k): v for k, v in sorted(dbest.items())} }  "
              f"L/L(d_S) = {lik(dbest) / lik(dS)}")

    print()
    print("Tightly bounded neighbourhood search (G<=6, L=3, n<=4)")
    print("-" * 56)
    hits = bounded_search()
    seen = set()
    uniq = []
    for S, starts, dD, r in hits:
        k = (tuple(S), tuple(starts), tuple(sorted(dD.items())))
        if k in seen:
            continue
        seen.add(k)
        uniq.append((S, starts, dD, r))
    uniq.sort(key=lambda t: -t[3])
    print(f"  hitting (truth, starts, competitor-throughput, ratio) tuples: "
          f"{len(uniq)}")
    for S, starts, dD, r in uniq[:12]:
        comp = " ".join(f"{s_of(k)}:{v}" for k, v in sorted(dD.items()))
        print(f"    S={s_of(S)} starts={starts}  d_D={{{comp}}}  "
              f"ratio={r} ({float(r):.4f})")
    if len(uniq) > 12:
        print(f"    ... and {len(uniq) - 12} more")

    print()
    print("All assertions passed.")


if __name__ == "__main__":
    main()
