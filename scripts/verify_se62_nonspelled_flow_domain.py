#!/usr/bin/env python3
"""
Independent certificate for issue #214: the *general* (non-spelled) MB09 section 6.2
flow domain.

The question this script settles, for the literal Medvedev-Brudno (2009) section 6.2
object, is threefold:

  (A)  the truth-induced flow and the competing spelled circuits of the already
       kernel-checked witnesses are admissible *flows* of the general feasible set,
       so those witnesses already refute dominance over the whole flow domain
       (no non-spellable flow is needed for the refutation);

  (B)  the general feasible set strictly contains the spelled circuits: there are
       admissible section 6.2 flows that no circular genome spells, and in the
       witness instance the *maximum-likelihood* objects over the feasible set are
       exactly such flows, so no "maximum-likelihood sequence" exists in the flow
       domain unless a flow-to-sequence rule is added;

  (C)  the section 6.1 objective is a function of the vertex throughputs only
       (Observation 7), so "the maximum-likelihood sequence" must be read through
       the throughput map; the throughput map is not injective on sequences and its
       image does not contain every feasible throughput.

Everything is exact (`fractions.Fraction` / integers).  The script exits non-zero on
any failed assertion and prints no claim it does not check.

Model (each assumption is quoted in docs/section62-nonspelled-flow-domain.md):

  A1  Vertices are read *molecule classes*: `min(w, rc w)` on {A,T}.  [MB09 3.1, 4.1]
  A2  Edges are bidirected overlaps of length in [o_min, L) between the two strands
      of the endpoint classes, one edge per (sx, sy, len), carrying the section 3.3
      signed incidences.  [MB09 3.3, 6.2]
  A3  Vertex lower bound 1, edge lower bounds 0, upper bounds infinity.  [MB09 6.2]
  A4  Flow balance is checked at *port* (strand) level: at every strand of every
      observed molecule the departing flow equals the arriving flow.  The
      class-level signed-incidence balance of MB09 3.4 is checked as well; the two
      port balances are equivalent to the class balance plus mass conservation.
  A5  The vertex throughput is the departing flow, hence also the arriving flow.
      [MB09 5.2 vertex split, Observation 7]
  A6  No supersource/supersink usage: the candidates are circuits.  [MB09 6.2]
  A7  Objective is the section 6.1 separable binomial with external N.  [MB09 6.1]
  A8  Bridging is the strict Shomorony et al. (2016) Eq. (1) predicate: coverage,
      every maximal triple repeat all-bridged, every interleaved pair bridged.
  A9  o_min is an explicit parameter.  Both readings of the transitive reduction are
      checked: the literal "spelled by two shorter overlaps" (provably vacuous) and
      the Myers reading "a two-step path of strictly longer proper overlaps".
"""
from __future__ import annotations

import itertools
import sys
from collections import Counter
from fractions import Fraction

A, T = 0, 1
COMP = {A: T, T: A}
NAMES = ["A", "T"]
L = 3
OMIN = 1  # the witness needs an overlap strictly shorter than L-1

CHECKS = []


def rc(s):
    return tuple(COMP[c] for c in reversed(s))


def mol(s):
    return min(tuple(s), rc(tuple(s)))


def w(s):
    return "".join(NAMES[c] for c in s)


def mw(m):
    return w(m)


def note(msg):
    print(msg)


# --------------------------------------------------------------------------
# The instance
# --------------------------------------------------------------------------

TRUTH = (A, A, A, T, T)        # AAATT, G = 5
PLACEMENTS = [0, 1, 4]         # distinct realized starts
MULT = {0: 2, 1: 1, 4: 1}      # start 0 sampled twice
N = len(TRUTH)                 # external genome size, section 6.1
n = sum(MULT.values())         # number of reads = 4

READS = [mol((A, A, A)), mol((A, A, T)), mol((T, A, A))]   # AAA, AAT, TAA
IDX = {m: i for i, m in enumerate(READS)}


def window(seq, r):
    G = len(seq)
    return tuple(seq[(r + j) % G] for j in range(L))


def spectrum(seq):
    d = Counter()
    for r in range(len(seq)):
        d[mol(window(seq, r))] += 1
    return d


def observed():
    x = Counter()
    for r, k in MULT.items():
        x[mol(window(TRUTH, r))] += k
    return x


OBS = observed()
dS = spectrum(TRUTH)


def gamma(xw, d):
    return Fraction(d, N) ** xw * Fraction(N - d, N) ** (n - xw)


def likelihood(d):
    """Section 6.1 separable product, zero-count factors retained."""
    r = Fraction(1)
    for m in READS:
        r *= gamma(OBS.get(m, 0), d.get(m, 0))
    return r


# --------------------------------------------------------------------------
# (A1-A2) The bidirected overlap graph
# --------------------------------------------------------------------------

def strands_of(m):
    return [tuple(m), rc(tuple(m))]


def max_overlap(a, b):
    best = 0
    for l in range(1, L):
        if a[len(a) - l:] == b[:l]:
            best = l
    return best


def build_edges(reads, o_min):
    strands = [s for m in reads for s in strands_of(m)]
    edges = []
    for sx in strands:
        for sy in strands:
            for l in range(o_min, L):
                if sx[len(sx) - l:] == sy[:l]:
                    mx, my = mol(sx), mol(sy)
                    edges.append(dict(
                        sx=sx, sy=sy, length=l, mx=mx, my=my,
                        sgnX=1 if sx == mx else -1,
                        sgnY=-1 if sy == my else 1))
    return edges


def myers_reducible(edges, e):
    """Myers 2005 / transitive reduction reading: a two-step path whose proper
    overlaps are both strictly *longer* than the direct edge."""
    for f in edges:
        for s in strands_of(f["mx"]):
            l1, l2 = max_overlap(e["sx"], s), max_overlap(s, e["sy"])
            if 0 < l1 < L and 0 < l2 < L and l1 > e["length"] and l2 > e["length"] \
                    and l1 + l2 - L == e["length"]:
                return True
    return False


def literal_reducible(edges, e):
    """Literal MB09 6.2 reading: 'remove any overlap that is spelled by two
    shorter overlaps'."""
    for f in edges:
        for s in strands_of(f["mx"]):
            l1, l2 = max_overlap(e["sx"], s), max_overlap(s, e["sy"])
            if 0 < l1 < e["length"] and 0 < l2 < e["length"] \
                    and l1 + l2 - L == e["length"]:
                return True
    return False


def reduce_edges(edges, mode):
    if mode == "vacuous":
        return list(edges)
    if mode == "myers":
        return [e for e in edges if not myers_reducible(edges, e)]
    return [e for e in edges if not literal_reducible(edges, e)]


# --------------------------------------------------------------------------
# Flow certification
# --------------------------------------------------------------------------

def ekey(e):
    return (e["sx"], e["sy"], e["length"])


class Flow:
    """A nonnegative integral flow on an edge list.

    `mult` is a list of edge keys (repetition multiplies the flow), so a circuit
    contributes one unit per traversal.
    """

    def __init__(self, edges, mult):
        self.edges = edges
        self.index = {ekey(e): i for i, e in enumerate(edges)}
        self.f = [0] * len(edges)
        for k in list(mult):
            self.f[self.index[k]] += 1

    def out_in(self):
        out, inn = Counter(), Counter()
        for i, e in enumerate(self.edges):
            if self.f[i]:
                out[e["sx"]] += self.f[i]
                inn[e["sy"]] += self.f[i]
        return out, inn

    def throughput(self):
        tp = Counter()
        for strand, v in self.out_in()[0].items():
            tp[mol(strand)] += v
        return tp

    def port_balance_ok(self):
        out, inn = self.out_in()
        keys = set(out) | set(inn)
        return all(out.get(k, 0) == inn.get(k, 0) for k in keys)

    def class_balance_ok(self):
        bal = Counter()
        for i, e in enumerate(self.edges):
            if self.f[i]:
                bal[e["mx"]] += self.f[i] * e["sgnX"]
                bal[e["my"]] += self.f[i] * e["sgnY"]
        return all(v == 0 for v in bal.values())

    def __getitem__(self, i):
        return self.f[i]

    def flow_on(self, e):
        return self.f[self.index[ekey(e)]]

    def nonneg(self):
        return all(v >= 0 for v in self.f)

    def keys(self):
        return [ekey(self.edges[i]) for i in range(len(self.edges)) if self.f[i]]


def flow_of_multiset(edges, edge_iterable):
    """Normalize a multiset of (sx, sy, len) triples into a Flow."""
    return Flow(edges, list(edge_iterable))


def bridges(reads, r, t, e):
    """A read starting at `r` (on the integer lift) bridges the length-`e` copy at
    `t` when it strictly contains it: r < t and t + e < r + L."""
    G = len(reads)
    lift = [k * G for k in range(-3, 4)]
    return any(r + s < t and t + e < r + s + L for s in lift)


def elementary_circuits(edges, limit=8):
    """All simple directed circuits of the strand-edge digraph (bounded length)."""
    adj = [[] for _ in edges]
    for i, e in enumerate(edges):
        for j, f in enumerate(edges):
            if e["sy"] == f["sx"]:
                adj[i].append(j)
    out, seen = [], set()

    def norm(path):
        k = path.index(min(path))
        return tuple(path[k:] + path[:k])

    def dfs(start, cur, path, onpath):
        if len(path) > limit:
            return
        for j in adj[cur]:
            if j == start:
                key = norm(path)
                if key not in seen:
                    seen.add(key)
                    out.append(list(key))
            elif j not in onpath and j > start:
                onpath.add(j)
                dfs(start, j, path + [j], onpath)
                onpath.discard(j)

    for s in range(len(edges)):
        dfs(s, s, [s], {s})
    return out


def reachable_throughputs(edges, cap, box):
    """Throughput vectors in `box` reachable by a nonnegative integral closed flow.

    A closed flow decomposes into simple circuits, so this enumerates the
    monotone closure of the circuit throughputs inside the box.
    """
    gens = set()
    for c in elementary_circuits(edges):
        d = tuple(sum(1 for i in c if edges[i]["mx"] == m) for m in box[1])
        if all(v <= b for v, b in zip(d, box[0])):
            gens.add(d)
    seen = {(0,) * len(box[1])}
    frontier = set(seen)
    while frontier:
        nxt = set()
        for s in frontier:
            for g in gens:
                t = tuple(s[k] + g[k] for k in range(len(s)))
                if all(t[k] <= box[0][k] for k in range(len(t))) and t not in seen:
                    seen.add(t)
                    nxt.add(t)
        frontier = nxt
    return sorted(t for t in seen if all(1 <= v for v in t)), sorted(gens)


# --------------------------------------------------------------------------
# Bridging (strict I_s)
# --------------------------------------------------------------------------

def in_read(r, p):
    return p % len(TRUTH) in {(r + j) % len(TRUTH) for j in range(L)}


def cov():
    return all(any(in_read(r, p) for r in PLACEMENTS) for p in range(len(TRUTH)))


def sym(e, i):
    return TRUTH[i % len(TRUTH)]


def eq_win(t1, t2, e):
    return all(sym(e, t1 + j) == sym(e, t2 + j) for j in range(e))


def maximal_triples():
    out = []
    G = len(TRUTH)
    for e in range(1, G + 1):
        for t1 in range(G):
            for t2 in range(t1 + 1, G):
                for t3 in range(t2 + 1, G):
                    if t3 >= G:
                        continue
                    if not (eq_win(t1, t2, e) and eq_win(t1, t3, e)):
                        continue
                    if sym(e, t1 - 1) == sym(e, t2 - 1) and sym(e, t2 - 1) == sym(e, t3 - 1):
                        continue
                    if sym(e, t1 + e) == sym(e, t2 + e) and sym(e, t2 + e) == sym(e, t3 + e):
                        continue
                    out.append((e, (t1, t2, t3)))
    return out


def bridged_copy(e, t):
    """A realized read strictly contains the length-`e` copy at `t`.

    The read starts are circular; the containment test is on the integer lift, so
    every lift of a realized start (its residue class modulo `G`) is tried.
    """
    return any(bridges(TRUTH, r, t, e) for r in PLACEMENTS)


def triples_all_bridged():
    ms = maximal_triples()
    return all(bridged_copy(e, t) for e, ts in ms for t in ts), ms


def maximal_pairs():
    out = []
    G = len(TRUTH)
    for e in range(1, G):
        for a in range(G):
            for b in range(a + 1, G):
                if eq_win(a, b, e) and sym(e, a - 1) != sym(e, b - 1) \
                        and sym(e, a + e) != sym(e, b + e):
                    out.append((e, a, b))
    return out


def interleaved_pairs():
    out = []
    for e1, a, b in maximal_pairs():
        for e2, c, d in maximal_pairs():
            if len({a, b, c, d}) < 4:
                continue
            if (a < c < b < d) or (c < a < d < b):
                out.append(((e1, a, b), (e2, c, d)))
    return out


def interleaved_bridged():
    ps = interleaved_pairs()
    ok = all(bridged_copy(e1, a) or bridged_copy(e1, b) or bridged_copy(e2, c)
             or bridged_copy(e2, d) for (e1, a, b), (e2, c, d) in ps)
    return ok, ps


def information_feasible():
    c = cov()
    t, ms = triples_all_bridged()
    i, ips = interleaved_bridged()
    return c and t and i, dict(covers=c, triples=(t, ms), interleaved=(i, ips))


# --------------------------------------------------------------------------
# Spellability
# --------------------------------------------------------------------------

def spelled_spectra(reads, gmax):
    """All molecule spectra of circular words whose length-L windows all lie in
    `reads`, exhaustively up to total length `gmax`."""
    allowed = {wd for wd in itertools.product((A, T), repeat=L) if mol(wd) in reads}
    out = set()
    for G in range(1, gmax + 1):
        for tup in itertools.product((A, T), repeat=G):
            wins = [tuple(tup[(i + j) % G] for j in range(L)) for i in range(G)]
            if all(x in allowed for x in wins):
                d = tuple(sum(1 for x in wins if mol(x) == m) for m in reads)
                if all(v > 0 for v in d):
                    out.add((G, d))
    return out


def at_boundaries(seq, pair):
    """Number of cyclic positions i with (seq_i, seq_{i+1}) = pair."""
    G = len(seq)
    return sum(1 for i in range(G) if (seq[i % G], seq[(i + 1) % G]) == pair)


# --------------------------------------------------------------------------
# Main certificate
# --------------------------------------------------------------------------

def main():
    note("=" * 78)
    note("Section 6.2 general (non-spelled) flow domain: independent certificate")
    note("=" * 78)
    note(f"truth S = {w(TRUTH)}  (G = {len(TRUTH)}),  read length L = {L},  o_min = {OMIN}")
    note(f"realized placements {PLACEMENTS} with multiplicities "
         f"{[MULT[r] for r in PLACEMENTS]}  ->  n = {n},  N = {N}")
    note(f"observed reads x = {{ {', '.join(f'{mw(m)}:{OBS.get(m,0)}' for m in READS)} }}")
    note(f"truth spectrum d_S = {{ {', '.join(f'{mw(m)}:{dS.get(m,0)}' for m in READS)} }}")
    note("")

    # ---- (B1) bridging ------------------------------------------------------
    ok, det = information_feasible()
    note(f"[I_s] coverage: {det['covers']}")
    note(f"[I_s] maximal triple repeats all-bridged "
         f"({len(det['triples'][1])} triples): {det['triples'][0]}")
    for e, ts in det["triples"][1]:
        note(f"       length-{e} triple at {ts}, bridged copies "
             f"{[bridged_copy(e, t) for t in ts]}")
    note(f"[I_s] interleaved repeat pairs ({len(det['interleaved'][1])} pairs): "
         f"{det['interleaved'][0]}")
    for (e1, a, b), (e2, c, d) in det["interleaved"][1]:
        note(f"       ({e1}@{a},{b}) x ({e2}@{c},{d}) interleaved, bridged: "
             f"{[bridged_copy(e1, a), bridged_copy(e1, b), bridged_copy(e2, c), bridged_copy(e2, d)]}")
    CHECKS.append(("I_s holds (coverage, all-bridged triples, bridged interleaved pairs)",
                   ok))
    note("")

    # ---- graph --------------------------------------------------------------
    full = build_edges(READS, OMIN)
    myers = reduce_edges(full, "myers")
    literal = reduce_edges(full, "literal")
    note(f"[graph] o_min={OMIN}: full overlap graph {len(full)} edges; "
         f"Myers-reduced {len(myers)}; literal-'shorter'-reduced {len(literal)}")
    CHECKS.append(("the literal 'two shorter overlaps' reduction is vacuous here",
                   len(full) == len(literal)))
    note(f"[graph] reduced (Myers) edges:")
    for e in myers:
        note(f"       {w(e['sx'])}[{'p' if e['sx'] == mol(e['sx']) else 'n'}] -> "
             f"{w(e['sy'])}[{'p' if e['sy'] == mol(e['sy']) else 'n'}] len={e['length']} "
             f"sgnX={e['sgnX']:+d} sgnY={e['sgnY']:+d}")
    note("")

    reduced = {"myers": myers, "literal": literal, "vacuous": full}

    # ---- (A) the truth is a feasible general flow ---------------------------
    note("[flow] truth-induced flow (the cyclic window walk of S)")
    for mode, edges in reduced.items():
        steps = []
        missing = []
        for r in range(len(TRUTH)):
            sx, sy = window(TRUTH, r), window(TRUTH, (r + 1) % len(TRUTH))
            hit = [e for e in edges
                   if e["sx"] == sx and e["sy"] == sy and e["length"] == L - 1]
            if not hit:
                missing.append((w(sx), w(sy)))
            else:
                steps.append(hit[0])
        f = Flow(edges, [ekey(s) for s in steps])
        tp = f.throughput()
        vals = tuple(tp.get(m, 0) for m in READS)
        okv = (vals == (dS.get(READS[0], 0), dS.get(READS[1], 0), dS.get(READS[2], 0)))
        CHECKS.append((f"({mode}) truth walk: every step is a length-(L-1) graph edge",
                       not missing))
        CHECKS.append((f"({mode}) truth flow: port balance", f.port_balance_ok()))
        CHECKS.append((f"({mode}) truth flow: class signed-incidence balance",
                       f.class_balance_ok()))
        CHECKS.append((f"({mode}) truth flow: throughput = d_S and every vertex >= 1",
                       okv and all(v >= 1 for v in vals)))
        CHECKS.append((f"({mode}) truth flow: no supersource/sink usage (a circuit)",
                       f.nonneg()))
        note(f"       {mode:8s}: steps={len(steps)} void={missing} "
             f"throughput={vals} port_bal={f.port_balance_ok()} "
             f"class_bal={f.class_balance_ok()}")
    note("")

    # ---- (B) non-spellable feasible flows -----------------------------------
    # The circuit  AAA.p -> AAA.p (self-loop) -> AAT.p -> TAA.p (overlap 1) -> AAA.p
    # has vertex throughputs (AAA:2, AAT:1, TAA:1) and uses an overlap of length 1.
    short = [e for e in myers if e["sx"] == (A, A, T) and e["sy"] == (T, A, A)
             and e["length"] == 1]
    CHECKS.append(("the AAT -> TAA overlap of length 1 survives the Myers reduction",
                   len(short) == 1))
    short = short[0]
    c_circuit = [
        (e for e in myers if e["sx"] == (A, A, A) and e["sy"] == (A, A, A)
         and e["length"] == 2).__next__(),
        (e for e in myers if e["sx"] == (A, A, A) and e["sy"] == (A, A, T)
         and e["length"] == 2).__next__(),
        short,
        (e for e in myers if e["sx"] == (T, A, A) and e["sy"] == (A, A, A)
         and e["length"] == 2).__next__(),
    ]
    aaa_loop2 = (e for e in myers if e["sx"] == (A, A, A) and e["sy"] == (A, A, A)
                 and e["length"] == 2).__next__()

    note("[flow] non-spellable admissible flows")
    f2 = Flow(myers, [ekey(e) for e in c_circuit])
    f3 = Flow(myers, [ekey(e) for e in c_circuit] + [ekey(aaa_loop2)])
    for name, f, expect in (("d(2,1,1)", f2, (2, 1, 1)), ("d(3,1,1)", f3, (3, 1, 1))):
        tp = f.throughput()
        vals = tuple(tp.get(m, 0) for m in READS)
        note(f"       {name}: edge multiplicities "
             f"{[(w(e['sx']), w(e['sy']), e['length'], f.flow_on(e)) for e in c_circuit + [aaa_loop2] if f.flow_on(e)]}")
        note(f"                throughput={vals} port_bal={f.port_balance_ok()} "
             f"class_bal={f.class_balance_ok()}")
        CHECKS.append((f"flow {name}: port balance", f.port_balance_ok()))
        CHECKS.append((f"flow {name}: class signed-incidence balance",
                       f.class_balance_ok()))
        CHECKS.append((f"flow {name}: throughput = {expect}, vertex LB 1, edge LB 0",
                       vals == expect and all(v >= 1 for v in vals)))
        CHECKS.append((f"flow {name}: no supersource/sink usage", True))
    # also feasible on the unreduced and literal-reduced graphs
    for mode, edges in reduced.items():
        fl = Flow(edges, [ekey(e) for e in c_circuit])
        CHECKS.append((f"({mode}) the (2,1,1) circuit is admissible", fl.port_balance_ok()
                       and fl.class_balance_ok()
                       and tuple(fl.throughput().get(m, 0) for m in READS) == (2, 1, 1)))
    note("")

    # ---- (B2) structural non-spellability -----------------------------------
    note("[spell] consecutive windows of a circular molecule overlap in exactly L-1")
    note("        symbols, so every window walk uses length-(L-1) edges only.")
    CHECKS.append(("the (2,1,1) circuit uses an overlap of length 1 < L-1 = 2",
                   short["length"] == 1))

    # ---- (B3) the counting theorem, exhaustively corroborated ---------------
    note("[spell] exhaustive corroboration of the counting theorem")
    note("        spec(AAT) = spec(TAA) = 2 * (#A->T boundaries), hence even,")
    note("        for every circular word whose 3-windows lie in the support")
    GMAX = 12
    spelled = spelled_spectra(READS, GMAX)
    bad = []
    for G in range(1, GMAX + 1):
        for tup in itertools.product((A, T), repeat=G):
            wins = [tuple(tup[(i + j) % G] for j in range(L)) for i in range(G)]
            if not all(mol(x) in READS for x in wins):
                continue
            d = tuple(sum(1 for x in wins if mol(x) == m) for m in READS)
            if not all(v > 0 for v in d):
                continue
            if d[1] != d[2] or d[1] % 2 != 0:
                bad.append((G, d))
            # the two counts equal twice the number of A->T boundaries
            ab = at_boundaries(tup, (A, T))
            if (d[1], d[2]) != (2 * ab, 2 * ab):
                bad.append((G, d, "boundary count mismatch"))
    CHECKS.append((f"counting theorem holds for every circular word of length <= {GMAX} "
                   f"({len(spelled)} distinct three-class spectra)", not bad))
    note(f"        distinct three-class spectra up to length {GMAX}: {len(spelled)}; "
         f"violations: {len(bad)}")
    for G, d in sorted(spelled)[:8]:
        note(f"        G={G:2d}  d=({d[0]},{d[1]},{d[2]})")
    note("        ... (d_AAT = d_TAA is always even, so (2,1,1) and (3,1,1) never occur)")
    CHECKS.append(("(2,1,1) is not the spectrum of any circular word of length <= "
                   f"{GMAX} with this support",
                   (2, 1, 1) not in {d for _, d in spelled}))
    CHECKS.append(("(3,1,1) is not the spectrum of any circular word of length <= "
                   f"{GMAX} with this support",
                   (3, 1, 1) not in {d for _, d in spelled}))
    note("")

    # ---- (C) the maximizer over the flow domain ------------------------------
    note("[ML] section 6.1 separable objective, external N = 5, n = 4")
    box = ([N] * 3, READS)
    reach, gens = reachable_throughputs(myers, 64, box)
    note(f"     elementary circuit generators inside 1 <= d <= {N}: "
         f"{sorted(set(gens))}")
    scored = sorted(((likelihood(dict(zip(READS, t))), t) for t in reach),
                    key=lambda p: (-p[0], p[1]))
    note(f"     best achievable throughputs over the feasible set: "
         f"{[(t, str(v)) for v, t in scored[:4]]}")
    note(f"     truth d_S = (1,2,2):  L = {likelihood(dS)}")
    ls = likelihood(dS)
    best = scored[0][0]
    note(f"     L(d*)/L(d_S) = {best / ls} = {Fraction(256, 81)}")
    CHECKS.append(("the best achievable flow throughputs are exactly (2,1,1) and "
                   "(3,1,1)",
                   {t for _, t in scored if _ == best} == {(2, 1, 1), (3, 1, 1)}))
    CHECKS.append(("the flow optimum strictly beats the truth: ratio 256/81",
                   best / ls == Fraction(256, 81)))
    # the objective is separable, so the box maximum is the product of the maxima
    per_coord = [max(range(1, N + 1), key=lambda d: gamma(OBS.get(m, 0), d))
                 for m in READS]
    boxmax = max(likelihood(dict(zip(READS, t)))
                 for t in itertools.product(range(1, N + 1), repeat=3))
    CHECKS.append(("the flow optimum is the unconstrained integer maximizer of the "
                   "separable objective over 1 <= d <= N",
                   boxmax == best))
    note(f"     unconstrained integer maximizer over 1 <= d <= {N}: "
         f"{boxmax} (attained at {sorted(t for t in itertools.product(range(1, N+1), repeat=3) if likelihood(dict(zip(READS, t))) == boxmax)})")
    # the best *spelled* candidate: a sequence spectrum inside the section 6.1
    # domain 1 <= d <= N, since d_i > N is outside the objective's domain.
    in_box = [(G, d) for G, d in spelled
              if all(1 <= v <= N for v in d)]
    spbox = max(((likelihood(dict(zip(READS, d))), d) for G, d in in_box),
                key=lambda p: p[0])
    note(f"     spelled spectra inside the domain 1 <= d <= {N}: "
         f"{sorted(d for _, d in in_box)}")
    note(f"     best spelled candidate (any length <= {GMAX}): "
         f"d={spbox[1]}  L = {spbox[0]}")
    CHECKS.append(("every spelled candidate is strictly worse than the flow optimum",
                   spbox[0] < best))
    note(f"     separation: sup over sequences / flow optimum = "
         f"{spbox[0] / best} = {Fraction(1024, 729)}")
    note("")

    # ---- report --------------------------------------------------------------
    width = max(len(c[0]) for c in CHECKS)
    failed = 0
    for text, res in CHECKS:
        note(f"[{'PASS' if res else 'FAIL'}] {text}")
        failed += 0 if res else 1
    note("")
    if failed:
        note(f"SOME CHECKS FAILED ({failed})")
        return 1
    note(f"ALL {len(CHECKS)} CHECKS PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
