#!/usr/bin/env python3
"""Independent exact verification of a disconnected-support feasible optimum
at full overlap (o_min = L-1 = 2) in the bidirected / reverse-complement
Medvedev-Brudno (2009) section 6.2 flow model.

Question settled (issue #214, section 6.2 genuine target): at o_min = L-1, is
every section 6.1-optimal section 6.2 flow positive-support connected?  This
script exhibits an explicit feasible flow whose throughput is the UNIQUE global
maximizer of the section 6.1 objective over its whole domain and whose positive
support is DISCONNECTED, starting from a truth that satisfies the strict
Shomorony I_s bridging predicate.  So the answer is NO.

Everything is exact (fractions.Fraction), deterministic, and exits non-zero on
any failed assertion.  It shares no code with the earlier section 6.2
searches.  The script is self-contained: it rebuilds the graph, re-checks I_s
from scratch, and re-derives every clause.

Instance
--------
alphabet {A,T}, reverse-complement involution A <-> T (molecule classes).
truth   S = AAATAT  (G = 6)
L = 3, o_min = L-1 = 2  (full overlap)
starts  (0, 0, 1, 3, 5)   ->  x = {AAA:2, AAT:1, ATA:1, TAA:1}, n = 5, N = 6
support {AAA, AAT, ATA, TAA}  (all four molecule classes)

Disconnected optimal flow f*:
  component 1:  AAA.p -> AAA.p  (self-overlap "AA")  x2
  component 2:  AAT.p -> ATA.p -> TAA.p -> AAT.p  (circuit)
  throughput  d* = (AAA:2, AAT:1, ATA:1, TAA:1)
  positive support = {AAA} u {AAT, ATA, TAA}   -> two components

The I_s certificate (coverage, all-bridged triples, bridged interleaved pairs)
is the one already kernel-checked by
AssemblyP1.SameLengthSection62Counterexample.truth_information_feasible for this
exact truth and realized start set {0,1,3,5}; this script re-derives it
independently as corroboration.
"""
from __future__ import annotations
import itertools
import sys
from collections import Counter, defaultdict
from fractions import Fraction

A, T = 0, 1
NAMES = ["A", "T"]
L = 3
OMIN = 2          # = L - 1  (full overlap)
G = 6
TRUTH = (A, A, A, T, A, T)          # AAATAT
STARTS = [0, 0, 1, 3, 5]             # start 0 sampled twice
N_READS = len(STARTS)                # 5
N_EXT = G                            # external genome size = |S| = 6
REALIZED = sorted(set(STARTS))       # {0,1,3,5}

failures = []


def check(cond, msg):
    tag = "ok " if cond else "FAIL"
    print(f"  [{tag}] {msg}")
    if not cond:
        failures.append(msg)


def w(s):
    return "".join(NAMES[c] for c in s)


def rc(s):
    return tuple({A: T, T: A}[c] for c in reversed(s))


def mol(s):
    return min(tuple(s), rc(tuple(s)))


def strands_of(m):
    return [tuple(m), rc(tuple(m))]


ALL3 = list(itertools.product((A, T), repeat=L))
CLASS_OF = {x: mol(x) for x in ALL3}
# the four molecule classes, as representative strands
CLASSES = [mol((A, A, A)), mol((A, A, T)), mol((A, T, A)), mol((T, A, A))]
CLASS_NAMES = {c: w(c) for c in CLASSES}


def sym(i):
    return TRUTH[i % G]


def window_at(seq, r):
    return tuple(seq[(r + j) % len(seq)] for j in range(L))


print("=" * 72)
print("Disconnected-support feasible optimum at o_min = L-1 = 2 (bidirected/RC)")
print("=" * 72)
print(f"truth S = {w(TRUTH)} (G={G}), L={L}, o_min={OMIN}")
print(f"starts {STARTS} -> n={N_READS}, N={N_EXT}, realized {REALIZED}")
print(f"classes: {[CLASS_NAMES[c] for c in CLASSES]}")

# ---------------------------------------------------------------------------
# 1. Section 6.2 bidirected overlap graph at o_min = 2 (proper overlaps: len 2)
# ---------------------------------------------------------------------------
print("\n[1] section 6.2 overlap graph at o_min = 2")
edges = []
for sx in [s for m in CLASSES for s in strands_of(m)]:
    for sy in [s for m in CLASSES for s in strands_of(m)]:
        for l in range(OMIN, L):
            if sx[len(sx) - l:] == sy[:l]:
                mx, my = mol(sx), mol(sy)
                sgnX = 1 if sx == mx else -1
                sgnY = -1 if sy == my else 1
                edges.append(dict(sx=tuple(sx), sy=tuple(sy), len=l,
                                  mx=mx, my=my, sgnX=sgnX, sgnY=sgnY))
print(f"  edges: {len(edges)}")
for e in edges:
    print(f"    {w(e['sx'])} -> {w(e['sy'])}  len={e['len']}  "
          f"sgn=({e['sgnX']},{e['sgnY']})")
# the four edges used by f*
used = [((A, A, A), (A, A, A)), ((A, A, T), (A, T, A)),
        ((A, T, A), (T, A, A)), ((T, A, A), (A, A, T))]
for (sx, sy) in used:
    check(any(e["sx"] == sx and e["sy"] == sy and e["len"] == 2 for e in edges),
          f"edge {w(sx)} -> {w(sy)} (len 2) is in the graph")

# ---------------------------------------------------------------------------
# 2. I_s (strict Shomorony), re-derived independently
# ---------------------------------------------------------------------------
print("\n[2] I_s re-derived independently (coverage, triples, interleaved)")
covered = set()
for r in REALIZED:
    for j in range(L):
        covered.add((r + j) % G)
check(len(covered) == G, "coverage: every position covered")


def eq_win(t1, t2, e):
    return all(sym(t1 + j) == sym(t2 + j) for j in range(e))


def bridges(t, e):
    # strict copy bridging: a realized read [r, r+L) with r < t < t+e < r+L
    # on the integer lift (t is already a lift in [0,G))
    for r in REALIZED:
        for s in range(-3, 4):
            if r + s * G < t and t + e < r + s * G + L:
                return True
    return False


trip_ok = True
for e in range(1, G + 1):
    for t1 in range(G):
        for t2 in range(t1 + 1, G):
            for t3 in range(t2 + 1, G):
                if not (eq_win(t1, t2, e) and eq_win(t1, t3, e)):
                    continue
                if sym(t1 - 1) == sym(t2 - 1) == sym(t3 - 1):
                    continue
                if sym(t1 + e) == sym(t2 + e) == sym(t3 + e):
                    continue
                if not all(bridges(t, e) for t in (t1, t2, t3)):
                    trip_ok = False
                    print(f"    unbridged triple e={e}@({t1},{t2},{t3})")
check(trip_ok, "every maximal triple repeat is all-bridged")


def maximal_pairs():
    out = []
    for e in range(1, G):
        for a in range(G):
            for b in range(a + 1, G):
                if eq_win(a, b, e) and sym(a - 1) != sym(b - 1) \
                        and sym(a + e) != sym(b + e):
                    out.append((e, a, b))
    return out


mps = maximal_pairs()
inter_ok = True
for e1, a, b in mps:
    for e2, c, d in mps:
        if len({a, b, c, d}) < 4:
            continue
        if (a < c < b < d) or (c < a < d < b):
            if not (bridges(a, e1) or bridges(b, e1)
                    or bridges(c, e2) or bridges(d, e2)):
                inter_ok = False
                print(f"    unbridged interleaved ({e1}@{a},{b})x({e2}@{c},{d})")
check(inter_ok, "every interleaved pair of maximal repeats is bridged")

# ---------------------------------------------------------------------------
# 3. Observed counts and the section 6.1 objective
# ---------------------------------------------------------------------------
print("\n[3] observed counts x and section 6.1 objective")
x = Counter()
for r in STARTS:
    x[mol(window_at(TRUTH, r))] += 1
print(f"  x = { {CLASS_NAMES[m]: x.get(m, 0) for m in CLASSES} }")
check(x[CLASSES[0]] == 2 and x[CLASSES[1]] == 1
      and x[CLASSES[2]] == 1 and x[CLASSES[3]] == 1,
      "x = {AAA:2, AAT:1, ATA:1, TAA:1}")


def gamma(xw, d):
    return Fraction(d, N_EXT) ** xw * Fraction(N_EXT - d, N_EXT) ** (N_READS - xw)


def lik(dvec):
    r = Fraction(1)
    for m in CLASSES:
        r *= gamma(x.get(m, 0), dvec.get(m, 0))
    return r


# ---------------------------------------------------------------------------
# 4. The disconnected optimal flow f*
# ---------------------------------------------------------------------------
print("\n[4] the disconnected feasible flow f*")
fidx = {tuple(sorted({e["sx"], e["sy"]})) + (e["sx"], e["sy"]): i
        for i, e in enumerate(edges)}


def eidx(sx, sy):
    for i, e in enumerate(edges):
        if e["sx"] == tuple(sx) and e["sy"] == tuple(sy) and e["len"] == 2:
            return i
    raise KeyError((sx, sy))


flow_mult = [0] * len(edges)
for (sx, sy), k in [(((A, A, A), (A, A, A)), 2),
                    (((A, A, T), (A, T, A)), 1),
                    (((A, T, A), (T, A, A)), 1),
                    (((T, A, A), (A, A, T)), 1)]:
    flow_mult[eidx(sx, sy)] += k

# 4a. edge lower bounds (all 0)
check(all(0 <= k for k in flow_mult), "edge lower bounds 0 <= f*(e) for all e")

# 4b. class-level signed-incidence balance = 0 at every class
bal = Counter()
for i, e in enumerate(edges):
    if flow_mult[i]:
        bal[e["mx"]] += flow_mult[i] * e["sgnX"]
        bal[e["my"]] += flow_mult[i] * e["sgnY"]
check(all(bal.get(m, 0) == 0 for m in CLASSES),
      f"class balance 0 at every class: { {CLASS_NAMES[m]: bal.get(m,0) for m in CLASSES} }")

# 4c. port-level (strand) balance at every strand of every class
port_ok = True
for m in CLASSES:
    for s in strands_of(m):
        out = sum(flow_mult[i] for i, e in enumerate(edges)
                  if e["sx"] == s and flow_mult[i])
        inn = sum(flow_mult[i] for i, e in enumerate(edges)
                  if e["sy"] == s and flow_mult[i])
        if out != inn:
            port_ok = False
            print(f"    port imbalance at {w(s)}: out={out} in={inn}")
check(port_ok, "port balance at every strand of every class")

# 4d. throughput = departing flow, and vertex lower bound 1
tp = Counter()
for i, e in enumerate(edges):
    if flow_mult[i]:
        tp[e["mx"]] += flow_mult[i]
tp_vec = tuple(tp.get(m, 0) for m in CLASSES)
check(tp_vec == (2, 1, 1, 1), f"throughput d* = {tp_vec}")
check(all(tp.get(m, 0) >= 1 for m in CLASSES), "vertex lower bound 1 at every class")

# 4e. no supersource / supersink (the flow is a circulation: balanced)
check(all(bal.get(m, 0) == 0 for m in CLASSES),
      "no terminal usage (balanced circulation)")

# 4f. positive support is disconnected
parent = {m: m for m in CLASSES}


def find(a):
    while parent[a] != a:
        parent[a] = parent[parent[a]]
        a = parent[a]
    return a


def union(a2, b2):
    ra, rb = find(a2), find(b2)
    if ra != rb:
        parent[ra] = rb


for i, e in enumerate(edges):
    if flow_mult[i]:
        union(e["mx"], e["my"])
comps = defaultdict(list)
for m in CLASSES:
    comps[find(m)].append(m)
comp_list = [sorted(v) for v in comps.values()]
print(f"  support components: {[[CLASS_NAMES[m] for m in v] for v in comp_list]}")
check(len(comp_list) == 2, "positive support is DISCONNECTED (exactly 2 components)")
check(sorted(len(v) for v in comp_list) == [1, 3],
      "components have sizes 1 and 3 (an isolated class + a 3-class circuit)")

# ---------------------------------------------------------------------------
# 5. f* is section 6.1-optimal: d* is the UNIQUE global maximizer over [1,N]^4
# ---------------------------------------------------------------------------
print("\n[5] f* is section 6.1-optimal (unique global maximizer)")
best_val = Fraction(-1)
argmax = []
for vals in itertools.product(range(1, N_EXT + 1), repeat=len(CLASSES)):
    dvec = dict(zip(CLASSES, vals))
    v = lik(dvec)
    if v > best_val:
        best_val = v
        argmax = [vals]
    elif v == best_val:
        argmax.append(vals)
print(f"  global argmax over [1,{N_EXT}]^4: {argmax}  value={best_val}")
check(argmax == [(2, 1, 1, 1)],
      "unique global maximizer is d* = (2,1,1,1), attained by the disconnected flow")
check(lik(dict(zip(CLASSES, tp_vec))) == best_val,
      "the disconnected flow attains the global maximum")

# ---------------------------------------------------------------------------
# 6. The truth is a feasible flow and is strictly beaten
# ---------------------------------------------------------------------------
print("\n[6] the truth is a feasible flow and is strictly beaten")
# truth window walk: AAATAT windows AAA,AAT,ATA,TAA,ATA,TAA (cyclic)
truth_windows = [mol(window_at(TRUTH, r)) for r in range(G)]
print(f"  truth windows: {[CLASS_NAMES[m] for m in truth_windows]}")
truth_tp = Counter(truth_windows)
truth_vec = tuple(truth_tp.get(m, 0) for m in CLASSES)
print(f"  truth spectrum d_S = {truth_vec}")
check(truth_vec == (1, 1, 3, 1), "truth spectrum d_S = (1,1,3,1)")
# truth walk edges (all length-2), verify they are graph edges + balanced
tw_edges = []
for r in range(G):
    s1 = tuple(window_at(TRUTH, r))
    s2 = tuple(window_at(TRUTH, (r + 1) % G))
    tw_edges.append((s1, s2))
check(all(any(e["sx"] == a and e["sy"] == b and e["len"] == 2 for e in edges)
          for a, b in tw_edges), "every truth-walk step is a len-2 graph edge")
# truth balance
tbal = Counter()
for (a, b) in tw_edges:
    for e in edges:
        if e["sx"] == a and e["sy"] == b and e["len"] == 2:
            tbal[e["mx"]] += e["sgnX"]
            tbal[e["my"]] += e["sgnY"]
check(all(tbal.get(m, 0) == 0 for m in CLASSES), "truth flow is balanced (a circuit)")
lik_truth = lik(dict(zip(CLASSES, truth_vec)))
lik_star = lik(dict(zip(CLASSES, tp_vec)))
print(f"  L(d_S) = {lik_truth}")
print(f"  L(d*)  = {lik_star}")
check(lik_truth < lik_star, "the truth is strictly beaten by the disconnected optimum")
ratio = lik_star / lik_truth
print(f"  L(d*)/L(d_S) = {ratio}")
# AAA factor: (2/6)^2(4/6)^3 / ((1/6)^2(5/6)^3) = 256/125
# ATA factor: (1/6)(5/6)^4 / ((3/6)(3/6)^4)   = 625/243
# AAT, TAA factors: 1 (d* = d_S = 1 there).  Total = (256/125)(625/243) = 1280/243.
check(ratio == Fraction(1280, 243), "ratio is exactly 1280/243")

# ---------------------------------------------------------------------------
# 7. Nuance: the optimal throughput (2,1,1,1) is itself spellable (AAAAT),
#    so disconnectedness at o_min=L-1 is a DIFFERENT phenomenon from the
#    o_min=1 non-spellability.  Also: (2,1,1,1) is achievable by a CONNECTED
#    flow (the AAAAT window walk), so the optimum set contains both a connected
#    and a disconnected realization.
# ---------------------------------------------------------------------------
print("\n[7] nuance: d* = (2,1,1,1) is spellable (AAAAT) and also connectedly realizable")
aaaat = (A, A, A, A, T)
aaaat_spec = Counter(mol(window_at(aaaat, r)) for r in range(len(aaaat)))
aaaat_vec = tuple(aaaat_spec.get(m, 0) for m in CLASSES)
print(f"  AAAAT spectrum = {aaaat_vec}")
check(aaaat_vec == (2, 1, 1, 1), "AAAAT has spectrum (2,1,1,1) = d*")
# connected realization: the AAAAT window walk
aw = [(tuple(window_at(aaaat, r)), tuple(window_at(aaaat, (r + 1) % 5)))
      for r in range(5)]
aparent = {m: m for m in CLASSES}


def afind(a):
    while aparent[a] != a:
        aparent[a] = aparent[aparent[a]]
        a = aparent[a]
    return a


for (a, b) in aw:
    ra, rb = afind(mol(a)), afind(mol(b))
    if ra != rb:
        aparent[ra] = rb
aroots = {afind(mol(a)) for (a, _) in aw}
check(len(aroots) == 1, "AAAAT window walk is a single connected circuit realizing d*")
print("  => the optimum d* has BOTH a connected realization (AAAAT walk) and")
print("     a disconnected realization (f*); the disconnected one is an optimum,")
print("     refuting positive-support connectedness of ALL optima.")

# ---------------------------------------------------------------------------
print("\n" + "=" * 72)
if failures:
    print(f"RESULT: {len(failures)} CHECK(S) FAILED")
    for m in failures:
        print(f"  - {m}")
    sys.exit(1)
print("RESULT: ALL CHECKS PASSED")
print("At o_min = L-1 = 2, an explicit I_s-bridged disconnected feasible optimum")
print("exists: positive-support connectedness of all optima is FALSE.")
print("=" * 72)
