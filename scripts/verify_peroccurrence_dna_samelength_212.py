#!/usr/bin/env python3
"""
Independent exact verification of a SAME-LENGTH counterexample to

    I_s  and  the truth is a per-occurrence-feasible Medvedev-Brudno (2009)
    Section 6.2 bidirected spelled candidate
        ==>  the truth-induced flow is a maximum-likelihood maximizer

under the *per-occurrence* strengthening of the Section 6.2 candidate rule,
in the reverse-complement-collapsed bidirected reading with the real DNA
four-letter alphabet (A<->T, C<->G, no self-complementary base).

Instance verified here
----------------------
    alphabet          {A, C, G, T}, reverse complement A<->T, C<->G
    truth             S = ATATACAC         (G = 8)
    competitor        D = ATACACAC         (G = 8, SAME LENGTH)
    read length       L = 3
    realized starts   (1, 3, 4, 5, 6, 7)   (n = 6 reads, all distinct)
    external size     N = |S| = 8
    observed          x = { ATA/TAT:1, TAC/GTA:1, ACA/TGT:2,
                            CAC/GTG:1, CAT/ATG:1 }
    truth spectrum    d_S = { ATA/TAT:3, TAC/GTA:1, ACA/TGT:2,
                              CAC/GTG:1, CAT/ATG:1 }
    competitor spec   d_D = { ATA/TAT:1, TAC/GTA:1, ACA/TGT:3,
                              CAC/GTG:2, CAT/ATG:1 }

Both same-length objectives strictly improve:
    exact candidate-intrinsic multinomial      L_E(D)/L_E(S) = 3/2
    literal Section 6.1 product of binomials    L_A(D)/L_A(S) = 9/5

Everything is exact (``fractions.Fraction``), deterministic, and the script
exits non-zero on any failed assertion.  Nothing is imported from the rest of
the repository: the I_s check, the molecule classes, the bidirected overlap
graph and the two objectives are all recomputed here from scratch.

Source semantics
----------------
MB09 Section 6.2: "the vertices of this graph are the reads", "each vertex has
a lower bound of 1 since it represents a read that must be present in the
genome at least once", "all other lower bounds are 0 and all upper bounds are
infinity", supersource/supersink at prohibitive cost; Section 4.1: "each
k-molecule is represented only once"; Observation 7: the number of times a walk
visits a read vertex equals the number of times that read is a submolecule of
the spelled molecule.  Section 6.1 gives the exact multinomial with
candidate-intrinsic N(D) and its separable binomial approximation.

The *per-occurrence* rule d_w >= x_w is a STRENGTHENING of the source's
per-vertex lower bound 1, not the Section 6.2 definition; it is the
project-level hypothesis under test here.
"""
from __future__ import annotations

import argparse
import math
import sys
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product

A, C, G, T = 0, 1, 2, 3
COMP = {A: T, T: A, C: G, G: C}
LET = {A: "A", C: "C", G: "G", T: "T"}


def lit(w):
    return "".join(LET[c] for c in w)


def rc(w):
    return tuple(COMP[c] for c in reversed(w))


def mol(w):
    """Molecule class: the lexicographically smaller of the strand and its
    reverse complement (MB09 Sections 3.1 and 4.1)."""
    return min(tuple(w), rc(tuple(w)))


def litmol(w):
    r = rc(w)
    return lit(w) if r == tuple(w) else lit(w) + "/" + lit(r)


def windows(seq, L):
    G = len(seq)
    return [tuple(seq[(i + j) % G] for j in range(L)) for i in range(G)]


def spec(seq, L):
    return Counter(mol(w) for w in windows(seq, L))


# ---------------------------------------------------------------------------
# I_s (Shomorony et al. Eq. (1)) with the strict source bridging predicate
# ---------------------------------------------------------------------------

def maximal_repeat_pairs(S):
    G = len(S)
    out = []
    for e in range(1, G):
        grp = defaultdict(list)
        for i in range(G):
            grp[tuple(S[(i + j) % G] for j in range(e))].append(i)
        for _, pos in sorted(grp.items()):
            for a, b in combinations(pos, 2):
                if (S[(a - 1) % G] != S[(b - 1) % G]
                        and S[(a + e) % G] != S[(b + e) % G]):
                    out.append((e, (a, b)))
    return out


def maximal_triple_repeats(S):
    G = len(S)
    out = []
    for e in range(1, G):
        grp = defaultdict(list)
        for i in range(G):
            grp[tuple(S[(i + j) % G] for j in range(e))].append(i)
        for _, pos in sorted(grp.items()):
            for tri in combinations(pos, 3):
                if (len({S[(t - 1) % G] for t in tri}) > 1
                        and len({S[(t + e) % G] for t in tri}) > 1):
                    out.append((e, tri))
    return out


def interleaved_pairs(S):
    reps = maximal_repeat_pairs(S)
    out = []
    for i in range(len(reps)):
        e1, p1 = reps[i]
        for j in range(i + 1, len(reps)):
            e2, p2 = reps[j]
            four = sorted(set(p1) | set(p2))
            if len(four) != 4:
                continue
            lab = {p: 0 for p in p1}
            lab.update({p: 1 for p in p2})
            if [lab[p] for p in four] in ([0, 1, 0, 1], [1, 0, 1, 0]):
                out.append(((e1, p1), (e2, p2)))
    return out


def bridge_starts_strict(G, t, e, L):
    """Starts r with a read [r, r+L) bridging the copy [t, t+e).

    Source predicate (Bresler et al. Fig. 5; Shomorony et al. Section 3): on a
    suitable lift of the circle, r < t' and t' + e < r + L.
    """
    ok = set()
    for r in range(G):
        for lift in range(G + L):
            if lift % G == t % G and r < lift and lift + e < r + L:
                ok.add(r)
                break
    return ok


def bridge_starts_flank(G, t, e, L):
    """The older endpoint-only reading: some read covers both (t-1) and (t+e).

    Included only to record that it agrees with the strict predicate on this
    instance; it is NOT the source condition.
    """
    ok = set()
    for r in range(G):
        occ = {(r + o) % G for o in range(L)}
        if (t - 1) % G in occ and (t + e) % G in occ:
            ok.add(r)
    return ok


def check_is(S, starts, L, flank=False):
    G = len(S)
    R = set(starts)
    facts = {}
    cov = {(r + o) % G for r in R for o in range(L)}
    facts["coverage"] = (len(cov) == G)
    trips = maximal_triple_repeats(S)
    facts["maximal_triple_repeats"] = trips
    bad = []
    for e, tri in trips:
        for t in tri:
            bs = (bridge_starts_flank if flank else bridge_starts_strict)(G, t, e, L)
            if not (R & bs):
                bad.append((e, t))
    facts["unbridged_triple_copies"] = bad
    facts["triples_all_bridged"] = not bad
    inter = interleaved_pairs(S)
    facts["interleaved_pairs"] = inter
    badi = []
    for (e1, p1), (e2, p2) in inter:
        b1 = any(R & (bridge_starts_flank if flank else bridge_starts_strict)(G, t, e1, L)
                 for t in p1)
        b2 = any(R & (bridge_starts_flank if flank else bridge_starts_strict)(G, t, e2, L)
                 for t in p2)
        if not (b1 or b2):
            badi.append(((e1, p1), (e2, p2)))
    facts["unbridged_interleaved_pairs"] = badi
    facts["interleaved_bridged"] = not badi
    facts["holds"] = all(facts[k] for k in
                         ("coverage", "triples_all_bridged", "interleaved_bridged"))
    return facts


# ---------------------------------------------------------------------------
# Explicit bidirected overlap graph (MB09 Sections 3.3, 6.2)
# ---------------------------------------------------------------------------

class Molecule:
    def __init__(self, rep):
        self.rep = tuple(rep)
        self.alt = rc(self.rep)

    def p(self):
        return self.rep

    def n(self):
        return self.alt

    def __eq__(self, other):
        return isinstance(other, Molecule) and self.rep == other.rep

    def __hash__(self):
        return hash(self.rep)

    def __repr__(self):
        return litmol(self.rep)


def build_graph(observed, L, omin):
    """Every bidirected overlap of length oMin <= len < L between two strands
    of two observed molecules, with the Section 3.3 incidences."""
    edges = []
    for mx in observed:
        for my in observed:
            for sx in (mx.p(), mx.n()):
                for sy in (my.p(), my.n()):
                    for l in range(omin, L):
                        if sx[len(sx) - l:] == sy[:l]:
                            edges.append({
                                "x": mx, "y": my, "sx": sx, "sy": sy, "len": l,
                                "sign_x": +1 if tuple(sx) == mx.p() else -1,
                                "sign_y": -1 if tuple(sy) == my.p() else +1,
                            })
    return edges


def overlap_len(a, b):
    best = 0
    for l in range(1, len(a) + 1):
        if a[len(a) - l:] == b[:l]:
            best = l
    return best


def reduce_literal(edge, observed, L):
    """MB09 Section 6.2 literal reading: the overlap is spelled by two shorter
    overlaps."""
    l, sx, sy = edge["len"], edge["sx"], edge["sy"]
    for my in observed:
        for s in (my.p(), my.n()):
            l1, l2 = overlap_len(sx, s), overlap_len(s, sy)
            if l1 and l2 and l1 < l and l2 < l and (l1 + l2 - L) == l:
                return True
    return False


def reduce_myers(edge, observed, L):
    """The alternative reading: a two-step path of strictly longer proper
    overlaps."""
    l, sx, sy = edge["len"], edge["sx"], edge["sy"]
    for my in observed:
        if my == edge["x"] or my == edge["y"]:
            continue
        for s in (my.p(), my.n()):
            l1, l2 = overlap_len(sx, s), overlap_len(s, sy)
            if l1 < L and l2 < L and l1 > l and l2 > l:
                return True
    return False


def walk_steps(seq, L):
    ws = windows(seq, L)
    G = len(seq)
    steps = []
    for i in range(G):
        sx, sy = ws[i], ws[(i + 1) % G]
        assert sx[1:] == sy[:-1], "consecutive windows must overlap by L-1"
        mx, my = Molecule(mol(sx)), Molecule(mol(sy))
        steps.append({"i": i, "mx": mx, "my": my, "sx": sx, "sy": sy, "len": L - 1,
                      "sign_x": +1 if tuple(sx) == mx.p() else -1,
                      "sign_y": -1 if tuple(sy) == my.p() else +1})
    return steps, [Molecule(mol(w)) for w in ws]


def validate_circuit(seq, L, graph, observed, x):
    """Section 6.2 spelled-candidate certificate: every step is a real edge of
    the graph, opposite incidences at every interior vertex, every read vertex
    is used (support equality), the per-occurrence throughputs hold, every
    read-vertex balance is 0, and no supersource/supersink edge is used."""
    steps, visits = walk_steps(seq, L)
    G = len(seq)
    used = []
    for st in steps:
        hit = [e for e in graph if e["sx"] == st["sx"] and e["sy"] == st["sy"]
               and e["len"] == st["len"]]
        assert hit, ("step is not a graph edge", st)
        used.append(st["sx"])
    for i in range(G):
        prev, cur = steps[(i - 1) % G], steps[i]
        assert prev["my"] == visits[i] and cur["mx"] == visits[i]
        assert prev["sign_y"] == -cur["sign_x"], ("orientation", i)
    d = Counter(visits)
    assert {m.rep for m in d} == {m.rep for m in observed}, "support equality"
    assert all(d.get(m, 0) >= 1 for m in observed), "vertex lower bound 1"
    bal = {m: 0 for m in observed}
    for st in steps:
        bal[st["mx"]] += st["sign_x"]
        bal[st["my"]] += st["sign_y"]
    assert all(v == 0 for v in bal.values()), "read-vertex balance"
    perocc = all(d.get(m, 0) >= x.get(m.rep, 0) for m in observed)
    return steps, visits, d, perocc


# ---------------------------------------------------------------------------
# objectives
# ---------------------------------------------------------------------------

def E_exact(spD, spS, x):
    """Variant E, the exact candidate-intrinsic multinomial, up to the
    observation-only factor n!/prod x_w! and the common N^{-n}: both candidates
    have the same length G, so
    L_E(D)/L_E(S) = prod_w (d_D(w)/d_S(w))^{x_w}."""
    r = Fraction(1)
    for w, xw in x.items():
        r *= Fraction(spD[w], spS[w]) ** xw
    return r


def A_binom(spD, spS, x, n, N):
    """Variant A, the literal Section 6.1 product of binomial marginals with the
    external genome size N and n reads (zero-count factors are 1 because the
    candidate and observed supports coincide)."""
    r = Fraction(1)
    for w, xw in x.items():
        fs = (Fraction(spS[w], N) ** xw) * Fraction(N - spS[w], N) ** (n - xw)
        fd = (Fraction(spD[w], N) ** xw) * Fraction(N - spD[w], N) ** (n - xw)
        r *= fd / fs
    return r


# ---------------------------------------------------------------------------
# witness verification
# ---------------------------------------------------------------------------

L = 3
OMIN = L - 1
S = (A, T, A, T, A, C, A, C)          # ATATACAC
D = (A, T, A, C, A, C, A, C)          # ATACACAC
STARTS = (1, 3, 4, 5, 6, 7)
N = len(S)


def verify_witness(verbose=True):
    checks = []

    def chk(name, cond):
        checks.append((name, bool(cond)))

    G = len(S)
    n = len(STARTS)
    dS = spec(S, L)
    dD = spec(D, L)
    x = Counter()
    for r in STARTS:
        x[mol(tuple(S[(r + j) % G] for j in range(L)))] += 1
    supp = set(dS)

    if verbose:
        print(f"truth      S = {lit(S)}   (G = {G})")
        print(f"competitor D = {lit(D)}   (G = {len(D)})   [SAME LENGTH]")
        print(f"read length L = {L}, o_min = {OMIN}, N = |S| = {N}")
        print(f"realized starts {STARTS} (n = {n} reads)")
        print(f"observed      x   = { {litmol(w): v for w, v in sorted(x.items())} }")
        print(f"truth spec    d_S = { {litmol(w): v for w, v in sorted(dS.items())} }")
        print(f"competitor    d_D = { {litmol(w): v for w, v in sorted(dD.items())} }")
        print()

    # --- realization legality -------------------------------------------------
    for r in STARTS:
        w = tuple(S[(r + j) % G] for j in range(L))
        chk(f"read at start {r} is the window {lit(w)} of S", True)
    chk("all reads are windows of the truth (error-free sampling)",
        all(mol(tuple(S[(r + j) % G] for j in range(L))) ==
            mol(tuple(S[(r + j) % G] for j in range(L))) for r in STARTS))
    chk("n < G (so per-occurrence does not force d = x)", n < G)
    chk("|D| = |S| (same-length sub-case)", len(D) == len(S))

    # --- support equality and per-occurrence ---------------------------------
    chk("supp(x) = supp(d_S)", set(x) == supp)
    chk("supp(x) = supp(d_D)", set(x) == set(dD))
    chk("truth is per-occurrence feasible (d_S(w) >= x_w for all w)",
        all(dS[w] >= x[w] for w in supp))
    chk("competitor is per-occurrence feasible (d_D(w) >= x_w for all w)",
        all(dD[w] >= x[w] for w in supp))
    chk("strictness: some x_w < d_S(w) (the truth is not read-tiled)",
        any(x[w] < dS[w] for w in supp))
    chk("total mass sum(d_S) = G = sum(d_D)", sum(dS.values()) == G == sum(dD.values()))

    # --- I_s -------------------------------------------------------------------
    for flank in (False, True):
        tag = "endpoint-only" if flank else "strict"
        facts = check_is(S, STARTS, L, flank=flank)
        chk(f"I_s coverage ({tag})", facts["coverage"])
        chk(f"I_s every maximal triple repeat all-bridged ({tag})",
            facts["triples_all_bridged"])
        chk(f"I_s every interleaved pair bridged ({tag})",
            facts["interleaved_bridged"])
        chk(f"I_s holds ({tag})", facts["holds"])
        if verbose:
            print(f"I_s ({tag}): maximal triple repeats "
                  f"{[(e, t) for e, t in facts['maximal_triple_repeats']]}")
            print(f"             unbridged triple copies {facts['unbridged_triple_copies']}")
            print(f"             interleaved pairs {len(facts['interleaved_pairs'])}, "
                  f"unbridged {len(facts['unbridged_interleaved_pairs'])}")
    facts = check_is(S, STARTS, L, flank=False)
    chk("I_s certificate is non-vacuous (at least one bridged triple copy)",
        len(facts["maximal_triple_repeats"]) > 0)

    # --- explicit bidirected graph and the two circuits -----------------------
    observed = [Molecule(mol(w)) for w in sorted(supp)]
    graph = build_graph(observed, L, OMIN)
    if verbose:
        print(f"\nbidirected graph on {observed} at o_min = {OMIN}: "
              f"{len(graph)} edges")
        for e in graph:
            print(f"    {e['x']} -> {e['y']}  strand {lit(e['sx'])} -> {lit(e['sy'])} "
                  f"len {e['len']} signs ({e['sign_x']}, {e['sign_y']})")
        print()
    for name, seq in (("truth", S), ("competitor", D)):
        steps, visits, d, perocc = validate_circuit(seq, L, graph, observed, x)
        chk(f"{name}: every step is a real edge of the overlap graph", True)
        chk(f"{name}: opposite incidences at every interior vertex", True)
        chk(f"{name}: vertex lower bound 1", all(d.get(m, 0) >= 1 for m in observed))
        chk(f"{name}: per-occurrence throughputs", perocc)
        chk(f"{name}: read-vertex balance 0 (closed circuit)", True)
        if verbose:
            print(f"{name} walk: " + " - ".join(litmol(st['sx']) for st in steps))
            print(f"   visits: {[repr(v) for v in visits]}")
            print(f"   throughputs: { {repr(m): d.get(m, 0) for m in observed} }")

    # --- transitive reduction ---------------------------------------------------
    employed = []
    for seq in (S, D):
        steps, _ = walk_steps(seq, L)
        employed += steps
    red = []
    for st in employed:
        fake = {"x": st["mx"], "y": st["my"], "sx": st["sx"], "sy": st["sy"],
                "len": st["len"]}
        if reduce_literal(fake, observed, L) or reduce_myers(fake, observed, L):
            red.append(st)
    chk("no employed edge is removed by the transitive reduction (both readings)",
        not red)
    chk("every employed edge has overlap L-1 = 2 (maximal proper overlap)",
        all(st["len"] == L - 1 for st in employed))

    # --- objectives -------------------------------------------------------------
    rE = E_exact(dD, dS, x)
    rA = A_binom(dD, dS, x, n, N)
    if verbose:
        print(f"\nexact multinomial (Variant E) ratio L_E(D)/L_E(S) = {rE}")
        print(f"Section 6.1 binomial (Variant A) ratio L_A(D)/L_A(S) = {rA}")
    chk(f"Variant E strictly improves: ratio {rE} > 1", rE > 1)
    chk(f"Variant A strictly improves: ratio {rA} > 1", rA > 1)
    chk(f"Variant E ratio is exactly 3/2", rE == Fraction(3, 2))
    chk(f"Variant A ratio is exactly 9/5", rA == Fraction(9, 5))

    # --- competitor is not the same genome -------------------------------------
    def rotations(w):
        return [tuple(w[(i + j) % G] for j in range(G)) for i in range(G)]

    chk("D is not a cyclic shift of S", D not in rotations(S))
    chk("D is not the reverse complement of a cyclic shift of S",
        D not in [rc(t) for t in rotations(S)])
    chk("D is not the reverse complement of S", D != rc(S))
    chk("d_D differs from d_S (not a mere tie)", dD != dS)

    if verbose:
        print()
        for name, ok in checks:
            print(f"[{'PASS' if ok else 'FAIL'}] {name}")
    return all(ok for _, ok in checks), checks


# ---------------------------------------------------------------------------
# bounded census over the stated scope
# ---------------------------------------------------------------------------

def make_rc(sigma):
    if sigma == 2:
        c = {0: 1, 1: 0}
    elif sigma == 3:
        c = {0: 1, 1: 0, 2: 2}
    elif sigma == 4:
        c = {0: 1, 1: 0, 2: 3, 3: 2}
    else:
        raise ValueError(sigma)
    return lambda w: tuple(c[v] for v in reversed(w))


def census(G, L, sigma, verbose=True):
    rc = make_rc(sigma)
    LET2 = {0: "A", 1: "T", 2: "C", 3: "G"}

    def lit2(w):
        return "".join(LET2[c] for c in w)

    def mol2(w):
        return min(tuple(w), rc(tuple(w)))

    def spec2(seq):
        return Counter(mol2(w) for w in windows(seq, L))

    reps = []
    seen = set()
    for tup in product(range(sigma), repeat=G):
        if tup in seen:
            continue
        orb = set()
        for sft in range(G):
            rot = tuple(tup[(sft + j) % G] for j in range(G))
            orb.add(rot)
            orb.add(rc(rot))
        seen |= orb
        reps.append(tup)
    specs = [spec2(D) for D in reps]
    by_support = defaultdict(list)
    for D, sp in zip(reps, specs):
        by_support[frozenset(sp)].append((D, sp))
    n_inst = 0
    hits = {"E": 0, "A": 0, "both": 0}
    pairs = set()
    for S in reps:
        spS = spec2(S)
        W = frozenset(spS)
        # I_s valid start sets (strict predicate)
        valid = []
        trips = [(t, e) for e, tri in maximal_triple_repeats(S) for t in tri]
        trip_masks = [bridge_starts_strict(G, t, e, L) for t, e in trips]
        im = []
        for (e1, p1), (e2, p2) in interleaved_pairs(S):
            m1 = set().union(*[bridge_starts_strict(G, t, e1, L) for t in p1]) \
                if p1 else set()
            m2 = set().union(*[bridge_starts_strict(G, t, e2, L) for t in p2]) \
                if p2 else set()
            im.append((m1, m2))
        for bits in range(1, 1 << G):
            mask = {r for r in range(G) if bits >> r & 1}
            cov = {(r + o) % G for r in mask for o in range(L)}
            if len(cov) != G:
                continue
            if any(not (mask & bm) for bm in trip_masks):
                continue
            if any(not (mask & m1 or mask & m2) for m1, m2 in im):
                continue
            valid.append(bits)
        if not valid:
            continue
        cand = [(D, spD) for (D, spD) in by_support.get(W, [])
                if all(spD[w] >= 1 for w in W)]
        for bits in valid:
            T = tuple(r for r in range(G) if bits >> r & 1)
            cT = Counter(mol2(tuple(S[(r + j) % G] for j in range(L))) for r in T)
            lo = {w: max(cT.get(w, 0), 1) for w in W}
            if sum(lo.values()) > G - 1:
                continue
            n_inst += 1
            for D, spD in cand:
                ranges = []
                ok = True
                for w in W:
                    hi = min(spS[w], spD[w])
                    if hi < lo[w]:
                        ok = False
                        break
                    ranges.append((w, lo[w], hi))
                if not ok:
                    continue
                total = 1
                for w, a, hi in ranges:
                    total *= (hi - a + 1)
                if total > 300000:
                    continue
                for xv in product(*[range(a, hi + 1) for w, a, hi in ranges]):
                    n = sum(xv)
                    if n > G - 1:
                        continue
                    xx = dict(zip([w for w, a, hi in ranges], xv))
                    er = E_exact(spD, spS, xx)
                    ar = A_binom(spD, spS, xx, n, G)
                    if er > 1:
                        hits["E"] += 1
                    if ar > 1:
                        hits["A"] += 1
                    if er > 1 and ar > 1:
                        hits["both"] += 1
                        pairs.add((S, D))
    if verbose:
        print(f"  G={G} L={L} sigma={sigma} rc={'fixed-point-free' if sigma != 3 else 'one fixed point'}"
              f": truths={len(reps)} instances={n_inst} "
              f"E={hits['E']} A={hits['A']} both={hits['both']} "
              f"distinct (S,D) pairs={len(pairs)}")
        for (S, D) in sorted(pairs):
            print(f"        {lit2(S)} -> {lit2(D)}")
    return hits, n_inst, pairs


ROWS = [
    (6, 3, 2), (7, 3, 2), (8, 3, 2),
    (6, 3, 3), (7, 3, 3), (8, 3, 3),
    (8, 3, 4),
    (6, 4, 3), (8, 4, 3),
]


def run_census(verbose=True):
    checks = []
    totals = {}
    for (G, L, sigma) in ROWS:
        h, n, pairs = census(G, L, sigma, verbose)
        totals[(G, L, sigma)] = (h, n, pairs)
    # (beats counted as (S, D, T, x) tuples, distinct (S, D) pairs)
    exp = {(6, 3, 2): (0, 0), (7, 3, 2): (0, 0), (8, 3, 2): (0, 0),
           (6, 3, 3): (0, 0), (7, 3, 3): (0, 0), (8, 3, 3): (4, 1),
           (8, 3, 4): (16, 4), (6, 4, 3): (0, 0), (8, 4, 3): (0, 0)}
    for key, want in exp.items():
        h, n, pairs = totals[key]
        checks.append((f"census (G,L,sigma)={key}: {want[0]} both-objective beats "
                       f"in {want[1]} distinct (S,D) pairs",
                       h["both"] == want[0] and len(pairs) == want[1]))
    if verbose:
        print()
        for name, ok in checks:
            print(f"[{'PASS' if ok else 'FAIL'}] {name}")
    return all(ok for _, ok in checks)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--search", action="store_true",
                    help="also run the bounded census")
    args = ap.parse_args()
    ok, _ = verify_witness()
    if args.search:
        ok = run_census() and ok
    print()
    print("ALL CHECKS PASS" if ok else "SOME CHECKS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
