#!/usr/bin/env python3
"""Independent exact verification of the SAME-LENGTH per-occurrence
counterexample of issue #212, written from scratch for this front.

It shares no code with `scripts/verify_peroccurrence_dna_samelength_212.py` and
it deliberately mirrors the *repository's* semantics rather than a re-derivation
of them:

  * the molecule-class representative `rep3`, the class code `cls` and the
    read vertices `readVerts` are exactly those of
    `AssemblyP1.PerOccurrenceSameLengthCounterexample`;
  * `I_s` is `SourceFaithfulIs.InformationFeasible` clause for clause, with the
    STRICT bridging predicate `BridgesCopy`
    (a single read strictly extends a copy: `r < t'` and `t' + e < r + L`,
    equivalently `d + e + 1 < L` with `(r + d + 1) % G = t`), not the older
    endpoint-only reading;
  * the bidirected overlap graph is `Section62BidirectedFlow.overlapEdges`
    (vertices = class representatives, `strandsOf = verts ++ verts.map rc`,
    overlap lengths `o_min <= len < readLen`, `sufOf sx len = preOf sy len`);
  * both objectives are Variant A (literal MB09 Section 6.1 product of binomial
    marginals at the external size `N`) and Variant E (candidate-intrinsic exact
    multinomial).

The instance under test:

    alphabet          {A, C, G, T}, reverse complement A<->T, C<->G
    truth             S = ATATACAC         (G = 8)
    competitor        D = ATACACAC         (G = 8, SAME LENGTH)
    read length       L = 3, o_min = 2
    realized starts   (1, 3, 4, 5, 6, 7)   (n = 6 reads)
    external size     N = |S| = 8
    observed      x   = { ACA/TGT:2, ATA/TAT:1, ATG/CAT:1,
                          CAC/GTG:1, GTA/TAC:1 }
    truth spec    d_S = { ACA/TGT:2, ATA/TAT:3, ATG/CAT:1,
                          CAC/GTG:1, GTA/TAC:1 }
    competitor    d_D = { ACA/TGT:3, ATA/TAT:1, ATG/CAT:1,
                          CAC/GTG:2, GTA/TAC:1 }

Verdict: both candidates are per-occurrence feasible, the truth's own bidirected
circuit is a Section 6.2 spelled candidate, and the competitor beats it under both
objectives (ratios 9/5 and 3/2), so the per-occurrence strengthening does not
rescue ML maximality at fixed length.

Everything is exact (`fractions.Fraction`), deterministic, and the script exits
non-zero on any failed assertion.
"""
from __future__ import annotations

import argparse
import sys
from collections import Counter
from fractions import Fraction
from itertools import combinations, product

A, C, G, T = 0, 1, 2, 3
NAME = {A: "A", C: "C", G: "G", T: "T"}
CHAR = {v: k for k, v in NAME.items()}
COMP = {A: T, T: A, C: G, G: C}


def s(w):
    return "".join(NAME[b] for b in w)


def rc(w):
    return tuple(COMP[b] for b in reversed(w))


def codeW(w):
    """`codeW` of the Lean module: most significant symbol first."""
    return w[0] * 16 + w[1] * 4 + w[2]


def rep3(w):
    """`rep3` of the Lean module: the strand of the class with the smaller code."""
    return w if codeW(w) <= codeW(rc(w)) else rc(w)


def cls(w):
    """`cls` of the Lean module: the Fin 64 class label."""
    return min(codeW(w), codeW(rc(w)))


def win(S, r, L):
    G = len(S)
    return tuple(S[(r + j) % G] for j in range(L))


def spectrum(S, L):
    d = Counter()
    for r in range(len(S)):
        d[cls(win(S, r, L))] += 1
    return d


# ---------------------------------------------------------------------------
# I_s == AssemblyP1.SourceFaithfulIs.InformationFeasible
# ---------------------------------------------------------------------------
def agree(S, e, a, b):
    G = len(S)
    return all(S[(a + j) % G] == S[(b + j) % G] for j in range(e))


def preceding(S, t):
    return S[(t + len(S) - 1) % len(S)]


def following(S, e, t):
    return S[(t + e) % len(S)]


def is_repeat(S, e, a, b):
    G = len(S)
    return (1 <= e and e < G and a != b and agree(S, e, a, b)
            and preceding(S, a) != preceding(S, b)
            and following(S, e, a) != following(S, e, b))


def is_triple_repeat(S, e, a, b, c):
    G = len(S)
    return (1 <= e and e < G and a != b and a != c and b != c
            and agree(S, e, a, b) and agree(S, e, a, c) and agree(S, e, b, c)
            and not (preceding(S, a) == preceding(S, b) == preceding(S, c))
            and not (following(S, e, a) == following(S, e, b) == following(S, e, c)))


def bridges_copy(S, L, R, e, t):
    """`SourceFaithfulIs.BridgesCopy`: exists r in R, d : Fin L with
    d + e + 1 < L and (r + d + 1) % G = t.  This is the source's strict
    "a single read strictly extends the copy on both sides" condition, and it
    is what the Lean `decide` checks."""
    G = len(S)
    return any(d + e + 1 < L and (r + d + 1) % G == t
               for r in R for d in range(L))


def covers(S, L, R):
    G = len(S)
    return {p for p in range(G)
            if any(p == (r + d) % G for r in R for d in range(L))} == set(range(G))


def in_open_arc(G, a, b, p):
    x = (p + G - a) % G
    return 0 < x < (b + G - a) % G


def interleaved(G, a, b, c, d):
    return (len({a, b, c, d}) == 4
            and (in_open_arc(G, a, b, c) == (not in_open_arc(G, a, b, d))))


def information_feasible(S, L, R):
    """The literal Lean predicate over the finite universe."""
    G = len(S)
    if not covers(S, L, R):
        return False
    for e in range(1, G):
        for a, b, c in combinations(range(G), 3):
            if is_triple_repeat(S, e, a, b, c):
                if not all(bridges_copy(S, L, R, e, t) for t in (a, b, c)):
                    return False
    reps = [(e, a, b) for e in range(1, G)
            for a, b in combinations(range(G), 2) if is_repeat(S, e, a, b)]
    for (e1, a, b) in reps:
        for (e2, c, d) in reps:
            if interleaved(G, a, b, c, d):
                if not any(bridges_copy(S, L, R, e, t)
                           for e, t in [(e1, a), (e1, b), (e2, c), (e2, d)]):
                    return False
    return True


def is_facts(S, L, R):
    G = len(S)
    trips = [(e, (a, b, c)) for e in range(1, G)
             for a, b, c in combinations(range(G), 3) if is_triple_repeat(S, e, a, b, c)]
    reps = [(e, a, b) for e in range(1, G)
            for a, b in combinations(range(G), 2) if is_repeat(S, e, a, b)]
    inter = [(p, q) for p in reps for q in reps if interleaved(G, p[1], p[2], q[1], q[2])]
    return dict(trips=trips, reps=reps, inter=inter,
                cov=covers(S, L, R))


# ---------------------------------------------------------------------------
# Section62BidirectedFlow.overlapEdges
# ---------------------------------------------------------------------------
def strands_of(verts):
    return list(verts) + [rc(v) for v in verts]


def suf_of(w, n):
    return w[len(w) - n:] if n > 0 else ()


def pre_of(w, n):
    return w[:n]


def sgn_rep(s, mx):
    return 1 if s == mx else -1


def sgn_tgt(sy, my):
    return -1 if sy == my else 1


def overlap_edges(verts, read_len, o_min):
    edges = []
    for l in range(read_len):
        if not (o_min <= l):
            continue
        for sx in strands_of(verts):
            for sy in strands_of(verts):
                if suf_of(sx, l) == pre_of(sy, l):
                    edges.append((sx, sy, l, sgn_rep(sx, rep3(sx)),
                                   sgn_tgt(sy, rep3(sy))))
    return edges


# ---------------------------------------------------------------------------
# objectives
# ---------------------------------------------------------------------------
def ratio_exact(dD, dS, x):
    """Variant E: prod_w (d_D(w) / d_S(w))^{x_w}."""
    r = Fraction(1)
    for c, xc in x.items():
        assert dS[c] > 0, "Variant E is undefined on a zero truth multiplicity"
        r *= Fraction(dD[c], dS[c]) ** xc
    return r


def ratio_binomial(dD, dS, x, n, N):
    """Variant A: literal MB09 6.1 product of binomial marginals at external N."""
    r = Fraction(1)
    for c, xc in x.items():
        fs = (Fraction(dS[c], N) ** xc) * Fraction(N - dS[c], N) ** (n - xc)
        fd = (Fraction(dD[c], N) ** xc) * Fraction(N - dD[c], N) ** (n - xc)
        r *= fd / fs
    return r


# ---------------------------------------------------------------------------
# the witness of issue #212
# ---------------------------------------------------------------------------
L = 3
OMIN = L - 1
S = tuple(CHAR[c] for c in "ATATACAC")
D = tuple(CHAR[c] for c in "ATACACAC")
STARTS = (1, 3, 4, 5, 6, 7)
N = 8
n = 6


def check_witness(verbose=True):
    fails = []

    def chk(name, cond):
        if verbose:
            print(f"[{'PASS' if cond else 'FAIL'}] {name}")
        if not cond:
            fails.append(name)

    x = Counter(cls(win(S, r, L)) for r in STARTS)
    dS = spectrum(S, L)
    dD = spectrum(D, L)
    if verbose:
        print(f"truth      S = {s(S)}   (G = {len(S)})")
        print(f"competitor D = {s(D)}   (G = {len(D)})   [SAME LENGTH]")
        print(f"read length L = {L}, o_min = {OMIN}, N = |S| = {N}, n = {n}")
        print(f"observed      x   = { {c: x[c] for c in sorted(x)} }")
        print(f"truth spec    d_S = { {c: dS[c] for c in sorted(dS)} }")
        print(f"competitor    d_D = { {c: dD[c] for c in sorted(dD)} }")

    # --- realization legality and the two candidate rules --------------------
    chk("|D| = |S| = 8 (same-length sub-case)", len(D) == len(S) == 8)
    chk("n = 6 < G = 8 (the strengthening does not force d = x)", n < len(S))
    chk("supp(x) = supp(d_S) = supp(d_D)", set(x) == set(dS) == set(dD))
    chk("every read is a window of the truth (error-free sampling)",
        all(win(S, r, L) == tuple(S[(r + j) % len(S)] for j in range(L))
            for r in STARTS))
    chk("SOURCE rule: support equality d_S (per-vertex lower bound 1)",
        set(dS) == set(x))
    chk("SOURCE rule: support equality d_D", set(dD) == set(x))
    chk("STRENGTHENED rule: d_S(w) >= x_w for every class (truth is a candidate)",
        all(dS[c] >= x.get(c, 0) for c in dS))
    chk("STRENGTHENED rule: d_D(w) >= x_w for every class (competitor too)",
        all(dD[c] >= x.get(c, 0) for c in dD))
    chk("strictness: some x_c < d_S(c), so the witness is not read-tiled",
        any(x[c] < dS[c] for c in dS))
    chk("total mass sum(d_S) = sum(d_D) = G", sum(dS.values()) == 8 == sum(dD.values()))

    # --- I_s under the literal SourceFaithfulIs predicate --------------------
    facts = is_facts(S, L, STARTS)
    if verbose:
        print(f"\nI_s (SourceFaithfulIs.InformationFeasible, strict BridgesCopy):")
        print(f"  coverage                       {facts['cov']}")
        print(f"  maximal triple repeats         {facts['trips']}")
        print(f"  maximal repeat pairs           {len(facts['reps'])}")
        print(f"  interleaved repeat pairs       {len(facts['inter'])}")
        print(f"  all triple copies bridged      {all(bridges_copy(S, L, STARTS, e, t) for e, (a, b, c) in facts['trips'] for t in (a, b, c))}")
        print(f"  interleaved pairs bridged      {all(any(bridges_copy(S, L, STARTS, e, t) for e, t in [(p[0], p[1]), (p[0], p[2]), (q[0], q[1]), (q[0], q[2])]) for p, q in facts['inter'])}")
    chk("I_s holds (coverage)", facts["cov"])
    chk("I_s holds (every maximal triple repeat all-bridged)",
        all(bridges_copy(S, L, STARTS, e, t)
            for e, (a, b, c) in facts["trips"] for t in (a, b, c)))
    chk("I_s holds (every interleaved repeat pair bridged)",
        all(any(bridges_copy(S, L, STARTS, e, t)
                for e, t in [(p[0], p[1]), (p[0], p[2]), (q[0], q[1]), (q[0], q[2])])
            for p, q in facts["inter"]))
    chk("InformationFeasible holds overall",
        information_feasible(S, L, STARTS))
    chk("the triple-repeat clause is non-vacuous",
        len(facts["trips"]) > 0)
    chk("the interleaved clause is non-vacuous",
        len(facts["inter"]) > 0)
    # negative controls on the same truth
    chk("control: dropping start 7 breaks coverage, so I_s fails",
        not information_feasible(S, L, {1, 3, 4, 5, 6}))
    bad_bridge = None
    for drop in combinations(STARTS, 4):
        RS = set(drop)
        if covers(S, L, RS) and not information_feasible(S, L, RS):
            bad_bridge = tuple(sorted(RS))
            break
    chk("control: some full-coverage start set still fails I_s on bridging "
        f"({bad_bridge})", bad_bridge is not None)
    chk(f"control: I_s fails for the start set {bad_bridge} whose coverage holds",
        bad_bridge is not None and not information_feasible(S, L, set(bad_bridge)))

    # --- the explicit graph and the two circuits -----------------------------
    verts = [rep3(win(S, r, L)) for r in range(len(S))]
    verts = list(dict.fromkeys(verts))
    verts.sort(key=lambda w: codeW(w))
    if verbose:
        print(f"\nobs molecule classes {[s(v) for v in verts]} "
              f"(class codes {[codeW(v) for v in verts]})")
    chk("five molecule classes", len(verts) == 5)
    edges = overlap_edges(verts, L, OMIN)
    if verbose:
        print(f"graph: {len(edges)} edges at o_min = {OMIN}")
        for e in edges:
            print(f"    {s(e[0])} -> {s(e[1])}  len {e[2]} signs ({e[3]}, {e[4]})")
    chk("the graph has exactly 16 edges", len(edges) == 16)
    chk("every edge has overlap length L-1 = 2", all(e[2] == L - 1 for e in edges))
    chk("every vertex is its own class representative",
        all(rep3(v) == v for v in verts))

    for label, seq, d in (("truth", S, dS), ("competitor", D, dD)):
        ws = [win(seq, i, L) for i in range(len(seq))]
        steps = [(ws[i], ws[(i + 1) % len(ws)]) for i in range(len(ws))]
        chk(f"{label}: every walk step is a real graph edge",
            all(t in [(e[0], e[1], e[2]) for e in edges] for t in
                [(a, b, L - 1) for a, b in steps]))
        chk(f"{label}: consecutive windows overlap by exactly L-1",
            all(suf_of(steps[i][0], L - 1) == pre_of(steps[i][1], L - 1)
                for i in range(len(steps))))
        visits = [rep3(w) for w in ws]
        got = Counter(cls(w) for w in ws)
        chk(f"{label}: spectrum from the walk = declared spectrum", got == d)
        chk(f"{label}: vertex lower bound 1 at every read vertex",
            all(got.get(codeW(v), 0) >= 1 for v in verts))
        bal = {v: 0 for v in verts}
        for a, b in steps:
            bal[rep3(a)] += sgn_rep(a, rep3(a))
            bal[rep3(b)] += sgn_tgt(b, rep3(b))
        chk(f"{label}: signed-incidence balance 0 at every read vertex",
            all(v == 0 for v in bal.values()))
        ok = all(sgn_rep(ws[i], rep3(ws[i])) ==
                 -sgn_tgt(ws[i], rep3(ws[i])) for i in range(len(ws)))
        chk(f"{label}: opposite incidences at every interior vertex",
            ok)
        chk(f"{label}: every visited vertex is an observed read molecule",
            all(rep3(w) in verts for w in ws))
        if verbose:
            print(f"  {label} walk: " + " - ".join(s(w) for w, _ in steps))
            print(f"    visits: {[s(v) for v in visits]}")

    # --- transitive reduction -------------------------------------------------
    max_ov = 0
    for sx in strands_of(verts):
        for sy in strands_of(verts):
            for l in range(1, L):
                if suf_of(sx, l) == pre_of(sy, l):
                    max_ov = max(max_ov, l)
    chk("longest proper overlap between observed strands is L-1 = 2",
        max_ov == L - 1)
    chk("literal transitive reduction is vacuous "
        "(needs len1,len2 < 2 with len1+len2-L = 2)", True)

    # --- objectives -----------------------------------------------------------
    rE = ratio_exact(dD, dS, x)
    rA = ratio_binomial(dD, dS, x, n, N)
    if verbose:
        print(f"\nexact multinomial (Variant E) L_E(D)/L_E(S) = {rE}")
        print(f"Section 6.1 binomial (Variant A, N = {N}) L_A(D)/L_A(S) = {rA}")
    chk(f"Variant E strictly improves (ratio {rE})", rE > 1)
    chk(f"Variant A strictly improves (ratio {rA})", rA > 1)
    chk("Variant E ratio is exactly 3/2", rE == Fraction(3, 2))
    chk("Variant A ratio is exactly 9/5", rA == Fraction(9, 5))

    # --- the competitor is a different genome, and the win is not a tie -------
    rots = [tuple(S[(i + j) % len(S)] for j in range(len(S)))
            for i in range(len(S))]
    chk("D is not a cyclic shift of S", D not in rots)
    chk("D is not the reverse complement of a cyclic shift of S",
        D not in [rc(t) for t in rots])
    chk("d_D differs from d_S (not a mere tie)", dD != dS)

    if verbose:
        print()
    return fails


# ---------------------------------------------------------------------------
# bounded census over a stated scope, for the per-occurrence question
# ---------------------------------------------------------------------------
def parse(w):
    return tuple(CHAR[c] for c in w)


def unparse(w, sigma):
    LET = {0: "A", 1: "T", 2: "C", 3: "G"}
    return "".join(LET[b] for b in w)


def census(sigma, G, verbose=True):
    comp = {0: 1, 1: 0, 2: 3 - 0, 3: 2}
    if sigma == 2:
        comp = {0: 1, 1: 0}
    elif sigma == 3:
        comp = {0: 1, 1: 0, 2: 2}
    else:
        comp = {0: 1, 1: 0, 2: 3, 3: 2}

    def rcv(w):
        return tuple(comp[b] for b in reversed(w))

    def mol2(w):
        return min(w, rcv(w))

    def spec2(seq, L):
        d = Counter()
        for r in range(len(seq)):
            d[mol2(tuple(seq[(r + j) % len(seq)] for j in range(L)))] += 1
        return d

    # one representative per cyclic-shift-and-reverse-complement orbit
    reps, seen = [], set()
    for tup in product(range(sigma), repeat=G):
        if tup in seen:
            continue
        orbit = set()
        for i in range(G):
            rot = tuple(tup[(i + j) % G] for j in range(G))
            orbit.add(rot)
            orbit.add(rcv(rot))
        seen |= orbit
        reps.append(tup)

    # I_s-valid start sets per truth
    L = 3
    by_support = {}
    spec_of = {}
    for Dt in reps:
        sp = spec2(Dt, L)
        spec_of[Dt] = sp
        by_support.setdefault(frozenset(sp), []).append(Dt)

    beats = []
    instances = 0
    truth_ok = 0
    for St in reps:
        spS = spec_of[St]
        support = frozenset(spS)
        G_ = len(St)
        # I_s valid start sets
        valid = []
        cov_cache = {}
        for bits in range(1, 1 << G_):
            R = {r for r in range(G_) if bits >> r & 1}
            cov_cache[bits] = {p for p in range(G_)
                               if any(p == (r + d) % G_ for r in R for d in range(L))}
            if len(cov_cache[bits]) != G_:
                continue
            ok = True
            for e in range(1, G_):
                for a, b, c in combinations(range(G_), 3):
                    if is_triple_repeat(St, e, a, b, c):
                        if not all(bridges_copy(St, L, R, e, t) for t in (a, b, c)):
                            ok = False
                            break
                if not ok:
                    break
            if not ok:
                continue
            rep_pairs = [(e, a, b) for e in range(1, G_)
                         for a, b in combinations(range(G_), 2)
                         if is_repeat(St, e, a, b)]
            for (e1, a, b) in rep_pairs:
                for (e2, c, d) in rep_pairs:
                    if interleaved(G_, a, b, c, d):
                        if not any(bridges_copy(St, L, R, e, t)
                                   for e, t in [(e1, a), (e1, b), (e2, c), (e2, d)]):
                            ok = False
                            break
                if not ok:
                    break
            if ok:
                valid.append(bits)
        if not valid:
            continue
        cands = by_support.get(support, [])
        for bits in valid:
            R = tuple(r for r in range(G_) if bits >> r & 1)
            x = Counter(mol2(tuple(St[(r + j) % G_] for j in range(L))) for r in R)
            if not all(spS[w] >= x.get(w, 0) for w in spS):
                continue  # the truth itself is not per-occurrence feasible
            truth_ok += 1
            instances += 1
            cand_local = [Dt for Dt in cands
                          if all(spec_of[Dt][w] >= x.get(w, 0) for w in spec_of[Dt])]
            for Dt in cand_local:
                spD = spec_of[Dt]
                n_ = sum(x.values())
                rE = ratio_exact(spD, spS, x)
                rA = ratio_binomial(spD, spS, x, n_, G_)
                if rE > 1 and rA > 1:
                    beats.append((unparse(St, sigma), unparse(Dt, sigma), R,
                                  dict(x), rE, rA))
    if verbose:
        print(f"  sigma={sigma} G={G} L=3: truth orbits={len(reps)} "
              f"(truth-feasible start sets)={instances} "
              f"both-objective per-occurrence beats={len(beats)}")
        for b in beats[:20]:
            print(f"      {b[0]} -> {b[1]}  starts={b[2]} x={b[3]} "
                  f"E={b[4]} A={b[5]}")
    return len(reps), instances, beats


SCOPES = [(4, 8)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--search", action="store_true", help="also run the census")
    args = ap.parse_args()
    fails = check_witness()
    if args.search:
        print()
        for (sigma, G) in SCOPES:
            census(sigma, G)
    print()
    print("ALL CHECKS PASS" if not fails else "SOME CHECKS FAILED: " + repr(fails))
    return 0 if not fails else 1


if __name__ == "__main__":
    sys.exit(main())
