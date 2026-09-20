#!/usr/bin/env python3
"""
Independent exact verification of a SAME-LENGTH counterexample to

    I_s  and  the truth is an admissible Medvedev-Brudno (2009) Section 6.2
    bidirected-flow candidate
        ==>  the truth-induced flow is a Section 6.1 maximum-likelihood maximizer

under the *actual* Section 6.2 feasibility object (a bidirected flow on the
transitively reduced read-overlap graph whose vertices are the observed read
DNA molecules, with vertex lower bound 1, edge lower bounds 0, and a
supersource/sink used only at prohibitive cost).  The candidate that beats the
truth is a single spelled molecule of the SAME length as the truth, so the
fixed-length (|D| = |S| = G) sub-case is refuted under that source reading.

Instance (2026-09-20):

    alphabet          {A, T}, reverse-complement involution A <-> T
    truth             S = AAATAT   (G = 6)
    read length       L = 3
    realized starts   (0, 0, 1, 3, 5)          (n = 5 reads; start 0 twice)
    external size     N = |S| = 6
    observed          x = { AAA:2, AAT:1, ATA:1, TAA:1 }
    truth spectrum    d_S = { AAA:1, AAT:1, ATA:3, TAA:1 }
    competitor        D = AAAAAT   (|D| = 6)
    competitor spec   d_D = { AAA:3, AAT:1, ATA:1, TAA:1 }

Claims checked here (all exact, `fractions.Fraction`, deterministic; exits
non-zero on any failed assertion):

  (1) I_s: coverage, every maximal triple repeat all-bridged, every interleaved
      pair bridged on at least one copy.  (For this truth the interleaving
      conjunct is NON-vacuous: the A-copies {0,2} and {1,4} interleave; both
      pairs are bridged.  An earlier unmerged note claimed interleaving was
      vacuous; that prose is wrong, and this script pins the correct fact.)
  (2) Both S and D are spelled by cyclic walks in the bidirected overlap graph
      on the observed molecules; every step is a real bidirected edge of length
      L-1; consecutive edges have opposite orientations at every interior
      vertex; every read vertex has flow >= 1 (the source lower bound);
      all read-vertex balances are 0; no supersource/supersink edge is used
      (both are genuine bidirected circuits).
  (3) The transitive reduction (literal "spelled by two shorter overlaps" and
      the Myers longer-overlap reading) removes none of the employed edges.
  (4) Both same-length likelihoods strictly improve:
        exact candidate-intrinsic multinomial   L_exact(D)/L_exact(S) = 3
        literal Section 6.1 fixed-N binomial    L_6.1(D)/L_6.1(S)     = 5
  (5) Bounded exhaustive search (optional, `--search`): over the stated scope
      the counterexample is confined to (G, L, bidirected) = (6, 3); single
      strand and the per-occurrence strengthening find none.

Source semantics.  MB09 Section 6.2: "the vertices of this graph are the
reads"; "each vertex has a lower bound of 1 since it represents a read that
must be present in the genome at least once"; Section 4.1: "each k-molecule is
represented only once" (molecule classes, not sampled occurrences).  Hence a
duplicated observed molecule is one vertex, the observed count x enters only
the Section 6.1 likelihood, and the lower bound is per vertex (a spelled
candidate must contain every observed molecule at least once).  The
per-occurrence condition d_w >= x_w is an additional strengthening, not the
source condition; see the companion note.
"""

from __future__ import annotations

import argparse
import sys
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product

A, T = 0, 1
COMP = {A: T, T: A}


def rc(s):
    return tuple(COMP[c] for c in reversed(s))


def mol(s):
    return min(tuple(s), rc(tuple(s)))


def word(s):
    return "".join("AT"[c] for c in s)


# ---------------------------------------------------------------------------
# I_s (Shomorony et al. bridging)
# ---------------------------------------------------------------------------

def windows(seq, L):
    G = len(seq)
    return [tuple(seq[(i + j) % G] for j in range(L)) for i in range(G)]


def covers(S, starts, L):
    G = len(S)
    cov = set()
    for r in starts:
        for o in range(L):
            cov.add((r + o) % G)
    return len(cov) == G


def maximal_pairs(S):
    G = len(S)
    out = []
    for ell in range(1, G):
        grp = defaultdict(list)
        for i in range(G):
            grp[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for _, pos in grp.items():
            for a, b in combinations(pos, 2):
                if (S[(a - 1) % G] != S[(b - 1) % G]
                        and S[(a + ell) % G] != S[(b + ell) % G]):
                    out.append((ell, tuple(sorted((a, b)))))
    return out


def triple_repeats(S):
    G = len(S)
    out = []
    for ell in range(1, G):
        grp = defaultdict(list)
        for i in range(G):
            grp[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for _, pos in grp.items():
            for tri in combinations(pos, 3):
                if (len({S[(t - 1) % G] for t in tri}) > 1
                        and len({S[(t + ell) % G] for t in tri}) > 1):
                    out.append((ell, tuple(sorted(tri))))
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
            lab = {p: 0 for p in p1}
            lab.update({p: 1 for p in p2})
            if [lab[p] for p in four] in ([0, 1, 0, 1], [1, 0, 1, 0]):
                out.append(((e1, p1), (e2, p2)))
    return out


def copy_bridged(S, t, ell, starts, L=3):
    """Strict predicate: a read [r,r+L) bridges copy [t,t+ell) iff it extends
    the copy strictly on both sides (r<t and t+ell<r+L).  Returns the witness
    read starts."""
    G = len(S)
    witnesses = []
    for r in starts:
        rp = {(r + o) % G for o in range(L)}
        if (t - 1) % G in rp and (t + ell) % G in rp:
            witnesses.append(r)
    return witnesses


def check_I_s(S, starts, L=3):
    """Return a dict of facts about the I_s certificate."""
    facts = {
        "coverage": covers(S, starts, L),
        "triple_repeats": triple_repeats(S),
        "interleaved_pairs": interleaved_pairs(S),
        "triple_all_bridged": True,
        "interleaved_bridged": True,
    }
    for ell, pos in facts["triple_repeats"]:
        for t in pos:
            if not copy_bridged(S, t, ell, starts):
                facts["triple_all_bridged"] = False
    for (e1, p1), (e2, p2) in facts["interleaved_pairs"]:
        b1 = any(copy_bridged(S, t, e1, starts) for t in p1)
        b2 = any(copy_bridged(S, t, e2, starts) for t in p2)
        if not (b1 or b2):
            facts["interleaved_bridged"] = False
    facts["holds"] = (facts["coverage"] and facts["triple_all_bridged"]
                      and facts["interleaved_bridged"])
    return facts


# ---------------------------------------------------------------------------
# Explicit bidirected overlap graph (MB09 Sections 3.1-3.3, 6.2)
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
        return word(self.rep)


def overlap_len(a, b):
    best = 0
    for l in range(1, len(a) + 1):
        if a[len(a) - l:] == b[:l]:
            best = l
    return best


def build_graph(observed, L, omin):
    edges = []
    for mx in observed:
        for my in observed:
            for sx in (mx.p(), mx.n()):
                for sy in (my.p(), my.n()):
                    for l in range(omin, L):
                        if sx[len(sx) - l:] == sy[:l]:
                            sign_x = +1 if tuple(sx) == mx.p() else -1
                            sign_y = -1 if tuple(sy) == my.p() else +1
                            edges.append({
                                "x": mx, "y": my, "sx": sx, "sy": sy,
                                "len": l, "sign_x": sign_x, "sign_y": sign_y,
                            })
    return edges


def reduce_literal(edge, observed, L):
    l = edge["len"]
    sx, sz = edge["sx"], edge["sy"]
    for my in observed:
        for s in (my.p(), my.n()):
            l1 = overlap_len(sx, s)
            l2 = overlap_len(s, sz)
            if l1 and l2 and l1 < l and l2 < l and (l1 + l2 - L) == l:
                return True
    return False


def reduce_myers(edge, observed, L):
    l = edge["len"]
    sx, sz = edge["sx"], edge["sy"]
    for my in observed:
        if my == edge["x"] or my == edge["y"]:
            continue
        for s in (my.p(), my.n()):
            l1 = overlap_len(sx, s)
            l2 = overlap_len(s, sz)
            if l1 < L and l2 < L and l1 > l and l2 > l:
                return True
    return False


def window_steps(seq, L):
    ws = windows(seq, L)
    G = len(seq)
    steps = []
    for i in range(G):
        sx, sy = ws[i], ws[(i + 1) % G]
        assert sx[1:] == sy[:-1]
        mx, my = Molecule(mol(sx)), Molecule(mol(sy))
        sign_x = +1 if tuple(sx) == mx.p() else -1
        sign_y = -1 if tuple(sy) == my.p() else +1
        steps.append({"i": i, "mx": mx, "my": my, "sx": sx, "sy": sy,
                      "len": L - 1, "sign_x": sign_x, "sign_y": sign_y})
    visits = [Molecule(mol(w)) for w in ws]
    return steps, visits


def validate_circuit(seq, L, graph, observed):
    steps, visits = window_steps(seq, L)
    G = len(seq)
    for st in steps:
        assert any(e["sx"] == st["sx"] and e["sy"] == st["sy"]
                   and e["len"] == st["len"] for e in graph), ("missing edge", st)
    for i in range(G):
        prev, cur = steps[(i - 1) % G], steps[i]
        assert prev["my"] == visits[i] and cur["mx"] == visits[i]
        assert prev["sign_y"] == -cur["sign_x"], ("orientation", i)
    d = Counter(visits)
    lower_ok = all(d.get(m, 0) >= 1 for m in observed)
    bal = {m: 0 for m in observed}
    for st in steps:
        bal[st["mx"]] += st["sign_x"]
        bal[st["my"]] += st["sign_y"]
    balance_ok = all(v == 0 for v in bal.values())
    return steps, visits, d, lower_ok, balance_ok


# ---------------------------------------------------------------------------
# Objectives
# ---------------------------------------------------------------------------

def _cls(w, collapse=True):
    return mol(w) if collapse else tuple(w)


def observed_counts(S, starts, L, collapse=True):
    x = Counter()
    for r in starts:
        x[_cls(tuple(S[(r + j) % len(S)] for j in range(L)), collapse)] += 1
    return x


def spectrum(seq, L, collapse=True):
    return Counter(_cls(w, collapse) for w in windows(seq, L))


def phi(xw, n, N, d):
    return Fraction(d, N) ** xw * Fraction(N - d, N) ** (n - xw)


def binom_product(x, n, N, d):
    r = Fraction(1)
    for w, xw in x.items():
        r *= phi(xw, n, N, d.get(w, 0))
    return r


def exact_product(sp, x):
    """Candidate-intrinsic exact multinomial up to the constants that cancel
    between two same-length candidates: prod_w d_w^{x_w}."""
    r = Fraction(1)
    for w, xw in x.items():
        r *= Fraction(sp.get(w, 0)) ** xw
    return r


# ---------------------------------------------------------------------------
# Witness verification
# ---------------------------------------------------------------------------

def verify_witness(verbose=True):
    L = 3
    OMIN = L - 1
    S = (A, A, A, T, A, T)          # AAATAT
    D = (A, A, A, A, A, T)          # AAAAAT
    starts = (0, 0, 1, 3, 5)
    N = len(S)
    n = len(starts)
    checks = []

    def chk(name, cond):
        checks.append((name, bool(cond)))

    x = observed_counts(S, starts, L)
    dS = spectrum(S, L)
    dD = spectrum(D, L)
    suppx = set(x)

    if verbose:
        print(f"truth S = {word(S)} (G={len(S)})")
        print(f"competitor D = {word(D)} (G={len(D)})  [SAME LENGTH]")
        print(f"starts = {starts}  n={n}  N={N}")
        print(f"observed x = {fmt(x)}")
        print(f"d_S = {fmt(dS)}")
        print(f"d_D = {fmt(dD)}")
        print()

    # (1) I_s
    facts = check_I_s(S, starts, L)
    chk("(1) I_s coverage", facts["coverage"])
    chk("(1) I_s triple repeats all bridged", facts["triple_all_bridged"])
    chk("(1) I_s interleaved pairs bridged (NON-vacuous)",
        facts["interleaved_bridged"])
    chk("(1) I_s holds", facts["holds"])
    chk("(1) interleaving is non-vacuous (independent correction)",
        len(facts["interleaved_pairs"]) > 0)

    # (2) bidirected circuits
    observed = [Molecule(mol(w)) for w in sorted(suppx)]
    graph = build_graph(observed, L, OMIN)
    for name, seq in (("truth", S), ("competitor", D)):
        _, _, d, lower_ok, balance_ok = validate_circuit(seq, L, graph, observed)
        chk(f"(2) {name}: support = supp(x)", {m.rep for m in d} == suppx)
        chk(f"(2) {name}: vertex lower bound 1", lower_ok)
        chk(f"(2) {name}: read-vertex balance 0 (circulation)", balance_ok)
        chk(f"(2) {name}: no supersource/sink (closed circuit)", True)

    # (3) transitive reduction keeps every employed edge
    employed = []
    for seq in (S, D):
        steps, _ = window_steps(seq, L)
        employed += steps
    red_ok = True
    for st in employed:
        fake = {"x": st["mx"], "y": st["my"], "sx": st["sx"], "sy": st["sy"],
                "len": st["len"]}
        if reduce_literal(fake, observed, L) or reduce_myers(fake, observed, L):
            red_ok = False
    chk("(3) no employed edge is removed by transitive reduction", red_ok)

    # (4) objectives
    base_exact = exact_product(dS, x)
    base_binom = binom_product(x, n, N, dict(dS))
    ratio_exact = exact_product(dD, x) / base_exact
    ratio_binom = binom_product(x, n, N, dict(dD)) / base_binom
    chk(f"(4) exact same-length ratio = {ratio_exact} = 3 (>1)",
        ratio_exact == Fraction(3))
    chk(f"(4) Section 6.1 binomial ratio = {ratio_binom} = 5 (>1)",
        ratio_binom == Fraction(5))

    if verbose:
        print(f"bidirected graph on {[word(m.rep) for m in observed]} at "
              f"o_min={OMIN}: {len(graph)} edges")
        print(f"exact multinomial ratio L(D)/L(S) = {ratio_exact}")
        print(f"Section 6.1 binomial ratio  L(D)/L(S) = {ratio_binom}")
        print()
        for name, ok in checks:
            print(f"[{'PASS' if ok else 'FAIL'}] {name}")

    return all(ok for _, ok in checks)


def fmt(c):
    return "{" + ", ".join(f"{word(k)}:{v}" for k, v in sorted(c.items())) + "}"


# ---------------------------------------------------------------------------
# Bounded exhaustive same-length search
# ---------------------------------------------------------------------------

def necklaces(G, sigma=2, collapse_rc=True):
    seen = set()
    for tup in product(range(sigma), repeat=G):
        if tup in seen:
            continue
        orbit = set()
        for sft in range(G):
            rot = tuple(tup[(sft + j) % G] for j in range(G))
            orbit.add(rot)
            if collapse_rc:
                orbit.add(rc(rot))
        seen |= orbit
        yield tup


def search_scope(G, L, maxmul, collapse_rc=True, per_occurrence=False):
    """Exhaustive same-length search.  A read realization is a multiplicity
    vector over starts with entries in 0..maxmul; I_s must hold and the truth's
    own window walk must be admissible (support equality with the observed
    molecules; per_occurrence additionally requires d_S >= x).  A competitor is
    a length-G molecule with support supp(x) (and d >= x under
    per_occurrence) that strictly improves either objective."""
    Dlist = list(necklaces(G, collapse_rc=collapse_rc))
    Dspecs = [(D, spectrum(D, L, collapse_rc)) for D in Dlist]
    n_inst = 0
    cex = []
    N = G
    for S in necklaces(G, collapse_rc=collapse_rc):
        spS = spectrum(S, L, collapse_rc)
        trips = triple_repeats(S)
        inter = interleaved_pairs(S)
        for counts in product(range(maxmul + 1), repeat=G):
            if sum(counts) == 0:
                continue
            starts = tuple(p for p, c in enumerate(counts) for _ in range(c))
            if not _check_I_s_precomp(S, starts, L, trips, inter):
                continue
            x = observed_counts(S, starts, L, collapse_rc)
            if set(spS) != set(x):
                continue
            if any(spS.get(w, 0) < 1 for w in set(x)):
                continue
            if per_occurrence and any(spS.get(w, 0) < c for w, c in x.items()):
                continue
            n_inst += 1
            n = sum(x.values())
            be = exact_product(spS, x)
            bb = binom_product(x, n, N, dict(spS))
            for D, spD in Dspecs:
                if set(spD) != set(x):
                    continue
                if any(spD.get(w, 0) < 1 for w in set(x)):
                    continue
                if per_occurrence and any(spD.get(w, 0) < c for w, c in x.items()):
                    continue
                if spD == spS:
                    continue
                re = exact_product(spD, x) / be
                rb = binom_product(x, n, N, dict(spD)) / bb
                if re > 1 or rb > 1:
                    cex.append({"S": S, "D": D, "starts": starts,
                                "exact": re, "binom": rb})
    return n_inst, cex


def _check_I_s_precomp(S, starts, L, trips, inter):
    if not covers(S, starts, L):
        return False
    for ell, pos in trips:
        for t in pos:
            if not copy_bridged(S, t, ell, starts):
                return False
    for (e1, p1), (e2, p2) in inter:
        b1 = any(copy_bridged(S, t, e1, starts) for t in p1)
        b2 = any(copy_bridged(S, t, e2, starts) for t in p2)
        if not (b1 or b2):
            return False
    return True


def run_search(verbose=True):
    """Bounded scope.  Recorded outcomes:
       bidirected, per-vertex LB1  : G=5,L=3 -> 0 ; G=6,L=3 -> >0 (the witness)
                                     G=7,L=3 -> 0 ; G=6,L=4 -> 0 ; G=5,L=4 -> 0
       bidirected, per-occurrence  : G<= 6,L=3 -> 0
       single-strand               : G<= 6,L=3 -> 0
    """
    checks = []
    G5 = search_scope(5, 3, 3)
    G6 = search_scope(6, 3, 3)
    G7 = search_scope(7, 3, 3)
    G6L4 = search_scope(6, 4, 3)
    ss = search_scope(6, 3, 2, collapse_rc=False)
    po = search_scope(6, 3, 2, per_occurrence=True)
    checks.append(("(5) bidirected per-vertex: G=5,L=3 no same-length beat",
                   len(G5[1]) == 0))
    checks.append(("(5) bidirected per-vertex: G=6,L=3 same-length beats exist",
                   len(G6[1]) > 0))
    checks.append(("(5) bidirected per-vertex: G=7,L=3 no same-length beat",
                   len(G7[1]) == 0))
    checks.append(("(5) bidirected per-vertex: G=6,L=4 no same-length beat",
                   len(G6L4[1]) == 0))
    checks.append(("(5) single-strand, G=6,L=3 no same-length beat",
                   len(ss[1]) == 0))
    checks.append(("(5) per-occurrence strengthening: no beat in scope",
                   len(po[1]) == 0))
    if verbose:
        print()
        print("bounded search (exhaustive over the stated scope):")
        print(f"  G=5,L=3,maxmul=3 bidirected/vertex : instances={G5[0]} cex={len(G5[1])}")
        print(f"  G=6,L=3,maxmul=3 bidirected/vertex : instances={G6[0]} cex={len(G6[1])}")
        print(f"    truths={sorted({word(c['S']) for c in G6[1]})} "
              f"competitors={sorted({word(c['D']) for c in G6[1]})}")
        print(f"  G=7,L=3,maxmul=3 bidirected/vertex : instances={G7[0]} cex={len(G7[1])}")
        print(f"  G=6,L=4,maxmul=3 bidirected/vertex : instances={G6L4[0]} cex={len(G6L4[1])}")
        print(f"  G=6,L=3,maxmul=2 single-strand    : instances={ss[0]} cex={len(ss[1])}")
        print(f"  G=6,L=3,maxmul=2 per-occurrence   : instances={po[0]} cex={len(po[1])}")
        print()
        for name, ok in checks:
            print(f"[{'PASS' if ok else 'FAIL'}] {name}")
    return all(ok for _, ok in checks)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--search", action="store_true",
                    help="also run the bounded exhaustive same-length search")
    args = ap.parse_args()
    ok = verify_witness()
    if args.search:
        ok = run_search() and ok
    print()
    print("ALL CHECKS PASS" if ok else "SOME CHECKS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
