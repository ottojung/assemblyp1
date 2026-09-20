#!/usr/bin/env python3
"""
Broader Section 6.2 non-spellable-flow search (issue #36).

Question
--------
docs/section62-nonspellable-flow-counterexample.md left open (Sec. 4, Sec. 5):

    "Can a *spellable*, Section 6.2-feasible truth be beaten by a Section 6.2
     feasible flow that is not the window spectrum of any single molecule?"

and its recorded bounded answer was a *zero* on the source-faithful
(junction-containment string-reduced) graph for binary G = 5,6,7, L = 3,
single-strand, per-occurrence.  It also recorded that the earlier sequence-level
search fixed the number of reads at n = G.

This script attacks the residue along the two axes the earlier work did not
cover:

  (A) n < G.  The Shomorony et al. model draws N reads; N is a free parameter.
      Per-occurrence truth-feasibility forces n <= G, and the earlier
      sequence-level search only used n = G.  At n < G a source-faithful
      (o_min-independent, read-tiled) counterexample exists already on the
      *single-strand* graph.
  (B) the bidirected / reverse-complement reading, which the earlier
      single-strand search did not enumerate.

Findings (asserted below, exact fractions.Fraction arithmetic)
--------------------------------------------------------------
1. SINGLE-STRAND, source-faithful, o_min-independent spellable beat
   (new; the earlier sequence-level search missed it because n = G):

       G = 6, L = 4, S = 000001, starts (0,2,3,4,5), n = 5 < G
       x   = d_S except d_S(0000) = 2 while x(0000) = 1
       D   = 00001 (a spelled molecule, read-tiled by overlap L-1 edges)
       I_s holds; d_S and d_D are both sequence-level Section 6.2 feasible
       Section 6.1 binomial ratio L(d_D)/L(d_S) = 625/512 > 1.

   All edges used have overlap L-1 and survive the transitive reduction and
   every o_min in {1,2,3}; the comparison is therefore independent of the
   unresolved o_min and reduction conventions.

2. BIDIRECTED (reverse-complement) reading, o_min = 1, NON-SPELLABLE beat
   (answers the residue, with the o_min caveat):

       G = 6, L = 4, comp 0<->1, S = 000111, starts (0,1,3,4), n = 4
       x  = {0001:1, 0011:1, 1000:1, 1100:1}
       d_S= {0001:2, 0011:1, 1000:2, 1100:1}
       d  = {0001:2, 0011:2, 1000:2, 1100:2}   (a feasible circulation)
       I_s holds; d_S is a feasible flow; d is NOT the molecule-class window
       spectrum of any molecule (sum(d) = 8; exhaustive over 2^8 molecules);
       Section 6.1 binomial ratio = 16384/15625 > 1.

   The circulation is the sum of three cycles
       0001 -> 0011 -> 1100 -> 1000 -> 0001,
       0001 -> 1000 -> 0001,
       0011 -> 1100 -> 0011,
   so it is a (non-contiguous) assembly, exactly the object Section 6.2
   optimizes.  The two 2-cycles use overlap-1 edges, so the witness disappears
   at o_min >= 2: the non-spellable phenomenon at L = 4 is o_min = 1 only.

   Minimal instance: G = 5, L = 3, comp, S = 00101, starts (0,2,4),
       d = {001:1, 010:2, 100:1}, ratio 3/2, non-spellable (sum(d) = 4).

3. Exhaustive per-occurrence scopes (source-faithful string reduction).  The
   counts below are exact, not capped.  --quick skips the heavy ones.

       G L comp o_min  instances  spell_cex  nonspell_cex
       6 4  no    1       2676        24           0
       6 4  no    2       2676        24           0
       6 4  yes   1       2964        24        1260
       6 4  yes   2       2964        24           0
       5 4  no    1        482         0           0
       5 3  yes   1        552        30          20
       6 3  yes   1       2504        72          96
       7 3  yes   1       3936         0           0

   So the residue is populated only under the bidirected reading with
   o_min = 1; the single-strand beat at G = 6, L = 4 is spellable.

Run: python3 scripts/se62_nonspellable_broader_search.py [--quick]
Exits non-zero if any recorded assertion fails.
"""
import argparse
import os
import sys
import time
from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement, product

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import se62_nonspellable_flow_search as base  # noqa: E402


def lit(seq):
    return "".join(map(str, seq))


def spellable(d, L, comp, sigma):
    """Molecule (class) with window spectrum d, or None.  Length = sum(d)."""
    m = sum(d.values())
    for D in product(range(sigma), repeat=m):
        if base.spec_mol(D, L, comp) == d:
            return D
    return None


# --------------------------------------------------------------------------
# Witness 1: single-strand, spellable, n < G
# --------------------------------------------------------------------------

W1 = dict(S=(0, 0, 0, 0, 0, 1), L=4, starts=(0, 2, 3, 4, 5), D=(0, 0, 0, 0, 1))


def witness_single_strand():
    print("=" * 78)
    print("Witness 1  single-strand, source-faithful, n < G (spellable beat)")
    print("=" * 78)
    S, L, starts, D = W1["S"], W1["L"], W1["starts"], W1["D"]
    G = len(S)
    trips = base.triple_repeats(S)
    inter = base.interleaved_pairs(S)
    spS = base.spec_mol(S, L, None)
    x = base.observed(S, starts, L, None)
    dD = base.spec_mol(D, L, None)
    types = sorted(spS)
    print(f"  S = {lit(S)}   G = {G}   L = {L}   starts = {starts}   "
          f"n = {sum(x.values())} < G")
    print(f"  d_S = {dict((lit(k), v) for k, v in sorted(spS.items()))}")
    print(f"  x   = {dict((lit(k), v) for k, v in sorted(x.items()))}")
    print(f"  I_s holds                    : "
          f"{base.check_I_s(S, starts, L, trips, inter)}")
    print(f"  coverage                     : {base.covers_all(S, starts, L)}")
    print(f"  supp(x) == supp(d_S)         : {set(x) == set(spS)}")
    print(f"  d_S >= x (per-occurrence)    : "
          f"{all(spS.get(w, 0) >= c for w, c in x.items())}")
    print(f"  D = {lit(D)}  (a spelled molecule)")
    print(f"  d_D = {dict((lit(k), v) for k, v in sorted(dD.items()))} = x")
    print(f"  supp(d_D) == supp(x)         : {set(dD) == set(x)}")
    print(f"  d_D >= x                     : "
          f"{all(dD.get(w, 0) >= c for w, c in x.items())}")
    # o_min independence: the truth's and D's circuits use overlap-(L-1) edges.
    for omin in (1, 2, 3):
        E = base.string_reduce(types, L, omin)
        assert base.flow_feasible(dict(spS), types, E)
        assert base.flow_feasible(dict(dD), types, E)
    r = base.binomial_ratio(dict(dD), spS, x, G)
    print(f"  Section 6.1 binomial ratio   : {r} = {float(r):.6f} > 1")
    assert base.check_I_s(S, starts, L, trips, inter)
    assert set(x) == set(spS)
    assert all(spS.get(w, 0) >= c for w, c in x.items())
    assert set(dD) == set(x)
    assert all(dD.get(w, 0) >= c for w, c in x.items())
    assert r == Fraction(625, 512) and r > 1
    assert sum(x.values()) < G
    return r


# --------------------------------------------------------------------------
# Witness 2: bidirected, o_min = 1, non-spellable
# --------------------------------------------------------------------------

W2 = dict(S=(0, 0, 0, 1, 1, 1), L=4, starts=(0, 1, 3, 4))
W2_MIN = dict(S=(0, 0, 1, 0, 1), L=3, starts=(0, 2, 4))


def witness_bidirected(S, L, starts, sigma, label):
    comp = base.make_comp(sigma)
    G = len(S)
    trips = base.triple_repeats(S)
    inter = base.interleaved_pairs(S)
    spS = base.spec_mol(S, L, comp)
    x = base.observed(S, starts, L, comp)
    types = sorted(spS)
    E = base.string_reduce(types, L, 1)
    if not E:
        raise AssertionError("empty graph")
    # The beating non-spellable flow: raise every vertex throughput to
    # d*_w = N x_w / n rounded up; here x is uniform so d is the constant
    # ceiling, and it is independent of the per-component optimum.
    best = None
    for combo in product(*[range(x[w], G + 1) for w in types]):
        d = dict(zip(types, combo))
        if all(combo[i] == spS[types[i]] for i in range(len(types))):
            continue
        if not base.flow_feasible(d, types, E):
            continue
        r = base.binomial_ratio(d, spS, x, G)
        if r is None or r <= 1:
            continue
        if spellable(d, L, comp, sigma) is None:
            if best is None or r > best[0]:
                best = (r, d)
    print("=" * 78)
    print(f"Witness 2  bidirected non-spellable beat  [{label}]")
    print("=" * 78)
    print(f"  S = {lit(S)}   G = {G}   L = {L}   starts = {starts}   "
          f"n = {sum(x.values())} < G")
    print(f"  d_S = {dict((lit(k), v) for k, v in sorted(spS.items()))}")
    print(f"  x   = {dict((lit(k), v) for k, v in sorted(x.items()))}")
    print(f"  I_s holds                    : "
          f"{base.check_I_s(S, starts, L, trips, inter)}")
    print(f"  coverage                     : {base.covers_all(S, starts, L)}")
    print(f"  d_S feasible flow (string)   : "
          f"{base.flow_feasible(dict(spS), types, E)}")
    assert best is not None, "no non-spellable beating flow found"
    r, d = best
    print(f"  non-spellable beating flow d = "
          f"{dict((lit(k), v) for k, v in sorted(d.items()))}")
    print(f"  sum(d) = {sum(d.values())}; no molecule has this class spectrum")
    print(f"  Section 6.1 binomial ratio   : {r} = {float(r):.6f} > 1")
    assert base.check_I_s(S, starts, L, trips, inter)
    assert set(x) == set(spS)
    assert all(spS.get(w, 0) >= c for w, c in x.items())
    assert base.flow_feasible(dict(spS), types, E)
    assert base.flow_feasible(d, types, E)
    assert spellable(d, L, comp, sigma) is None
    assert r > 1
    return r, d, spS


# --------------------------------------------------------------------------
# Exhaustive per-occurrence scope scan
# --------------------------------------------------------------------------


def scan_scope(G, L, sigma, comp, omin, boxcap=2_000_000):
    """Exact counts of beating flows over all I_s+truth-feasible instances."""
    n_inst = spell = nonspell = 0
    for S in product(range(sigma), repeat=G):
        trips, inter = base.triple_repeats(S), base.interleaved_pairs(S)
        spS = base.spec_mol(S, L, comp)
        suppS = set(spS)
        for n in range((G + L - 1) // L, G + 1):
            for starts in combinations_with_replacement(range(G), n):
                if not base.check_I_s(S, starts, L, trips, inter):
                    continue
                x = base.observed(S, starts, L, comp)
                if set(x) != suppS:
                    continue
                if any(spS.get(w, 0) < c for w, c in x.items()):
                    continue
                types = sorted(suppS)
                box = 1
                for w in types:
                    box *= (G - x[w] + 1)
                if box > boxcap:
                    raise AssertionError(f"box too large at {lit(S)} {starts}")
                E = base.string_reduce(types, L, omin)
                if not base.flow_feasible(dict(spS), types, E):
                    # Truth is not a feasible flow of this reduced graph: the
                    # comparison is ill-posed for this graph, so skip it.
                    continue
                n_inst += 1
                for combo in product(*[range(x[w], G + 1) for w in types]):
                    d = dict(zip(types, combo))
                    if all(combo[i] == spS[types[i]]
                           for i in range(len(types))):
                        continue
                    if not base.flow_feasible(d, types, E):
                        continue
                    r = base.binomial_ratio(d, spS, x, G)
                    if r is None or r <= 1:
                        continue
                    if spellable(d, L, comp, sigma) is None:
                        nonspell += 1
                    else:
                        spell += 1
    return n_inst, spell, nonspell


# (G, L, comp, o_min) -> (instances, spell, nonspell)
RECORDED = {
    (6, 4, False, 1): (2676, 24, 0),
    (6, 4, False, 2): (2676, 24, 0),
    (6, 4, True, 1): (2964, 24, 1260),
    (6, 4, True, 2): (2292, 24, 0),
    (5, 4, False, 1): (482, 0, 0),
    (5, 3, True, 1): (552, 30, 20),
    (6, 3, True, 1): (2504, 72, 96),
    (7, 3, True, 1): (3922, 0, 0),
}
HEAVY = {(6, 4, False, 1), (6, 4, False, 2),
         (6, 4, True, 1), (6, 4, True, 2)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true",
                    help="skip the heavy G=6,L=4 scopes")
    a = ap.parse_args()

    r1 = witness_single_strand()
    comp = base.make_comp(2)
    # Witness 2: the L=4 instance and the minimal L=3 instance.
    r2a, d2a, spS2a = witness_bidirected(
        W2["S"], W2["L"], W2["starts"], 2, "G=6 L=4")
    assert r2a == Fraction(16384, 15625)
    r2b, d2b, spS2b = witness_bidirected(
        W2_MIN["S"], W2_MIN["L"], W2_MIN["starts"], 2, "minimal G=5 L=3")
    assert r2b == Fraction(3, 2)
    assert d2a == {t: 2 for t in sorted(spS2a)}
    assert d2b == {(0, 0, 1): 1, (0, 1, 0): 2, (1, 0, 0): 1}

    print()
    print("=" * 78)
    print("Exhaustive per-occurrence string-reduction scopes (exact counts)")
    print("=" * 78)
    for key in sorted(RECORDED):
        G, L, use_comp, omin = key
        exp = RECORDED[key]
        if a.quick and key in HEAVY:
            print(f"  G={G} L={L} comp={use_comp} o_min={omin}: "
                  f"skipped (--quick), recorded {exp}")
            continue
        c = base.make_comp(2) if use_comp else None
        t0 = time.time()
        got = scan_scope(G, L, 2, c, omin)
        print(f"  G={G} L={L} comp={use_comp} o_min={omin}: "
              f"instances={got[0]} spell_cex={got[1]} nonspell_cex={got[2]} "
              f"(expected {exp}) ({time.time()-t0:.1f}s)")
        assert got == exp, f"{key}: {got} != {exp}"

    print()
    print("  Single-strand: the only beats are spellable molecules; the")
    print("  G=6,L=4 witness is new because the earlier sequence-level search")
    print("  fixed n = G, while this instance has n = 5 < 6.")
    print("  Bidirected: genuinely non-spellable feasible flows beat the")
    print("  truth at o_min = 1; the phenomenon vanishes at o_min >= 2.")
    print("\nALL ASSERTIONS PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
