#!/usr/bin/env python3
"""
Fixed-length likelihood-improving competitors under the Medvedev-Brudno
Section 6.2 bidirected-flow feasibility constraints.

Question (issue #36 follow-up)
------------------------------
Does there exist a *fixed-length* candidate genome D (|D| = |S| = G) that
(a) strictly improves the maximum-likelihood objective over the truth S and
(b) is admissible under the Medvedev-Brudno Section 6.2 read-overlap
    bidirected-flow constraints, in an instance where the truth S is itself
    admissible and the bridging hypotheses I_s hold?

Model (source-faithful reading)
-------------------------------
Section 6.2 builds a transitively reduced *bidirected* overlap graph from
"the set of reads, which are DNA molecules" (PMC3154397 Sec. 6.2).  Each read
vertex has lower bound 1; the output is a flow, i.e. a (possibly
non-contiguous) assembly, and a single circular molecule D corresponds to a
circuit/Walk that spells D.  By Observation 7 of the source, a molecule D is
spelled by a walk of read vertices iff

    (*) every length-L submolecule of D is an observed read molecule, and

    (**) every observed read molecule is a submolecule of D,

i.e. support equality of the L-window spectrum with the observed read set
(molecule classes, reverse complements identified).  The lower bound is read
either per *occurrence* (duplicate sampled molecules are distinct vertices,
d_D(w) >= x_w) or per *type* (the source's "set of reads" deduplicates,
d_D(w) >= 1 for every observed molecule w).  Both readings are tested here;
the two are exactly the ambiguity flagged in
docs/section-6-2-feasible-set-membership.md Sec. 6.

Objectives tested
-----------------
* exact fixed-length multinomial, common length G:
      L_exact(D|x) / L_exact(S|x) = prod_w (d_D(w)/d_S(w))^{x_w}.
* literal Medvedev-Brudno Sec. 6.1 separable binomial with the external
  denominator N0 = G (true genome length) and n = sum(x) reads:
      ratio = prod_w [ (d_D/N0)^{x_w}(1-d_D/N0)^{n-x_w} ]
                   / [ (d_S/N0)^{x_w}(1-d_S/N0)^{n-x_w} ].

Result
------
* Under the bidirected (reverse-complement) reading together with the per-type
  lower bound, there is a counterexample at G = 6, L = 3:
      truth S = AA AT AT   (symbols 0=A, 1=T)
      competitor D = AA AA AT
      starts (0,0,1,3,5), observed molecules {AAA:2, AAT:1, ATA:1, TAA:1}
  I_s holds, S and D are both Section 6.2 sequence-level feasible, and D
  strictly improves both objectives (exact ratio 3, binomial ratio 5).
* Under the per-occurrence lower bound there is no counterexample in the
  recorded scope, and under the single-strand reading there is none either.
  Both scopes are bounded and exhaustive, hence computational evidence and not
  a proof of absence.

Run:  python3 scripts/se62_fixed_length_bidirected_search.py [--quick]
Exact fractions.Fraction arithmetic throughout.  Exits non-zero if any
recorded assertion fails.
"""
import argparse
import sys
import time
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product

# --------------------------------------------------------------------------
# Self-contained Section 6.2 / I_s machinery
# --------------------------------------------------------------------------


def make_comp(sigma):
    """Reverse-complement involution: 0<->1, 2<->3, ... (last symbol fixed if odd)."""
    c = {}
    for i in range(0, sigma - 1, 2):
        c[i] = i + 1
        c[i + 1] = i
    if sigma % 2:
        c[sigma - 1] = sigma - 1
    return c


def mol(seq, comp):
    """Molecule class of a read: min(word, revcomp(word)) when comp given."""
    if comp is None:
        return tuple(seq)
    rc = tuple(comp[c] for c in reversed(seq))
    return min(tuple(seq), rc)


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


def covers_all(S, starts, L):
    G = len(S)
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
        for kmer, pos in groups.items():
            if len(pos) < 2:
                continue
            for pair in combinations(pos, 2):
                t1, t2 = pair
                if (S[(t1 - 1) % G] != S[(t2 - 1) % G]
                        and S[(t1 + ell) % G] != S[(t2 + ell) % G]
                        and pair not in seen):
                    seen.add(pair)
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
                    out.append(((e1, tuple(sorted(p1))), (e2, tuple(sorted(p2)))))
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
# Independent walk / feasibility check
# --------------------------------------------------------------------------
def window_walk(seq, L):
    """Ordered cyclic length-L windows of seq; consecutive ones overlap in L-1."""
    G = len(seq)
    return [tuple(seq[(i + j) % G] for j in range(L)) for i in range(G)]


def walk_is_bidirected_circuit(seq, L, obs, comp, per_occ):
    """Directly verify seq is a Section 6.2 circuit (spelled molecule).

    Checks (i) each consecutive window pair overlaps in exactly L-1 symbols in
    the same orientation (so an overlap edge with o_min <= L-1 exists), (ii)
    every window is an observed read molecule class, and (iii) every observed
    read is visited (per-type) or used with multiplicity (per-occurrence).
    """
    for a, b in zip(window_walk(seq, L)[:-1], window_walk(seq, L)[1:]):
        if a[1:] != b[:-1]:
            return False
    classes = Counter(mol(w, comp) for w in window_walk(seq, L))
    if any(w not in obs for w in classes):
        return False
    if per_occ:
        return all(classes.get(w, 0) >= c for w, c in obs.items())
    return all(classes.get(w, 0) >= 1 for w in obs)


# --------------------------------------------------------------------------
# Objectives
# --------------------------------------------------------------------------
def exact_ratio(spD, spS, x):
    r = Fraction(1)
    for w, xw in x.items():
        r *= Fraction(spD.get(w, 0), spS[w]) ** xw
    return r


def binomial_ratio(spD, spS, x, N0):
    n = sum(x.values())
    r = Fraction(1)
    for w, xw in x.items():
        dd, ds = spD.get(w, 0), spS[w]
        if dd > N0 or ds > N0:
            return None
        num = Fraction(dd, N0) ** xw * Fraction(N0 - dd, N0) ** (n - xw)
        den = Fraction(ds, N0) ** xw * Fraction(N0 - ds, N0) ** (n - xw)
        r *= num / den
    return r


# --------------------------------------------------------------------------
# Bounded exhaustive search over fixed-length candidates |D| = G
# --------------------------------------------------------------------------
def search(G, L, sigma, comp, per_occ, Ns, cap=None):
    Dbest = {}
    for D in product(range(sigma), repeat=G):
        sp = spec_mol(D, L, comp)
        Dbest.setdefault(frozenset(sp), []).append((D, sp))
    out, inst = [], 0
    for S in product(range(sigma), repeat=G):
        trips = triple_repeats(S)
        inter = interleaved_pairs(S)
        spS = spec_mol(S, L, comp)
        suppS = set(spS)
        for N in Ns:
            for starts in combinations_with_replacement(range(G), N):
                if not check_I_s(S, starts, L, trips, inter):
                    continue
                x = observed(S, starts, L, comp)
                if set(x) != suppS:
                    continue
                if per_occ and any(spS.get(w, 0) < c for w, c in x.items()):
                    continue
                inst += 1
                for D, spD in Dbest.get(frozenset(x), []):
                    if per_occ and any(spD.get(w, 0) < c for w, c in x.items()):
                        continue
                    if not per_occ and any(spD.get(w, 0) < 1 for w in set(x)):
                        continue
                    if spD == spS:
                        continue
                    r = exact_ratio(spD, spS, x)
                    if r > 1:
                        out.append((S, starts, N, x, spS, D, spD, r,
                                    binomial_ratio(spD, spS, x, G)))
                        if cap is not None and len(out) >= cap:
                            return inst, out
    return inst, out


def ns(G, L):
    return list(range(max(1, (G + L - 1) // L), G + 3))


# Recorded exhaustive scope and observed counterexample counts.
# (G, L, sigma, reading, lower bound) -> expected number of counterexamples.
# Counts are deterministic; the search asserts equality so a regression fails
# loudly.  "occ" = per-occurrence lower bound (d_D(w) >= x_w); "type" =
# per-type lower bound (d_D(w) >= 1 for every observed molecule).
RECORDED = {
    (4, 3, 2, "ss", "occ"): 0, (4, 3, 2, "ss", "type"): 0,
    (4, 3, 2, "rc", "occ"): 0, (4, 3, 2, "rc", "type"): 0,
    (5, 3, 2, "ss", "occ"): 0, (5, 3, 2, "ss", "type"): 0,
    (5, 3, 2, "rc", "occ"): 0, (5, 3, 2, "rc", "type"): 0,
    (6, 3, 2, "ss", "occ"): 0, (6, 3, 2, "ss", "type"): 0,
    (6, 3, 2, "rc", "occ"): 0, (6, 3, 2, "rc", "type"): 4608,
    (7, 3, 2, "ss", "occ"): 0, (7, 3, 2, "ss", "type"): 0,
    (7, 3, 2, "rc", "occ"): 0, (7, 3, 2, "rc", "type"): 0,
    (5, 3, 3, "ss", "occ"): 0, (5, 3, 3, "ss", "type"): 0,
    (5, 3, 3, "rc", "occ"): 0, (5, 3, 3, "rc", "type"): 0,
    (6, 3, 3, "ss", "occ"): 0, (6, 3, 3, "ss", "type"): 0,
    (6, 3, 3, "rc", "occ"): 0, (6, 3, 3, "rc", "type"): 4608,
    (6, 4, 2, "ss", "occ"): 0, (6, 4, 2, "ss", "type"): 0,
    (6, 4, 2, "rc", "occ"): 0, (6, 4, 2, "rc", "type"): 0,
    (7, 4, 2, "ss", "occ"): 0, (7, 4, 2, "ss", "type"): 0,
    (7, 4, 2, "rc", "occ"): 0, (7, 4, 2, "rc", "type"): 0,
}


def witness_report():
    print("=" * 78)
    print("Counterexample: fixed-length competitor under bidirected Section 6.2")
    print("=" * 78)
    S = (0, 0, 0, 1, 0, 1)      # AAATAT with A=0, T=1
    D = (0, 0, 0, 0, 0, 1)      # AAAAAT
    L = 3
    starts = (0, 0, 1, 3, 5)
    comp = make_comp(2)         # A<->T
    lit = lambda s: "".join("AT"[c] for c in s)
    trips = triple_repeats(S)
    inter = interleaved_pairs(S)
    x = observed(S, starts, L, comp)
    spS = spec_mol(S, L, comp)
    spD = spec_mol(D, L, comp)
    ok_Is = check_I_s(S, starts, L, trips, inter)
    obsS = set(spS)
    obsD = set(spD)
    suppx = set(x)
    print(f"  truth S = {lit(S)}   competitor D = {lit(D)}   L = {L}")
    print(f"  starts = {starts}   observed molecule counts = "
          f"{ {lit(k): v for k, v in x.items()} }")
    print(f"  I_s holds: {ok_Is}")
    print(f"  supp(spec(S)) = supp(x): {obsS == suppx}")
    print(f"  supp(spec(D)) = supp(x): {obsD == suppx}")
    # per-type and per-occurrence feasibility, direct walk check
    truth_type = walk_is_bidirected_circuit(S, L, x, comp, per_occ=False)
    comp_type = walk_is_bidirected_circuit(D, L, x, comp, per_occ=False)
    truth_occ = walk_is_bidirected_circuit(S, L, x, comp, per_occ=True)
    comp_occ = walk_is_bidirected_circuit(D, L, x, comp, per_occ=True)
    print(f"  direct circuit check  truth (per-type): {truth_type}   "
          f"competitor (per-type): {comp_type}")
    print(f"  direct circuit check  truth (per-occ) : {truth_occ}   "
          f"competitor (per-occ) : {comp_occ}")
    print(f"  d_S = { {lit(k): v for k, v in spS.items()} }")
    print(f"  d_D = { {lit(k): v for k, v in spD.items()} }")
    er = exact_ratio(spD, spS, x)
    br = binomial_ratio(spD, spS, x, len(S))
    print(f"  exact multinomial ratio L(D)/L(S)  = {er}")
    print(f"  Section 6.1 binomial ratio         = {br}")
    print("  truth windows:", [lit(w) for w in window_walk(S, L)])
    print("  competitor windows:", [lit(w) for w in window_walk(D, L)])
    print("  (TAT is the reverse complement of ATA, so the truth has three")
    print("   ATA-class windows; the competitor concentrates the same support")
    print("   on AAA and wins.)")
    assert ok_Is, "I_s failed on the witness"
    assert obsS == suppx and obsD == suppx, "support equality failed"
    assert truth_type and comp_type, "per-type circuit check failed"
    assert comp_occ, "competitor per-occurrence circuit check failed"
    assert not truth_occ, "truth unexpectedly per-occurrence feasible"
    assert er == 3, f"exact ratio {er} != 3"
    assert br == 5, f"binomial ratio {br} != 5"
    return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true",
                    help="only G,L <= 6,3 scopes")
    a = ap.parse_args()
    witness_report()
    print()
    print("=" * 78)
    print("Bounded exhaustive search, fixed-length candidates |D| = G")
    print("=" * 78)
    scopes = [k for k in RECORDED if not a.quick or (k[0] <= 6 and k[1] <= 3)]
    total_inst = 0
    total_cex = 0
    for (G, L, sigma, reading, lb) in scopes:
        comp = None if reading == "ss" else make_comp(sigma)
        per_occ = (lb == "occ")
        t0 = time.time()
        inst, out = search(G, L, sigma, comp, per_occ, ns(G, L), cap=None)
        exp = RECORDED[(G, L, sigma, reading, lb)]
        total_inst += inst
        total_cex += len(out)
        print(f"  reading={reading:2} lb={lb:4} G={G} L={L} sigma={sigma}: "
              f"instances={inst:>7} cex={len(out):>5} (expected {exp}) "
              f"({time.time()-t0:.1f}s)")
        if out:
            truths = {"".join(map(str, c[0])) for c in out}
            ratios = [c[7] for c in out]
            binoms = [c[8] for c in out]
            print(f"      distinct truths={len(truths)}  "
                  f"exact-ratio range [{min(ratios)}, {max(ratios)}]  "
                  f"all binomial ratios > 1: {all(b > 1 for b in binoms)}")
            # Independent verification: I_s, direct bidirected circuit check for
            # truth and competitor, and a recomputation of the exact ratio.
            for (S, starts, N, x, spS, D, spD, r, br) in out:
                assert check_I_s(S, starts, L, triple_repeats(S),
                                 interleaved_pairs(S)), "I_s regression"
                assert walk_is_bidirected_circuit(S, L, x, comp, per_occ=False)
                assert walk_is_bidirected_circuit(D, L, x, comp, per_occ=False)
                assert exact_ratio(spec_mol(D, L, comp),
                                   spec_mol(S, L, comp), x) == r
            for (S, starts, N, x, spS, D, spD, r, br) in out[:2]:
                print(f"      S={''.join(map(str, S))} D={''.join(map(str, D))} "
                      f"N={N} exact={r} binom={br}")
        assert len(out) == exp, \
            f"scope {(G, L, sigma, reading, lb)}: got {len(out)} != {exp}"
    # Strong pattern asserted by the recorded table: no counterexample with the
    # per-occurrence lower bound or the single-strand reading in scope.
    assert all(v == 0 for k, v in RECORDED.items()
               if k[4] == "occ" or k[3] == "ss"), "pattern regression"
    print(f"\n  total instances searched: {total_inst}   counterexamples: {total_cex}")
    print("  Per-occurrence lower bound: zero counterexamples in scope")
    print("  Single-strand reading:      zero counterexamples in scope")
    print("  Bidirected + per-type:      counterexamples at G=6, L=3 only")
    print("\nALL ASSERTIONS PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
