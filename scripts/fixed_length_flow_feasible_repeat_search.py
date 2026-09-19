#!/usr/bin/env python3
"""
Fixed-length exact Variant E under the per-occurrence flow candidate set F*:
does Proposition D extend from repeat-free truths to truths with repeats?

MODEL
-----
Circular truth S of length G over a finite alphabet; error-free reads of common
length L; a realized sequencing is a multiplicity vector m over the G start
positions (m_s = number of reads starting at circular position s).  The observed
read-type counts are x_w = sum_{s : window(S,s,L)=w} m_s, and n = sum_w x_w.

Hypothesis I_s (Shomorony et al. 2016 Eq. (1), inherited from Bresler et al.):
  (1) coverage: the starts with m_s > 0 cover every position of S;
  (2) every maximal triple repeat of S is all-bridged;
  (3) every interleaved pair of maximal repeat pairs is bridged.
Repeat / triple-repeat / interleaving / bridging semantics follow
docs/bridging-source-semantics.md (strict two-sided extension, cyclic
interleaving, three-copy maximality).

Candidate objective (fixed-length exact Variant E):
  L(D | x) = n! / prod_w x_w! * prod_w (d_D(w) / G)^{x_w},
  d_D(w) = number of circular length-L windows of D equal to type w.
Since G is fixed, ordering is by prod_w d_D(w)^{x_w}.

Candidate universes (the feasibility ladder)
  U0 all      : every circular D with |D| = G.
  U1 support  : supp(D) subset of supp(S)          (read-supported types only).
  U2 F*       : supp(D) subset of supp(S) and d_D(w) >= x_w for every observed
                type w.  This is the per-occurrence reading of the Medvedev-Brudno
                Section 6.2 lower-bound-one per read vertex, restricted to length
                G; it is the candidate set of Proposition D in
                docs/bridging-schemas-and-flow-feasibility-gaps.md.

We also impose S in F*(R): supp(R) = supp(S) and x_w <= d_S(w) for all w.

QUESTION
--------
Proposition D proves that for repeat-free S with S in F*(R), S is an exact ML
maximizer (not unique).  Its stated open question is whether that extends to
truths with (bridged) repeats.  This script enumerates every bounded instance
whose truth has a repeated length-L window, satisfies I_s, and satisfies
S in F*(R), and checks whether any same-length F*-feasible competitor strictly
beats S.  It records the counterexample count per universe and the minimal
witnesses.

REPRODUCIBILITY
---------------
Deterministic; exact rational arithmetic (fractions.Fraction); self-contained.
Scope is a finite exhaustive enumeration, not a proof of absence.
"""

from fractions import Fraction
from itertools import combinations, product
import json
import sys
import time


# ---------------------------------------------------------------------------
# Circular genome utilities
# ---------------------------------------------------------------------------

def window(g, s, L):
    G = len(g)
    return tuple(g[(s + j) % G] for j in range(L))


def spectrum(g, L):
    G = len(g)
    return {window(g, s, L) for s in range(G)}


def occ(g, r):
    G = len(g)
    L = len(r)
    return sum(1 for s in range(G) if window(g, s, L) == r)


def gstr(g):
    """Render a genome tuple of small ints as a letter string for reporting."""
    return "".join(chr(65 + c) if isinstance(c, int) and 0 <= c < 26 else str(c)
                   for c in g)


def canon(g):
    G = len(g)
    return min(tuple(g[(i + j) % G] for j in range(G)) for i in range(G))


def rotation_reps(G, alphabet):
    seen = {}
    for bases in product(alphabet, repeat=G):
        c = canon(bases)
        if c not in seen:
            seen[c] = bases
    return sorted(seen.values())


# ---------------------------------------------------------------------------
# Source-faithful repeat / bridging predicates
# ---------------------------------------------------------------------------

def maximal_repeat_pairs(g, ell):
    """All unordered pairs of distinct starts with equal length-ell windows and
    the Bresler maximality condition (preceding symbols differ, following
    symbols differ).  ell == G is excluded (a full-cycle window is trivial)."""
    G = len(g)
    if ell >= G:
        return []
    out = []
    for t1 in range(G):
        w1 = window(g, t1, ell)
        for t2 in range(t1 + 1, G):
            if window(g, t2, ell) != w1:
                continue
            if g[(t1 - 1) % G] == g[(t2 - 1) % G]:
                continue
            if g[(t1 + ell) % G] == g[(t2 + ell) % G]:
                continue
            out.append((t1, t2))
    return out


def triple_repeats(g, ell):
    """All 3-subsets of starts with equal length-ell windows and the three-copy
    maximality condition (preceding symbols not all equal, following symbols not
    all equal)."""
    G = len(g)
    if ell >= G:
        return []
    out = []
    for combo in combinations(range(G), 3):
        w = window(g, combo[0], ell)
        if any(window(g, t, ell) != w for t in combo[1:]):
            continue
        prev = {g[(t - 1) % G] for t in combo}
        nxt = {g[(t + ell) % G] for t in combo}
        if len(prev) >= 2 and len(nxt) >= 2:
            out.append(combo)
    return out


def copy_bridged(g, L, m, t, ell):
    """A read occurrence strictly extends beyond the length-ell copy at t on both
    sides.  Read starts are lifted by +/- G to handle the circular origin."""
    G = len(g)
    for s in range(G):
        if m[s] == 0:
            continue
        for k in (-1, 0, 1):
            r = s + k * G
            if r < t and t + ell < r + L:
                return True
    return False


def interleaved(a, b):
    """Two repeat pairs (a1,a2), (b1,b2) with four distinct starts whose labels
    alternate in cyclic order.  Returns True iff interleaved."""
    starts = [a[0], a[1], b[0], b[1]]
    if len(set(starts)) != 4:
        return False
    labelled = sorted([(a[0], 0), (a[1], 0), (b[0], 1), (b[1], 1)])
    seq = [lab for _, lab in labelled]
    return seq == [0, 1, 0, 1] or seq == [1, 0, 1, 0]


def covers(g, L, m):
    G = len(g)
    covered = [False] * G
    for s in range(G):
        if m[s] > 0:
            for j in range(L):
                covered[(s + j) % G] = True
    return all(covered)


def genome_structure(g):
    """Precompute the m-independent I_s obligations: maximal triple repeats and
    interleaved maximal repeat pairs, each tagged with its length and starts."""
    G = len(g)
    pairs_by_ell = {ell: maximal_repeat_pairs(g, ell) for ell in range(1, G)}
    triples = []
    for ell in range(1, G):
        for combo in triple_repeats(g, ell):
            triples.append((ell, combo))
    interleaved_pairs = []
    for ell1 in range(1, G):
        for a in pairs_by_ell[ell1]:
            for ell2 in range(ell1, G):
                for b in pairs_by_ell[ell2]:
                    if a == b:
                        continue
                    if interleaved(a, b):
                        interleaved_pairs.append((ell1, a, ell2, b))
    return {"triples": triples, "interleaved": interleaved_pairs}


def satisfies_Is(g, L, m, struct):
    """Source-faithful information-feasible hypothesis for the realization m."""
    if not covers(g, L, m):
        return False
    for ell, combo in struct["triples"]:
        if not all(copy_bridged(g, L, m, t, ell) for t in combo):
            return False
    for ell1, a, ell2, b in struct["interleaved"]:
        bridged = (
            copy_bridged(g, L, m, a[0], ell1)
            or copy_bridged(g, L, m, a[1], ell1)
            or copy_bridged(g, L, m, b[0], ell2)
            or copy_bridged(g, L, m, b[1], ell2)
        )
        if not bridged:
            return False
    return True


# ---------------------------------------------------------------------------
# Observation vectors and candidate universes
# ---------------------------------------------------------------------------

def observed_counts(g, L, m):
    G = len(g)
    x = {}
    for s in range(G):
        if m[s] > 0:
            w = window(g, s, L)
            x[w] = x.get(w, 0) + m[s]
    return x


def compositions(total, parts):
    """All tuples of length `parts` of nonnegative ints summing to total."""
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in compositions(total - first, parts - 1):
            yield (first,) + rest


def score(cand, x):
    """proportional fixed-length exact score prod_w d_C(w)^{x_w}; zero if a
    positive-count type is missing."""
    p = Fraction(1)
    for w, c in x.items():
        d = occ(cand, w)
        if d == 0:
            return Fraction(0)
        p *= Fraction(d) ** c
    return p


# ---------------------------------------------------------------------------
# Search
# ---------------------------------------------------------------------------

def search(G, L, alphabet, max_reads=None, require_Is=True, verbose=False):
    if max_reads is None:
        max_reads = G
    reps = rotation_reps(G, alphabet)
    results = {
        "params": {"G": G, "L": L, "alphabet_size": len(alphabet),
                   "max_reads": max_reads},
        "instances_Is_SinFstar": 0,
        "repeat_truth_instances": 0,
        "stricter_than_truth": [],  # U0 counterexamples
        "U1_counterexamples": [],
        "U2_counterexamples": [],
        "minscore_by_universe": {},
    }
    seen_instances = set()

    for S in reps:
        S_list = list(S)
        spec = spectrum(S_list, L)
        dS = {w: occ(S_list, w) for w in spec}
        struct = genome_structure(S_list)
        repeat_free = (len(spec) == G)
        # Enumerate start-multiplicity vectors m with n <= max_reads.
        for n in range(1, max_reads + 1):
            for m in compositions(n, G):
                m = list(m)
                x = observed_counts(S_list, L, m)
                if not x:
                    continue
                # S in F*(R): all window types observed and x_w <= d_S(w).
                if set(x) != spec:
                    continue
                if any(x[w] > dS[w] for w in x):
                    continue
                if require_Is and not satisfies_Is(S_list, L, m, struct):
                    continue
                key = (S, tuple(sorted(x.items())), not repeat_free)
                if key in seen_instances:
                    continue
                seen_instances.add(key)
                results["instances_Is_SinFstar"] += 1
                if not repeat_free:
                    results["repeat_truth_instances"] += 1

                sS = score(S_list, x)
                for universe in ("U0", "U1", "U2"):
                    for D in reps:
                        Dl = list(D)
                        if canon(Dl) == canon(S_list):
                            continue
                        if universe != "U0":
                            if not spectrum(Dl, L) <= spec:
                                continue
                            if universe == "U2":
                                if any(occ(Dl, w) < x[w] for w in x):
                                    continue
                        sD = score(Dl, x)
                        if sD > sS:
                            rec = {
                                "S": gstr(S), "D": gstr(D),
                                "G": G, "L": L,
                                "x": {gstr(w): c for w, c in x.items()},
                                "n": sum(x.values()),
                                "truth_score": str(sS), "cand_score": str(sD),
                                "repeat_free": repeat_free,
                            }
                            if universe == "U0":
                                results["stricter_than_truth"].append(rec)
                            elif universe == "U1":
                                results["U1_counterexamples"].append(rec)
                            else:
                                results["U2_counterexamples"].append(rec)
                if verbose and results["U2_counterexamples"]:
                    pass
    return results


def summarize(results, label):
    tot = {
        "instances": sum(r["instances_Is_SinFstar"] for r in results),
        "repeated_truth_instances": sum(r["repeat_truth_instances"] for r in results),
        "U0_counterexamples": sum(len(r["stricter_than_truth"]) for r in results),
        "U1_counterexamples": sum(len(r["U1_counterexamples"]) for r in results),
        "U2_counterexamples": sum(len(r["U2_counterexamples"]) for r in results),
    }
    print(f"[{label}] instances={tot['instances']} "
          f"(repeated-truth={tot['repeated_truth_instances']}) "
          f"U0cex={tot['U0_counterexamples']} "
          f"U1cex={tot['U1_counterexamples']} "
          f"U2cex={tot['U2_counterexamples']}")
    return tot


def main():
    t0 = time.time()
    print("Fixed-length exact Variant E under per-occurrence flow F*")
    print("Primary hypothesis: I_s AND S in F*(R).")

    primary = []
    print("\n-- primary scope: binary, G=4..8, all L, I_s required --")
    for G in range(4, 9):
        for L in range(2, G):
            r = search(G, L, (0, 1), require_Is=True)
            primary.append(r)
            n_u0 = len(r["stricter_than_truth"])
            n_u2 = len(r["U2_counterexamples"])
            print(f"  G={G} L={L}: inst={r['instances_Is_SinFstar']:4d} "
                  f"rep={r['repeat_truth_instances']:4d} U0cex={n_u0} U2cex={n_u2}")
    primary_sum = summarize(primary, "primary I_s")

    extended = []
    print("\n-- extended scope: binary G=9 L<=4 and ternary G=5..6, I_s required --")
    for G, L, alpha in [(9, 2, (0, 1)), (9, 3, (0, 1)), (9, 4, (0, 1)),
                        (5, 2, (0, 1, 2)), (5, 3, (0, 1, 2)),
                        (6, 2, (0, 1, 2)), (6, 3, (0, 1, 2))]:
        r = search(G, L, alpha, require_Is=True)
        r["alphabet_size"] = len(alpha)
        extended.append(r)
        print(f"  G={G} L={L} |A|={len(alpha)}: inst={r['instances_Is_SinFstar']:4d} "
              f"rep={r['repeat_truth_instances']:4d} "
              f"U0cex={len(r['stricter_than_truth'])} "
              f"U2cex={len(r['U2_counterexamples'])}")
    extended_sum = summarize(extended, "extended I_s")

    control = []
    print("\n-- control: I_s DROPPED, only S in F* (binary G=5..7) --")
    for G in range(5, 8):
        for L in range(2, G):
            r = search(G, L, (0, 1), require_Is=False)
            control.append(r)
            print(f"  G={G} L={L}: inst={r['instances_Is_SinFstar']:4d} "
                  f"rep={r['repeat_truth_instances']:4d} "
                  f"U0cex={len(r['stricter_than_truth'])} "
                  f"U2cex={len(r['U2_counterexamples'])}")
    control_sum = summarize(control, "control no I_s")

    elapsed = time.time() - t0
    print(f"\nElapsed {elapsed:.1f}s")

    out = {
        "model": "fixed-length exact Variant E, circular genomes, candidate length = G",
        "objective": "L(D|x) proportional to prod_w d_D(w)^{x_w} (multinomial coefficient cancels at fixed length)",
        "hypothesis": "I_s = coverage AND all-bridged maximal triple repeats AND bridged interleaved repeat pairs (Bresler et al. via Shomorony et al. Eq. (1))",
        "candidate_universes": {
            "U0": "all circular candidates of length G",
            "U1": "supp(D) subset of supp(S)",
            "U2": "supp(D) subset of supp(S) and d_D(w) >= x_w for every observed type (per-occurrence F*)",
        },
        "truth_side_assumption": "S in F*(R): supp(R) = supp(S) and x_w <= d_S(w) for all w",
        "primary_scope": {
            "alphabet": "binary {A,B}", "G": "4..8", "L": "2..G-1",
            "max_reads": "n <= G (automatic from S in F*)",
        },
        "extended_scope": "binary G=9 L<=4; ternary G=5..6 L<=3",
        "control": "same search with I_s dropped, showing bridging is load-bearing",
        "summary": {
            "primary_Is": primary_sum,
            "extended_Is": extended_sum,
            "control_no_Is": control_sum,
            "elapsed_seconds": elapsed,
        },
        "control_U2_witnesses": [c for r in control for c in r["U2_counterexamples"]][:20],
        "results_primary": primary,
        "results_extended": extended,
        "results_control": control,
    }
    with open("results/fixed-length-flow-feasible-repeat-search.json", "w") as f:
        json.dump(out, f, indent=2)
    print("Wrote results/fixed-length-flow-feasible-repeat-search.json")

    ok = (primary_sum["U0_counterexamples"] == 0
          and extended_sum["U0_counterexamples"] == 0
          and control_sum["U2_counterexamples"] > 0)
    print("EXPECTED PATTERN HOLDS" if ok else "UNEXPECTED RESULT")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
