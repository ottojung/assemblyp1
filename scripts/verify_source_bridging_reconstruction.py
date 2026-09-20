#!/usr/bin/env python3
"""
Independent, self-contained verification that the repository's strongest
maximum-likelihood counterexample witnesses satisfy the *source* Shomorony /
Bresler information-feasible bridging hypothesis I_s.

The repeat / triple-repeat / interleaving / bridging definitions below are
reconstructed directly from the primary prose of

  Guy Bresler, Ma'ayan Bresler, David Tse, "Optimal assembly for high
  throughput shotgun sequencing", BMC Bioinformatics 14(Suppl 5):S18, 2013,
  PMC3706340, retrieved 2026-09-20.

quoted here so the provenance is auditable:

  "A repeat of length l is a subsequence appearing twice, at some positions
   t1, t2 (so s_t1^l = s_t2^l) that is maximal (i.e. s(t1 - 1) != s(t2 - 1)
   and s(t1 + l) != s(t2 + l)). Similarly, a triple repeat of length l is a
   subsequence appearing three times, at positions t1, t2, t3, such that
   s_t1^l = s_t2^l = s_t3^l, and such that neither of
   s(t1 - 1) = s(t2 - 1) = s(t3 - 1) nor s(t1 + l) = s(t2 + l) = s(t3 + l)
   holds. (Note that a subsequence that is repeated f times gives rise to
   C(f,2) repeats and C(f,3) triple repeats.) ... A pair of repeats refers to
   two repeats, each having two copies. A pair of repeats, one at positions
   t1, t3 with t1 < t3 and the second at positions t2, t4 with t2 < t4, is
   interleaved if t1 < t2 < t3 < t4 or t2 < t1 < t4 < t3."

  Figure 5: "A subsequence s_t^l is bridged if and only if there exists at
   least one read which covers at least one base on both sides of the
   subsequence, i.e. the read arrives in the preceding length L-l-1 interval."

  "we will call a repeat or a triple repeat bridged if at least one copy of the
   repeat is bridged, and a pair of interleaved repeats bridged if at least one
   of the repeats is bridged."

  MultiBridging (Theorem 6): (a) all interleaved repeats are bridged,
                               (b) all triple repeats are all-bridged,
                               (c) the sequence is covered by the reads.

Shomorony et al. (2016) Eq. (1) delegates this exact information-feasible set
to Bresler et al. and uses it as I_s.

This file is deliberately independent of the repository's exploratory Python
(scripts/fixed_length_bridging_search_v2.py, scripts/audit_copy_bridging_predicate.py,
...): none of them is imported.  Run:

    python3 scripts/verify_source_bridging_reconstruction.py

Exit status is non-zero on any failed assertion.
"""

from fractions import Fraction
from itertools import combinations, product
from math import comb

# --------------------------------------------------------------------------
# circular substrate
# --------------------------------------------------------------------------

def sym(S, i):
    return S[i % len(S)]

def window(S, t, ell):
    return tuple(sym(S, t + j) for j in range(ell))

def covers(S, starts, L):
    G = len(S)
    covered = set()
    for r in starts:
        for j in range(L):
            covered.add((r + j) % G)
    return covered == set(range(G))

# --------------------------------------------------------------------------
# source repeats
# --------------------------------------------------------------------------

def maximal_repeat_pairs(S):
    G = len(S)
    out = []
    for ell in range(1, G):
        groups = {}
        for t in range(G):
            groups.setdefault(window(S, t, ell), []).append(t)
        for w, ts in groups.items():
            for t1, t2 in combinations(ts, 2):
                if sym(S, t1 - 1) != sym(S, t2 - 1) and \
                   sym(S, t1 + ell) != sym(S, t2 + ell):
                    out.append((ell, frozenset((t1, t2)), w))
    return out

def maximal_triple_repeats(S):
    G = len(S)
    out = []
    for ell in range(1, G):
        groups = {}
        for t in range(G):
            groups.setdefault(window(S, t, ell), []).append(t)
        for w, ts in groups.items():
            for tri in combinations(ts, 3):
                if len({sym(S, t - 1) for t in tri}) > 1 and \
                   len({sym(S, t + ell) for t in tri}) > 1:
                    out.append((ell, frozenset(tri), w))
    return out

def interleaved_pairs(S):
    reps = maximal_repeat_pairs(S)
    out = []
    for i in range(len(reps)):
        for j in range(i + 1, len(reps)):
            e1, p1, _ = reps[i]
            e2, p2, _ = reps[j]
            pts = list(p1) + list(p2)
            if len(set(pts)) != 4:
                continue
            labels = {t: 0 for t in p1}
            labels.update({t: 1 for t in p2})
            order = sorted(pts)
            lab = [labels[t] for t in order]
            if lab[0] == lab[2] and lab[1] == lab[3] and lab[0] != lab[1]:
                out.append((e1, p1, e2, p2))
    return out

# --------------------------------------------------------------------------
# source bridging (strict two-sided extension)
# --------------------------------------------------------------------------

def copy_bridged(S, t, ell, starts, L):
    """True iff some read strictly contains the length-ell copy at t.

    On an integer lift, read [r, r+L) bridges copy [t + mG, t + mG + ell) iff
    r < t + mG and t + mG + ell < r + L.
    """
    G = len(S)
    for r in starts:
        for m in range(-2, 3):
            T = t + m * G
            if r < T and T + ell < r + L:
                return True
    return False

# --------------------------------------------------------------------------
# the source hypothesis I_s, with a full audit trail
# --------------------------------------------------------------------------

def check_I_s(S, starts, L):
    G = len(S)
    audit = {
        "coverage": covers(S, starts, L),
        "repeat_pairs": [],
        "triple_repeats": [],
        "interleaved_pairs": [],
    }
    for ell, p, w in maximal_repeat_pairs(S):
        audit["repeat_pairs"].append(
            (ell, tuple(sorted(p)), w, tuple(copy_bridged(S, t, ell, starts, L)
                                             for t in sorted(p))))
    all_triple = True
    for ell, ts, w in maximal_triple_repeats(S):
        bridged = tuple(copy_bridged(S, t, ell, starts, L) for t in sorted(ts))
        all_triple = all_triple and all(bridged)
        audit["triple_repeats"].append((ell, tuple(sorted(ts)), w, bridged))
    inter = True
    for e1, p1, e2, p2 in interleaved_pairs(S):
        b1 = any(copy_bridged(S, t, e1, starts, L) for t in p1)
        b2 = any(copy_bridged(S, t, e2, starts, L) for t in p2)
        inter = inter and (b1 or b2)
        audit["interleaved_pairs"].append((e1, tuple(sorted(p1)),
                                           e2, tuple(sorted(p2)), b1 or b2))
    audit["all_triple_all_bridged"] = all_triple
    audit["all_interleaved_bridged"] = inter
    audit["I_s"] = (audit["coverage"] and all_triple and inter)
    return audit

# --------------------------------------------------------------------------
# objectives (for the likelihood ratios quoted in the note)
# --------------------------------------------------------------------------

def spectrum(S, L):
    d = {}
    for t in range(len(S)):
        d[window(S, t, L)] = d.get(window(S, t, L), 0) + 1
    return d

def observed(S, starts, L):
    x = {}
    for r in starts:
        w = window(S, r, L)
        x[w] = x.get(w, 0) + 1
    return x

def fixed_length_exact_ratio(S, D, starts, L):
    """Ratio L(D|x)/L(S|x) of the exact multinomial restricted to |D|=|S|."""
    assert len(S) == len(D)
    G = len(S)
    x = observed(S, starts, L)
    dS, dD = spectrum(S, L), spectrum(D, L)
    num = den = Fraction(1)
    for w, c in x.items():
        num *= Fraction(dD.get(w, 0)) ** c
        den *= Fraction(dS.get(w, 0)) ** c
    return num / den

ALPHABET = "ACGT"

def binomial_ratio(S, D, starts, L):
    """Ratio of the literal MB 6.1 product-of-binomial-marginals, external N=|S|."""
    assert len(S) == len(D)
    N = len(S)
    x = observed(S, starts, L)
    n = sum(x.values())
    dS, dD = spectrum(S, L), spectrum(D, L)

    def like(d):
        val = Fraction(1)
        for w in product(ALPHABET, repeat=L):
            wi = x.get(w, 0)
            di = d.get(w, 0)
            if wi == 0 and di == 0:
                continue
            val *= comb(n, wi) * Fraction(di, N) ** wi * Fraction(N - di, N) ** (n - wi)
        return val
    return like(dD) / like(dS)

# --------------------------------------------------------------------------
# tests
# --------------------------------------------------------------------------

WITNESSES = [
    # name, truth, competitor, latent starts, L
    ("fixed-length exact #31   ", "AAABB",  "AAAAB",   [0, 1, 4],                 3),
    ("fixed-length binomial #32", "AAACC",  "AAAAC",   [0, 1, 4],                 3),
    ("interleaved (fixed)      ", "ABACABC", "ACABACB", [1, 1, 1, 3, 6],          3),
    ("interleaved (unrestricted)", "ABACABC", "ABAC",   [1, 1, 1, 3, 6],          3),
    ("read-tiled §6.2 per-type ", "AAABCBC", None,      [0, 0, 0, 1, 2, 5, 6],    3),
    ("§6.2 non-spellable       ", "AAATT",   None,      [0, 0, 1, 4],             3),
    ("§6.2 strongest ratio      ", "AATAT",   None,      [0, 0, 2, 4],             3),
    ("§6.2 per-type            ", "AAATAT",  None,      [0, 0, 1, 3, 5],          3),
    ("unrestricted kernel ACGT ", "ACGT",    "ACACGT",  [0, 0, 2],                2),
]

def test_witnesses():
    print("A) strongest documented witnesses against the SOURCE I_s")
    for name, S, D, starts, L in WITNESSES:
        a = check_I_s(S, starts, L)
        line = f"   {name} S={S:8s} I_s={a['I_s']!s:5s}"
        if D is not None:
            if len(D) == len(S):
                r = fixed_length_exact_ratio(S, D, starts, L)
                line += f"  fixed-length exact D/S={r}"
                if "C" in S and S == "AAACC":
                    line += f"  binomial D/S={binomial_ratio(S, D, starts, L)}"
            else:
                # unrestricted exact ratio
                G, n = len(S), len(starts)
                x = observed(S, starts, L)
                dS, dD = spectrum(S, L), spectrum(D, L)
                num = den = Fraction(1)
                for w, c in x.items():
                    num *= Fraction(G * dD.get(w, 0)) ** c
                    den *= Fraction(len(D) * dS.get(w, 0)) ** c
                line += f"  unrestricted exact D/S={num/den}"
        print(line)
        assert a["I_s"], name
    print("   -> every listed witness satisfies the source I_s (coverage + all")
    print("      triple repeats all-bridged + all interleaved pairs bridged).")

def test_exempt_repeats():
    """Maximal repeats that are neither triple nor interleaved need NOT be
    bridged by I_s; the strongest witness contains two such repeats."""
    print("B) unbridged maximal repeats exempt from I_s (the GREEDY trap)")
    cases = [("AAABB", [0, 1, 4], 3), ("AATAT", [0, 0, 2, 4], 3)]
    for S, starts, L in cases:
        a = check_I_s(S, starts, L)
        unbridged = [(e, p, w) for e, p, w, br in a["repeat_pairs"]
                     if not any(br)]
        print(f"   S={S:6s} I_s={a['I_s']}  unbridged maximal pairs: "
              f"{[(e, p) for e, p, w in unbridged]}")
        required = {frozenset(t) for e, t, w, b in a["triple_repeats"]}
        required |= {frozenset(p) for e1, p1, e2, p2, b in a["interleaved_pairs"]
                     for p in (p1, p2)}
        for e, p, w in unbridged:
            assert p not in required, (S, p)
        assert unbridged, S
    print("   -> those pairs are not triple repeats and not interleaved, so I_s")
    print("      does not require them to be bridged (Bresler's GREEDY condition")
    print("      'every repeat is bridged' is strictly stronger and is not I_s).")

def test_coverage_failure_of_unbounded_family():
    """The (G/L)^n universality family uses single-read-type samples that have a
    single latent start, so they FAIL the coverage clause of I_s."""
    print("C) the unbounded-ratio {k:n} family fails I_s coverage")
    for S, k, L in [("ACGT", "AC", 2), ("AACGT", "AA", 2)]:
        t = S.index(k)
        starts = [t] * 4
        a = check_I_s(S, starts, L)
        print(f"   S={S:6s} k={k} starts={starts} coverage={a['coverage']} "
              f"I_s={a['I_s']}")
        assert not a["coverage"] and not a["I_s"]
    print("   -> ratio (G/L)^n is real but is NOT an I_s counterexample.")

def test_corrected_nearby_witness():
    """Coverage-corrected family: same truth AAABB, k copies of the dominant
    read plus one read each of two other observed types; I_s holds and the
    fixed-length exact ratio is 2^k."""
    print("D) nearby witness that DOES satisfy I_s (coverage-corrected)")
    for k in (1, 2, 5, 8):
        starts = [0] * k + [1, 4]
        a = check_I_s("AAABB", starts, 3)
        r = fixed_length_exact_ratio("AAABB", "AAAAB", starts, 3)
        print(f"   k={k:2d} starts={starts} I_s={a['I_s']} ratio={r} "
              f"(2^k={2**k})")
        assert a["I_s"] and r == 2 ** k

def main():
    test_witnesses()
    print()
    test_exempt_repeats()
    print()
    test_coverage_failure_of_unbounded_family()
    print()
    test_corrected_nearby_witness()
    print("\nAll assertions passed.")

if __name__ == "__main__":
    main()
