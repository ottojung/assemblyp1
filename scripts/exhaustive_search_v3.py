#!/usr/bin/env python3
"""
Exhaustive search for counterexamples to I_s => ML under fixed-length exact
Variant E (Medvedev-Brudno exact multinomial restricted to candidate length G).

Source-faithful I_s bridging (Bresler et al. 2013 / Shomorony et al. 2016):
  1. Coverage: every position of S covered by at least one read.
  2. Triple repeats: every selected copy is bridged (all-bridged).
  3. Interleaved repeats: at least one of the two repeats is bridged.

Fixed-length exact Variant E (Medvedev-Brudno 2009, §6.1, |D| = G):
  L(D | x) ∝ ∏_i d_D(i)^{x_i}
  where d_D(i) = occurrence count of L-mer type i in candidate D.

Epistemic status: computational evidence from exhaustive search.
All arithmetic uses exact rational computation (fractions.Fraction).
A counterexample found here is evidence, not proof, of I_s failing to imply ML.

Assumptions and scope (all explicit):
  - Circular genomes over alphabet of size sigma (sigma ∈ {2, 3}).
  - Fixed read length L, fixed read count N (N ≥ G).
  - Candidate genomes have the SAME length G as the truth.
  - I_s bridging conditions per source semantics (maximal repeats, all-bridged
    triples, bridged interleaved pairs).
  - Genome equivalence = identity (not cyclic shift). We check whether truth
    is THE maximizer, not just A maximizer up to cyclic shift.
  - N = G is the default; we also test N = G+1, G+2 for selected instances.
"""
import argparse
import sys
import time
import json
from itertools import combinations, product as iterproduct
from fractions import Fraction
from collections import Counter, defaultdict


# ---------------------------------------------------------------------------
# L-mer spectrum
# ---------------------------------------------------------------------------

def circular_kmer_spectrum(S, L):
    """Return dict mapping L-mer tuple -> occurrence count for circular string S."""
    G = len(S)
    spec = defaultdict(int)
    for i in range(G):
        kmer = tuple(S[(i + j) % G] for j in range(L))
        spec[kmer] += 1
    return dict(spec)


# ---------------------------------------------------------------------------
# Coverage
# ---------------------------------------------------------------------------

def covers_all_positions(S, starts, L):
    """Check that every position of circular S is covered by at least one read."""
    G = len(S)
    covered = set()
    for r in starts:
        for offset in range(L):
            covered.add((r + offset) % G)
    return len(covered) == G


# ---------------------------------------------------------------------------
# Repeat detection (source-faithful: maximal repeats with maximality condition)
# ---------------------------------------------------------------------------

def find_all_maximal_repeat_pairs(S):
    """
    Find all maximal repeat pairs in S.

    A maximal repeat pair of length ell has two occurrences at positions t1, t2
    such that:
      - S[t1..t1+ell] = S[t2..t2+ell] (equal length-ell substring)
      - S[t1-1] != S[t2-1] (differ on the left)
      - S[t1+ell] != S[t2+ell] (differ on the right)

    This is the source-faithful definition from Bresler et al. 2013.
    Returns list of (ell, (t1, t2), kmer_tuple).
    """
    G = len(S)
    results = []
    for ell in range(1, G):
        seen = {}
        for i in range(G):
            kmer = tuple(S[(i + j) % G] for j in range(ell))
            if kmer not in seen:
                seen[kmer] = []
            seen[kmer].append(i)
        for kmer, starts_list in seen.items():
            if len(starts_list) < 2:
                continue
            for pair in combinations(starts_list, 2):
                t1, t2 = pair
                if S[(t1 - 1) % G] != S[(t2 - 1) % G] and \
                   S[(t1 + ell) % G] != S[(t2 + ell) % G]:
                    results.append((ell, (t1, t2), kmer))
    # Deduplicate by position pair
    seen_r = set()
    deduped = []
    for ell, pos, kmer in results:
        if pos not in seen_r:
            seen_r.add(pos)
            deduped.append((ell, pos, kmer))
    return deduped


def find_all_triple_repeats(S):
    """
    Find all triple repeats in S.

    A triple repeat of length ell has three occurrences at t1, t2, t3 with
    equal length-ell substrings and the three-copy maximality condition:
      - Not all preceding symbols equal
      - Not all following symbols equal

    Source: Bresler et al. 2013, repeat-definition paragraph around Fig. 4.
    Returns list of (ell, (t1, t2, t3), kmer_tuple).
    """
    G = len(S)
    results = []
    for ell in range(1, G):
        seen = {}
        for i in range(G):
            kmer = tuple(S[(i + j) % G] for j in range(ell))
            if kmer not in seen:
                seen[kmer] = []
            seen[kmer].append(i)
        for kmer, starts_list in seen.items():
            if len(starts_list) < 3:
                continue
            for triple in combinations(starts_list, 3):
                pres = [S[(t - 1) % G] for t in triple]
                posts = [S[(t + ell) % G] for t in triple]
                if len(set(pres)) > 1 and len(set(posts)) > 1:
                    results.append((ell, tuple(sorted(triple)), kmer))
    seen_r = set()
    deduped = []
    for ell, pos, kmer in results:
        if pos not in seen_r:
            seen_r.add(pos)
            deduped.append((ell, pos, kmer))
    return deduped


def find_all_interleaved_pairs(S):
    """
    Find all pairs of interleaved maximal repeats.

    Two maximal repeats (t1,t2) and (t3,t4) are interleaved when their starts
    alternate in cyclic order: t1 < t3 < t2 < t4 (or vice versa) after
    choosing any origin that avoids the four starts.

    Source: Bresler et al. 2013, Theorem 1 discussion.
    Returns list of ((ell1, pos1, kmer1), (ell2, pos2, kmer2)).
    """
    repeats = find_all_maximal_repeat_pairs(S)
    results = []
    seen_pairs = set()
    for i in range(len(repeats)):
        ell1, pos1, kmer1 = repeats[i]
        for j in range(i + 1, len(repeats)):
            ell2, pos2, kmer2 = repeats[j]
            all_four = sorted(set(list(pos1) + list(pos2)))
            if len(all_four) != 4:
                continue
            label = {}
            for p in pos1:
                label[p] = 0
            for p in pos2:
                label[p] = 1
            labels_cyclic = [label[p] for p in sorted(all_four)]
            if labels_cyclic in ([0, 1, 0, 1], [1, 0, 1, 0]):
                pk = (ell1, tuple(sorted(pos1)), ell2, tuple(sorted(pos2)))
                if pk not in seen_pairs:
                    seen_pairs.add(pk)
                    results.append((
                        (ell1, tuple(sorted(pos1)), kmer1),
                        (ell2, tuple(sorted(pos2)), kmer2)
                    ))
    return results


# ---------------------------------------------------------------------------
# Bridging check (source-faithful)
# ---------------------------------------------------------------------------

def check_copy_bridged(S, t, ell, starts, L):
    """
    Check if copy at position t of length-ell repeat is bridged.

    A copy is bridged iff some read [r, r+L) strictly extends beyond
    the copy on both sides: r < t and t + ell < r + L (on integer lift).

    Source: Bresler et al. 2013, paragraph before Theorem 1;
            Shomorony et al. 2016, §3/Fig. 6.
    """
    G = len(S)
    for r in starts:
        rp = set((r + offset) % G for offset in range(L))
        if (t - 1) % G in rp and (t + ell) % G in rp:
            return True
    return False


def check_I_s(S, starts, L):
    """
    Check if the information-feasible hypothesis I_s holds.

    I_s = coverage ∧ all-bridged triple repeats ∧ bridged interleaved repeats.

    Source: Shomorony et al. 2016, Eq. (1).
    """
    if not covers_all_positions(S, starts, L):
        return False
    for ell, positions, kmer in find_all_triple_repeats(S):
        for t in positions:
            if not check_copy_bridged(S, t, ell, starts, L):
                return False
    for (ell1, pos1, kmer1), (ell2, pos2, kmer2) in find_all_interleaved_pairs(S):
        b1 = any(check_copy_bridged(S, t, ell1, starts, L) for t in pos1)
        b2 = any(check_copy_bridged(S, t, ell2, starts, L) for t in pos2)
        if not (b1 or b2):
            return False
    return True


# ---------------------------------------------------------------------------
# Likelihood ratio (exact)
# ---------------------------------------------------------------------------

def compute_ratio_from_obs(spec_S, spec_D, obs):
    """
    Compute exact likelihood ratio L(D|x) / L(S|x) = ∏ (d_D(i)/d_S(i))^{x_i}.

    Uses exact rational arithmetic (fractions.Fraction).
    Returns 0 if any observed type has d_S = 0 or d_D = 0.
    """
    ratio = Fraction(1)
    for kmer, count in obs.items():
        d_S = spec_S.get(kmer, 0)
        d_D = spec_D.get(kmer, 0)
        if d_S == 0 or d_D == 0:
            return Fraction(0)
        ratio *= Fraction(d_D, d_S) ** count
    return ratio


# ---------------------------------------------------------------------------
# Combinations with replacement (read start positions)
# ---------------------------------------------------------------------------

def combinations_with_replacement(iterable, r):
    """Yield all r-length combinations with replacement from iterable."""
    pool = tuple(iterable)
    n = len(pool)
    if n == 0 and r:
        return
    indices = [0] * r
    yield tuple(pool[i] for i in indices)
    while True:
        for i in range(r - 1, -1, -1):
            if indices[i] != n - 1:
                break
        else:
            return
        indices[i] += 1
        for j in range(i + 1, r):
            indices[j] = indices[i]
        yield tuple(pool[i] for i in indices)


# ---------------------------------------------------------------------------
# Self-validation of counterexamples
# ---------------------------------------------------------------------------

def validate_counterexample(S, D, starts, L):
    """
    Self-validate a counterexample: recompute all quantities from scratch.
    Returns dict with validation results or None if invalid.
    """
    G = len(S)
    if len(D) != G:
        return None  # Not same length

    spec_S = circular_kmer_spectrum(S, L)
    spec_D = circular_kmer_spectrum(D, L)
    obs = Counter()
    for r in starts:
        kmer = tuple(S[(r + j) % G] for j in range(L))
        obs[kmer] += 1

    # Coverage
    if not covers_all_positions(S, list(starts), L):
        return None

    # I_s
    if not check_I_s(S, list(starts), L):
        return None

    # All observed types have d_S > 0 and d_D > 0
    for kmer in obs:
        if spec_S.get(kmer, 0) == 0 or spec_D.get(kmer, 0) == 0:
            return None

    # Ratio
    ratio = compute_ratio_from_obs(spec_S, spec_D, obs)
    if ratio <= 1:
        return None

    return {
        "truth": S,
        "competitor": D,
        "starts": tuple(sorted(starts)),
        "L": L,
        "ratio": ratio,
        "obs": dict(obs),
        "d_S": {k: v for k, v in spec_S.items() if k in obs},
        "d_D": {k: v for k, v in spec_D.items() if k in obs},
        "validated": True,
    }


# ---------------------------------------------------------------------------
# Exhaustive search for one (G, L, sigma, N) instance
# ---------------------------------------------------------------------------

def search_instance(G, L_inst, sigma, N):
    """
    Exhaustive search over all circular genomes of length G over alphabet
    {0, ..., sigma-1}, all read start multisets of size N from {0, ..., G-1}.

    For each (truth, starts) pair:
      - Check I_s bridging conditions.
      - If I_s holds, check whether any same-length competitor beats the truth
        under fixed-length exact Variant E.

    Returns dict with counterexamples and statistics.
    """
    counterexamples = []
    truths_checked = 0
    truths_with_is = 0
    observations_checked = 0
    all_genomes = list(iterproduct(range(sigma), repeat=G))
    total_genomes = len(all_genomes)

    # Precompute spectra
    all_specs = [circular_kmer_spectrum(g, L_inst) for g in all_genomes]

    # Precompute k-mer -> genome index mapping for fast competitor filtering
    all_kmer_types = set()
    for spec in all_specs:
        all_kmer_types.update(spec.keys())
    kmer_to_genomes = {}
    for kmer in all_kmer_types:
        kmer_to_genomes[kmer] = frozenset(
            i for i, spec in enumerate(all_specs) if spec.get(kmer, 0) > 0
        )

    for s_idx, S in enumerate(all_genomes):
        truths_checked += 1
        spec_S = all_specs[s_idx]
        is_repeat_free = all(v == 1 for v in spec_S.values())
        has_triple = len(find_all_triple_repeats(S)) > 0
        has_interleaved = len(find_all_interleaved_pairs(S)) > 0
        has_repeats = has_triple or has_interleaved

        for starts in combinations_with_replacement(range(G), N):
            starts_list = list(starts)
            observations_checked += 1

            if not check_I_s(S, starts_list, L_inst):
                continue
            truths_with_is += 1

            # Build observation
            obs = Counter()
            for r in starts_list:
                kmer = tuple(S[(r + j) % G] for j in range(L_inst))
                obs[kmer] += 1
            obs_support = set(obs.keys())

            # Filter candidates: must support all observed types
            candidate_indices = None
            for kmer in obs_support:
                if candidate_indices is None:
                    candidate_indices = set(kmer_to_genomes.get(kmer, set()))
                else:
                    candidate_indices &= kmer_to_genomes.get(kmer, set())
                if not candidate_indices:
                    break
            if not candidate_indices:
                continue
            candidate_indices.discard(s_idx)

            # Find best competitor
            best_ratio = Fraction(1)
            best_competitor = None
            best_d_D = None
            for d_idx in candidate_indices:
                ratio = compute_ratio_from_obs(spec_S, all_specs[d_idx], obs)
                if ratio > best_ratio:
                    best_ratio = ratio
                    best_competitor = all_genomes[d_idx]
                    best_d_D = {k: v for k, v in all_specs[d_idx].items() if k in obs}

            if best_ratio > 1:
                # Self-validate
                vresult = validate_counterexample(
                    S, best_competitor, starts_list, L_inst
                )
                counterexamples.append({
                    "truth": S,
                    "competitor": best_competitor,
                    "starts": tuple(sorted(starts_list)),
                    "ratio": best_ratio,
                    "obs": dict(obs),
                    "d_S": {k: v for k, v in spec_S.items() if k in obs},
                    "d_D": best_d_D,
                    "is_repeat_free": is_repeat_free,
                    "has_triple_repeats": has_triple,
                    "has_interleaved": has_interleaved,
                    "bridging_type": "vacuous" if not has_repeats else "substantive",
                    "validated": vresult is not None,
                })

    return {
        "counterexamples": counterexamples,
        "truths_checked": truths_checked,
        "truths_with_is": truths_with_is,
        "observations_checked": observations_checked,
        "total_genomes": total_genomes,
    }


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Exhaustive search for I_s => ML counterexamples "
                    "(fixed-length exact Variant E)"
    )
    parser.add_argument("--G", type=int, default=8,
                        help="Maximum genome length (searches G=4..G)")
    parser.add_argument("--L", type=int, default=3,
                        help="Read length")
    parser.add_argument("--alpha", type=int, default=3,
                        help="Alphabet size (2 or 3)")
    parser.add_argument("--N", type=str, default="G",
                        help="Read count: 'G' (default), or comma-separated offsets like '0,1,2'")
    parser.add_argument("--detailed", action="store_true",
                        help="Print detailed counterexample info")
    parser.add_argument("--json", action="store_true",
                        help="Output JSON")
    args = parser.parse_args()

    sigma = args.alpha
    if sigma not in (2, 3):
        print(f"Warning: sigma={sigma} may be too large for exhaustive search", file=sys.stderr)

    alphabet = "ABCDEF"[:sigma]
    print(f"Exhaustive I_s => ML counterexample search (v3)")
    print(f"Alphabet: {{{', '.join(alphabet[:sigma])}}} (size {sigma})")
    print(f"Fixed-length exact Variant E (Medvedev-Brudno §6.1)")
    print(f"Source-faithful I_s bridging (Bresler et al. 2013 / Shomorony et al. 2016)")
    print(f"Exact rational arithmetic throughout")
    print("=" * 70)

    # Parse N specification
    if args.N == "G":
        n_offsets = [0]
    else:
        n_offsets = [int(x) for x in args.N.split(",")]

    all_output = []

    for G in range(4, args.G + 1):
        if G < args.L:
            continue
        L_inst = min(args.L, G)

        for n_off in n_offsets:
            N = G + n_off
            if N < L_inst:
                continue

            t0 = time.time()
            result = search_instance(G, L_inst, sigma, N)
            t1 = time.time()

            cex = result["counterexamples"]
            total_cex = len(cex)
            vacuous_cex = sum(1 for c in cex if c["bridging_type"] == "vacuous")
            substantive_cex = total_cex - vacuous_cex
            validated_cex = sum(1 for c in cex if c.get("validated", False))

            # Compute max ratio among substantive counterexamples
            substantive_ratios = [
                c["ratio"] for c in cex if c["bridging_type"] == "substantive"
            ]
            max_substantive_ratio = max(substantive_ratios) if substantive_ratios else None

            entry = {
                "G": G, "L": L_inst, "N": N, "sigma": sigma,
                "n_offset": n_off,
                "total_genomes": result["total_genomes"],
                "truths_checked": result["truths_checked"],
                "truths_with_is": result["truths_with_is"],
                "observations_checked": result["observations_checked"],
                "counterexamples": total_cex,
                "vacuous": vacuous_cex,
                "substantive": substantive_cex,
                "validated": validated_cex,
                "max_substantive_ratio": (
                    str(max_substantive_ratio) if max_substantive_ratio else None
                ),
                "time": t1 - t0,
            }
            all_output.append(entry)

            print(f"\nG={G}, L={L_inst}, N={N} (sigma={sigma}):")
            print(f"  Circular strings: {sigma**G}")
            print(f"  Truths checked: {result['truths_checked']}")
            print(f"  I_s-satisfying pairs: {result['truths_with_is']}")
            print(f"  Observations checked: {result['observations_checked']}")
            print(f"  Counterexamples: {total_cex} "
                  f"(vacuous: {vacuous_cex}, substantive: {substantive_cex})")
            print(f"  Self-validated: {validated_cex}/{total_cex}")
            if max_substantive_ratio:
                print(f"  Max substantive ratio: {max_substantive_ratio}")
            print(f"  Time: {t1 - t0:.2f}s")

            if cex and args.detailed:
                # Show up to 5 substantive and 3 vacuous examples
                shown_sub = 0
                shown_vac = 0
                for ex in sorted(cex, key=lambda e: (-int(e["ratio"]),
                                                      e["bridging_type"])):
                    if ex["bridging_type"] == "substantive" and shown_sub >= 5:
                        continue
                    if ex["bridging_type"] == "vacuous" and shown_vac >= 3:
                        continue
                    if ex["bridging_type"] == "substantive":
                        shown_sub += 1
                    else:
                        shown_vac += 1

                    ts = "".join(alphabet[c] for c in ex["truth"])
                    cs = "".join(alphabet[c] for c in ex["competitor"])
                    print(f"\n    [{ex['bridging_type']}] Truth: {ts}, "
                          f"Competitor: {cs}")
                    print(f"      Starts: {ex['starts']}, Obs: {ex['obs']}")
                    print(f"      d_S(obs): {ex['d_S']}, d_D(obs): {ex['d_D']}")
                    print(f"      Ratio: {ex['ratio']}, "
                          f"Validated: {ex.get('validated', '?')}")

    # Summary
    print(f"\n{'=' * 70}")
    print(f"SUMMARY")
    print(f"{'=' * 70}")
    total_cex_all = 0
    total_substantive = 0
    for e in all_output:
        total_cex_all += e["counterexamples"]
        total_substantive += e["substantive"]
        status = "COUNTEREXAMPLES" if e["counterexamples"] > 0 else "none"
        print(f"  G={e['G']}, L={e['L']}, N={e['N']}, "
              f"sigma={e['sigma']}: "
              f"{e['counterexamples']} cex "
              f"(vac: {e['vacuous']}, sub: {e['substantive']}) "
              f"[{status}] ({e['time']:.2f}s)")

    print(f"\nTotal counterexamples: {total_cex_all} "
          f"(substantive: {total_substantive})")
    if total_cex_all > 0:
        print("\nRESULT: I_s bridging conditions FAIL to guarantee ML "
              "optimality under fixed-length exact Variant E.")
        print("  At every parameter combination where I_s is satisfiable, "
              "counterexamples exist.")
    else:
        print("\nNo counterexamples found at these parameter values.")

    print("\nEpistemic status: These are computational evidence from exhaustive")
    print("search with exact rational arithmetic. They are NOT proofs.")
    print("A finite search is evidence unless its completeness is itself proved.")

    if args.json:
        # Convert Fraction to str for JSON serialization
        def default_serializer(obj):
            if isinstance(obj, Fraction):
                return str(obj)
            return str(obj)
        json.dump(all_output, sys.stdout, indent=2, default=default_serializer)
        print()

    return total_cex_all


if __name__ == "__main__":
    main()
