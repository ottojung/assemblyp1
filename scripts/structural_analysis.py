#!/usr/bin/env python3
"""
Structural analysis of fixed-length exact ML: characterize exactly
when counterexamples exist and their maximum ratios.

Key structural findings to verify:
1. Self-loop kmer (a,a): max d = G (genome a^G)
2. Heterologous kmer (a,b): max d = floor(G/2) (genome (ab)^{G/2} for even G)
3. For repeat-free truth: complete-spectrum sample is safe, skewed sample admits counterexamples
4. For repeat-free truth: max ratio = d_max^{x_k} for dominant type k
"""
from fractions import Fraction
from itertools import product as iterproduct
from collections import defaultdict, Counter

def spectrum(S, L):
    G = len(S)
    spec = defaultdict(int)
    for i in range(G):
        kmer = tuple(S[(i+j) % G] for j in range(L))
        spec[kmer] += 1
    return dict(spec)

def is_repeat_free(spec):
    return all(v == 1 for v in spec.values())

def covers_all_positions(S, starts, L):
    G = len(S)
    covered = set()
    for r in starts:
        for offset in range(L):
            covered.add((r + offset) % G)
    return len(covered) == G

def find_all_triple_repeats(S):
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
            from itertools import combinations
            for triple in combinations(starts_list, 3):
                pres = [S[(t - 1) % G] for t in triple]
                posts = [S[(t + ell) % G] for t in triple]
                if len(set(pres)) > 1 and len(set(posts)) > 1:
                    results.append((ell, tuple(sorted(triple)), kmer))
    return results

def find_all_maximal_repeat_pairs(S):
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
            from itertools import combinations
            for pair in combinations(starts_list, 2):
                t1, t2 = pair
                if S[(t1 - 1) % G] != S[(t2 - 1) % G] and S[(t1 + ell) % G] != S[(t2 + ell) % G]:
                    results.append((ell, (t1, t2), kmer))
    return results

def find_all_interleaved_pairs(S):
    repeats = find_all_maximal_repeat_pairs(S)
    results = []
    seen_pairs = set()
    from itertools import combinations
    for i in range(len(repeats)):
        ell1, pos1, kmer1 = repeats[i]
        for j in range(i + 1, len(repeats)):
            ell2, pos2, kmer2 = repeats[j]
            all_four = sorted(set(list(pos1) + list(pos2)))
            if len(all_four) != 4:
                continue
            label = {}
            for p in pos1: label[p] = 0
            for p in pos2: label[p] = 1
            labels_cyclic = [label[p] for p in sorted(all_four)]
            if labels_cyclic in ([0,1,0,1], [1,0,1,0]):
                pk = (ell1, tuple(sorted(pos1)), ell2, tuple(sorted(pos2)))
                if pk not in seen_pairs:
                    seen_pairs.add(pk)
                    results.append(((ell1, tuple(sorted(pos1)), kmer1), (ell2, tuple(sorted(pos2)), kmer2)))
    return results

def check_copy_bridged(S, t, ell, starts, L):
    G = len(S)
    for r in starts:
        rp = set((r + offset) % G for offset in range(L))
        if (t - 1) % G in rp and (t + ell) % G in rp:
            return True
    return False

def check_I_s(S, starts, L):
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

def max_competitor_ratio(S, L, obs, all_specs, all_genomes, s_idx):
    """Find the maximum ratio L(D)/L(S) for any same-length competitor D."""
    obs_support = set(obs.keys())
    candidate_indices = None
    for kmer in obs_support:
        if candidate_indices is None:
            candidate_indices = set(i for i, spec in enumerate(all_specs) if spec.get(kmer, 0) > 0)
        else:
            candidate_indices &= set(i for i, spec in enumerate(all_specs) if spec.get(kmer, 0) > 0)
        if not candidate_indices:
            break
    if not candidate_indices:
        return Fraction(0), None
    candidate_indices.discard(s_idx)

    spec_S = all_specs[s_idx]
    best_ratio = Fraction(1)
    best_competitor = None
    for d_idx in candidate_indices:
        ratio = Fraction(1)
        for kmer, count in obs.items():
            d_S = spec_S.get(kmer, 0)
            d_D = all_specs[d_idx].get(kmer, 0)
            if d_S == 0 or d_D == 0:
                ratio = Fraction(0)
                break
            ratio *= Fraction(d_D, d_S) ** count
        if ratio > best_ratio:
            best_ratio = ratio
            best_competitor = all_genomes[d_idx]
    return best_ratio, best_competitor

def structural_analysis():
    """
    Key structural finding: for repeat-free truths with L=2 and sigma=4,
    characterize exactly when counterexamples exist and their max ratios.
    """
    sigma = 4
    L = 2

    print("=" * 80)
    print("STRUCTURAL ANALYSIS: Repeat-free truths, L=2, sigma=4 (ACGT)")
    print("=" * 80)

    for G in [4, 5, 6]:
        print(f"\n{'='*60}")
        print(f"G = {G}")
        print(f"{'='*60}")

        all_genomes = list(iterproduct(range(sigma), repeat=G))
        all_specs = [spectrum(g, L) for g in all_genomes]

        # Find repeat-free genomes
        repeat_free = []
        for i, spec in enumerate(all_specs):
            if is_repeat_free(spec):
                repeat_free.append(i)

        print(f"  Total genomes: {len(all_genomes)}")
        print(f"  Repeat-free genomes: {len(repeat_free)}")

        # For each repeat-free truth, check what counterexamples exist
        for rf_idx in repeat_free[:5]:  # Show first 5
            S = all_genomes[rf_idx]
            spec_S = all_specs[rf_idx]
            s_str = "".join("ABCD"[c] for c in S)

            # Check: does this truth have any self-loop kmers?
            has_self_loop = any(k[0] == k[1] for k in spec_S.keys())
            kmer_types = list(spec_S.keys())

            # Find max achievable d(k) for each kmer type in this truth
            max_d_for_truth = {}
            for kmer in kmer_types:
                # Find genome with max d(kmer)
                best_d = 0
                for g_idx, spec in enumerate(all_specs):
                    d = spec.get(kmer, 0)
                    if d > best_d:
                        best_d = d
                max_d_for_truth[kmer] = best_d

            print(f"\n  Truth: {s_str}")
            print(f"    Kmer types: {[''.join('ABCD'[c] for c in k) for k in kmer_types]}")
            print(f"    Has self-loop kmers: {has_self_loop}")
            print(f"    Max achievable d(k) per type:")
            for kmer, max_d in max_d_for_truth.items():
                k_str = "".join("ABCD"[c] for c in kmer)
                print(f"      d({k_str}) <= {max_d}")

            # For each I_s-satisfying observation, find counterexamples
            # (Limited to avoid combinatorial explosion)
            N = G  # Use N=G for simplicity
            from itertools import combinations_with_replacement
            max_ratio_overall = Fraction(1)
            n_cex = 0
            n_is = 0

            for starts in combinations_with_replacement(range(G), N):
                starts_list = list(starts)
                if not check_I_s(S, starts_list, L):
                    continue
                n_is += 1
                obs = Counter()
                for r in starts_list:
                    kmer = tuple(S[(r + j) % G] for j in range(L))
                    obs[kmer] += 1

                ratio, comp = max_competitor_ratio(S, L, obs, all_specs, all_genomes, rf_idx)
                if ratio > 1:
                    n_cex += 1
                    if ratio > max_ratio_overall:
                        max_ratio_overall = ratio

            print(f"    I_s-satisfying observations (N={N}): {n_is}")
            print(f"    Counterexamples found: {n_cex}")
            print(f"    Max ratio: {max_ratio_overall}")


def main():
    structural_analysis()

    # Also verify the Eulerian bounds precisely
    print("\n" + "=" * 80)
    print("VERIFICATION: Eulerian bounds for L=2, sigma=4")
    print("=" * 80)

    sigma = 4
    L = 2

    for G in [4, 5, 6, 7, 8]:
        all_genomes = list(iterproduct(range(sigma), repeat=G))
        all_specs = [spectrum(g, L) for g in all_genomes]

        max_d_self = 0
        max_d_het = 0
        for spec in all_specs:
            for kmer, count in spec.items():
                if kmer[0] == kmer[1]:
                    max_d_self = max(max_d_self, count)
                else:
                    max_d_het = max(max_d_het, count)

        print(f"G={G}: max d(self-loop) = {max_d_self} (= G? {max_d_self == G})")
        print(f"       max d(heterologous) = {max_d_het} (= floor(G/2)? {max_d_het == G//2})")
        print(f"       max ratio (self-loop, n=G): {max_d_self**G}")
        print(f"       max ratio (heterologous, n=G): {max_d_het**G}")


if __name__ == "__main__":
    main()
