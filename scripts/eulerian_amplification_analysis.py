#!/usr/bin/env python3
"""
Eulerian amplification analysis: characterize the maximum achievable
d_D(k) for a given kmer type k on a circular genome of length G.

For a repeat-free truth where d_S(k) = 1, the ML ratio for a
concentrated sample {k:n} is d_D(k)^n. The maximum ratio is thus
determined by max d_D(k) over all achievable d-vectors.

An occurrence vector d is achievable iff:
1. sum_i d(i) = G
2. d(i) >= 0 for all i
3. Eulerian balance on B(Sigma, L-1)

For L=2, the Eulerian constraint is: for each character a in Sigma,
  sum_b d(a,b) = sum_b d(b,a)

We solve this as a linear program (maximize d(k) subject to constraints).
"""
from fractions import Fraction
from itertools import product as iterproduct
from collections import defaultdict

def eulerian_max_dk(G, L, sigma, target_kmer):
    """
    Compute the maximum possible d_D(target_kmer) for a circular genome
    of length G with L-mers over an alphabet of size sigma.

    Uses exact integer linear programming via enumeration for small instances.
    For L=2, we enumerate all achievable d-vectors.
    """
    # For L=2, k-mers are pairs (a,b), and Eulerian balance is:
    # for each char c: sum_b d(c,b) = sum_b d(b,c)

    if L == 2:
        n_types = sigma * sigma
        # We want to maximize d(target_kmer) subject to:
        # sum d = G, d >= 0, Eulerian balance

        # The Eulerian polytope for L=2 over sigma symbols:
        # Variables: d_{(a,b)} for a,b in range(sigma)
        # Constraints:
        #   sum_{a,b} d_{(a,b)} = G
        #   for each c: sum_b d_{(c,b)} = sum_b d_{(b,c)}
        #   d_{(a,b)} >= 0

        # For small G, enumerate all integer solutions.
        # Use dynamic programming approach.

        target = target_kmer  # tuple of length L
        target_idx = target[0] * sigma + target[1]

        # Generate all integer vectors d with sum = G
        # This is too expensive for large sigma^L, so use LP relaxation.
        # For L=2, sigma=4: 16 variables, manageable via LP.

        # Actually, let's use a smarter approach:
        # For L=2, the Eulerian polytope has dimension sigma^2 - sigma.
        # The extreme points are Eulerian flows of value G on the complete
        # directed graph on sigma vertices.

        # The maximum d(target) is achieved at an extreme point.
        # For a self-loop (a,a), the max is G (genome = a^G).
        # For a heterologous pair (a,b) with a != b, the max is G - (sigma-1)
        # (repeat (a,b) as many times as possible, fill remaining with
        # a chain through other symbols).

        # Let's verify this with exact enumeration for small cases.
        if target[0] == target[1]:
            # Self-loop: can achieve d = G by genome a^G
            return G
        else:
            # Heterologous: need to balance in/out degrees at a and b
            # and at all other sigma-2 symbols.
            # Minimum fill: need at least 1 edge entering a from non-b,
            # and 1 edge leaving b to non-a.
            # For sigma=2: max d(a,b) = G (when G even, ABAB...)
            # For sigma>=3: max d(a,b) = G - (sigma - 1) ? Not quite.

            # Let's enumerate for small G.
            max_d = 0

            # For sigma=2: A,B
            # d(A,A) + d(A,B) = d(A,A) + d(B,A)  [Eulerian at A]
            # => d(A,B) = d(B,A)
            # d(B,A) + d(B,B) = d(A,B) + d(B,B)  [Eulerian at B]
            # => d(B,A) = d(A,B)  (same equation)
            # So d(A,B) = d(B,A) = m, d(A,A) = a, d(B,B) = b
            # a + b + 2m = G
            # max m = floor(G/2)

            if sigma == 2:
                return G // 2  # floor(G/2)

            # For sigma >= 3, enumerate.
            # Use DP over the de Bruijn graph.
            # For L=2, vertices are characters, edges are 2-mers.
            # Eulerian flow: out(c) = in(c) for all c.
            # Total flow = G.

            # Simple enumeration: distribute G edges among sigma^2 types
            # with Eulerian balance. Use recursive enumeration with pruning.

            # For sigma=3, G up to ~8: sigma^2 = 9 types, G edges.
            # Stars and bars: C(G+8, 8) solutions, filter by Eulerian.
            # For G=8: C(16,8) = 12870, feasible.

            def gen_flows(remaining, vertex, flows):
                """Generate all Eulerian flows with remaining = G - sum(flows)."""
                if vertex == sigma:
                    if remaining == 0:
                        yield flows[:]
                    return

                # For vertex 'vertex': out(v) = sum_b d(v,b), in(v) = sum_b d(b,v)
                # We need out(v) = in(v) for all v.

                # Use a DP approach: track the "excess" at each vertex.
                # excess(v) = out(v) - in(v) so far.
                pass

            # Simpler approach: enumerate all d-vectors with sum G
            # and check Eulerian balance. For sigma=3, G<=8, this is feasible.

            if sigma == 3 and G <= 10:
                # 9 variables, sum = G. Stars and bars: C(G+8,8).
                # For G=8: C(16,8) = 12870.
                from itertools import combinations_with_replacement

                # Generate all non-negative integer vectors summing to G
                # with 9 components.
                n = sigma * sigma

                # Use a different approach: generate all genomes directly
                # and compute their spectra.
                best_d = 0
                for genome in iterproduct(range(sigma), repeat=G):
                    spec = defaultdict(int)
                    for i in range(G):
                        kmer = tuple(genome[(i+j) % G] for j in range(L))
                        spec[kmer] += 1
                    d_target = spec.get(target, 0)
                    if d_target > best_d:
                        best_d = d_target

                return best_d

            elif sigma == 4 and G <= 8:
                # 16 variables, G up to 8.
                # Stars and bars: C(G+15,15). For G=8: C(23,15) = 490314.
                # Too many. Enumerate genomes instead.
                best_d = 0
                for genome in iterproduct(range(sigma), repeat=G):
                    spec = defaultdict(int)
                    for i in range(G):
                        kmer = tuple(genome[(i+j) % G] for j in range(L))
                        spec[kmer] += 1
                    d_target = spec.get(target, 0)
                    if d_target > best_d:
                        best_d = d_target

                return best_d

    return None


def analyze_amplification_bounds():
    """Analyze maximum amplification for various (G, L, sigma) combinations."""
    print("=" * 70)
    print("Eulerian Amplification Bounds Analysis")
    print("=" * 70)

    # For L=2, analyze sigma=2,3,4
    for sigma in [2, 3, 4]:
        print(f"\n--- Sigma = {sigma} ---")
        for G in range(4, 9):
            results = []
            # Analyze self-loops and heterologous pairs
            if L == 2:
                # Self-loop (0,0): max d = G
                results.append(((0,0), G))

                # Heterologous (0,1): depends on sigma and G
                if sigma == 2:
                    max_het = G // 2
                    results.append(((0,1), max_het))
                elif sigma == 3 and G <= 10:
                    # Enumerate genomes
                    best_het = 0
                    for genome in iterproduct(range(sigma), repeat=G):
                        spec = defaultdict(int)
                        for i in range(G):
                            kmer = tuple(genome[(i+j) % G] for j in range(2))
                            spec[kmer] += 1
                        d_target = spec.get((0,1), 0)
                        if d_target > best_het:
                            best_het = d_target
                    results.append(((0,1), best_het))
                elif sigma == 4 and G <= 8:
                    best_het = 0
                    for genome in iterproduct(range(sigma), repeat=G):
                        spec = defaultdict(int)
                        for i in range(G):
                            kmer = tuple(genome[(i+j) % G] for j in range(2))
                            spec[kmer] += 1
                        d_target = spec.get((0,1), 0)
                        if d_target > best_het:
                            best_het = d_target
                    results.append(((0,1), best_het))

            for kmer, max_d in results:
                kmer_str = "".join(str(c) for c in kmer)
                print(f"  G={G}, kmer={kmer_str}: max d = {max_d}, "
                      f"max ratio for sample n = {max_d}^n")


def enumerate_achievable_vectors(G, L, sigma):
    """
    Enumerate all achievable d-vectors for circular genomes of length G.
    Returns a set of tuples (d_vector_as_dict, genome_string).
    """
    specs = set()
    for genome in iterproduct(range(sigma), repeat=G):
        spec = defaultdict(int)
        for i in range(G):
            kmer = tuple(genome[(i+j) % G] for j in range(L))
            spec[kmer] += 1
        spec_key = tuple(sorted(spec.items()))
        if spec_key not in specs:
            specs.add(spec_key)
    return specs


def find_max_amplification_exhaustive(G, L, sigma):
    """
    For each kmer type k, find the maximum d(k) over all achievable
    d-vectors for circular genomes of length G.

    Returns dict: kmer -> max_d
    """
    max_d = defaultdict(int)
    for genome in iterproduct(range(sigma), repeat=G):
        spec = defaultdict(int)
        for i in range(G):
            kmer = tuple(genome[(i+j) % G] for j in range(L))
            spec[kmer] += 1
        for kmer, count in spec.items():
            if count > max_d[kmer]:
                max_d[kmer] = count
    return dict(max_d)


def ratio_table():
    """
    Compute and display the ratio table: for each (G, L, sigma, kmer type),
    what is the max achievable d(k), and hence the max ratio for sample {k:n}?
    """
    print("\n" + "=" * 70)
    print("MAX AMPLIFICATION TABLE: d_D(k) for repeat-free truth (d_S(k)=1)")
    print("Ratio = d_D(k)^n for concentrated sample {k:n}")
    print("=" * 70)

    for sigma in [2, 3, 4]:
        alphabet = "ABCD"[:sigma]
        print(f"\n--- Alphabet size {sigma}: {{{', '.join(alphabet)}}} ---")
        print(f"{'G':>4} | {'L':>2} | {'Self-loop max':>14} | {'Heterologous max':>16} | {'Max ratio n=2':>13} | {'Max ratio n=G':>13}")
        print("-" * 75)
        for G in range(4, 9):
            for L in [2, 3]:
                if L > G:
                    continue
                max_d_self = find_max_amplification_exhaustive(G, L, sigma)
                # Find max for self-loop (first kmer type with a==b)
                self_loop_kmer = None
                het_kmer = None
                for kmer in sorted(max_d_self.keys()):
                    if kmer[0] == kmer[1] and self_loop_kmer is None:
                        self_loop_kmer = kmer
                    elif kmer[0] != kmer[1] and het_kmer is None:
                        het_kmer = kmer

                self_max = max_d_self.get(self_loop_kmer, 0) if self_loop_kmer else 0
                het_max = max_d_self.get(het_kmer, 0) if het_kmer else 0
                overall_max = max(max_d_self.values()) if max_d_self else 0

                print(f"{G:>4} | {L:>2} | {self_max:>14} | {het_max:>16} | {overall_max**2:>13} | {overall_max**G:>13}")


def main():
    ratio_table()

    # Detailed analysis for specific cases
    print("\n" + "=" * 70)
    print("DETAILED: Max d(k) per kmer type for sigma=4 (ACGT), L=2")
    print("=" * 70)

    for G in [4, 5, 6, 7, 8]:
        max_d = find_max_amplification_exhaustive(G, 2, 4)
        print(f"\nG={G}:")
        for kmer in sorted(max_d.keys()):
            kmer_str = "".join("ABCD"[c] for c in kmer)
            print(f"  d({kmer_str}) <= {max_d[kmer]}")
        overall = max(max_d.values())
        print(f"  Overall max d(k) = {overall}")
        print(f"  Max ratio for concentrated sample n=2: {overall**2}")
        print(f"  Max ratio for concentrated sample n=G: {overall**G}")


if __name__ == "__main__":
    main()
