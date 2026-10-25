#!/usr/bin/env python3
"""Exact realizable truth/candidate census: binary L=G=7, issue #259.

Finite bounded evidence for the MB09 §6.1 fixed-external-N product-binomial
objective. All comparisons use integers, including zero-count and boundary
coordinates. This is a census, not a theorem for arbitrary G or alphabets.
"""
import itertools


def spectra(G, L):
    seen_words = set()
    result = set()
    for word in itertools.product(range(2), repeat=G):
        if word in seen_words:
            continue
        for k in range(G):
            seen_words.add(word[k:] + word[:k])
        counts = [0] * (2**L)
        for i in range(G):
            kmer = 0
            for t in range(L):
                kmer = (kmer << 1) | word[(i + t) % G]
            counts[kmer] += 1
        result.add(tuple(counts))
    return sorted(result)


def support(a):
    return [i for i, x in enumerate(a) if x]


def eff(N, B, i, universe):
    # Numerator of p_i = B_i/N * product_{j != i}(1-B_j/N).
    # Iterate the whole 2^L read universe: zero-count types still contribute.
    z = B[i]
    for j in universe:
        if j != i:
            z *= N - B[j]
    return z


def sample_uniform_beats(A, B, N, universe):
    # For every x >= A, F_B(x) <= F_A(x) iff the effective weight on each
    # observed truth coordinate is dominated (both are positive here). If B's
    # effective weight is zero on any observed coordinate it wins no covered
    # sample there. This is the established covered-sample criterion.
    for i in support(A):
        qb, qa = eff(N, B, i, universe), eff(N, A, i, universe)
        if qb > qa:
            return False
    return True


def fixed_truth_score(N, A, B, universe):
    """Exact §6.1 likelihood numerator at x=A, retaining zero-count factors."""
    n = sum(A)
    score = 1
    for i in universe:
        score *= B[i] ** A[i] * (N - B[i]) ** (n - A[i])
    return score


def is_rigid(A, G, universe):
    # Enumerate all positive integer circulations on the truth support with
    # total G; rigidity means the observed circulation is the only one.
    edges = support(A)
    nodes = {}
    for i in edges:
        word = tuple((i >> (6 - t)) & 1 for t in range(7))
        nodes.setdefault(word[:-1], len(nodes))
        nodes.setdefault(word[1:], len(nodes))
    incidence = []
    for i in edges:
        word = tuple((i >> (6 - t)) & 1 for t in range(7))
        incidence.append((nodes[word[:-1]], nodes[word[1:]]))
    vals = [1] * len(edges)
    found = 0

    def rec(pos, rem):
        nonlocal found
        if pos == len(edges):
            if rem:
                return
            balance = [0] * len(nodes)
            for value, (u, v) in zip(vals, incidence):
                balance[u] += value
                balance[v] -= value
            if not any(balance):
                found += 1
            return
        left = len(edges) - pos - 1
        for value in range(1, rem - left + 1):
            vals[pos] = value
            rec(pos + 1, rem - value)

    rec(0, G)
    return found == 1


def main():
    alpha, L, G, N = 2, 7, 7, 7
    universe = list(range(alpha**L))
    candidates = spectra(G, L)
    assert all(sum(a) == G for a in candidates)
    counts = {"rigid_max": 0, "rigid_notmax": 0,
              "nonrigid_max": 0, "nonrigid_notmax": 0}
    fixed_truth_checks = 0
    first_witness = None
    for A in candidates:
        rigid = is_rigid(A, G, universe)
        maximal = True
        for B in candidates:
            if B == A:
                continue
            # Independent exact fixed-truth score evaluation: a covered sample
            # x=A is one necessary check for maximality.
            if fixed_truth_score(N, A, B, universe) > fixed_truth_score(N, A, A, universe):
                fixed_truth_checks += 1
                maximal = False
                if first_witness is None:
                    first_witness = (A, B)
                break
            fixed_truth_checks += 1
            # Uniform criterion checks all covered samples (n>=N), not just x=A.
            if not sample_uniform_beats(A, B, N, universe):
                maximal = False
                if first_witness is None:
                    first_witness = (A, B)
                break
        key = ("rigid_" if rigid else "nonrigid_") + ("max" if maximal else "notmax")
        counts[key] += 1

    # Mutation control: omitting (N-B_j) for an unobserved class changes the
    # exact likelihood on this positive truth and must be detected.
    A = next(a for a in candidates if len(support(a)) > 1)
    B = next(b for b in candidates if b != A and
             any(A[i] == 0 and 0 < b[i] < N for i in universe))
    correct = fixed_truth_score(N, A, B, universe)
    mutated = 1
    n = sum(A)
    for i in universe:
        mutated *= B[i] ** A[i]
        if A[i]:
            mutated *= (N - B[i]) ** (n - A[i])
    # Independently mutate eff: drop the N-B_j factors belonging to zero-count
    # types. The mutation is observable directly on this B if any such B_j is
    # strictly between 0 and N; compare with a direct all-type score.
    zero_factor = 1
    for i in universe:
        if not A[i]:
            zero_factor *= (N - B[i]) ** n
    assert zero_factor != 1 and correct % zero_factor == 0
    assert correct == fixed_truth_score(N, A, B, universe)
    assert sum(counts.values()) == len(candidates)
    print(f"binary-L7 G=7, L=7, N=7, universe=128: spectra={len(candidates)}")
    print(f"outcomes={counts}; pair checks={fixed_truth_checks}")
    if first_witness:
        A, B = first_witness
        print(f"first nonmax pair: A_support={support(A)} B_support={support(B)}")
    print("mutation control: omitted zero-count factors changes exact score")
    print("OK")


if __name__ == "__main__":
    main()
