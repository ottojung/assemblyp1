#!/usr/bin/env python3
"""Exact realizable census: binary L=G=8, issue #259.

All likelihood comparisons use integer products over all 256 k-mer types.
This is finite computational evidence, not a general theorem.
"""
import itertools


def spectra(G, L):
    seen_words, result = set(), set()
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


def score(N, A, B, universe):
    n = sum(A)
    value = 1
    for e in universe:
        value *= B[e] ** A[e] * (N - B[e]) ** (n - A[e])
    return value


def effective(N, B, e, universe):
    value = B[e]
    for j in universe:
        if j != e:
            value *= N - B[j]
    return value


def sample_uniform_beats(A, B, N, universe):
    """Decide F_B(x)<=F_A(x) for every integer x>=A, exactly.

    If every truth-supported effective numerator for B is <= A's, then each
    factor ratio is at most one. Conversely, if one is greater, increasing
    that coordinate's count makes the likelihood ratio unbounded above.
    A zero effective numerator is handled as a losing (zero likelihood)
    candidate, including probability-boundary cases.
    """
    for e in support(A):
        qb = effective(N, B, e, universe)
        qa = effective(N, A, e, universe)
        if qb > qa:
            return False
    return True


def is_rigid(A, L, G):
    edges = support(A)
    nodes = {}
    for e in edges:
        w = tuple((e >> (L - 1 - t)) & 1 for t in range(L))
        nodes.setdefault(w[:-1], len(nodes))
        nodes.setdefault(w[1:], len(nodes))
    incidence = []
    for e in edges:
        w = tuple((e >> (L - 1 - t)) & 1 for t in range(L))
        incidence.append((nodes[w[:-1]], nodes[w[1:]]))
    values, count = [1] * len(edges), 0

    def visit(pos, remaining):
        nonlocal count
        if pos == len(edges):
            if remaining:
                return
            balance = [0] * len(nodes)
            for value, (u, v) in zip(values, incidence):
                balance[u] += value
                balance[v] -= value
            if not any(balance):
                count += 1
            return
        left = len(edges) - pos - 1
        for value in range(1, remaining - left + 1):
            values[pos] = value
            visit(pos + 1, remaining - value)

    visit(0, G)
    return count == 1


def main():
    L = G = N = 8
    universe = list(range(2**L))
    candidates = spectra(G, L)
    assert len(candidates) == 36 and all(sum(a) == G for a in candidates)
    result = {"rigid_max": 0, "rigid_notmax": 0,
              "nonrigid_max": 0, "nonrigid_notmax": 0}
    pairs = fixed_checks = uniform_checks = 0
    for A in candidates:
        rigid = is_rigid(A, L, G)
        maximal = True
        for B in candidates:
            if B == A:
                continue
            pairs += 1
            # At x=A (n=G), the literal MB09 §6.1 product-binomial score
            # includes every unobserved type's (N-B[e])**n factor.
            if score(N, A, B, universe) > score(N, A, A, universe):
                fixed_checks += 1
                maximal = False
                break
            fixed_checks += 1
            uniform_checks += 1
            if not sample_uniform_beats(A, B, N, universe):
                maximal = False
                break
        result[("rigid_" if rigid else "nonrigid_") + ("max" if maximal else "notmax")] += 1

    # Non-vacuous mutation control: choose a truth with support >1 and a
    # realizable competitor placing an intermediate count on an unobserved
    # coordinate. Deleting all such factors must change its score.
    A = next(a for a in candidates if len(support(a)) > 1)
    B = next(b for b in candidates if b != A and any(
        A[e] == 0 and 0 < b[e] < N for e in universe))
    exact = score(N, A, B, universe)
    omitted_zero_counts = 1
    n = sum(A)
    for e in universe:
        omitted_zero_counts *= B[e] ** A[e]
        if A[e] > 0:
            omitted_zero_counts *= (N - B[e]) ** (n - A[e])
    omitted_factor = 1
    for e in universe:
        if A[e] == 0:
            omitted_factor *= (N - B[e]) ** n
    assert omitted_factor > 1 and exact == omitted_zero_counts * omitted_factor
    assert sum(result.values()) == len(candidates)
    print(f"binary L=G=N=8, universe=256, spectra={len(candidates)}")
    assert pairs == len(candidates) * (len(candidates) - 1)
    print(f"truth/competitor pairs={pairs}")
    print(f"outcomes={result}; fixed-truth checks={fixed_checks}; covered-uniform checks={uniform_checks}")
    print(f"mutation control: A_support={len(support(A))}, B_unobserved_intermediate=True")
    print("All scores are exact integer products; OK")


if __name__ == "__main__":
    main()
