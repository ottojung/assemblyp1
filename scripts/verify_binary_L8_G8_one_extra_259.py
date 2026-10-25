#!/usr/bin/env python3
"""Exact covered-sample extension probe for binary L=G=N=8 spectra.

For every realizable truth A, competitor B, and supported coordinate i, test
the complete-support sample x=A+1_i (so n=N+1) against the literal MB09 §6.1
fixed-external-N product-binomial objective.  The check includes all 256
coordinates, including x_e=0 coordinates, and independently compares its
integer numerator with the effective-weight product.  This is a finite
identity/evidence check, not a new general theorem.
"""

import itertools


def spectra(G, L):
    seen, result = set(), set()
    for word in itertools.product(range(2), repeat=G):
        if word in seen:
            continue
        seen.update(word[k:] + word[:k] for k in range(G))
        counts = [0] * (2**L)
        for i in range(G):
            edge = 0
            for t in range(L):
                edge = (edge << 1) | word[(i + t) % G]
            counts[edge] += 1
        result.add(tuple(counts))
    return sorted(result)


def literal_score(N, B, x):
    n = sum(x)
    value = 1
    for e in range(len(B)):
        value *= B[e] ** x[e] * (N - B[e]) ** (n - x[e])
    return value


def effective_weight(N, B, e):
    value = B[e]
    for j in range(len(B)):
        if j != e:
            value *= N - B[j]
    return value


def effective_product(N, B, x):
    value = 1
    for e, count in enumerate(x):
        value *= effective_weight(N, B, e) ** count
    return value


def main():
    N = 8
    candidates = spectra(N, N)
    assert len(candidates) == 36
    comparisons = 0
    extra_samples = 0
    for A in candidates:
        support = [e for e, count in enumerate(A) if count]
        for B in candidates:
            for i in support:
                x = list(A)
                x[i] += 1
                x = tuple(x)
                assert sum(x) == N + 1
                direct = literal_score(N, B, x)
                factored = effective_product(N, B, x)
                assert direct == factored, (A, B, i, direct, factored)
                comparisons += 1
                extra_samples += 1

    # Explicit mutation control: a zero-count coordinate contributes its
    # failure factor (N-B[e])**n.  The chosen B has an intermediate count at
    # such a coordinate, so omitting these coordinates changes the score.
    A = (2, 1, 1, 0)
    B = (1, 1, 1, 1)
    x = list(A)
    x[next(e for e, count in enumerate(A) if count)] += 1
    x = tuple(x)
    mutation_N = sum(A)
    full = literal_score(mutation_N, B, x)
    omit_zero_count_failures = 1
    n = sum(x)
    for e in range(len(A)):
        omit_zero_count_failures *= B[e] ** x[e]
        if A[e] > 0:
            omit_zero_count_failures *= (mutation_N - B[e]) ** (n - x[e])
    assert full != omit_zero_count_failures
    print(f"binary L=G=N=8, spectra={len(candidates)}, universe=256")
    print(f"A,B,supported-coordinate one-extra samples checked={extra_samples}; exact numerator identities={comparisons}")
    print(f"mutation control: L=2,G=N=4, A={A}, B={B}; omitting zero-count failure factors changes score (n={n})")
    print("All checks use integer arithmetic; OK")


if __name__ == "__main__":
    main()
