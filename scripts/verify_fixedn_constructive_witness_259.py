#!/usr/bin/env python3
"""Exact regression census for the scoped finite product-binomial witness.

Candidate vectors use the same fixed positive support and total G.
N is an external, candidate-independent integer >= G.  This tests
algebraic scores, *not* the general bidirected MB09 flow candidate set.
"""

from itertools import combinations
from math import prod


def positive_spectra(G, k):
    for cuts in combinations(range(1, G), k - 1):
        coordinates = tuple(
            right - left
            for left, right in zip((0, *cuts), (*cuts, G))
        )
        yield coordinates


def q_weights(N, C):
    return tuple(
        c * prod(N - C[j] for j in range(len(C)) if j != i)
        for i, c in enumerate(C)
    )


def score(q, x):
    return prod(w**count for w, count in zip(q, x))


def check(G, N, A, B):
    T = sum(b * (N - b) for b in B)
    x = tuple(b * (T + (N - G) * (N - b)) for b in B)
    n = N * T
    assert sum(x) == n
    assert 0 < T and all(0 < xi < n for xi in x)
    assert all(a <= G * xi for a, xi in zip(A, x))
    assert score(q_weights(N, B), x) > score(q_weights(N, A), x)
    k = G
    x_scaled = tuple(k * xi for xi in x)
    assert sum(x_scaled) == k * n
    assert score(q_weights(N, B), x_scaled) > score(q_weights(N, A), x_scaled)


def main():
    cases = 0
    for k in range(2, 5):
        for G in range(k, 9):
            spectra = list(positive_spectra(G, k))
            for N in (G, G + 1, G + 3):
                for A in spectra:
                    for B in spectra:
                        if A == B:
                            continue
                        check(G, N, A, B)
                        cases += 1
    print(f"PASS {cases} exact fixed-N constructive witnesses")


if __name__ == "__main__":
    main()
