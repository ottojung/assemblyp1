#!/usr/bin/env python3
"""Exact bounded census of circular binary k=2 spectra for issue #259.

Enumerates binary circular words up to rotation, maps each length-L word to
its cyclic k-mer spectrum for k=2 (L >= k), deduplicates spectra, and tests
whether each truth is an ML maximizer at x=A and whether it remains maximal
against every spectrum for every complete-support x >= A in a bounded excess
box. Comparisons use the integer numerator of the MB09 §6.1
fixed-external-N product-binomial objective, including all zero-count classes:

    q_N(B,i) = B_i * product_{j != i}(N-B_j)
    score(B,x) = product_i q_N(B,i)**x_i.

Here N=L is held fixed and x is the complete-support observed count vector,
equal to the truth spectrum. This is only a bounded census, not a general
maximality theorem or a claim about exact multinomial likelihood.
"""

from itertools import combinations, product
from math import prod


def rotation_representatives(length):
    seen = set()
    for word in product(range(2), repeat=length):
        rotations = [word[i:] + word[:i] for i in range(length)]
        canonical = min(rotations)
        if canonical not in seen:
            seen.add(canonical)
            yield canonical


def spectrum(word, k):
    length = len(word)
    classes = 1 << k
    counts = [0] * classes
    for start in range(length):
        code = 0
        for offset in range(k):
            code = 2 * code + word[(start + offset) % length]
        counts[code] += 1
    return tuple(counts)


def q_weights(N, B):
    return tuple(B[i] * prod(N - B[j] for j in range(len(B)) if j != i)
                 for i in range(len(B)))


def score(q, x):
    return prod(qi ** xi for qi, xi in zip(q, x))


def covered_samples(A, max_extra):
    """All x >= A with total excess at most max_extra."""
    m = len(A)
    for extra in range(max_extra + 1):
        # Weak compositions of extra into m observed-count coordinates.
        for cuts in combinations(range(extra + m - 1), m - 1):
            bounds = (-1,) + cuts + (extra + m - 1,)
            delta = tuple(bounds[i + 1] - bounds[i] - 1 for i in range(m))
            yield tuple(a + d for a, d in zip(A, delta))


def run():
    # L=2 and 3 are valid circular k-mer windows too, but the requested
    # nontrivial k=2 spectrum cells are extended through L=16 here.
    rows = []
    for L in range(2, 17):
        spectra = sorted({spectrum(word, 2) for word in rotation_representatives(L)})
        weights = {B: q_weights(L, B) for B in spectra}
        maximal_at_truth_x = []
        max_over_covered_box = []
        for A in spectra:
            truth_score = score(weights[A], A)
            if all(score(weights[B], A) <= truth_score for B in spectra):
                maximal_at_truth_x.append(A)
            if all(score(weights[B], x) <= score(weights[A], x)
                   for x in covered_samples(A, max_extra=8)
                   for B in spectra):
                max_over_covered_box.append(A)
        rows.append((L, len(spectra), len(maximal_at_truth_x),
                     len(max_over_covered_box), max_over_covered_box))
    for L, total, at_truth, covered, maximizers in rows:
        print(f"L={L:2d}: spectra={total:4d}, maximal_at_x=A={at_truth:3d}, "
              f"uniform over x>=A, sum(x-A)<=8={covered:3d}, "
              f"survivors={maximizers}")
    return rows


if __name__ == "__main__":
    run()
