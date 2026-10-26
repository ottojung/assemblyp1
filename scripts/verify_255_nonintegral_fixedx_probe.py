#!/usr/bin/env python3
"""Exact bounded probe for non-integral fixed-x product-binomial scores.

This is computational evidence only. It exhausts a small finite box and does
not assert a general integer-optimizer classification.
"""

from fractions import Fraction
from itertools import product


def score(candidate, counts, external_n):
    total = sum(counts)
    value = Fraction(1)
    for b, x in zip(candidate, counts):
        value *= Fraction(b) ** x * Fraction(external_n - b) ** (total - x)
    return value


def candidates(dim, external_n, total):
    return (
        point
        for point in product(range(external_n + 1), repeat=dim)
        if sum(point) == total
    )


def maxima(counts, external_n, total):
    feasible = list(candidates(len(counts), external_n, total))
    scored = [(score(point, counts, external_n), point) for point in feasible]
    best = max(value for value, _ in scored)
    return best, tuple(point for value, point in scored if value == best)


def main():
    checked = 0
    strict_nonintegral_cases = 0
    tie_cases = 0
    witness = None
    # N=5, mass=4 and counts summing to four; retain only vectors with a
    # non-integral empirical coordinate x_i*N/n (here equivalently odd x_i).
    for counts in product(range(5), repeat=3):
        if sum(counts) != 4 or not any((x * 5) % 4 for x in counts):
            continue
        best, winners = maxima(counts, 5, 4)
        checked += 1
        tie_cases += len(winners) > 1
        strict_nonintegral_cases += len(winners) == 1
        if witness is None and len(winners) == 1:
            witness = (counts, best, winners[0])

    assert checked > 0
    assert witness is not None
    counts, best, winner = witness
    # Report exact rational score and explicit scope; no floating point used.
    print(f"N=5, dimension=3, candidate mass=4; checked={checked}")
    print(f"unique-max cases={strict_nonintegral_cases}; tie cases={tie_cases}")
    print(f"first unique-max sample x={counts}, score={best}, winner={winner}")
    print("PASS: exhaustive bounded probe; no general classification claimed")


if __name__ == "__main__":
    main()
