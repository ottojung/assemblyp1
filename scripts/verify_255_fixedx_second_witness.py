#!/usr/bin/env python3
"""Exact rational checks for two fixed-x AAABBB likelihood losses."""

from fractions import Fraction


def likelihood(spectrum: tuple[int, ...], counts: tuple[int, ...]) -> Fraction:
    length = sum(spectrum)
    result = Fraction(1)
    for multiplicity, count in zip(spectrum, counts, strict=True):
        result *= Fraction(multiplicity, length) ** count
    return result


truth = (2, 1, 1, 2)  # AAABBB, order AA, AB, BA, BB
candidate = (1, 1, 1, 3)  # AABBBB

for observation, expected_ratio in (
    ((1, 0, 0, 5), Fraction(243, 64)),
    ((1, 0, 1, 4), Fraction(81, 32)),
):
    truth_score = likelihood(truth, observation)
    candidate_score = likelihood(candidate, observation)
    assert candidate_score / truth_score == expected_ratio
    assert candidate_score > truth_score

assert likelihood(truth, (1, 0, 0, 5)) == Fraction(1, 729)
assert likelihood(candidate, (1, 0, 0, 5)) == Fraction(1, 192)
assert likelihood(truth, (1, 0, 1, 4)) == Fraction(1, 1458)
assert likelihood(candidate, (1, 0, 1, 4)) == Fraction(1, 576)
print("PASS: both exact fixed-x likelihood ratios are strictly above one")
