#!/usr/bin/env python3
"""Exact rational check for a second fixed-x AAABBB likelihood loss."""

from fractions import Fraction


def likelihood(spectrum: tuple[int, ...], counts: tuple[int, ...]) -> Fraction:
    length = sum(spectrum)
    result = Fraction(1)
    for multiplicity, count in zip(spectrum, counts, strict=True):
        result *= Fraction(multiplicity, length) ** count
    return result


truth = (2, 1, 1, 2)  # AAABBB, oriented pair order AA, AB, BA, BB
candidate = (1, 1, 1, 3)  # AABBBB
observation = (1, 0, 1, 4)  # six oriented reads, all on truth support

truth_score = likelihood(truth, observation)
candidate_score = likelihood(candidate, observation)
ratio = candidate_score / truth_score

assert truth_score == Fraction(1, 1458)
assert candidate_score == Fraction(1, 576)
assert ratio == Fraction(81, 32)

# Cross-check the earlier fixed-x certificate: AABBBB has three BB edges.
first_observation = (1, 0, 0, 5)
first_truth_score = likelihood(truth, first_observation)
first_candidate_score = likelihood(candidate, first_observation)
assert first_truth_score == Fraction(1, 729)
assert first_candidate_score == Fraction(1, 192)
assert first_candidate_score / first_truth_score == Fraction(243, 64)
print(
    "PASS: S=AAABBB, D=AABBBB, x=(1,0,1,4): "
    f"P(S;x)={truth_score}, P(D;x)={candidate_score}, ratio={ratio}; "
    "cross-check x=(1,0,0,5) ratio=243/64"
)
