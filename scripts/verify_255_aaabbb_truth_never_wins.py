#!/usr/bin/env python3
"""Exhaust the support-admissible six-read samples for truth AAABBB."""

from fractions import Fraction
from itertools import product


LENGTH = 6
TRUTH = (2, 1, 1, 2)  # AA, AB, BA, BB
SUPPORT = tuple(i for i, count in enumerate(TRUTH) if count)


def histograms(total: int, width: int):
    if width == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in histograms(total - first, width - 1):
            yield (first,) + rest


def score(spectrum: tuple[int, ...], counts: tuple[int, ...]) -> Fraction:
    result = Fraction(1)
    for multiplicity, count in zip(spectrum, counts, strict=True):
        if count:
            if multiplicity == 0:
                return Fraction(0)
            result *= Fraction(multiplicity, LENGTH) ** count
    return result


def main() -> None:
    samples = 0
    truth_maximizers = 0
    max_truth_to_competitor = Fraction(0)
    worst_observation = None
    for active in histograms(LENGTH, len(SUPPORT)):
        observation = [0] * len(TRUTH)
        for edge, count in zip(SUPPORT, active, strict=True):
            observation[edge] = count
        x = tuple(observation)
        truth_score = score(TRUTH, x)
        best = Fraction(0)
        for spectrum in product(range(LENGTH + 1), repeat=4):
            if sum(spectrum) != LENGTH:
                continue
            candidate_score = score(spectrum, x)
            best = max(best, candidate_score)
        samples += 1
        if truth_score == best:
            truth_maximizers += 1
        ratio = best / truth_score
        if ratio > max_truth_to_competitor:
            max_truth_to_competitor = ratio
            worst_observation = x

    assert samples == 84  # compositions of six into four truth-supported types
    assert truth_maximizers == 1
    assert max_truth_to_competitor == Fraction(46656)
    assert worst_observation == (0, 0, 6, 0)
    print(
        "PASS: among 84 support-admissible N=6 samples for S=AAABBB, "
        f"truth maximizes in {truth_maximizers}; largest competitor/truth ratio is "
        f"{max_truth_to_competitor} at x={worst_observation}"
    )


if __name__ == "__main__":
    main()
