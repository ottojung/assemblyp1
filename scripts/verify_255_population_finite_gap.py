#!/usr/bin/env python3
"""Exact rational check of a population-ML / fixed-sample-ML separation.

This checks the two-type example recorded in docs/population-finite-gap-255.md.
The comparison uses the candidate-dependent exact multinomial likelihood
product p_i ** x_i; the multinomial coefficient cancels between candidates.
"""

from fractions import Fraction
from math import prod


def likelihood(probabilities: tuple[Fraction, ...], counts: tuple[int, ...]) -> Fraction:
    return prod(p**x for p, x in zip(probabilities, counts, strict=True))


def population_score_ratio(
    truth: tuple[Fraction, ...], candidate: tuple[Fraction, ...]
) -> Fraction:
    """Exact rational for the likelihood-ratio base; its log is the score gap."""
    return prod((p / t) ** t.numerator for p, t in zip(candidate, truth, strict=True))


def main() -> None:
    truth = (Fraction(1, 2), Fraction(1, 2))
    competitor = (Fraction(1, 4), Fraction(3, 4))
    counts = (1, 3)

    # Population: score(candidate) - score(truth) = log(sqrt(3)/2) < 0.
    pop_ratio_base = population_score_ratio(truth, competitor)
    assert pop_ratio_base == Fraction(3, 4) < 1

    # Fixed sample: exact likelihood(candidate; x) / likelihood(truth; x) = 27/16 > 1.
    sample_ratio = likelihood(competitor, counts) / likelihood(truth, counts)
    assert sample_ratio == Fraction(27, 16) > 1

    # Same truth distribution, different admissible samples can favor the truth.
    truth_favoring_counts = (3, 1)
    reverse_ratio = likelihood(competitor, truth_favoring_counts) / likelihood(
        truth, truth_favoring_counts
    )
    assert reverse_ratio == Fraction(3, 16) < 1

    print(f"population score-ratio base (log is the score gap): {pop_ratio_base}")
    print(f"sample x={counts} competitor/truth likelihood ratio: {sample_ratio}")
    print(f"sample x={truth_favoring_counts} competitor/truth likelihood ratio: {reverse_ratio}")


if __name__ == "__main__":
    main()
