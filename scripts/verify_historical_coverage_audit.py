#!/usr/bin/env python3
"""Independent executable checks for the historical finite read-coverage model.

Shomorony et al. (2016), author-hosted supplement, section 6.4 Definition 1:
https://web.stanford.edu/~gkamath/nsgIlan.pdf

This is NOT a Lean proof or a replacement for SourceFaithfulIs.Covers. It
checks both separately, with exact arithmetic for a proposed ML witness.
"""

from collections import Counter
from fractions import Fraction
from itertools import product


def circular_words(genome: str, length: int) -> list[str]:
    assert 2 <= length <= len(genome)
    return [
        "".join(genome[(start + offset) % len(genome)] for offset in range(length))
        for start in range(len(genome))
    ]


def sampled_base_coverage(genome: str, length: int, starts: list[int]) -> bool:
    """Existing model: the ACTUAL sampled placements cover every genome base."""
    g = len(genome)
    return all(
        any((r + offset) % g == base for r in starts for offset in range(length))
        for base in range(g)
    )


def matching_positions(genome: str, length: int, starts: list[int]) -> set[int]:
    """All locations whose words match an OBSERVED type, not only sample starts."""
    words = circular_words(genome, length)
    observed = {words[r] for r in starts}
    return {r for r, word in enumerate(words) if word in observed}


def historical_uncovered(genome: str, length: int, starts: list[int]) -> list[int]:
    """Source Definition 1: each interval of L-1 starts contains a word match."""
    g = len(genome)
    matches = matching_positions(genome, length, starts)
    return [
        t for t in range(g)
        if not any((t + delta) % g in matches for delta in range(length - 1))
    ]


def multinomial_score(genome: str, length: int, observations: Counter[str]) -> Fraction:
    """Candidate-intrinsic exact ordered-sample score, excluding a common factor."""
    g = len(genome)
    spectrum = Counter(circular_words(genome, length))
    value = Fraction(1)
    for word, multiplicity in observations.items():
        value *= Fraction(spectrum[word], g) ** multiplicity
    return value


def binomial_score(
    genome: str,
    length: int,
    observations: Counter[str],
    external_length: int,
    alphabet: str,
) -> Fraction:
    """Literal product of binomial marginals, including zero-count type factors.

    Common combinatorial coefficients cancel from the candidate likelihood ratio.
    """
    spectrum = Counter(circular_words(genome, length))
    n = sum(observations.values())
    value = Fraction(1)
    for chars in product(alphabet, repeat=length):
        word = "".join(chars)
        count = observations[word]
        frequency = Fraction(spectrum[word], external_length)
        assert 0 <= frequency <= 1
        value *= frequency ** count * (1 - frequency) ** (n - count)
    return value


def main() -> None:
    # (name, truth genome, L, sampled starts with multiplicity, old, historical)
    cases = [
        ("repeat-matching beats placements", "AAAA", 3, [0], False, True),
        ("separated reads cover bases only", "ACGT", 2, [0, 2], True, False),
        ("old fixed-length exact", "AAABB", 3, [0, 1, 4], True, False),
        ("old fixed-length binomial", "AAACC", 3, [0, 1, 4], True, False),
        ("old primitive witness", "AABB", 2, [1, 3], True, False),
        ("old oriented variable witness", "AAATT", 3, [0, 1, 4], True, False),
        ("genuine molecule flow, same length", "AAATAT", 3, [0, 0, 1, 3, 5], True, True),
        ("per-occurrence molecule flow", "ATATACAC", 3, [1, 3, 4, 5, 6, 7], True, True),
        ("oriented variable length, dense", "AAATT", 3, [0, 0, 1, 2, 3, 4], True, True),
        ("new unrestricted oriented ML", "AAABBABB", 3, list(range(8)) + [0] * 4, True, True),
    ]
    for name, truth, length, starts, old, historical in cases:
        assert all(0 <= r < len(truth) for r in starts)
        old_result = sampled_base_coverage(truth, length, starts)
        bad = historical_uncovered(truth, length, starts)
        assert old_result == old, (name, "old coverage", old_result, old)
        assert (not bad) == historical, (name, "historical coverage", bad)
        print(
            f"{name}: sampled_base={old_result}, historical={not bad}, "
            f"matching_starts={sorted(matching_positions(truth, length, starts))}, "
            f"uncovered_intervals={bad}"
        )

    truth, competitor, length = "AAABBABB", "AAAABABB", 3
    starts = list(range(8)) + [0] * 4
    observations = Counter(circular_words(truth, length)[r] for r in starts)
    old = multinomial_score(truth, length, observations)
    new = multinomial_score(competitor, length, observations)
    exact_ratio = new / old
    assert exact_ratio == Fraction(2), exact_ratio

    b_old = binomial_score(truth, length, observations, 8, "AB")
    b_new = binomial_score(competitor, length, observations, 8, "AB")
    binomial_ratio = b_new / b_old
    assert binomial_ratio == Fraction(
        1341068619663964900807, 448762029294263205888
    ), binomial_ratio

    # The competing genome contains an UNOBSERVED ABA window: §6.2 support
    # equality fails; this witness is for unrestricted circular candidates.
    assert "ABA" not in observations
    assert "ABA" in circular_words(competitor, length)
    assert not historical_uncovered(truth, length, starts)
    print(f"oriented exact ML competitor/truth = {exact_ratio}")
    print(f"fixed-N binomial competitor/truth = {binomial_ratio} "
          f"(approx. {float(binomial_ratio):.12f})")
    print("PASS: all historical coverage fixtures and exact-rational checks")


if __name__ == "__main__":
    main()
