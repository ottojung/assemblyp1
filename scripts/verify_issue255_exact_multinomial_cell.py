#!/usr/bin/env python3
"""Exact finite check for issue #255's G=6, L=2 oriented sample cell.

Scope: binary circular genomes of length six; oriented adjacent-pair molecule
types; exact multinomial likelihood with the common multinomial coefficient
omitted. Truth is AAABBB and observed counts are AA=1, AB=0, BA=0, BB=5.
This finite computation does not claim a general characterization.
"""

from collections import Counter
from fractions import Fraction
from itertools import product


def spectrum(genome):
    return Counter((genome[i], genome[(i + 1) % len(genome)])
                   for i in range(len(genome)))


def likelihood_factor(spec, observed, total):
    result = Fraction(1)
    for molecule, count in observed.items():
        result *= Fraction(spec[molecule], total) ** count
    return result


def main():
    truth = tuple("AAABBB")
    observed = {("A", "A"): 1, ("A", "B"): 0,
                ("B", "A"): 0, ("B", "B"): 5}
    candidates = list(product("AB", repeat=6))
    scores = [(genome, likelihood_factor(spectrum(genome), observed, 6))
              for genome in candidates]
    truth_score = dict((genome, score) for genome, score in scores)[truth]
    maximum = max(score for _, score in scores)
    maximizers = {genome for genome, score in scores if score == maximum}
    expected = {tuple(word) for word in ("AABBBB", "ABBBBA", "BBBBAA",
                                         "BBBAAB", "BBAABB", "BAABBB")}

    assert len(candidates) == 64
    assert truth_score == Fraction(1, 729)
    assert maximum == Fraction(1, 192)
    assert maximum / truth_score == Fraction(243, 64)
    assert maximizers == expected
    assert len(maximizers) == 6
    print(f"candidates: {len(candidates)}")
    print(f"truth: {''.join(truth)} likelihood={truth_score}")
    print(f"maximum likelihood={maximum}; ratio={maximum / truth_score}")
    print("maximizers: " + ", ".join(sorted("".join(g) for g in maximizers)))


if __name__ == "__main__":
    main()
