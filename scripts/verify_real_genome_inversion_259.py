#!/usr/bin/env python3
"""Independent exact-rational verification of the #259 ranking-inversion witness.

This script shares no code with the Lean module
``AssemblyP1/Section62BinomialRealGenomeInversion.lean``: the candidate words,
their cyclic 2-mer spectra, and both likelihood expressions are re-derived
here with ``fractions.Fraction`` and brute-force enumeration of all cyclic
start positions.

Scope (identical to the Lean witness): alphabet {0,1}, read length L = 2,
fixed external N = 100, and a single observed read ``00`` (sample size n = 1,
count vector x = (1,0,0,0) over the oriented alphabet (00,01,10,11)).

Candidates (genuine connected circular words):

  A = 0^51 1^49          spectrum (00,01,10,11) = (50,1,1,48)
  B = 0^50 1^18 (01)^16  spectrum (00,01,10,11) = (49,17,17,17)

Checked facts:

  * both words have length 100 and the cyclic 2-mer counts match;
  * both words are connected circular (both 0->1 and 1->0 transitions occur)
    and realize the full oriented 2-mer alphabet;
  * exact joint iid likelihoods (multinomial point probability at n = 1):
    P_A(00) = 50/100 = 1/2  >  P_B(00) = 49/100, so exact ML prefers A;
  * MB09 section 6.1 full-alphabet product of marginal binomials, retaining
    all three zero-count coordinates:
    Lt_A = (50/100)(99/100)^2(52/100) = 127413/500000 = 0.254826
    Lt_B = (49/100)(83/100)^3        = 28017563/100000000 = 0.28017563
    so the section 6.1 surrogate prefers B while the exact joint law prefers
    A (the ranking inversion), cross-checked against the integer numerators
    asserted in Lean: 50, 49, 50*99*99*52, 49*83*83*83.

This is a finite source-model witness only: it does not claim the candidates
satisfy primitive P2 at L = 2, and it does not refute the primitive-P2 positive
theorems.  The section 6.1 sample-uniform maximality question is kept
distinct from the exact joint read law.
"""

from __future__ import annotations

import sys
from fractions import Fraction
from math import comb

N = 100
L = 2
WORD_A = [0] * 51 + [1] * 49
WORD_B = [0] * 50 + [1] * 18 + [0, 1] * 16
ALPHABET = ((0, 0), (0, 1), (1, 0), (1, 1))
OBSERVED = (0, 0)


def circular_spectrum(word: list[int]) -> dict[tuple[int, int], int]:
    """Count oriented L-mers over all cyclic start positions of ``word``."""
    n = len(word)
    counts: dict[tuple[int, int], int] = {}
    for start in range(n):
        lmer = tuple(word[(start + k) % n] for k in range(L))
        counts[lmer] = counts.get(lmer, 0) + 1
    return counts


def binomial_factors(counts: dict[tuple[int, int], int]):
    """Section 6.1 product of marginal binomial factors for n=1, x=OBSERVED.

    Returns the exact rational product
      prod_w C(1, x_w) * p_w^x_w * (1 - p_w)^(1 - x_w),  p_w = d(w)/N,
    over the full oriented alphabet, including every zero-count coordinate.
    """
    total = Fraction(1, 1)
    for w in ALPHABET:
        x_w = 1 if w == OBSERVED else 0
        p = Fraction(counts[w], N)
        total *= comb(1, x_w) * p**x_w * (1 - p) ** (1 - x_w)
    return total


def exact_joint(counts: dict[tuple[int, int], int]) -> Fraction:
    """Exact joint iid (multinomial) likelihood of the single observed read."""
    return Fraction(counts[OBSERVED], N)


def main() -> int:
    failures: list[str] = []

    def check(label: str, condition: bool) -> None:
        if not condition:
            failures.append(label)

    spec_a = circular_spectrum(WORD_A)
    spec_b = circular_spectrum(WORD_B)

    check("len(A) == 100", len(WORD_A) == N)
    check("len(B) == 100", len(WORD_B) == N)
    check("A spectrum == (50,1,1,48)",
          [spec_a[w] for w in ALPHABET] == [50, 1, 1, 48])
    check("B spectrum == (49,17,17,17)",
          [spec_b[w] for w in ALPHABET] == [49, 17, 17, 17])

    for name, spec in (("A", spec_a), ("B", spec_b)):
        check(f"{name} connected (01 and 10 both occur)",
              spec[(0, 1)] > 0 and spec[(1, 0)] > 0)
        check(f"{name} realizes the full oriented alphabet",
              all(spec[w] > 0 for w in ALPHABET))

    exact_a = exact_joint(spec_a)
    exact_b = exact_joint(spec_b)
    check("P_A(00) == 50/100 == 1/2", exact_a == Fraction(50, 100) == Fraction(1, 2))
    check("P_B(00) == 49/100", exact_b == Fraction(49, 100))
    check("exact joint law ranks A strictly above B", exact_b < exact_a)

    lt_a = binomial_factors(spec_a)
    lt_b = binomial_factors(spec_b)
    check("Lt_A == 127413/500000", lt_a == Fraction(127413, 500000))
    check("Lt_B == 28017563/100000000", lt_b == Fraction(28017563, 100000000))
    check("Lt_A == 0.254826", lt_a == Fraction(254826, 1000000))
    check("Lt_B == 0.28017563", lt_b == Fraction(28017563, 100000000))
    check("surrogate ranks B strictly above A", lt_a < lt_b)

    check("surrogate numerator A == 50*99*99*52", lt_a * 10**8 == 50 * 99 * 99 * 52)
    check("surrogate numerator B == 49*83*83*83", lt_b * 10**8 == 49 * 83 * 83 * 83)

    if failures:
        for failure in failures:
            print(f"FAIL: {failure}", file=sys.stderr)
        print(f"FAIL ({len(failures)} checks failed)", file=sys.stderr)
        return 1

    print("OK: circular spectra (50,1,1,48) and (49,17,17,17); "
          "exact joint 1/2 > 49/100; §6.1 surrogate 127413/500000 < 28017563/100000000; "
          "ranking inversion verified with exact rationals")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
