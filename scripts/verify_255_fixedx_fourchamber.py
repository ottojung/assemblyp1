#!/usr/bin/env python3
"""Exact check of the fixed-x four-chamber iff regimes (AAABBB instance).

Oriented same-length model, S=AAABBB (G=6, L=2), types ordered (AA,AB,BA,BB).
Mirrors kernel-checked FixedXExactML: fixedX_four_chamber_iff_258,
fixedX_unique_at_xWin258, fixedX_top_tie_at_xTie258,
fixedX_strict_loss_at_xLose258 (decide-closed integer comparisons).
"""

from fractions import Fraction
import math

def lik_product(spectrum, counts):
    return math.prod(m**c for m, c in zip(spectrum, counts, strict=True))

def likelihood(spectrum, counts):
    return Fraction(lik_product(spectrum, counts), 6 ** sum(counts))

# Order: (AA, AB, BA, BB).
truth = (2, 1, 1, 2)
b2 = (1, 1, 1, 3)
b3 = (3, 1, 1, 1)
b4 = (1, 2, 2, 1)

x_win = (2, 1, 1, 2)
x_tie = (1, 1, 1, 1)
x_lose = (1, 2, 2, 1)

assert lik_product(truth, x_win) == 16
assert lik_product(b2, x_win) == 9
assert lik_product(b3, x_win) == 9
assert lik_product(b4, x_win) == 4

assert lik_product(truth, x_tie) == 4
assert lik_product(b4, x_tie) == 4
assert lik_product(b2, x_tie) == 3
assert lik_product(b3, x_tie) == 3

assert lik_product(truth, x_lose) == 4
assert lik_product(b4, x_lose) == 16

assert likelihood(truth, x_tie) == Fraction(1, 324)
assert likelihood(b4, x_tie) == Fraction(1, 324)

print(
    "PASS: four-chamber regimes: "
    f"x_win 16>9,9,4; x_tie 4=4>3,3 (P={likelihood(truth, x_tie)}); "
    f"x_lose 4<16"
)
