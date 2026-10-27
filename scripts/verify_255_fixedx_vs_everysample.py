#!/usr/bin/env python3
"""Exact rational check that fixed-x maximality does not imply every-sample maximality.

Oriented same-length model, S=AAABBB (G=6, L=2), types ordered (AA,AB,BA,BB)
per verifier convention (AA,AB,BA,BB) -- note FixedXExactML uses E255 order
(AA,AB,BB,BA); products are order-independent so values compare directly.

  truth B1    = (2,1,2,1) in (AA,AB,BB,BA) = (2,1,1,2) in (AA,AB,BA,BB)
  rival B4    = (1,2,1,2) in (AA,AB,BB,BA) = (1,2,2,1) in (AA,AB,BA,BB)

x_win  = B1 (six reads): truth likProduct 16 beats B2/B3 (9) and B4 (4).
x_lose = B4 (six reads): truth likProduct 4 loses to B4 likProduct 16.
Both samples are supported on the truth window support. Hence truth is the
unique fixed-x maximizer at x_win and a strict loser at x_lose: (A) does not
imply (B). Mirrors kernel-checked fixedX_unique_at_xWin258 /
fixedX_strict_loss_at_xLose258 (decide-closed integer comparisons).
"""

from fractions import Fraction


def lik_product(spectrum: tuple[int, ...], counts: tuple[int, ...]) -> int:
    return int(sum(1 for _ in []) or 1) if False else __import__("math").prod(
        m**c for m, c in zip(spectrum, counts, strict=True)
    )


def likelihood(spectrum: tuple[int, ...], counts: tuple[int, ...]) -> Fraction:
    n = sum(counts)
    return Fraction(lik_product(spectrum, counts), 6**n)


# Order: (AA, AB, BA, BB) to match existing 255 verifiers.
truth = (2, 1, 1, 2)
b2 = (1, 1, 1, 3)
b3 = (3, 1, 1, 1)
b4 = (1, 2, 2, 1)

x_win = (2, 1, 1, 2)  # = B1
x_lose = (1, 2, 2, 1)  # = B4

# Integer products at x_win (cf. fixedX_unique_at_xWin258: 16 > 9, 4).
assert lik_product(truth, x_win) == 16
assert lik_product(b2, x_win) == 9
assert lik_product(b3, x_win) == 9
assert lik_product(b4, x_win) == 4

# Integer products at x_lose (cf. fixedX_strict_loss_at_xLose258: 4 < 16).
assert lik_product(truth, x_lose) == 4
assert lik_product(b4, x_lose) == 16

# Rational likelihoods (G^n = 6^6 = 46656).
assert likelihood(truth, x_win) == Fraction(1, 2916)
assert likelihood(b4, x_win) == Fraction(1, 11664)
assert likelihood(truth, x_lose) == Fraction(1, 11664)
assert likelihood(b4, x_lose) == Fraction(1, 2916)

print(
    "PASS: fixed-x vs every-sample separation: "
    f"x_win P(S)={likelihood(truth, x_win)} > P(B4)={likelihood(b4, x_win)}; "
    f"x_lose P(S)={likelihood(truth, x_lose)} < P(B4)={likelihood(b4, x_lose)}"
)
