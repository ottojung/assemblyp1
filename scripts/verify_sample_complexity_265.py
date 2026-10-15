#!/usr/bin/env python3
"""Independent check of the #265 scoped sample-complexity bound.

Verifies, with exact rational arithmetic where possible and high-precision
decimals for the transcendental step, that:

1. the worked read-law example has affinity rho = sqrt(3)/2 exactly squared to
   3/4, and the closed-form sufficient sample size for a 1% union-bound target
   is n = 33, with rho^33 <= 1/100 < rho^32;
2. the union-Bhattacharyya inequality
       Pr_p[exists q in Theta : L_q >= L_p] <= sum_q rho(p,q)^n
   holds by exhaustive enumeration for a small two-symbol alphabet over
   n = 1..14, using exact fractions for the probabilities;
3. the closed-form inversion
       n >= ceil( ln(|Theta|/delta) / ln(1/rho_*) )  =>  |Theta| rho_*^n <= delta
   is correct on a grid of families and tolerances, and that this n is the
   least integer for which the bound holds;
4. the kernel-checked numerical illustration il_confidence_99
   (3 * (9/10)^55 < 1/100) is reproduced by the closed form.

This script checks the mathematics of the scoped bound, not any genome-class
numerical affinity. Exit status is 0 on success and 1 on any failure.
"""

from __future__ import annotations

import math
from decimal import Decimal, getcontext
from fractions import Fraction

getcontext().prec = 60

FAILURES: list[str] = []


def check(condition: bool, message: str) -> None:
    if not condition:
        FAILURES.append(message)


def dsqrt(x: Fraction) -> Decimal:
    return Decimal(x.numerator).sqrt() / Decimal(x.denominator).sqrt()


def affinity(p: tuple[Fraction, ...], q: tuple[Fraction, ...]) -> Decimal:
    total = Decimal(0)
    for a, b in zip(p, q):
        total += dsqrt(a * b)
    return total


def ceil_div_log(card: int, rho: Decimal, delta: Decimal) -> int:
    """ceil( ln(card/delta) / ln(1/rho) ), the sufficient sample size."""
    value = (Decimal(card) / delta).ln() / (Decimal(1) / rho).ln()
    return int(value.to_integral_value(rounding="ROUND_CEILING"))


# --- 1. Worked exact example --------------------------------------------------

P = (Fraction(3, 4), Fraction(1, 4))
Q = (Fraction(1, 4), Fraction(3, 4))
rho = affinity(P, Q)
# rho = 2*sqrt((3/4)(1/4)) = sqrt(3)/2, so rho^2 = 3/4 exactly. The high-
# precision value agrees with 3/4 to within the working precision.
check(abs(rho * rho - Decimal(3) / Decimal(4)) < Decimal("1e-50"),
      "affinity squared of the worked example is not 3/4")
check(abs(rho - Decimal(3).sqrt() / Decimal(2)) < Decimal("1e-50"),
      "affinity of the worked example is not sqrt(3)/2")

delta = Decimal(1) / Decimal(100)
n_example = ceil_div_log(1, rho, delta)
check(n_example == 33, f"worked-example sample size is {n_example}, expected 33")

rho33 = rho ** 33
rho32 = rho ** 32
check(rho33 <= delta, f"rho^33 = {rho33} is not <= 1/100")
check(rho32 > delta, f"rho^32 = {rho32} is not > 1/100 (bound not tight at 33)")

# --- 2. Exhaustive union-bound check (exact fractions) ------------------------

W = (Fraction(3, 4), Fraction(1, 4))          # truth read law p
ALT = (Fraction(1, 4), Fraction(3, 4))        # competitor q1
ALT2 = (Fraction(0), Fraction(1))             # competitor q2
FAMILY = (ALT, ALT2)


def likelihood(law: tuple[Fraction, ...], counts: tuple[int, int]) -> Fraction:
    out = Fraction(1)
    for prob, k in zip(law, counts):
        out *= prob ** k
    return out


for n in range(1, 15):
    error = Fraction(0)
    # enumerate compositions (k, n-k) with binomial multiplicity
    for k in range(n + 1):
        weight = Fraction(math.comb(n, k)) * (Fraction(3, 4) ** (n - k)) * (Fraction(1, 4) ** k)
        counts = (n - k, k)
        lp = likelihood(W, counts)
        wrong = any(likelihood(q, counts) >= lp for q in FAMILY)
        if wrong:
            error += weight
    bound = sum((affinity(W, q) ** n for q in FAMILY), Decimal(0))
    check(Decimal(error.numerator) / Decimal(error.denominator) <= bound,
          f"exhaustive union bound fails at n={n}: error={error} bound={bound}")

# --- 3. Closed-form inversion is correct and least ----------------------------

grid = [
    (1, Decimal("0.8660254037844386467637231707529362"), Decimal(1) / Decimal(100)),
    (1, Decimal("0.8660254037844386467637231707529362"), Decimal(1) / Decimal(1000000)),
    (3, Decimal("0.9"), Decimal(1) / Decimal(100)),
    (10, Decimal("0.99"), Decimal("0.05")),
    (1000000, Decimal("0.999"), Decimal(1) / Decimal(1000)),
]
for card, r, d in grid:
    n = ceil_div_log(card, r, d)
    bound_n = Decimal(card) * (r ** n)
    check(bound_n <= d, f"inversion fails: card={card} rho={r} delta={d} n={n} bound={bound_n}")
    if n > 1:
        bound_prev = Decimal(card) * (r ** (n - 1))
        check(bound_prev > d,
              f"inversion not least: card={card} rho={r} delta={d} n-1={n-1} bound={bound_prev}")

# --- 4. Kernel-checked il_confidence_99 instance ------------------------------

check(Fraction(3) * Fraction(9, 10) ** 55 < Fraction(1, 100),
      "il_confidence_99 exact inequality fails")
check(ceil_div_log(3, Decimal("0.9"), Decimal(1) / Decimal(100)) == 55,
      "closed form does not reproduce il_confidence_99's n = 55")

# --- Report -------------------------------------------------------------------

if FAILURES:
    for failure in FAILURES:
        print(f"FAIL: {failure}")
    raise SystemExit(1)
print("verify_sample_complexity_265: PASS")
print(f"  worked example: rho = sqrt(3)/2, n(1% bound) = {n_example}, "
      f"rho^33 = {rho33:.6f}, rho^32 = {rho32:.6f}")
print("  exhaustive union bound: verified exactly for n = 1..14 (two competitors)")
print("  closed-form inversion: verified sufficient and least on 5 families")
print("  il_confidence_99: reproduced (n = 55)")
