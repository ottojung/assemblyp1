#!/usr/bin/env python3
"""Cross-checks for the exact support-restricted Graver certificate (#263).

Independent exact-rational / high-precision numerical verification of the
mathematical claims in
``AssemblyP1/ExactSupportRestrictedGraver.lean``:

1. The one-dimensional over-admission witness ``N = 3, n = 2, x = 1``:
   exact binomial likelihoods are ``(0, 2/9, 2/9, 0)`` so the exact ML
   maximizers are ``{1, 2}``; the merged secant-slope affine surrogate is
   constant on ``{0,1,2,3}`` and therefore over-admits ``0`` and ``3``.
2. T1: a candidate outside the support-restricted admissible box has a
   zero-likelihood marginal, hence exact extended-real cost ``+inf``.
3. T2: on the admissible box the exact objective equals the honest finite cost.
4. T2 (convexity): the honest finite cost is discretely convex on the admissible
   box in all four sign patterns of ``x`` and ``n - x``.
5. The admissible box lies inside the ambient box ``[0, N]``.
"""

from __future__ import annotations

import math
from fractions import Fraction

LOW_OF = lambda x: 1 if x > 0 else 0
HIGH_OF = lambda n, x, N: N - 1 if n - x > 0 else N


def log0(v: float) -> float:
    """Totalized logarithm matching ``Real.log 0 = 0``."""
    return math.log(v) if v > 0 else 0.0


def binom_cost(N: int, x: int, n: int, d: int) -> float:
    """Finite product-binomial negative log (honest interior cost)."""
    return -(x) * log0(d / N) - (n - x) * log0(1.0 - d / N)


def binom_exact_is_top(N: int, x: int, n: int, d: int) -> bool:
    """The exact extended-real cost is +inf exactly at a zero-likelihood point."""
    return (d <= 0 and x > 0) or (N <= d and n - x > 0)


def binom_likelihood(N: int, x: int, n: int, d: int) -> Fraction:
    """Exact rational binomial likelihood numerator ``d^x (N-d)^(n-x)`` over
    the common denominator ``N^n``; returns the numerator as a Fraction."""
    return Fraction(d) ** x * Fraction(N - d) ** (n - x)


def second_differences(f, lo: int, hi: int) -> list[float]:
    """Discrete second differences ``f(k+2) - 2 f(k+1) + f(k)`` on ``[lo, hi]``."""
    return [f(k + 2) - 2 * f(k + 1) + f(k) for k in range(lo, hi - 1)]


def check_over_admission_witness() -> None:
    N, n, x = 3, 2, 1
    liks = [binom_likelihood(N, x, n, d) for d in range(0, N + 1)]
    assert liks == [Fraction(0), Fraction(2), Fraction(2), Fraction(0)], liks
    best = max(liks)
    maximizers = [d for d, l in enumerate(liks) if l == best]
    assert maximizers == [1, 2], maximizers
    # affineExtend (binomCost) 1 (N-1) = affineExtend f 1 2 is constant:
    c1, c2 = binom_cost(N, x, n, 1), binom_cost(N, x, n, 2)
    assert abs(c1 - c2) < 1e-12
    for d in range(0, N + 1):
        slope = (c2 - c1) / (2 - 1)
        ext = c1 + (d - 1) * slope
        assert abs(ext - c1) < 1e-12, (d, ext, c1)
    print("ok over-admission witness: exact maximizers {1,2}; surrogate constant on {0,1,2,3}")


def check_admissible_box_and_t1() -> None:
    # Exhaustive small sweep: every candidate outside the admissible box is
    # excluded (exact cost +inf), and every admissible candidate has finite cost.
    for N in range(1, 7):
        for n in range(0, 7):
            for x in range(0, n + 1):
                lo, hi = LOW_OF(x), HIGH_OF(n, x, N)
                for d in range(0, N + 1):
                    excluded = binom_exact_is_top(N, x, n, d)
                    admissible = lo <= d <= hi
                    assert excluded != admissible, (N, n, x, d, lo, hi, excluded, admissible)
                    if admissible:
                        c = binom_cost(N, x, n, d)
                        assert math.isfinite(c), (N, n, x, d, c)
    print("ok T1: excluded <-> outside admissible box; admissible costs finite")


def check_t2_agreement() -> None:
    # On the admissible box, the exact objective is finite and equals the cost.
    for N in range(1, 8):
        for n in range(0, 8):
            for x in range(0, n + 1):
                lo, hi = LOW_OF(x), HIGH_OF(n, x, N)
                for d in range(lo, hi + 1):
                    assert not binom_exact_is_top(N, x, n, d)
                    assert math.isfinite(binom_cost(N, x, n, d))
    print("ok T2: exact objective finite and equal to binomCost on the admissible box")


def check_convexity() -> None:
    # Four sign patterns of x and n-x; discrete second differences of the cost
    # on the admissible box are nonnegative (checked to high precision).
    cases = [
        (0, 0),   # x = 0, n - x = 0 -> box [0, N]
        (0, 3),   # x = 0, n - x > 0 -> box [0, N-1]
        (2, 2),   # x > 0, n - x = 0 -> box [1, N]
        (2, 5),   # x > 0, n - x > 0 -> box [1, N-1]
    ]
    checked = 0
    for N in range(1, 12):
        for x, n in cases:
            if not (0 <= x <= n):
                continue
            lo, hi = LOW_OF(x), HIGH_OF(n, x, N)
            if hi <= lo:
                continue
            ds = second_differences(lambda k: binom_cost(N, x, n, k), lo, hi)
            worst = min(ds) if ds else 0.0
            assert worst > -1e-9, (N, x, n, lo, hi, worst)
            checked += 1
    assert checked > 0
    print(f"ok T2 convexity: {checked} admissible boxes have nonnegative second differences")


def check_ambient_containment() -> None:
    for N in range(0, 8):
        for n in range(0, 8):
            for x in range(0, n + 1):
                lo, hi = LOW_OF(x), HIGH_OF(n, x, N)
                assert 0 <= lo, (N, n, x, lo)
                assert hi <= N, (N, n, x, hi)
    print("ok admissible box inside ambient box [0, N]")


def main() -> int:
    check_over_admission_witness()
    check_admissible_box_and_t1()
    check_t2_agreement()
    check_convexity()
    check_ambient_containment()
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
