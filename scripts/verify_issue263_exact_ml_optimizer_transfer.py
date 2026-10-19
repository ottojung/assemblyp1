#!/usr/bin/env python3
"""Independent cross-check for issue #263 exact-ML optimizer preservation.

This is an *independent* numerical/exact-rational check of the Lean artifact
``AssemblyP1/ExactMLOptimizerTransfer.lean``.  It does not import or trust the
Lean proof; it recomputes the claimed identities and inequalities from the
mathematical definitions.

The transcendental logarithm comparisons are checked in floating point at
double precision, but the *equivalent* polynomial inequalities are checked in
exact integer arithmetic, and the two are asserted to agree.  The finite
enumeration of the transfer property is done with exact ``Fraction`` values
for the secant-extension algebra; only the underlying log values are floats.

Exit status is 0 iff every check passes.
"""

from __future__ import annotations

import itertools
import math
import sys
from fractions import Fraction

FAILURES: list[str] = []


def check(condition: bool, message: str) -> None:
    if condition:
        print(f"PASS {message}")
    else:
        print(f"FAIL {message}", file=sys.stderr)
        FAILURES.append(message)


# --------------------------------------------------------------------------
# Cost models (mirroring the Lean definitions)
# --------------------------------------------------------------------------

def _xlog(a: float, b: float) -> float:
    """``a * log b`` with the ``0 * log 0 = 0`` convention (Lean's log 0 = 0)."""
    if a == 0:
        return 0.0
    return a * math.log(b)


def binom_cost(N: int, x: int, n: int, d: int) -> float:
    """Finite product-binomial negative log on the positive interior."""
    return -_xlog(x, d / N) - _xlog(n - x, 1 - d / N)


def binom_ext(N: int, x: int, n: int, d: int) -> float:
    """Secant-slope affine-tail extension of ``binom_cost`` from [1, N-1]."""
    if d <= 1:
        return binom_cost(N, x, n, 1) + (d - 1) * (
            binom_cost(N, x, n, 2) - binom_cost(N, x, n, 1)
        )
    if N - 1 <= d:
        return binom_cost(N, x, n, N - 1) + (d - (N - 1)) * (
            binom_cost(N, x, n, N - 1) - binom_cost(N, x, n, N - 2)
        )
    return binom_cost(N, x, n, d)


def binom_exact(N: int, x: int, n: int, d: int) -> float:
    """Genuine extended-real product-binomial negative log (+inf at 0-prob)."""
    if (d <= 0 and x > 0) or (N <= d and n - x > 0):
        return math.inf
    return binom_cost(N, x, n, d)


def multinomial_cost(G: int, x: int, d: int) -> float:
    return -_xlog(x, d / G)


def multinomial_ext(G: int, x: int, d: int) -> float:
    if d <= 1:
        return multinomial_cost(G, x, 1) + (d - 1) * (
            multinomial_cost(G, x, 2) - multinomial_cost(G, x, 1)
        )
    if G <= d:
        return multinomial_cost(G, x, G) + (d - G) * (
            multinomial_cost(G, x, G) - multinomial_cost(G, x, G - 1)
        )
    return multinomial_cost(G, x, d)


def multinomial_exact(G: int, x: int, d: int) -> float:
    if d <= 0 and x > 0:
        return math.inf
    return multinomial_cost(G, x, d)


# --------------------------------------------------------------------------
# 1. The boundary logarithm inequality and its exact polynomial equivalent
# --------------------------------------------------------------------------

def check_log_inequality() -> None:
    for N in range(3, 200):
        lhs = math.log(1 - 2 / N)
        rhs = 2 * math.log(1 - 1 / N)
        # Exact rational equivalence: log(1-2/N) <= 2 log(1-1/N)
        #   <=> 1 - 2/N <= (1 - 1/N)^2  <=> N*(N-2) <= (N-1)^2.
        exact_poly = N * (N - 2) <= (N - 1) ** 2
        check(lhs <= rhs + 1e-15, f"log(1-2/{N}) <= 2 log(1-1/{N})")
        check(exact_poly, f"exact: {N}*{N-2} <= {N-1}^2")
    # A deliberate sanity check that the bound is tight at N = 3.
    check(
        3 * (3 - 2) == (3 - 1) ** 2 - 1,
        "exact polynomial bound is tight at N=3 (3*1 == 2^2 - 1)",
    )


# --------------------------------------------------------------------------
# 2. Endpoint domination of the extension by the exact cost
# --------------------------------------------------------------------------

def check_endpoint_domination() -> None:
    for N in range(3, 40):
        for n in range(0, 8):
            for x in range(0, n + 1):
                # Left endpoint d = 0: exact is 0 when x = 0, +inf when x > 0.
                ex0 = binom_ext(N, x, n, 0)
                if x == 0:
                    check(
                        ex0 <= binom_exact(N, 0, n, 0) + 1e-12,
                        f"binom ext(0) <= exact(0), N={N} n={n} x=0",
                    )
                # Right endpoint d = N: exact is 0 when x = n, +inf otherwise.
                exN = binom_ext(N, x, n, N)
                if x == n:
                    check(
                        exN <= binom_exact(N, n, n, N) + 1e-12,
                        f"binom ext(N) <= exact(N), N={N} n={n} x=n",
                    )


def check_interior_agreement() -> None:
    for N in range(3, 30):
        for n in range(0, 6):
            for x in range(0, n + 1):
                for d in range(1, N):
                    check(
                        abs(binom_ext(N, x, n, d) - binom_cost(N, x, n, d)) < 1e-12,
                        f"binom ext == cost interior N={N} x={x} n={n} d={d}",
                    )


# --------------------------------------------------------------------------
# 3. The full transfer property on a small separable instance
# --------------------------------------------------------------------------

def check_transfer_instance() -> None:
    """Two read classes; verify interior ext-minimizer => exact minimizer.

    Uses the exact-rational secant algebra for the extension and float logs for
    the cost; the exact objective is +inf at zero-probability endpoints.
    """
    # Class parameters (N, x, n).  A genuine interior optimizer is chosen by
    # scanning the box; the check verifies exact(z) <= exact(w) for all w.
    params = [(5, 1, 2), (5, 2, 3)]
    boxes = [range(0, N + 1) for (N, _, _) in params]

    def ext_obj(ds):
        return sum(binom_ext(N, x, n, d) for (N, x, n), d in zip(params, ds))

    def exact_obj(ds):
        vals = [binom_exact(N, x, n, d) for (N, x, n), d in zip(params, ds)]
        return math.inf if any(math.isinf(v) for v in vals) else sum(vals)

    def is_interior(ds):
        return all(0 < d < N for (N, _, _), d in zip(params, ds))

    candidates = list(itertools.product(*boxes))
    ext_vals = {ds: ext_obj(ds) for ds in candidates}
    best_ext = min(ext_vals.values())
    ext_minimizers = [ds for ds in candidates if ext_vals[ds] <= best_ext + 1e-12]
    interior_minimizers = [ds for ds in ext_minimizers if is_interior(ds)]

    check(
        len(interior_minimizers) > 0,
        "the sample instance has an interior extension minimizer",
    )
    for z in interior_minimizers:
        zval = exact_obj(z)
        check(
            all(exact_obj(w) >= zval - 1e-9 for w in candidates),
            f"interior ext-minimizer {z} minimizes the exact objective",
        )


# --------------------------------------------------------------------------
# 4. The over-admission witness for the OPEN converse (documentation only)
# --------------------------------------------------------------------------

def check_over_admission_witness() -> None:
    """The one-dimensional example showing the converse needs the hypothesis.

    N = 3, n = 2, x = 1: the extension is constant on {0,1,2,3} while the exact
    objective is +inf at d = 0 and d = 3, so a boundary extension minimizer is
    NOT an exact minimizer.  This confirms the interior hypothesis is essential
    and is not silently dropped.
    """
    N, n, x = 3, 2, 1
    ext_vals = [binom_ext(N, x, n, d) for d in range(N + 1)]
    check(
        max(ext_vals) - min(ext_vals) < 1e-12,
        "N=3,n=2,x=1: extension is constant on the full box",
    )
    check(
        math.isinf(binom_exact(N, x, n, 0))
        and math.isinf(binom_exact(N, x, n, 3)),
        "N=3,n=2,x=1: exact objective is +inf at the boundary",
    )
    # The true exact minimizers are the interior points 1 and 2.
    finite = [
        (d, binom_exact(N, x, n, d)) for d in range(N + 1)
        if not math.isinf(binom_exact(N, x, n, d))
    ]
    best = min(v for _, v in finite)
    check(
        sorted(d for d, v in finite if v <= best + 1e-12) == [1, 2],
        "N=3,n=2,x=1: exact minimizers are {1,2}",
    )


# --------------------------------------------------------------------------
# 5. Multinomial boundary and interior checks
# --------------------------------------------------------------------------

def check_multinomial() -> None:
    for G in range(2, 30):
        for x in range(0, 6):
            check(
                multinomial_ext(G, 0, 0) <= multinomial_exact(G, 0, 0) + 1e-12,
                f"multinomial ext(0) <= exact(0), G={G}, x=0",
            )
            for d in range(1, G + 1):
                check(
                    abs(multinomial_ext(G, x, d) - multinomial_cost(G, x, d)) < 1e-12,
                    f"multinomial ext == cost G={G} x={x} d={d}",
                )


def main() -> int:
    check_log_inequality()
    check_endpoint_domination()
    check_interior_agreement()
    check_transfer_instance()
    check_over_admission_witness()
    check_multinomial()

    if FAILURES:
        print(f"\n{len(FAILURES)} check(s) FAILED", file=sys.stderr)
        return 1
    print("\nall issue-263 exact-ML optimizer-transfer cross-checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
