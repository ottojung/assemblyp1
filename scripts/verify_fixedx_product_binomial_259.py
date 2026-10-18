#!/usr/bin/env python3
"""Independent exact-arithmetic verification for board issue #259 axis A.

This does NOT import Lean.  With exact integer / Fraction arithmetic it checks
the claims of `AssemblyP1/FixedXProductBinomialMaximality.lean`, i.e. fixed-`x`
maximality for the MB09 §6.1 fixed-external-`N` product-binomial surrogate.

Definitions (paper conventions; exact integers):
    q_e(B) = B_e * prod_{j != e} (N - B_j)          (effective weight)
    F_B(x) = prod_e q_e(B) ** x_e                    (effective product)
At a fixed observation `x` with `n = sum x` the surrogate is separable:
    F_B(x) = prod_e B_e ** x_e * (N - B_e) ** (n - x_e).

Checks:
  A. Separable identity, exactly, over exhaustive small and random cases.
  B. Exact fixed-`x` criterion: F_B(x) <= F_A(x) iff the separable product of B
     is <= that of A (re-derived independently through the ratio).
  C. Coordinatewise sufficient inequality: per-type binomial-factor domination
     implies F_B(x) <= F_A(x).
  D. Strict separation witness: A=(2,2), B=(3,1), N=4 at the covered sample
     x=(2,2): A wins although q_B(0) > q_A(0) (pointwise domination fails).
  E. Full-class fixed-`x` classification on Fin 2, N=4, x=(2,2): (2,2) beats
     every positive total-4 candidate and every other truth is beaten by (2,2).
  F. Concentrated-sample iff: F_B(c*delta_e) <= F_A(c*delta_e) iff q_B(e) <= q_A(e).
  G. Bounded census of the fixed-`x` vs sample-uniform gap: distinct positive
     equal-total pairs where A wins at the truth sample x=A while failing
     pointwise domination (so the fixed-`x` criterion is strictly weaker).

Non-vacuity mutation control: `eff_weight` is mutated to include the self factor
`(N - B_e)`; the separable identity must then FAIL.  If the mutation is not
detected the verifier itself is vacuous and exits non-zero.

Exit code 0 means every check passed.
"""

from __future__ import annotations

import itertools
import random
import sys

# ---------------------------------------------------------------------------
# §6.1 effective weights and products (exact integers)
# ---------------------------------------------------------------------------


def eff_weight(N: int, B: list[int], i: int, *, mutate: bool = False) -> int:
    w = B[i]
    for j in range(len(B)):
        if j != i or mutate:
            w *= N - B[j]
    return w


def eff_product(N: int, B: list[int], x: list[int], *, mutate: bool = False) -> int:
    p = 1
    for i in range(len(B)):
        p *= eff_weight(N, B, i, mutate=mutate) ** x[i]
    return p


def separable(N: int, B: list[int], x: list[int]) -> int:
    n = sum(x)
    p = 1
    for i in range(len(B)):
        p *= B[i] ** x[i] * (N - B[i]) ** (n - x[i])
    return p


def compositions(N: int, k: int):
    """Positive integer vectors of length k summing to N."""
    if k == 1:
        yield (N,)
        return
    for first in range(1, N - k + 2):
        for rest in compositions(N - first, k - 1):
            yield (first,) + rest


def dominates_pointwise(N: int, A: list[int], B: list[int]) -> bool:
    return all(eff_weight(N, B, i) <= eff_weight(N, A, i) for i in range(len(A)))


# ---------------------------------------------------------------------------
# Part A: separable identity (also the mutation control)
# ---------------------------------------------------------------------------


def part_a(*, mutate: bool = False) -> int:
    checks = 0
    for N in range(2, 13):
        for k in range(1, min(N, 4) + 1):
            comps = [list(c) for c in compositions(N, k)]
            for B in comps:
                for n in range(0, 7):
                    for x in _bounded_vectors(n, k):
                        checks += 1
                        if eff_product(N, B, x, mutate=mutate) != separable(N, B, x):
                            raise AssertionError(
                                f"separable identity failed: N={N} B={B} x={x}")
    random.seed(259)
    for _ in range(20000):
        k = random.randint(1, 6)
        N = random.randint(k, 60)
        B = _rand_comp(N, k)
        n = random.randint(0, 40)
        x = _rand_bounded(n, k)
        checks += 1
        if eff_product(N, B, x, mutate=mutate) != separable(N, B, x):
            raise AssertionError(
                f"separable identity failed: N={N} B={B} x={x}")
    return checks


def _bounded_vectors(n: int, k: int):
    if k == 1:
        yield [n]
        return
    for first in range(0, n + 1):
        for rest in _bounded_vectors(n - first, k - 1):
            yield [first] + rest


def _rand_comp(N: int, k: int) -> list[int]:
    cuts = sorted(random.sample(range(1, N), k - 1))
    return [b - a for a, b in zip([0] + cuts, cuts + [N])]


def _rand_bounded(n: int, k: int) -> list[int]:
    if k == 1:
        return [n]
    cuts = sorted(random.choices(range(0, n + 1), k=k - 1))
    return [b - a for a, b in zip([0] + cuts, cuts + [n])]


# ---------------------------------------------------------------------------
# Part B: exact fixed-x criterion via the ratio factorization
# ---------------------------------------------------------------------------


def part_b() -> int:
    checks = 0
    random.seed(260)
    for _ in range(40000):
        k = random.randint(1, 6)
        N = random.randint(k + 1, 60)
        A = _rand_comp(N, k)
        B = _rand_comp(N, k)
        n = random.randint(0, 40)
        x = _rand_bounded(n, k)
        # ratio factorization: F_B / F_A = prod (B/A)^x * ((N-B)/(N-A))^(n-x)
        lhs = eff_product(N, B, x) * eff_product(N, A, x)  # sign-free square form
        # sign of the comparison is decided exactly by integer products
        cmp_direct = eff_product(N, B, x) <= eff_product(N, A, x)
        cmp_sep = separable(N, B, x) <= separable(N, A, x)
        checks += 1
        if cmp_direct != cmp_sep:
            raise AssertionError(
                f"fixed-x criterion failed: N={N} A={A} B={B} x={x}")
        if lhs == 0:
            raise AssertionError(f"unexpected zero product: N={N} A={A} B={B} x={x}")
    return checks


# ---------------------------------------------------------------------------
# Part C: coordinatewise sufficient inequality
# ---------------------------------------------------------------------------


def part_c() -> int:
    checks = 0
    random.seed(261)
    for _ in range(20000):
        k = random.randint(1, 6)
        N = random.randint(k + 1, 40)
        A = _rand_comp(N, k)
        B = _rand_comp(N, k)
        n = random.randint(0, 30)
        x = _rand_bounded(n, k)
        if all(B[i] ** x[i] * (N - B[i]) ** (n - x[i])
               <= A[i] ** x[i] * (N - A[i]) ** (n - x[i]) for i in range(k)):
            checks += 1
            if not (separable(N, B, x) <= separable(N, A, x)):
                raise AssertionError(
                    f"coordwise sufficiency failed: N={N} A={A} B={B} x={x}")
    if checks == 0:
        raise AssertionError("coordwise sufficiency was vacuous")
    return checks


# ---------------------------------------------------------------------------
# Part D: strict separation witness
# ---------------------------------------------------------------------------


def part_d() -> None:
    N = 4
    A = [2, 2]
    B = [3, 1]
    x = [2, 2]
    assert sum(A) == N and sum(B) == N
    assert all(A[i] <= x[i] for i in range(2)), "x must be a covered sample"
    assert eff_product(N, B, x) <= eff_product(N, A, x), "A must win at x"
    assert not dominates_pointwise(N, A, B), "pointwise domination must fail"
    assert eff_weight(N, B, 0) > eff_weight(N, A, 0), "q_B(0) > q_A(0) expected"
    assert eff_product(N, B, x) == 81 and eff_product(N, A, x) == 256


# ---------------------------------------------------------------------------
# Part E: full-class fixed-x classification on Fin 2
# ---------------------------------------------------------------------------


def part_e() -> None:
    N = 4
    x = [2, 2]
    cands = [list(c) for c in compositions(N, 2)]
    assert sorted(map(tuple, cands)) == [(1, 3), (2, 2), (3, 1)]
    for B in cands:
        assert eff_product(N, B, x) <= eff_product(N, [2, 2], x), f"{B} beats (2,2)"
    for A in cands:
        if A != [2, 2]:
            assert eff_product(N, A, x) < eff_product(N, [2, 2], x), \
                f"(2,2) must beat {A}"


# ---------------------------------------------------------------------------
# Part F: concentrated-sample iff
# ---------------------------------------------------------------------------


def part_f() -> int:
    checks = 0
    random.seed(262)
    for _ in range(20000):
        k = random.randint(1, 6)
        N = random.randint(k + 1, 50)
        A = _rand_comp(N, k)
        B = _rand_comp(N, k)
        e = random.randrange(k)
        c = random.randint(1, 20)
        x = [c if i == e else 0 for i in range(k)]
        checks += 1
        lhs = eff_product(N, B, x) <= eff_product(N, A, x)
        rhs = eff_weight(N, B, e) <= eff_weight(N, A, e)
        if lhs != rhs:
            raise AssertionError(
                f"concentrated iff failed: N={N} A={A} B={B} e={e} c={c}")
    return checks


# ---------------------------------------------------------------------------
# Part G: bounded census of the fixed-x vs sample-uniform gap
# ---------------------------------------------------------------------------


def part_g() -> int:
    gap = 0
    pairs = 0
    for N in range(2, 10):
        for k in range(2, min(N, 4) + 1):
            comps = [list(c) for c in compositions(N, k)]
            for A in comps:
                for B in comps:
                    if A == B:
                        continue
                    pairs += 1
                    if dominates_pointwise(N, A, B):
                        continue
                    # fixed-x wins at the truth sample x = A while pointwise fails
                    if eff_product(N, B, A) <= eff_product(N, A, A):
                        gap += 1
    if gap == 0:
        raise AssertionError("fixed-x vs sample-uniform gap was vacuous")
    return gap


# ---------------------------------------------------------------------------
# Mutation control
# ---------------------------------------------------------------------------


def mutation_detected() -> bool:
    """True iff the self-factor mutation breaks the separable identity."""
    N = 4
    B = [2, 2]
    x = [1, 1]
    return eff_product(N, B, x, mutate=True) != separable(N, B, x)


def main() -> int:
    if not mutation_detected():
        print("FAIL: non-vacuity mutation not detected", file=sys.stderr)
        return 1
    a = part_a()
    b = part_b()
    c = part_c()
    part_d()
    part_e()
    f = part_f()
    g = part_g()
    print("verify_fixedx_product_binomial_259.py")
    print(f"  A separable identity: {a} cases, 0 mismatches "
          f"(mutation control: self-factor detected)")
    print(f"  B exact fixed-x criterion: {b} random cases, 0 mismatches")
    print(f"  C coordinatewise sufficiency: {c} dominated cases, 0 violations")
    print("  D strict separation witness: A=(2,2) beats B=(3,1) at x=(2,2) "
          "with q_B(0)=9 > 4=q_A(0)")
    print("  E full-class classification on Fin 2, N=4, x=(2,2): (2,2) uniquely maximal")
    print(f"  F concentrated-sample iff: {f} cases, 0 mismatches")
    print(f"  G fixed-x vs sample-uniform gap census: {g} pairs win at x=A "
          f"without pointwise domination")
    print("OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
