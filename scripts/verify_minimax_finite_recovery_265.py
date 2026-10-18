#!/usr/bin/env python3
"""Exact finite-n minimax/optimal recovery for one explicit #265 read family.

This is the quantitative companion to the paper's Remark
`rem:minimax-sample-size` in `paper/sections/03-open-question.tex` and to the
note `docs/minimax-finite-recovery-265.md`.  It computes, from scratch and with
exact rational arithmetic, the *tight* finite-n recovery numbers for the single
explicitly specified finite distinguishable family

    A = (1/2, 1/2),  B = (3/4, 1/4),  C = (1/4, 3/4)

on the binary read alphabet {0, 1}, with n iid reads summarised by the count
k of symbol 1 and the exact product likelihood L_t(k) = P_t(0)^(n-k) P_t(1)^k.

It checks, exactly:

1. the uniform-prior Bayes-optimal (prior-averaged) success
   V_n = sum_k max_t (1/3) P_t(k)  for n = 1..100 is non-decreasing, and the
   exact minimal n with V_n >= 99/100 is n = 85 (V_84 < 99/100 <= V_85);
2. the per-truth success of the optimal (tie-splitting) rule differs from the
   prior average: at n = 85 the middle truth A is strictly harder than B = C,
   while the average of the three equals V_85;
3. the minimax-over-truths success: for a symmetric prior (gamma, gamma, 1-2g)
   the Bayes error R_n(g) is concave and piecewise linear with the listed
   breakpoints, its maximum is the exact minimax error, and the exact minimal n
   with minimax success >= 99/100 is n = 87 (error at n = 86 exceeds 1/100);
4. a matching certificate at the least favourable prior: the Bayes rule for the
   maximising symmetric prior, with its two likelihood ties split optimally,
   attains the minimax error exactly (so the prior gives the lower bound and the
   exhibited rule the upper bound);
5. conservativeness of the kernel-checked Hellinger union bound: its sufficient
   size for 1% error is 153, far above the exact 85/87, and it dominates the
   exact error at n = 85;
6. the zero-mass convention on a small boundary sub-case.

All statements here are standard decision theory (Bayes risk, minimax =
maximising the Bayes risk over priors) plus finite exact arithmetic; NONE of
them is a Lean theorem.  The only kernel-checked constants in this circle are
the abstract Bayes-optimality statements of `AssemblyP1.FiniteBayesDecision` /
`FiniteMapOptimality` and the Hellinger union bound of
`AssemblyP1.FiniteReadRecovery`.  Exit status is 0 on success, 1 on failure.
"""

from __future__ import annotations

from fractions import Fraction
from functools import lru_cache
from math import comb

FAILURES: list[str] = []


def check(condition: bool, message: str) -> None:
    if not condition:
        FAILURES.append(message)


# --- The family --------------------------------------------------------------

LAWS: dict[str, tuple[Fraction, Fraction]] = {
    "A": (Fraction(1, 2), Fraction(1, 2)),
    "B": (Fraction(3, 4), Fraction(1, 4)),
    "C": (Fraction(1, 4), Fraction(3, 4)),
}
TRUTHS = ("A", "B", "C")


def pmf(truth: str, k: int, n: int) -> Fraction:
    """Exact P_truth(count of 1s = k) = C(n,k) p0^(n-k) p1^k."""

    return _pmf(truth, k, n)


@lru_cache(maxsize=None)
def _pmf(truth: str, k: int, n: int) -> Fraction:
    p0, p1 = LAWS[truth]
    return Fraction(comb(n, k)) * p0 ** (n - k) * p1 ** k


def bayes_success(weights: dict[str, Fraction], n: int) -> Fraction:
    """Optimal prior-averaged success sum_k max_t weights[t] P_t(k)."""

    total = Fraction(0)
    for k in range(n + 1):
        total += max(weights[t] * pmf(t, k, n) for t in TRUTHS)
    return total


def per_truth_success(weights: dict[str, Fraction], n: int) -> dict[str, Fraction]:
    """Per-truth success of the tie-splitting Bayes rule for ``weights``."""

    succ = {t: Fraction(0) for t in TRUTHS}
    for k in range(n + 1):
        vals = {t: weights[t] * pmf(t, k, n) for t in TRUTHS}
        top = max(vals.values())
        argmax = [t for t in TRUTHS if vals[t] == top]
        for t in argmax:
            succ[t] += pmf(t, k, n) / len(argmax)
    return succ


UNIFORM = {t: Fraction(1, 3) for t in TRUTHS}


def symmetric_weights(gamma: Fraction) -> dict[str, Fraction]:
    return {"A": 1 - 2 * gamma, "B": gamma, "C": gamma}


def bayes_error_symmetric(gamma: Fraction, n: int) -> Fraction:
    return 1 - _bayes_success_symmetric(gamma, n)


@lru_cache(maxsize=None)
def _bayes_success_symmetric(gamma: Fraction, n: int) -> Fraction:
    return bayes_success(symmetric_weights(gamma), n)


# --- Minimax over truths via symmetric priors --------------------------------

@lru_cache(maxsize=None)
def breakpoints(n: int) -> list[Fraction]:
    """gamma where the A/B (and A/C) Bayes boundary changes, plus endpoints."""

    pts = {Fraction(0), Fraction(1, 2)}
    for k in range(n + 1):
        pa, pb = pmf("A", k, n), pmf("B", k, n)
        # (1 - 2 gamma) P_A(k) = gamma P_B(k)  ->  gamma = P_A / (P_B + 2 P_A)
        pts.add(pa / (pb + 2 * pa))
    return sorted(g for g in pts if 0 <= g <= Fraction(1, 2))


def minimax_error(n: int) -> tuple[Fraction, Fraction]:
    """Exact minimax-over-truths error and the least favourable gamma."""

    pts = breakpoints(n)
    return max((bayes_error_symmetric(g, n), g) for g in pts)


def check_piecewise_linear_and_concave(n: int) -> None:
    """R_n(gamma) is linear between consecutive breakpoints and concave."""

    pts = breakpoints(n)
    slopes = []
    for i in range(len(pts) - 1):
        a, b = pts[i], pts[i + 1]
        mid = (a + b) / 2
        ra, rm, rb = (bayes_error_symmetric(x, n) for x in (a, mid, b))
        check(rm == (ra + rb) / 2,
              f"R_n is not linear on [{a},{b}] at n={n}")
        if b != a:
            slopes.append((rb - ra) / (b - a))
    for i in range(len(slopes) - 1):
        check(slopes[i] >= slopes[i + 1] - Fraction(1, 10**12),
              f"R_n is not concave (slopes increase) at n={n}")


def tie_split_certificate(n: int, gamma: Fraction) -> tuple[Fraction, Fraction]:
    """Minimax-optimal Bayes rule for ``gamma``: return (split p, max error).

    The Bayes rule for the symmetric least favourable prior is
    B on k <= k1, an A/B tie at k1, A in between, an A/C tie at n-k1, and C on
    k >= n-k1+1.  Splitting both ties toward A with probability ``p`` yields
    per-truth errors linear in ``p``; the minimax rule equalises them.
    """

    weights = symmetric_weights(gamma)
    # Locate the A/B tie point k1 (a k<n/2 where A and B are exactly tied).
    k1 = None
    for k in range(n // 2 + 1):
        va = weights["A"] * pmf("A", k, n)
        vb = weights["B"] * pmf("B", k, n)
        if va == vb:
            k1 = k
    check(k1 is not None, f"no A/B likelihood tie found at n={n}, gamma={gamma}")
    if k1 is None:
        return Fraction(0), Fraction(1)

    k2 = n - k1  # symmetric A/C tie
    # err_A(p) = P_A(k<k1) + (1-p) P_A(k1) + P_A(k>k2) + (1-p) P_A(k2)
    # err_B(p) = P_B(k>k1) + p P_B(k1)
    # (err_C equals err_B by symmetry.)
    base_a = sum(pmf("A", k, n) for k in range(0, k1)) + sum(
        pmf("A", k, n) for k in range(k2 + 1, n + 1))
    tie_a = pmf("A", k1, n) + pmf("A", k2, n)
    base_b = sum(pmf("B", k, n) for k in range(k1 + 1, n + 1))
    tie_b = pmf("B", k1, n)

    # err_A = base_a + (1-p) tie_a is decreasing in p;
    # err_B = base_b + p tie_b is increasing in p.  Equalise.
    p = (base_a + tie_a - base_b) / (tie_a + tie_b)
    check(0 <= p <= 1, f"tie-split probability {p} outside [0,1] at n={n}")
    p = min(max(p, Fraction(0)), Fraction(1))
    err_a = base_a + (1 - p) * tie_a
    err_b = base_b + p * tie_b
    return p, max(err_a, err_b)


# --- 1 and 2: prior-averaged optimum and its per-truth breakdown -------------

V_85 = Fraction(2893972976464393907418071635325873973663341063781,
                2923003274661805836407369665432566039311865085952)
check(bayes_success(UNIFORM, 85) == V_85,
      "V_85 does not match the pinned exact value")
check(bayes_success(UNIFORM, 84) < Fraction(99, 100),
      "V_84 should be below 99/100")
check(V_85 >= Fraction(99, 100), "V_85 should reach 99/100")
check(abs(float(V_85) - 0.99006833) < 1e-8, "V_85 magnitude drifted")

prev = Fraction(0)
for n in range(1, 101):
    cur = bayes_success(UNIFORM, n)
    check(cur >= prev, f"uniform-prior Bayes success decreased at n={n}")
    prev = cur

n_star_bayes = next(n for n in range(1, 200)
                    if bayes_success(UNIFORM, n) >= Fraction(99, 100))
check(n_star_bayes == 85,
      f"prior-averaged minimax sample size is {n_star_bayes}, expected 85")

succ85 = per_truth_success(UNIFORM, 85)
check(succ85["B"] == succ85["C"],
      "B and C per-truth success should coincide by symmetry")
check(succ85["A"] < succ85["B"],
      "the middle truth A should be strictly harder than B = C")
check((succ85["A"] + succ85["B"] + succ85["C"]) / 3 == V_85,
      "per-truth successes should average to the prior-averaged optimum")


# --- 3 and 4: minimax over truths, sample size, and the certificate ----------

err_86, _ = minimax_error(86)
err_87, gamma_87 = minimax_error(87)
check(err_86 > Fraction(1, 100),
      f"minimax error at n=86 is {float(err_86)}, should exceed 1/100")
check(err_87 <= Fraction(1, 100),
      f"minimax error at n=87 is {float(err_87)}, should be at most 1/100")
check(abs(float(err_87) - 0.00973853) < 1e-8, "minimax error at n=87 drifted")
check(abs(float(gamma_87) - 0.31975938) < 1e-8,
      "least favourable gamma at n=87 drifted")

# The maximising symmetric prior is genuinely least favourable: no other
# symmetric prior gives a larger Bayes error.
for n in (86, 87):
    me, g = minimax_error(n)
    check(all(bayes_error_symmetric(x, n) <= me for x in breakpoints(n)),
          f"a symmetric prior beats the least favourable one at n={n}")
    check(bayes_error_symmetric(g, n) == me,
          f"least favourable prior does not attain the max at n={n}")

# The minimax-over-truths error is non-increasing in n, so n=87 is exact.
prev_err = Fraction(1)
for n in range(1, 101):
    cur_err, _ = minimax_error(n)
    check(cur_err <= prev_err,
          f"minimax error increased at n={n}: {float(cur_err)}")
    prev_err = cur_err

n_star_minimax = next(n for n in range(1, 200)
                      if minimax_error(n)[0] <= Fraction(1, 100))
check(n_star_minimax == 87,
      f"minimax-over-truths sample size is {n_star_minimax}, expected 87")

# Matching certificate: the optimally tie-split Bayes rule for the least
# favourable prior attains the minimax error (upper bound), and the prior gives
# the lower bound (minimax >= Bayes risk for every prior).
for n in (85, 86, 87):
    me, g = minimax_error(n)
    _p, achieved = tie_split_certificate(n, g)
    check(achieved == me,
          f"tie-split Bayes rule at n={n} achieves {float(achieved)}, "
          f"not the minimax {float(me)}")

# Piecewise linearity and concavity of the symmetric-prior Bayes error.
for n in (16, 32, 64, 87):
    check_piecewise_linear_and_concave(n)


# --- 5: conservativeness of the kernel-checked Hellinger union bound ---------

def affinity(x: tuple[Fraction, Fraction],
             y: tuple[Fraction, Fraction]) -> float:
    return sum((float(a) * float(b)) ** 0.5 for a, b in zip(x, y))


rho_star = max(affinity(LAWS["A"], LAWS["B"]),
               affinity(LAWS["A"], LAWS["C"]))
check(abs(rho_star - 0.9659258263) < 1e-9, "rho_* drifted")
import math  # noqa: E402  (kept local to the numeric comparison)

hellinger_n = math.ceil(math.log(2 / 0.01) / math.log(1 / rho_star))
check(hellinger_n == 153, f"Hellinger sufficient size is {hellinger_n}, expected 153")
check(hellinger_n > n_star_bayes,
      "the union bound should be strictly more conservative than the exact optimum")

# At n = 85 the union bound still dominates the exact per-truth error of A.
union85 = 2 * rho_star ** 85
exact_A85 = float(1 - succ85["A"])
check(union85 > exact_A85,
      "the union bound should dominate the exact error at n=85")


# --- 6: zero-mass boundary convention ---------------------------------------

def zero_mass_error(n: int) -> Fraction:
    """P_A{ L_Z >= L_A } for A=(1/2,1/2) and the zero-mass competitor Z=(0,1)."""

    # L_Z(k) = 0 for k < n and 1 for k = n; L_A(k) = 2^{-n} > 0 always.
    # So Z ties/beats A exactly on k = n, whose A-probability is 2^{-n}.
    return pmf("A", n, n)


for n in range(1, 11):
    check(zero_mass_error(n) == Fraction(1, 2 ** n),
          f"zero-mass error at n={n} is not 2^-n")


# --- Report ------------------------------------------------------------------

if FAILURES:
    for failure in FAILURES:
        print(f"FAIL: {failure}")
    raise SystemExit(1)

print("verify_minimax_finite_recovery_265: PASS")
print(f"  family A=(1/2,1/2) B=(3/4,1/4) C=(1/4,3/4), rho_* = {rho_star:.6f}")
print(f"  prior-averaged optimum: n*(99%) = {n_star_bayes}, "
      f"V_85 = {float(V_85):.8f} (V_84 = {float(bayes_success(UNIFORM, 84)):.8f})")
print(f"  per-truth success at n=85: A = {float(succ85['A']):.6f}, "
      f"B = C = {float(succ85['B']):.6f}")
print(f"  minimax-over-truths: n*(99%) = {n_star_minimax}, "
      f"error_87 = {float(err_87):.8f} (error_86 = {float(err_86):.8f})")
print(f"  least favourable prior at n=87: gamma* = {float(gamma_87):.6f}, "
      f"tie-split p = {float(tie_split_certificate(87, gamma_87)[0]):.6f}")
print(f"  Hellinger union bound sufficient size = {hellinger_n} "
      f"(vs exact {n_star_bayes}/{n_star_minimax})")
