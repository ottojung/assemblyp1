#!/usr/bin/env python3
"""Check finite-read large-deviation rates, including asymmetric support.

The one-sided event Pr_p(L_q >= L_p) has exponent
    E_+(p,q) = -log inf_{t>0} E_p[(q/p)^t],
not in general the symmetric Chernoff information optimized on [0,1].
The full-support two-symbol family happens to satisfy equality; the
oriented AAB/AABB read-law pair is the regression for E_+=infinity.
This independent verifier is not a Lean proof.
"""

from __future__ import annotations

import math
from fractions import Fraction

FAILURES: list[str] = []


def check(condition: bool, message: str) -> None:
    if not condition:
        FAILURES.append(message)


def chernoff(p: tuple[Fraction, ...], q: tuple[Fraction, ...]) -> float:
    """sup_t -ln sum_{p(w)>0} p(w)^(1-t) q(w)^t by ternary search."""

    def g(t: float) -> float:
        total = 0.0
        for a, b in zip(p, q):
            if a == 0:
                continue
            total += float(a) ** (1.0 - t) * float(b) ** t
        return total

    lo, hi = 0.0, 1.0
    for _ in range(500):
        m1 = lo + (hi - lo) / 3.0
        m2 = hi - (hi - lo) / 3.0
        if g(m1) < g(m2):
            hi = m2
        else:
            lo = m1
    t = (lo + hi) / 2.0
    return -math.log(g(t))


def one_sided_exponent(p: tuple[Fraction, ...],
                       q: tuple[Fraction, ...]) -> float:
    """One-sided log-moment rate, including infinite impossible-error rates."""
    positive = [(float(a), math.log(float(b / a)))
                for a, b in zip(p, q) if a > 0 and b > 0]
    if not positive or max(lr for _, lr in positive) < 0:
        return math.inf

    def log_moment_and_slope(t: float) -> tuple[float, float]:
        xs = [math.log(w) + t * lr for w, lr in positive]
        hi = max(xs)
        exp_xs = [math.exp(x - hi) for x in xs]
        sm = sum(exp_xs)
        return hi + math.log(sm), sum(v * lr for v, (_, lr) in zip(exp_xs, positive)) / sm

    if max(lr for _, lr in positive) == 0:
        eqmass = sum(w for w, lr in positive if lr == 0)
        return -math.log(eqmass)
    if log_moment_and_slope(0.0)[1] >= 0:
        return -log_moment_and_slope(0.0)[0]
    lo, hi = 0.0, 1.0
    while log_moment_and_slope(hi)[1] < 0:
        hi *= 2
        if hi > 1e7:
            raise RuntimeError("Unreasonably distant one-sided optimum")
    for _ in range(110):
        mid = (lo + hi) / 2
        if log_moment_and_slope(mid)[1] < 0:
            lo = mid
        else:
            hi = mid
    return -log_moment_and_slope((lo + hi) / 2)[0]


def affinity(p: tuple[Fraction, ...], q: tuple[Fraction, ...]) -> float:
    return sum(math.sqrt(float(a) * float(b)) for a, b in zip(p, q))


def likelihood(law: tuple[Fraction, ...], counts: tuple[int, int]) -> Fraction:
    out = Fraction(1)
    for prob, k in zip(law, counts):
        out *= prob ** k
    return out


# --- Worked family ------------------------------------------------------------

P = (Fraction(3, 4), Fraction(1, 4))          # truth read law p_S
Q1 = (Fraction(1, 4), Fraction(3, 4))         # symmetric competitor
Q2 = (Fraction(0), Fraction(1))               # one-sided competitor
FAMILY = (Q1, Q2)

C_PQ1 = chernoff(P, Q1)
C_PQ2 = chernoff(P, Q2)
C_STAR = min(C_PQ1, C_PQ2)
RHO_PQ1 = affinity(P, Q1)
RHO_PQ2 = affinity(P, Q2)
RHO_STAR = max(RHO_PQ1, RHO_PQ2)

check(C_STAR > 0.0, f"C_* = {C_STAR} is not positive")
check(RHO_STAR < 1.0, f"rho_* = {RHO_STAR} is not < 1")

# Symmetric pair: C = -ln rho exactly (t* = 1/2); C >= -ln rho throughout.
check(abs(C_PQ1 - (-math.log(RHO_PQ1))) < 1e-9,
      "symmetric pair should have C = -ln rho")
check(C_PQ1 >= -math.log(RHO_PQ1) - 1e-9, "C(q1) < -ln rho(q1)")
check(C_PQ2 >= -math.log(RHO_PQ2) - 1e-9, "C(q2) < -ln rho(q2)")


def exact_error(n: int) -> Fraction:
    err = Fraction(0)
    for k in range(n + 1):
        weight = (Fraction(math.comb(n, k))
                  * (Fraction(3, 4) ** (n - k)) * (Fraction(1, 4) ** k))
        counts = (n - k, k)
        lp = likelihood(P, counts)
        if any(likelihood(q, counts) >= lp for q in FAMILY):
            err += weight
    return err


# --- 1 and 2: exact enumeration, both bounds, termwise ordering, gap ----------

ratio_at_16 = None
for n in range(1, 17):
    error = exact_error(n)
    error_f = float(error)
    hell = RHO_PQ1 ** n + RHO_PQ2 ** n
    cher = math.exp(-n * C_PQ1) + math.exp(-n * C_PQ2)
    check(error_f <= hell + 1e-15, f"Hellinger bound fails at n={n}")
    check(error_f <= cher + 1e-15, f"Chernoff bound fails at n={n}")
    check(cher <= hell + 1e-15, f"Chernoff bound exceeds Hellinger at n={n}")
    check(math.exp(-n * C_PQ1) <= RHO_PQ1 ** n + 1e-15,
          f"termwise Chernoff > Hellinger for q1 at n={n}")
    check(math.exp(-n * C_PQ2) <= RHO_PQ2 ** n + 1e-15,
          f"termwise Chernoff > Hellinger for q2 at n={n}")
    if n == 16:
        ratio_at_16 = cher / error_f

check(ratio_at_16 is not None, "no n = 16 ratio computed")
check(3.0 < ratio_at_16 < 4.5,
      f"recorded n=16 gap ratio {ratio_at_16} is outside (3.0, 4.5)")


# --- 3: C >= -ln rho, equality symmetric, strict non-symmetric ----------------

Pn = (Fraction(9, 10), Fraction(1, 10))
Qn = (Fraction(1, 2), Fraction(1, 2))
C_nonsym = chernoff(Pn, Qn)
rho_nonsym = affinity(Pn, Qn)
check(C_nonsym >= -math.log(rho_nonsym) - 1e-9, "non-symmetric pair violates C >= -ln rho")
check(C_nonsym > -math.log(rho_nonsym) + 1e-6,
      "non-symmetric pair should have strictly C > -ln rho")

# --- 4: exact exponent converges to C_* and to C(p,q) -------------------------

N_EXP = 512
error_big = exact_error(N_EXP)
exp_family = -math.log(float(error_big)) / N_EXP
check(abs(exp_family - C_STAR) < 1.5e-2,
      f"family exponent {exp_family} does not approach C_* = {C_STAR}")

# The bound columns of the docs table at n = 64, 256, 512 must agree with the
# exact q1 term 3^(n/2)/2^n (the q2 terms are negligible there).  This pins the
# large-n rows that floating-point evaluation of rho^n or exp(-n C) could spoil.
DOC_BOUNDS = {64: 1.004524e-04, 256: 1.018220e-16, 512: 1.036772e-32}
DOC_RATIOS = {64: 6.896, 256: 13.483, 512: 18.988}
for n, recorded in DOC_BOUNDS.items():
    exact_q1 = float(Fraction(3) ** (n // 2) / Fraction(2) ** n)
    check(abs(exact_q1 / recorded - 1.0) < 1e-4,
          f"docs bound at n={n} ({recorded}) disagrees with 3^(n/2)/2^n")
    check(abs(math.exp(-n * C_PQ1) / exact_q1 - 1.0) < 1e-9,
          f"exp(-n C(q1)) disagrees with the exact 3^(n/2)/2^n at n={n}")
    check(abs(RHO_PQ1 ** n / exact_q1 - 1.0) < 1e-9,
          f"rho(q1)^n disagrees with the exact 3^(n/2)/2^n at n={n}")
    ratio = (math.exp(-n * C_PQ1) + math.exp(-n * C_PQ2)) / float(exact_error(n))
    check(abs(ratio / DOC_RATIOS[n] - 1.0) < 0.01,
          f"docs bound/exact ratio at n={n} ({ratio:.3f}) disagrees with "
          f"{DOC_RATIOS[n]}")


def exact_binary_error(n: int, p: tuple[Fraction, ...],
                       q: tuple[Fraction, ...]) -> Fraction:
    err = Fraction(0)
    for k in range(n + 1):
        weight = (Fraction(math.comb(n, k))
                  * (p[0] ** (n - k)) * (p[1] ** k))
        counts = (n - k, k)
        if likelihood(q, counts) >= likelihood(p, counts):
            err += weight
    return err


exp_binary = -math.log(float(exact_binary_error(N_EXP, Pn, Qn))) / N_EXP
check(abs(exp_binary - C_nonsym) < 1.5e-2,
      f"binary exponent {exp_binary} does not approach C = {C_nonsym}")

# --- Support-mismatch regression: S=AAB, D=AABB, L=2 -----------------------
# Truth has AA, AB, BA uniformly; competitor also has BB.
P3 = (Fraction(1, 3), Fraction(1, 3), Fraction(1, 3), Fraction(0))
Q4 = (Fraction(1, 4), Fraction(1, 4), Fraction(1, 4), Fraction(1, 4))
assert sum(P3) == sum(Q4) == 1
C_SYMMETRIC = chernoff(P3, Q4)
ONE_SIDED = one_sided_exponent(P3, Q4)
check(abs(C_SYMMETRIC - math.log(Fraction(4, 3))) < 1e-9,
      "conventional Chernoff for AAB/AABB should be log(4/3)")
check(ONE_SIDED == math.inf, "one-sided AAB/AABB rate must be infinite")
for n in range(1, 11):
    ratio = Fraction(3, 4) ** n
    check(ratio < 1, f"AAB/AABB competitor unexpectedly ties at n={n}")
check(abs(one_sided_exponent(P, Q1) - C_PQ1) < 1e-8,
      "full-support symmetric rate differs")
check(abs(one_sided_exponent(P, Q2) - C_PQ2) < 1e-8,
      "competitor supported inside truth differs")
P_EXTRA = (Fraction(3, 4), Fraction(1, 4), Fraction(0))
Q_EXTRA = (Fraction(2, 5), Fraction(2, 5), Fraction(1, 5))
check(one_sided_exponent(P_EXTRA, Q_EXTRA) > chernoff(P_EXTRA, Q_EXTRA) + 1e-5,
      "asymmetric extra-support example should require t>1")

# --- Report -------------------------------------------------------------------

if FAILURES:
    for failure in FAILURES:
        print(f"FAIL: {failure}")
    raise SystemExit(1)

print("verify_chernoff_finite_recovery_265: PASS")
print(f"  worked family: rho_* = {RHO_STAR:.6f}, "
      f"C_* = {C_STAR:.6f} (>= ln(1/rho_*) = {-math.log(RHO_STAR):.6f})")
print(f"  n = 16: exact error {float(exact_error(16)):.6e}, "
      f"bound/exact ratio {ratio_at_16:.4f} (~3.7 recorded)")
print(f"  exact family exponent at n = {N_EXP}: {exp_family:.6f} "
      f"-> C_* = {C_STAR:.6f}")
print(f"  non-symmetric pair: C = {C_nonsym:.6f} > -ln rho = "
      f"{-math.log(rho_nonsym):.6f}")
print(f"  exact binary exponent at n = {N_EXP}: {exp_binary:.6f} "
      f"-> C = {C_nonsym:.6f}")

print(f"  support-mismatch AAB/AABB: symmetric C={C_SYMMETRIC:.6f}; one-sided E_+=infinity; error=0")
