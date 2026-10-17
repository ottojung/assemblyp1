#!/usr/bin/env python3
"""Independent exact validation of the #269 Bayes/MAP optimality certificate.

Scope: `AssemblyP1/BayesOptimalityCertificate.lean` (Antonina #269).  That Lean
module closes target B by proving the *necessary* half of finite MAP optimality
and packaging it as an exact certificate, and instantiates the
conditional-posterior-one boundary of target D to the finite family of genome
rotation-equivalence classes.

This script recomputes, from scratch with exact rational arithmetic and no trust
in the Lean output:

  * the optimality certificate `pointwiseMAP_iff_bayesOptimal`: over every
    deterministic policy on a small finite decision problem, a policy attains
    the maximal prior-averaged zero-one success iff it is pointwise MAP, for
    several joint masses including strictly negative entries (the algebraic
    statement needs no positivity);
  * the forcing corollary `pointwiseMAP_forces_strictMax` on a strict-maximizer
    sample;
  * the conditional-posterior-one boundary
    `posterior_eq_one_iff_singleton_support`: with nonnegative joint mass and
    positive predictive mass, the posterior is 1 at theta iff every
    positive-mass candidate is theta;
  * the two smallest witnesses: `TieWitness.both_optimal` (two distinct optimal
    policies) and `StrictLossWitness.strict_loss` (a non-pointwise policy
    strictly loses);
  * the prior-averaged corollary check: the merged
    `GenomeOrbitAdapter.PerTruthDrop` per-truth drop `16/25 < 4/5` is consistent
    with a strictly *increasing* prior-averaged MAP success (`13/20 -> 139/200`).

It is deterministic and exits non-zero on any failed assertion.  It shares no
code with the Lean module.
"""
from fractions import Fraction
from itertools import product
import sys

FAILURES = []


def check(condition, message):
    if not condition:
        FAILURES.append(message)


# --- 1. the optimality certificate on finite decision problems ---------------
# J[theta][x] is the joint mass; may contain negative entries on purpose.
JOINTS = [
    # a generic positive 3x2 joint
    [[Fraction(3), Fraction(1)], [Fraction(2), Fraction(4)], [Fraction(1), Fraction(1)]],
    # ties and a zero entry
    [[Fraction(2), Fraction(0)], [Fraction(2), Fraction(1)], [Fraction(0), Fraction(1)]],
    # strictly negative entries (the algebraic statement is sign-free)
    [[Fraction(-3), Fraction(1)], [Fraction(-1), Fraction(4)], [Fraction(-2), Fraction(-5)]],
    # two candidates, one sample (pure tie)
    [[Fraction(1)], [Fraction(1)]],
]

for J in JOINTS:
    n_theta = len(J)
    n_x = len(J[0])
    thetas = range(n_theta)
    xs = range(n_x)

    def success(d):
        return sum(J[d[x]][x] for x in xs)

    def pointwise(d):
        return all(J[t][x] <= J[d[x]][x] for x in xs for t in thetas)

    policies = list(product(thetas, repeat=n_x))
    best = max(success(d) for d in policies)
    for d in policies:
        optimal = success(d) == best
        check(optimal == pointwise(d),
              f"certificate failed for policy {d} on J={J}: optimal={optimal} pointwise={pointwise(d)}")

# --- 2. forcing at a strict maximizer ---------------------------------------
J = [[Fraction(2), Fraction(1)], [Fraction(1), Fraction(2)]]
# theta=0 strictly maximizes at x=0 (2 > 1) and theta=1 at x=1.
for x, strict in ((0, 0), (1, 1)):
    others = [t for t in range(2) if t != strict]
    check(all(J[t][x] < J[strict][x] for t in others),
          f"strict maximizer expected at x={x}")
# every pointwise (hence every optimal) policy must return the strict maximizer
for d in product(range(2), repeat=2):
    if all(J[t][x] <= J[d[x]][x] for x in range(2) for t in range(2)):
        check(d[0] == 0 and d[1] == 1,
              f"forcing failed: pointwise policy {d} did not return strict maximizers")

# --- 3. posterior-one boundary ----------------------------------------------
# J[theta][x] nonnegative; posterior(theta | x) = J[theta][x] / sum_t J[t][x].
for J in ([[Fraction(3), Fraction(1)], [Fraction(2), Fraction(4)], [Fraction(1), Fraction(1)]],
          [[Fraction(2), Fraction(0)], [Fraction(0), Fraction(0)], [Fraction(0), Fraction(5)]]):
    n_theta = len(J)
    n_x = len(J[0])
    for x in range(n_x):
        denom = sum(J[t][x] for t in range(n_theta))
        if denom == 0:
            continue
        for theta in range(n_theta):
            posterior = J[theta][x] / denom
            singleton = all(J[t][x] <= 0 or t == theta for t in range(n_theta))
            check((posterior == 1) == singleton,
                  f"posterior-one boundary failed: x={x} theta={theta} post={posterior} singleton={singleton}")

# --- 4. smallest witnesses ---------------------------------------------------
# Tie: two candidates, one sample, equal mass.
Jtie = [[Fraction(1)], [Fraction(1)]]
d0, d1 = (0,), (1,)
best_tie = max(sum(Jtie[d[x]][x] for x in range(1)) for d in product(range(2), repeat=1))
check(sum(Jtie[d0[x]][x] for x in range(1)) == best_tie, "tie: policy 0 not optimal")
check(sum(Jtie[d1[x]][x] for x in range(1)) == best_tie, "tie: policy 1 not optimal")
check(d0 != d1, "tie: policies should be distinct")

# Strict loss: constant-1 policy is not pointwise and strictly loses.
Jsl = [[Fraction(2), Fraction(1)], [Fraction(1), Fraction(2)]]
d_const1 = (1, 1)
success_const1 = sum(Jsl[d_const1[x]][x] for x in range(2))
best_sl = max(sum(Jsl[d[x]][x] for x in range(2)) for d in product(range(2), repeat=2))
check(success_const1 == Fraction(3), f"strict-loss: const-1 success {success_const1}")
check(best_sl == Fraction(4), f"strict-loss: best success {best_sl}")
check(success_const1 < best_sl, "strict-loss: const-1 should strictly lose")

# --- 5. PerTruthDrop and prior-averaged monotonicity ------------------------
# Candidate 0: p(A)=4/5, p(C)=1/5; candidate 1: p(A)=p(C)=1/2; uniform prior.
readP = {(0, 0): Fraction(4, 5), (0, 1): Fraction(1, 5),
         (1, 0): Fraction(1, 2), (1, 1): Fraction(1, 2)}
prior = Fraction(1, 2)
half = Fraction(1, 2)


def ml1(w):
    return 0 if half * readP[(0, w)] >= half * readP[(1, w)] else 1


def ml2(a, b):
    return 0 if (half * readP[(0, a)] * readP[(0, b)]
                 >= half * readP[(1, a)] * readP[(1, b)]) else 1


perTruth1 = sum(readP[(0, w)] for w in (0, 1) if ml1(w) == 0)
perTruth2 = sum(readP[(0, a)] * readP[(0, b)]
                for a in (0, 1) for b in (0, 1) if ml2(a, b) == 0)
check(perTruth1 == Fraction(4, 5), f"perTruth_true_one failed: {perTruth1}")
check(perTruth2 == Fraction(16, 25), f"perTruth_true_two failed: {perTruth2}")
check(perTruth2 < perTruth1, "perTruth_true_drops failed")

# Prior-averaged MAP success: sum_x max_theta prior * prod_i p_theta(x_i).
def map_success(n):
    total = Fraction(0)
    for sample in product((0, 1), repeat=n):
        best = Fraction(0)
        for theta in (0, 1):
            prod = prior
            for w in sample:
                prod *= readP[(theta, w)]
            best = max(best, prod)
        total += best
    return total


V1 = map_success(1)
V2 = map_success(2)
check(V1 == Fraction(13, 20), f"prior-averaged V_1 should be 13/20, got {V1}")
check(V2 == Fraction(139, 200), f"prior-averaged V_2 should be 139/200, got {V2}")
check(V1 <= V2, "prior-averaged success must not decrease (PerTruthDrop is not a prior-average claim)")

# --- report -----------------------------------------------------------------
if FAILURES:
    print(f"FAIL: {len(FAILURES)} assertion(s) failed", file=sys.stderr)
    for f in FAILURES[:20]:
        print(f"  - {f}", file=sys.stderr)
    sys.exit(1)

print("PASS: verify_269_bayes_optimality_certificate — all exact rational checks succeeded")
print(f"  certificate over {sum(len(list(product(range(len(J)), repeat=len(J[0])))) for J in JOINTS)} policies; "
      f"per-truth 1-read={perTruth1} 2-read={perTruth2}; prior-averaged V_1={V1} V_2={V2}")
