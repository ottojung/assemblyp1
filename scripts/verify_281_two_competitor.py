#!/usr/bin/env python3
"""Cross-check for issue #281: two-competitor exact-ML error vs rho^n bound.

Binary read alphabet W = {0, 1} with truth p = (3/4, 1/4) and competitors
q1 = (1/4, 3/4), q2 = (1/2, 1/2).  For each n in 0..N, brute-force
enumeration over all 2^n read tuples (exact rational arithmetic via
Fraction) computes:

  exact(n) = P_p(exists q in {q1,q2} with L_q(t) >= L_p(t))

i.e. the exact wrong-selection probability with ties counted as errors
(matching `wrongEvent`/`eventProb` in AssemblyP1/FiniteReadRecovery.lean),
and checks exact(n) <= rho1^n + rho2^n where rhoi is the Hellinger
affinity sum_w sqrt(p(w)*q(w)).

Mutation control: `--mutate` scales the bound down by 10x.  The script
must then report at least one violation and exit 0 (control passes,
proving the comparison is non-vacuous); if no violation appears the
control fails with a nonzero exit.

Usage:
  python3 scripts/verify_281_two_competitor.py [--n-max N] [--mutate]
"""

import argparse
import itertools
import math
import sys
from fractions import Fraction

P = (Fraction(3, 4), Fraction(1, 4))
Q1 = (Fraction(1, 4), Fraction(3, 4))
Q2 = (Fraction(1, 2), Fraction(1, 2))


def affinity(p, q):
    return sum(math.sqrt(float(pw * qw)) for pw, qw in zip(p, q))


def likelihood(dist, tup):
    r = Fraction(1, 1)
    for w in tup:
        r *= dist[w]
    return r


def exact_wrong_prob(n, competitors, strict=False):
    """Exact P_p(some competitor ties-or-beats truth)."""
    total = Fraction(0, 1)
    for tup in itertools.product((0, 1), repeat=n):
        lp = likelihood(P, tup)
        wrong = any(
            (likelihood(q, tup) > lp if strict else likelihood(q, tup) >= lp)
            for q in competitors
        )
        if wrong:
            total += lp
    return total


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n-max", type=int, default=10)
    ap.add_argument("--mutate", action="store_true",
                    help="shrink the bound 10x; violations must then appear")
    args = ap.parse_args()
    shrink = 0.1 if args.mutate else 1.0

    rho1 = affinity(P, Q1)
    rho2 = affinity(P, Q2)
    print(f"rho(p,q1) = {rho1:.12f}  (sqrt(3)/2 = {math.sqrt(3)/2:.12f})")
    print(f"rho(p,q2) = {rho2:.12f}")
    assert rho1 < 1.0 and rho2 < 1.0, "identifiability hypothesis violated"

    failures = 0
    for n in range(args.n_max + 1):
        exact = exact_wrong_prob(n, (Q1, Q2), strict=False)
        bound = shrink * (rho1 ** n + rho2 ** n)
        ok = float(exact) <= bound + 1e-12
        status = "OK " if ok else "FAIL"
        if not ok:
            failures += 1
        print(f"n={n:2d} exact={float(exact):.10f} ({exact}) "
              f"bound={bound:.10f} [{status}]")

    if args.mutate:
        if failures == 0:
            print("MUTATION-CONTROL FAILURE: shrunk bound never violated; "
                  "check is vacuous")
            return 1
        print(f"mutation control: shrunk bound violated at {failures} "
              f"value(s) of n; check is non-vacuous")
        return 0

    if failures:
        print(f"{failures} bound violation(s)")
        return 1
    print("all bounds hold")
    return 0


if __name__ == "__main__":
    sys.exit(main())
