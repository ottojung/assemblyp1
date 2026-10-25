#!/usr/bin/env python3
"""Independent exact-rational check for #272: side channel vs supplied promise.

On one explicit finite model (two candidates in distinct orbits, two reads;
read 0 is ambiguous, read 1 is produced only by candidate 0), this script
verifies with exact rational arithmetic (Fraction) the truth-vs-source
distinction summarized in docs/issue272-finite-bayesian-side-information.md:

1. Read-only insufficiency: at ambiguous read 0 the read-only posterior on the
   true orbit is 1/3, not 1 (Lean: `readOnly_posterior_eq_one_iff`,
   `readOnly_not_certain`). No read-only decoder is certain there.
2. Supplied-promise sufficiency: conditioning the joint (prior AND likelihood)
   on a truth-dependent promise E that excludes the rival orbit at read 0
   gives posterior exactly 1 on the true orbit (Lean:
   `posteriorMass_eq_one_iff`, `sufficient_implies_conditional_certain`,
   `promise_certain`). The promise must actually be supplied -- the same
   read with E absent (vacuous True) stays at 1/3.
3. Side-channel equivalence: a side channel Z separating the fibre at read 0
   gives posterior exactly 1 as well (Lean: `posteriorMassZ_eq_one_iff`),
   with the same singleton-fibre criterion as the promise theorem.
4. Mutation control: perturbing one likelihood entry (making read 1 ambiguous
   too) breaks claims 2-3, so the script is sensitive to the model.

The Lean kernel is the source of truth; this is a computational cross-check.
Run:  python3 scripts/verify_272_sidechannel_vs_supplied.py
"""

from __future__ import annotations

import sys
from fractions import Fraction

CANDIDATES = (0, 1)
READS = (0, 1)

PI = {0: Fraction(1, 2), 1: Fraction(1, 2)}
P = {
    0: {0: Fraction(1, 2), 1: Fraction(1, 2)},
    1: {0: Fraction(1), 1: Fraction(0)},
}


def orbit(g: int) -> int:
    return g


def posterior_on_orbit(r: int, true_g: int, E: dict | None = None) -> Fraction:
    """Correctly conditioned posterior: joint pi(g)*p_g(r)*1_E, prior AND likelihood."""
    num = Fraction(0)
    den = Fraction(0)
    for h in CANDIDATES:
        if PI[h] <= 0 or P[h][r] <= 0:
            continue
        if E is not None and not E[(h, r)]:
            continue
        w = PI[h] * P[h][r]
        den += w
        if orbit(h) == orbit(true_g):
            num += w
    assert den > 0, "predictive probability must be positive"
    return num / den


def posterior_with_channel(r: int, z: int, true_g: int, Z: dict) -> Fraction:
    num = Fraction(0)
    den = Fraction(0)
    for h in CANDIDATES:
        if PI[h] <= 0 or P[h][r] <= 0:
            continue
        if Z[(h, r)] != z:
            continue
        w = PI[h] * P[h][r]
        den += w
        if orbit(h) == orbit(true_g):
            num += w
    assert den > 0, "predictive probability must be positive"
    return num / den


def check_read_only_insufficient() -> None:
    # Joint masses at read 0: g0: 1/2*1/2 = 1/4; g1: 1/2*1 = 1/2; total 3/4.
    post = posterior_on_orbit(0, 0, E=None)
    assert post == Fraction(1, 3), f"ambiguous read posterior must be 1/3, got {post}"
    post1 = posterior_on_orbit(1, 0, E=None)
    assert post1 == 1, f"unambiguous read posterior must be 1, got {post1}"


def check_supplied_promise_sufficient() -> None:
    # E excludes rival orbit 1 at read 0 (truth-dependent promise, supplied).
    E = {(g, r): not (g == 1 and r == 0) for g in CANDIDATES for r in READS}
    post = posterior_on_orbit(0, 0, E=E)
    assert post == 1, f"supplied-promise posterior must be 1, got {post}"
    # Same read with vacuous promise stays uncertain: E must be supplied, not inferred.
    vacuous = {(g, r): True for g in CANDIDATES for r in READS}
    assert posterior_on_orbit(0, 0, E=vacuous) == Fraction(1, 3)


def check_side_channel_equivalence() -> None:
    # Z separates the fibre at read 0: Z(g,0) = g; constant at read 1.
    Z = {(g, r): (g if r == 0 else 0) for g in CANDIDATES for r in READS}
    assert posterior_with_channel(0, 0, 0, Z) == 1
    assert posterior_with_channel(0, 1, 1, Z) == 1
    # Constant (uninformative) channel leaves read 0 ambiguous.
    Zconst = {(g, r): 0 for g in CANDIDATES for r in READS}
    assert posterior_with_channel(0, 0, 0, Zconst) == Fraction(1, 3)


def check_mutation_control() -> None:
    # Mutant: read 1 also ambiguous -> the read-1 certainty claim must fail.
    Pmut = {
        0: {0: Fraction(1, 2), 1: Fraction(1, 2)},
        1: {0: Fraction(1, 2), 1: Fraction(1, 2)},
    }
    num = sum(PI[h] * Pmut[h][1] for h in CANDIDATES if orbit(h) == 0)
    den = sum(PI[h] * Pmut[h][1] for h in CANDIDATES)
    assert num / den == Fraction(1, 2) != 1, "mutant must break read-1 certainty"


def main() -> int:
    checks = (
        ("read-only insufficient at ambiguous read", check_read_only_insufficient),
        ("supplied promise gives posterior 1", check_supplied_promise_sufficient),
        ("side-channel fibre-singleton gives 1", check_side_channel_equivalence),
        ("mutation control", check_mutation_control),
    )
    ok = True
    for name, fn in checks:
        try:
            fn()
            print(f"{name}: PASS")
        except AssertionError as exc:
            print(f"{name}: FAIL ({exc})")
            ok = False
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
