#!/usr/bin/env python3
"""Independent verifier for AssemblyP1/FiniteSourceDefinedMinimal.lean (#272, target 4).

Cross-checks, by brute force over the finite promise space, the kernel-checked
results about the minimum / minimal / weakest distinction in the source-defined
family on the ambiguous TwoCandidate model (two candidates, one read, both
realizable, distinct orbits):

1. sufficient_iff_not_both: a promise is sufficient iff it does not admit both
   candidates.
2. nonvacuous_sufficient_is_designation: every non-vacuous sufficient promise is
   a candidate designation (g = 0 or g = 1).
3. designation_nonvacuous_sufficient: both designations are non-vacuous and
   sufficient.
4. designations_incomparable: the two designations are incomparable.
5. three_way_distinction: a minimum exists (empty), the non-vacuous sufficient
   certificates are the designations, and no weakest source-defined member exists.

The Lean kernel is the source of truth; this is an independent computational
cross-check.  Run:  python3 scripts/verify_272_minimal_sufficient.py
"""

import sys


CANDIDATES = [0, 1]
READS = [0]


def orbit(x):
    return x


def pi(g):
    return 0.5


def p(g, r):
    return 1.0


def promises():
    """All promises Fin 2 -> Fin 1 -> Prop, as (E00, E10) boolean pairs."""
    for e00 in (False, True):
        for e10 in (False, True):
            yield e00, e10


def E_val(e, g, r):
    return e[g]


def sufficient(e):
    for g in CANDIDATES:
        for r in READS:
            if pi(g) <= 0 or p(g, r) <= 0 or not E_val(e, g, r):
                continue
            for h in CANDIDATES:
                if pi(h) <= 0 or p(h, r) <= 0 or not E_val(e, h, r):
                    continue
                if orbit(h) != orbit(g):
                    return False
    return True


def nonvacuous(e):
    return any(E_val(e, g, r) for g in CANDIDATES for r in READS)


def check_sufficient_iff_not_both():
    for e in promises():
        admits_both = E_val(e, 0, 0) and E_val(e, 1, 0)
        assert sufficient(e) == (not admits_both), (
            f"sufficient_iff_not_both failed for {e}: "
            f"sufficient={sufficient(e)}, admits_both={admits_both}"
        )


def check_nonvacuous_sufficient_is_designation():
    for e in promises():
        if sufficient(e) and nonvacuous(e):
            is_designation = (
                all(E_val(e, g, r) == (g == 0) for g in CANDIDATES for r in READS)
                or all(E_val(e, g, r) == (g == 1) for g in CANDIDATES for r in READS)
            )
            assert is_designation, (
                f"nonvacuous sufficient promise {e} is not a candidate designation"
            )


def check_designation_nonvacuous_sufficient():
    for g0 in CANDIDATES:
        e = tuple((g == g0) for g in CANDIDATES)
        assert sufficient(e), f"designation g={g0} is not sufficient"
        assert nonvacuous(e), f"designation g={g0} is vacuous"


def check_designations_incomparable():
    e0 = tuple((g == 0) for g in CANDIDATES)
    e1 = tuple((g == 1) for g in CANDIDATES)

    def stronger(a, b):
        return all((not E_val(a, g, r)) or E_val(b, g, r)
                   for g in CANDIDATES for r in READS)

    assert not stronger(e0, e1), "g=0 designation implies g=1 designation"
    assert not stronger(e1, e0), "g=1 designation implies g=0 designation"


def check_three_way():
    # A minimum sufficient promise exists: the empty promise is vacuously sufficient.
    empty = tuple(False for _ in CANDIDATES)
    assert sufficient(empty), "empty promise is not sufficient"
    assert not nonvacuous(empty), "empty promise is non-vacuous"

    # Non-vacuous sufficient promises are exactly the two designations.
    nv_sufficient = [e for e in promises() if sufficient(e) and nonvacuous(e)]
    designations = [tuple((g == 0) for g in CANDIDATES),
                    tuple((g == 1) for g in CANDIDATES)]
    assert sorted(nv_sufficient) == sorted(designations), (
        f"non-vacuous sufficient promises {nv_sufficient} != designations {designations}"
    )

    # No weakest source-defined member: the union (True) is insufficient.
    union = tuple(True for _ in CANDIDATES)
    assert not sufficient(union), "union (True) is sufficient, so a weakest exists"


if __name__ == "__main__":
    ok = True
    checks = [
        ("sufficient_iff_not_both", check_sufficient_iff_not_both),
        ("nonvacuous_sufficient_is_designation", check_nonvacuous_sufficient_is_designation),
        ("designation_nonvacuous_sufficient", check_designation_nonvacuous_sufficient),
        ("designations_incomparable", check_designations_incomparable),
        ("three_way_distinction", check_three_way),
    ]
    for name, fn in checks:
        try:
            fn()
            print(f"{name}: PASS")
        except AssertionError as e:
            print(f"{name}: FAIL ({e})")
            ok = False
    sys.exit(0 if ok else 1)
