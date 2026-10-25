#!/usr/bin/env python3
"""Independent exact-rational check for #272 promise-family weakness (#272).

On one explicit finite model (two candidates in distinct orbits, two reads;
read 0 is ambiguous, read 1 is produced only by candidate 0), this script
enumerates all 2**(2*2) = 16 truth-dependent promises E : Genome x Obs -> Prop
with exact rational arithmetic (Fraction) and verifies the family distinction
summarized in docs/issue272-finite-bayesian-side-information.md section 8:

1. The read-only family HAS a weakest sufficient promise, namely Unambiguous
   (holds exactly at read 1); it is implied by every sufficient read-only
   promise and is itself sufficient and read-only.
2. The source-defined family (read-only OR truth-only) has NO weakest
   sufficient promise: the union of all sufficient source-defined promises is
   the vacuous promise True, and True is insufficient (read 0 stays ambiguous).
3. Minimum vs minimal: at least two incomparable *minimal* sufficient
   source-defined promises exist (no strictly weaker sufficient source-defined
   promise below either), so minimal elements exist while no minimum does.

Definitions mirror the Lean kernel (AssemblyP1/FiniteBayesianSideInformation.lean
`Sufficient`, `Stronger`; AssemblyP1/FiniteSideInformationOrder.lean
`IsWeakestAdmissible` restricted to each family): E is sufficient iff every
positive-prior, positive-likelihood fibre selected by E at a read lies in one
orbit class.  The Lean kernel is the source of truth; this is a computational
cross-check.  Run:  python3 scripts/verify_272_source_vs_arbitrary.py
"""

from __future__ import annotations

import itertools
import sys
from fractions import Fraction

CANDIDATES = (0, 1)
READS = (0, 1)

# Equal priors; read 0 ambiguous, read 1 only from candidate 0.
PI = {0: Fraction(1, 2), 1: Fraction(1, 2)}
P = {
    0: {0: Fraction(1, 2), 1: Fraction(1, 2)},
    1: {0: Fraction(1), 1: Fraction(0)},
}


def orbit(g: int) -> int:
    return g


def sufficient(E: dict) -> bool:
    """Lean `Sufficient`: supported fibre at each read is a single orbit."""
    for g in CANDIDATES:
        if PI[g] <= 0:
            continue
        for r in READS:
            if P[g][r] <= 0:
                continue
            if not E[(g, r)]:
                continue
            for h in CANDIDATES:
                if PI[h] <= 0:
                    continue
                if P[h][r] <= 0:
                    continue
                if not E[(h, r)]:
                    continue
                if orbit(h) != orbit(g):
                    return False
    return True


def implies(E1: dict, E2: dict) -> bool:
    """Lean `Stronger E1 E2`: E1 is at least as strong (informative) as E2."""
    return all((not E1[k]) or E2[k] for k in E1)


def is_read_only(E: dict) -> bool:
    return all(E[(g, r)] == E[(gp, r)] for g in CANDIDATES for gp in CANDIDATES for r in READS)


def is_truth_only(E: dict) -> bool:
    return all(E[(g, r)] == E[(g, rp)] for g in CANDIDATES for r in READS for rp in READS)


def is_source_defined(E: dict) -> bool:
    return is_read_only(E) or is_truth_only(E)


def all_promises() -> list[dict]:
    keys = [(g, r) for g in CANDIDATES for r in READS]
    out = []
    for mask in range(1 << len(keys)):
        out.append({k: bool(mask & (1 << i)) for i, k in enumerate(keys)})
    return out


def unambiguous_promise() -> dict:
    """Read-only `Unambiguous`: holds exactly where the read support is one orbit."""
    E = {}
    for g in CANDIDATES:
        for r in READS:
            seen = {orbit(h) for h in CANDIDATES if PI[h] > 0 and P[h][r] > 0}
            E[(g, r)] = len(seen) == 1
    return E


def check_read_only_weakest(promises: list[dict]) -> None:
    ro_sufficient = [E for E in promises if is_read_only(E) and sufficient(E)]
    assert ro_sufficient, "expected sufficient read-only promises (False and read-1)"
    W = unambiguous_promise()
    assert is_read_only(W), "Unambiguous must be read-only"
    assert sufficient(W), "Unambiguous must be sufficient"
    assert W[(0, 0)] is False and W[(0, 1)] is True, "read 0 ambiguous, read 1 not"
    for E in ro_sufficient:
        assert implies(E, W), "Unambiguous must be implied by every sufficient read-only E"
    # Uniqueness within read-only: any other weakest read-only W' agrees with W
    # wherever the comparison is decided by the positive support.
    for E in promises:
        if is_read_only(E) and sufficient(E) and all(implies(F, E) for F in ro_sufficient):
            for r in READS:
                assert E[(0, r)] == W[(0, r)], "weakest read-only is unique on support"


def check_no_weakest_source_defined(promises: list[dict]) -> None:
    sd_sufficient = [E for E in promises if is_source_defined(E) and sufficient(E)]
    assert sd_sufficient, "singletons are sufficient source-defined promises"
    union = {k: any(E[k] for E in sd_sufficient) for k in sd_sufficient[0]}
    assert all(union.values()), "union of sufficient source-defined must be True"
    assert not sufficient(union), "union True must be insufficient (read 0 ambiguous)"
    for W in promises:
        if not (is_source_defined(W) and sufficient(W)):
            continue
        assert any(not implies(E, W) for E in sd_sufficient), (
            "no sufficient source-defined W is implied by all of them"
        )


def check_minimal_without_minimum(promises: list[dict]) -> None:
    sd_sufficient = [E for E in promises if is_source_defined(E) and sufficient(E)]

    def strictly_weaker(E: dict, W: dict) -> bool:
        return implies(W, E) and not implies(E, W)

    minimals = [
        W
        for W in sd_sufficient
        if not any(
            is_source_defined(E) and sufficient(E) and strictly_weaker(E, W)
            for E in sd_sufficient
        )
    ]
    assert len(minimals) >= 2, f"expected >= 2 minimal sufficient source-defined, got {len(minimals)}"
    assert any(
        not implies(A, B) and not implies(B, A)
        for A, B in itertools.combinations(minimals, 2)
    ), "minimal elements must include an incomparable pair"


def main() -> int:
    promises = all_promises()
    assert len(promises) == 16
    checks = (
        ("read-only weakest = Unambiguous", check_read_only_weakest),
        ("no weakest source-defined", check_no_weakest_source_defined),
        ("minimal without minimum", check_minimal_without_minimum),
    )
    ok = True
    for name, fn in checks:
        try:
            fn(promises)
            print(f"{name}: PASS")
        except AssertionError as exc:
            print(f"{name}: FAIL ({exc})")
            ok = False
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
