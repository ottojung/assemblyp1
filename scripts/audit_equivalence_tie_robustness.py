#!/usr/bin/env python3
"""Audit how cyclic-shift / reverse-complement equivalence and tie semantics
interact with the integrated strict-improvement counterexamples.

The audit is purely logical on the equivalence side:

  * A witness with ``L(D) > L(S)`` refutes "truth is a maximizer" over any
    candidate class containing ``D``, no matter how genomes are quotiented,
    because the maximizer predicate never mentions the equivalence relation.
  * If the objective is invariant on the equivalence classes, then ``L(D) >
    L(S)`` also forces ``D`` and ``S`` to be non-equivalent.  There is no
    convention under which a strict-improvement witness can be "quotiented
    away".
  * This script confirms those two hypotheses for every integrated witness:
    each competitor is outside the truth's cyclic-shift orbit (and, where a
    DNA reverse complement is defined, outside its dihedral orbit), while the
    per-witness objective is invariant under those operations.

Exits non-zero on any failed assertion.  Uses exact ``fractions.Fraction``.
Run: ``python3 scripts/audit_equivalence_tie_robustness.py``
"""

from __future__ import annotations

import sys
from fractions import Fraction
from itertools import product
from math import factorial


DNA_COMP = {"A": "T", "T": "A", "C": "G", "G": "C"}


def rotations(s: str):
    n = len(s)
    return {s[i:] + s[:i] for i in range(n)}


def revcomp(s: str, comp=None):
    comp = comp or DNA_COMP
    return "".join(comp[c] for c in reversed(s))


def dihedral_orbit(s: str, comp=None):
    comp = comp or DNA_COMP
    if not set(s) <= set(comp):
        return None
    r = revcomp(s, comp)
    return rotations(s) | rotations(r)


# ---------------------------------------------------------------------------
# Objective helpers
# ---------------------------------------------------------------------------

def windows(s: str, L: int):
    n = len(s)
    return ["".join(s[(i + d) % n] for d in range(L)) for i in range(n)]


def exact_multinomial(seq: str, obs_counts: dict, L: int) -> Fraction:
    """Exact MB09 §6.1 candidate-intrinsic-N multinomial (constants kept)."""
    n = sum(obs_counts.values())
    N = len(seq)
    spec = windows(seq, L)
    coeff = Fraction(factorial(n), 1)
    for k in obs_counts.values():
        coeff /= factorial(k)
    val = coeff
    for w, x in obs_counts.items():
        d = spec.count(w)
        val *= Fraction(d, N) ** x
    return val


def fixedN_binomial(seq: str, obs_counts: dict, L: int, N: int,
                    alphabet: str) -> Fraction:
    """Literal §6.1 product of binomial marginals over the full type space."""
    n = sum(obs_counts.values())
    spec = windows(seq, L)
    val = Fraction(1)
    for tup in product(alphabet, repeat=L):
        w = "".join(tup)
        d = spec.count(w)
        x = obs_counts.get(w, 0)
        val *= Fraction(factorial(n), factorial(x) * factorial(n - x))
        val *= Fraction(d, N) ** x
        val *= Fraction(N - d, N) ** (n - x)
    return val


def fixedN_binomial_observed_only(seq: str, obs_counts: dict, L: int,
                                  N: int) -> Fraction:
    """Product of binomial marginals restricted to positive observed counts
    (zero-count factors omitted)."""
    n = sum(obs_counts.values())
    spec = windows(seq, L)
    val = Fraction(1)
    for w, x in obs_counts.items():
        d = spec.count(w)
        val *= Fraction(factorial(n), factorial(x) * factorial(n - x))
        val *= Fraction(d, N) ** x
        val *= Fraction(N - d, N) ** (n - x)
    return val


# ---------------------------------------------------------------------------
# Witness table
# ---------------------------------------------------------------------------
# Each entry: name, truth, competitor, L, observed counts, equivalence test
# mode ("shift" or "dihedral"), and the objective used for the strict cmp.

def W_exact_variant_e():
    S, D, L = "ACGT", "ACACGT", 2
    obs = {"AC": 2, "GT": 1}
    return dict(
        name="ExactVariantE #24 (oriented, unrestricted length)",
        S=S, D=D, L=L, obs=obs, alphabet="ACGT", mode="shift",
        ratio=lambda s: exact_multinomial(s, obs, L),
    )


def W_fixed_exact():
    # 4-letter abstract alphabet; symbols B do not form a DNA complement, so
    # only the cyclic-shift orbit is defined for this witness.
    S, D, L = "AAABB", "AAAAB", 3
    obs = {"AAA": 1, "AAB": 1, "BAA": 1}
    return dict(
        name="FixedLengthExact #31 (abstract alphabet, same length)",
        S=S, D=D, L=L, obs=obs, alphabet="ABCG", mode="shift",
        ratio=lambda s: exact_multinomial(s, obs, L),
    )


def W_fixed_binomial():
    S, D, L, N = "AAACC", "AAAAC", 3, 5
    obs = {"AAA": 1, "AAC": 1, "CAA": 1}
    return dict(
        name="FixedLengthBinomial #32 (abstract alphabet, same length)",
        S=S, D=D, L=L, obs=obs, alphabet="ACGT", mode="shift",
        ratio=lambda s: fixedN_binomial(s, obs, L, N, "ACGT"),
    )


def W_section62():
    S, D, L, N = "AAATT", "AAAATT", 3, 5
    comp = {"A": "T", "T": "A"}
    obs = {"AAA": 1, "AAT": 1, "TAA": 1}
    return dict(
        name="Section62 #36 (molecule classes, variable length)",
        S=S, D=D, L=L, obs=obs, alphabet="AT", mode="dihedral",
        comp=comp,
        ratio=lambda s: _molecule_fixedN(s, obs, L, N, comp),
    )


def W_same_length():
    S, D, L, N = "AAATAT", "AAAAAT", 3, 6
    comp = {"A": "T", "T": "A"}
    obs = {"AAA": 2, "AAT": 1, "ATA": 1, "TAA": 1}
    return dict(
        name="SameLength #43 (molecule classes, same length)",
        S=S, D=D, L=L, obs=obs, alphabet="AT", mode="dihedral",
        comp=comp,
        ratio=lambda s: _molecule_fixedN(s, obs, L, N, comp),
    )


def _molecule_class(w: str, comp) -> str:
    return min(w, revcomp(w, comp))


def _molecule_fixedN(seq: str, obs: dict, L: int, N: int, comp) -> Fraction:
    """§6.1 product of binomial marginals indexed by molecule classes."""
    n = sum(obs.values())
    spec = [_molecule_class(w, comp) for w in windows(seq, L)]
    val = Fraction(1)
    for w, x in obs.items():
        d = spec.count(w)
        val *= Fraction(factorial(n), factorial(x) * factorial(n - x))
        val *= Fraction(d, N) ** x
        val *= Fraction(N - d, N) ** (n - x)
    return val


def main() -> int:
    failures = []

    def check(cond, msg):
        if not cond:
            failures.append(msg)
            print(f"  FAIL: {msg}")
        else:
            print(f"  ok:   {msg}")

    for w in [W_exact_variant_e(), W_fixed_exact(), W_fixed_binomial(),
              W_section62(), W_same_length()]:
        print(f"\n== {w['name']} ==")
        S, D = w["S"], w["D"]
        print(f"   S = {S}  (|S|={len(S)})")
        print(f"   D = {D}  (|D|={len(D)})")

        # 1. Strict improvement.
        rS, rD = w["ratio"](S), w["ratio"](D)
        ratio = rD / rS
        print(f"   L(D)/L(S) = {ratio}  ({float(ratio):.6f})")
        check(ratio > 1, "competitor strictly improves the objective")

        # 2. Non-equivalence of D from S.
        if w["mode"] == "dihedral":
            orb = dihedral_orbit(S, w["comp"])
            check(orb is not None, "reverse complement defined on this alphabet")
            check(D not in orb,
                  "D is outside the dihedral (shift + revcomp) orbit of S")
            # objective invariance under the full dihedral group
            inv = True
            for r in orb:
                if w["ratio"](r) != rS:
                    inv = False
            check(inv, "objective is invariant on the dihedral orbit of S")
        else:
            orb = rotations(S)
            check(D not in orb,
                  "D is outside the cyclic-shift orbit of S")
            inv = all(w["ratio"](r) == rS for r in orb)
            check(inv, "objective is invariant on the cyclic-shift orbit of S")

        # 3. Strict improvement forces non-equivalence when the objective is
        #    equivalence-invariant: if D ~ S then ratio would be 1.
        check(ratio != 1, "ratio != 1, so no invariant quotient can identify D with S")

        # 4. No witness is a tie-based uniqueness counterexample.
        check(ratio != 1, "witness is strict, not a tie (uniqueness refuted a fortiori)")

    # 5. Sanity: full-type-space binomial ratio reproduces issue #32.
    print("\n== issue #32 full-type-space binomial ratio ==")
    S, D, L, N = "AAACC", "AAAAC", 3, 5
    obs = {"AAA": 1, "AAC": 1, "CAA": 1}
    lS = fixedN_binomial(S, obs, L, N, "ACGT")
    lD = fixedN_binomial(D, obs, L, N, "ACGT")
    print(f"   L(S)={lS}  L(D)={lD}  ratio={lD/lS}")
    check(lD / lS == Fraction(1125, 512), "full-type-space ratio is 1125/512")

    print()
    if failures:
        print(f"AUDIT FAILED: {len(failures)} failure(s)")
        return 1
    print("AUDIT PASSED: every integrated witness is strict and non-equivalent "
          "under the relevant quotient")
    return 0


if __name__ == "__main__":
    sys.exit(main())
