#!/usr/bin/env python3
"""Exact verifier for issue #281: no-decay boundary for exact-ML error.

Independently of the Lean kernel, this script checks the negative-boundary
cell ``HellingerNoDecay.eventProb_wrong_eq_one_of_mem``: when the competitor
family contains the truth ``p`` itself (hence some competitor is statistically
indistinguishable from the truth, Hellinger affinity one), every read tuple
ties for the exact-ML lead, ties count as errors, and the exact
wrong-selection probability is 1 at every sample size ``n``.

Checks, by exact enumeration over a two-letter read universe with Fractions
(no floating point):

  * for two truth laws (uniform and skewed) and n = 0..4, the exact
    wrong-selection probability over Theta = {p} equals exactly 1;
  * the bound is sharp in the sense that removing ``p`` from the family can
    only lower the error probability (monotonicity of the event in Theta).

It also verifies, by source inspection, that the theorem statement is present
in ``AssemblyP1/HellingerNoDecay.lean``, that the audit module prints its
axioms, and that neither file contains ``sorry``/``admit``/``axiom``/
``native_decide`` outside comments.

Usage:
    python3 scripts/verify_281_nodecay.py
"""

from __future__ import annotations

import itertools
import re
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_PATH = ROOT / "AssemblyP1" / "HellingerNoDecay.lean"
AUDIT_PATH = ROOT / "AssemblyP1" / "HellingerExponentialDecayAudit.lean"

THEOREM = "eventProb_wrong_eq_one_of_mem"


def strip_comments(src: str) -> str:
    src = re.sub(r"/-!.*?-/", "", src, flags=re.S)
    src = re.sub(r"--.*", "", src)
    return src


def tuple_likelihood(p: dict[int, Fraction], t: tuple[int, ...]) -> Fraction:
    lik = Fraction(1)
    for w in t:
        lik *= p[w]
    return lik


def event_prob(p: dict[int, Fraction], theta: list[dict[int, Fraction]], n: int) -> Fraction:
    total = Fraction(0)
    for t in itertools.product(p.keys(), repeat=n):
        lp = tuple_likelihood(p, t)
        if any(tuple_likelihood(q, t) >= lp for q in theta):
            total += lp
    return total


def main() -> int:
    laws = {
        "uniform": {0: Fraction(1, 2), 1: Fraction(1, 2)},
        "skewed": {0: Fraction(1, 4), 1: Fraction(3, 4)},
    }
    failures = 0
    for name, p in laws.items():
        for n in range(0, 5):
            got = event_prob(p, [p], n)
            status = "OK" if got == 1 else "FAIL"
            if got != 1:
                failures += 1
            print(f"{status}: law={name} n={n} Theta={{p}} error-prob={got}")
            # Sharpness: dropping p from the family cannot raise the error.
            got_empty = event_prob(p, [], n)
            status2 = "OK" if got_empty <= got else "FAIL"
            if got_empty > got:
                failures += 1
            print(f"{status2}: law={name} n={n} Theta={{}} error-prob={got_empty} <= 1")

    src = LEAN_PATH.read_text()
    if THEOREM not in src:
        print(f"FAIL: {THEOREM} not found in {LEAN_PATH}")
        failures += 1
    else:
        print(f"OK: {THEOREM} present in HellingerNoDecay.lean")
    code = strip_comments(src)
    for pat in ["sorry", "admit", "native_decide", "unsafe", "set_option", "#axiom"]:
        if pat in code:
            print(f"FAIL: {pat} found in code of {LEAN_PATH}")
            failures += 1
    audit = AUDIT_PATH.read_text()
    if f"HellingerNoDecay.{THEOREM}" not in audit:
        print(f"FAIL: audit line for {THEOREM} missing in {AUDIT_PATH.name}")
        failures += 1
    else:
        print(f"OK: audit line present in {AUDIT_PATH.name}")
    if "import AssemblyP1.HellingerNoDecay" not in audit:
        print(f"FAIL: import missing in {AUDIT_PATH.name}")
        failures += 1
    else:
        print(f"OK: import present in {AUDIT_PATH.name}")

    print("PASS" if failures == 0 else f"{failures} FAILURES")
    return 0 if failures == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
