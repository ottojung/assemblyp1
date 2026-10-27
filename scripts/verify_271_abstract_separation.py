#!/usr/bin/env python3
"""Independent verifier for the #271 abstract same-model separation witness.

Re-derives, with exact rationals, the finite pmf model of
`AssemblyP1/ConditionalVsOrdinaryMLSeparation.lean`:

  * hypotheses Theta = {A, B}, observations W = {r0, r1} (= {0, 1}),
  * equal positive prior pi = 1/2 each,
  * likelihoods P_A(0) = 1/4, P_A(1) = 3/4, P_B(0) = 3/4, P_B(1) = 1/4,
  * truth-dependent side observation E(h, r) <=> (h=A,r=0) or (h=B,r=1),

and checks the two separation directions proved in Lean:

  * separation_A_not_B: at r0, conditional recovery is certain on A
    (condPosterior = 1) while ordinary R-only ML strictly prefers wrong B,
    and the ordinary posterior on A is 1/4 (not certain);
  * separation_B_not_A: at r1, ordinary ML uniquely selects truth A, yet
    the ordinary posterior on A is 3/4 (not certain).

Also checks Lean source integrity (expected theorem names, no
sorry/admit/axiom/native_decide outside comments).

Exit status 0 iff every check passes. This is an ABSTRACT finite-pmf
witness, not a source-faithful genome witness.
"""

from __future__ import annotations

import re
import sys
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULE = ROOT / "AssemblyP1" / "ConditionalVsOrdinaryMLSeparation.lean"

HYPS = ("A", "B")
OBS = ("r0", "r1")

LIK = {("A", "r0"): Q(1, 4), ("A", "r1"): Q(3, 4),
       ("B", "r0"): Q(3, 4), ("B", "r1"): Q(1, 4)}
PRIOR = {"A": Q(1, 2), "B": Q(1, 2)}


def side_info(h: str, r: str) -> bool:
    return (h == "A" and r == "r0") or (h == "B" and r == "r1")


def joint(h: str, r: str) -> Q:
    return PRIOR[h] * LIK[(h, r)]


def evidence(r: str) -> Q:
    return joint("A", r) + joint("B", r)


def posterior(h: str, r: str) -> Q:
    return joint(h, r) / evidence(r)


def joint_e(h: str, r: str) -> Q:
    return joint(h, r) if side_info(h, r) else Q(0)


def evidence_e(r: str) -> Q:
    return joint_e("A", r) + joint_e("B", r)


def cond_posterior(h: str, r: str) -> Q:
    return joint_e(h, r) / evidence_e(r)


def is_ml_maximizer(h: str, r: str) -> bool:
    return all(LIK[(h2, r)] <= LIK[(h, r)] for h2 in HYPS)


def main() -> int:
    errors: list[str] = []

    def check(name: str, cond: bool) -> None:
        if not cond:
            errors.append(name)

    # 1. Likelihood rows are pmfs; prior is uniform positive.
    for h in HYPS:
        check(f"lik pmf sums to 1 for {h}",
              LIK[(h, "r0")] + LIK[(h, "r1")] == Q(1))
        check(f"prior positive for {h}", PRIOR[h] > Q(0))
    check("prior uniform", PRIOR["A"] == PRIOR["B"] == Q(1, 2))

    # 2. Exact joint/evidence/posterior tables.
    check("joint A r0 = 1/8", joint("A", "r0") == Q(1, 8))
    check("joint B r0 = 3/8", joint("B", "r0") == Q(3, 8))
    check("joint A r1 = 3/8", joint("A", "r1") == Q(3, 8))
    check("joint B r1 = 1/8", joint("B", "r1") == Q(1, 8))
    check("evidence r0 = 1/2", evidence("r0") == Q(1, 2))
    check("evidence r1 = 1/2", evidence("r1") == Q(1, 2))
    check("posterior A r0 = 1/4", posterior("A", "r0") == Q(1, 4))
    check("posterior B r0 = 3/4", posterior("B", "r0") == Q(3, 4))
    check("posterior A r1 = 3/4", posterior("A", "r1") == Q(3, 4))
    check("posterior B r1 = 1/4", posterior("B", "r1") == Q(1, 4))

    # 3. Separation A-not-B at r0: E certain on A, ML strictly prefers wrong B.
    check("condPosterior A r0 = 1", cond_posterior("A", "r0") == Q(1))
    check("condPosterior B r0 = 0", cond_posterior("B", "r0") == Q(0))
    check("ML at r0 uniquely prefers B",
          is_ml_maximizer("B", "r0") and not is_ml_maximizer("A", "r0"))
    check("ordinary posterior A r0 not certain", posterior("A", "r0") != Q(1))

    # 4. Separation B-not-A at r1: ML uniquely selects truth A, posterior not 1.
    check("ML at r1 uniquely selects A",
          is_ml_maximizer("A", "r1") and not is_ml_maximizer("B", "r1"))
    check("ordinary posterior A r1 not certain", posterior("A", "r1") != Q(1))
    # Certainty under E is correctness-independent: at r1, E certifies wrong B.
    check("condPosterior B r1 = 1 (wrong candidate)", cond_posterior("B", "r1") == Q(1))
    check("condPosterior A r1 = 0", cond_posterior("A", "r1") == Q(0))

    # 5. E is hypothesis-dependent, not data-only.
    check("E truth-dependent at r0",
          side_info("A", "r0") and not side_info("B", "r0"))
    check("E fibre at r0 is {A}",
          [h for h in HYPS if side_info(h, "r0")] == ["A"])
    check("E fibre at r1 is {B}",
          [h for h in HYPS if side_info(h, "r1")] == ["B"])

    # 6. Lean source integrity.
    src = MODULE.read_text(encoding="utf-8")
    for name in (
        "posterior_A_r0",
        "posterior_A_r1",
        "ml_unique_maximizer_r0",
        "ml_unique_maximizer_r1",
        "truth_not_ml_maximizer_r0",
        "condPosterior_A_r0",
        "sideInfo_not_dataOnly",
        "condRecoveryCertain_iff",
        "separation_A_not_B",
        "separation_B_not_A",
    ):
        check(f"Lean module declares {name}", name in src)
    code = re.sub(r"/-.*?-/", "", src, flags=re.DOTALL)
    code = re.sub(r"--[^\n]*", "", code)
    for token in ("sorry", "admit", "axiom", "native_decide"):
        check(f"Lean module has no `{token}`", not re.search(rf"\b{token}\b", code))

    if errors:
        print("FAILED checks:")
        for e in errors:
            print("  -", e)
        return 1

    print("All #271 abstract-separation checks passed:")
    print(f"  posterior(A|r0)={posterior('A','r0')}, ML-max(r0)=B, "
          f"condPosterior(A|r0,E)={cond_posterior('A','r0')}")
    print(f"  posterior(A|r1)={posterior('A','r1')}, ML-max(r1)=A unique, "
          f"condPosterior(B|r1,E)={cond_posterior('B','r1')}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
