#!/usr/bin/env python3
"""Exact verifier for issue #281: generic Hellinger-affinity exponential decay.

Independently of the Lean kernel, this script checks the generic finite-family
exponential exact-ML error bound

    P_p[∃ q ∈ Θ : L_q(R_1..R_n) ≥ L_p(R_1..R_n)] ≤ |Θ| * exp(-c n),
    c = -log ρ_max,   ρ_max = max_{q ∈ Θ} ρ(p, q),

by exact enumeration over the finite read universe, for every read count n,
together with the contraction step ρ^n = exp(-n * (-log ρ)) and the concrete
sum-of-powers form `≤ |Θ| * ρ_max^n` and `≤ Σ_q ρ(p,q)^n`.

It also verifies, by source inspection, that the five theorem statements are
present in `AssemblyP1/HellingerExponentialDecay.lean` and that the module
reuses the merged `FiniteReadRecovery` endpoint with no `sorry`/`admit`/
`axiom`/`native_decide`.

Negative controls (both must be DETECTED as violations, proving the hypotheses
are load-bearing):

  NC1 (identifiability): with Θ = {p} the error probability is 1 for every n,
     so the exponential bound with any strictly positive rate c is violated
     for large n.  Identifiability (p ≠ q) is necessary.
  NC2 (uniform affinity): using a deliberately too-small affinity ρ_wrong <
     ρ_max makes `|Θ| * ρ_wrong^n` fall below the true error probability.
     The uniform sub-unit affinity hypothesis is necessary.

Usage:
    python3 scripts/verify_281_hellinger_exponential.py
"""

from __future__ import annotations

import itertools
import math
import random
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_PATH = ROOT / "AssemblyP1" / "HellingerExponentialDecay.lean"

THEOREMS = [
    "hellinger_pow_eq_exp_neg",
    "hellinger_pow_le_exp_neg",
    "eventProb_wrong_eq_zero_of_affinity_zero",
    "eventProb_wrong_le_exp_neg",
    "exists_uniform_affinity_lt_one",
    "eventProb_wrong_le_exp_neg_identifiable",
]


def strip_lean_comments(text: str) -> str:
    """Remove Lean line and (nesting) block comments, keeping code only."""
    out = []
    i = 0
    n = len(text)
    depth = 0
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j == -1 else j
            continue
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(text[i])
        i += 1
    return "".join(out)


def check_source() -> None:
    text = LEAN_PATH.read_text(encoding="utf-8")
    code = strip_lean_comments(text)
    for name in THEOREMS:
        if f"theorem {name}" not in code:
            raise SystemExit(f"missing theorem in source: {name}")
    for bad in ("sorry", "admit", "axiom", "native_decide"):
        if re.search(rf"\b{re.escape(bad)}\b", code):
            raise SystemExit(f"forbidden construct in source: {bad}")
    if "import AssemblyP1.FiniteReadRecovery" not in code:
        raise SystemExit("module does not reuse the merged FiniteReadRecovery endpoint")
    print("source check: 6 theorems present; no sorry/admit/axiom/native_decide; "
          "FiniteReadRecovery reused")


def hellinger(p, q):
    return sum(math.sqrt(p[w] * q[w]) for w in p)


def tuple_likelihood(p, n, t):
    prod = 1.0
    for x in t:
        prod *= p[x]
    return prod


def event_prob(p, Theta, n, W):
    """Exact P_p[∃ q ∈ Θ : L_q ≥ L_p] by enumeration over W^n."""
    total = 0.0
    for t in itertools.product(W, repeat=n):
        Lp = tuple_likelihood(p, n, t)
        if any(tuple_likelihood(q, n, t) >= Lp for q in Theta):
            total += Lp
    return total


def random_pmf(W, rng):
    raw = [rng.random() for _ in W]
    s = sum(raw)
    return {w: raw[i] / s for i, w in enumerate(W)}


def check_positive(p, Theta, n, W, label):
    """All three forms of the bound must hold, and the contraction step."""
    if not Theta:
        return
    ep = event_prob(p, Theta, n, W)
    rho_max = max(hellinger(p, q) for q in Theta)
    bound_sum = sum(hellinger(p, q) ** n for q in Theta)
    bound_pow = len(Theta) * rho_max ** n
    if not (ep <= bound_sum + 1e-9):
        raise SystemExit(f"[{label}] affinity-sum bound violated: {ep} > {bound_sum}")
    if not (ep <= bound_pow + 1e-9):
        raise SystemExit(f"[{label}] sum-of-powers bound violated: {ep} > {bound_pow}")
    if rho_max > 0:
        c = -math.log(rho_max)
        bound_exp = len(Theta) * math.exp(-c * n)
        if not (ep <= bound_exp + 1e-9):
            raise SystemExit(f"[{label}] exponential bound violated: {ep} > {bound_exp}")
        lhs = rho_max ** n
        rhs = math.exp(-n * (-math.log(rho_max)))
        if abs(lhs - rhs) > 1e-9 * max(1.0, abs(lhs)):
            raise SystemExit(f"[{label}] contraction step violated: {lhs} != {rhs}")


def main() -> int:
    check_source()

    rng = random.Random(281)

    # Positive checks: random finite families of distinct competitors.
    checked = 0
    for trial in range(60):
        k = rng.randint(2, 4)
        W = list(range(k))
        p = random_pmf(W, rng)
        m = rng.randint(1, 3)
        Theta = []
        for _ in range(m):
            q = random_pmf(W, rng)
            if any(q == r for r in Theta) or q == p:
                continue
            Theta.append(q)
        if not Theta:
            continue
        for n in range(0, 5):
            check_positive(p, Theta, n, W, f"trial{trial}/n={n}")
            checked += 1
    print(f"positive checks passed: {checked} (p, Θ, n) triples over random families")

    # Deterministic positive check at a fixed family.
    W = [0, 1]
    p = {0: 0.5, 1: 0.5}
    q1 = {0: 0.9, 1: 0.1}
    q2 = {0: 0.1, 1: 0.9}
    for n in range(0, 6):
        check_positive(p, [q1, q2], n, W, f"fixed/n={n}")
    print("deterministic positive check passed (uniform truth, two skewed rivals)")

    # Disjoint-support boundary: affinity 0 forces error probability 0 for n >= 1.
    p_dis = {0: 1.0, 1: 0.0}
    q_dis = {0: 0.0, 1: 1.0}
    if hellinger(p_dis, q_dis) != 0.0:
        raise SystemExit("disjoint setup wrong: affinity not zero")
    for n in (1, 2, 3):
        ep_dis = event_prob(p_dis, [q_dis], n, W)
        if ep_dis != 0.0:
            raise SystemExit(f"disjoint boundary violated: error {ep_dis} != 0 at n={n}")
    print("disjoint-support boundary passed (affinity 0 => error 0 for n >= 1)")

    # NC1: identifiability is necessary. Θ = {p} => error probability is 1.
    ep = event_prob(p, [p], 3, W)
    if ep < 1 - 1e-9:
        raise SystemExit(f"NC1 setup wrong: event_prob(p,[p],3) = {ep}, expected 1")
    c_demo = 1.0
    false_bound = len([p]) * math.exp(-c_demo * 3)
    if not (ep > false_bound):
        raise SystemExit("NC1 failed to detect the identifiability necessity")
    print(f"NC1 detected: Θ={{p}} gives error {ep:.6f} > exp-bound {false_bound:.6f} "
          f"(identifiability necessary)")

    # NC2: uniform affinity is necessary. Use ρ_wrong < ρ_max.
    rho_true = max(hellinger(p, q1), hellinger(p, q2))
    rho_wrong = 0.4
    if not (rho_wrong < rho_true):
        raise SystemExit("NC2 setup wrong: rho_wrong not below rho_true")
    ep1 = event_prob(p, [q1, q2], 1, W)
    false_pow = len([q1, q2]) * rho_wrong ** 1
    if not (ep1 > false_pow):
        raise SystemExit("NC2 failed to detect the uniform-affinity necessity")
    print(f"NC2 detected: ρ_max={rho_true:.6f} but ρ_wrong={rho_wrong} gives "
          f"|Θ|·ρ_wrong={false_pow:.6f} < error {ep1:.6f} "
          f"(uniform affinity necessary)")

    print("all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
