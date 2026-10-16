#!/usr/bin/env python3
"""Independent exact-arithmetic verification for board issue #259 (necessity).

This does NOT import Lean.  It checks, with exact integer / Fraction
arithmetic and (for the transcendental log identity only) a tight float
tolerance, the four claims of `AssemblyP1/ProductBinomialRigidityNecessity.lean`:

  A. Necessity lemma (`effectiveWeight_le_imp_eq`):
     two distinct positive count vectors of equal total `N` can never be
     pointwise dominated in effective weight, i.e. some class has
     `effectiveWeight N B e > effectiveWeight N A e`.
     Equivalently: `(∀ e, effB e ≤ effA e) ⟹ A = B`.

  B. The weighted log-ratio identity
     `∑ B_e log(effB_e/effA_e) = KL(B||A) + KL(N-B||N-A)`,
     together with `KL ≥ 0` (the Gibbs engine of the proof).

  C. The necessity classification (`robust_iff_unique`): for a candidate set
     `F` of positive count vectors of total `N` containing `A`, `A` is a
     covered-sample maximizer over `F` iff `F = {A}`.  Maximizer status is
     decided with the merged `#259` covered-sample iff
     (`CoveredBinomialWeightsIff`).

  D. The sufficiency failure: the rigid truth `A = (2,1,1,0)` (spectrum of
     `0001`) is beaten by the new-support candidate `B = (1,1,1,1)` (spectrum
     of `0011`); and a bounded census over binary necklaces confirms 0
     non-rigid maximizers (necessity) and the 257 rigid-but-not-maximal
     new-support counterexamples (sufficiency fails).

Exit code 0 means every check passed.
"""

from __future__ import annotations

import itertools
import math
import random
import sys
from collections import defaultdict
from fractions import Fraction

# ---------------------------------------------------------------------------
# §6.1 effective weights and products (exact integers)
# ---------------------------------------------------------------------------


def eff_weight(N: int, B: list[int], i: int) -> int:
    w = B[i]
    for j in range(len(B)):
        if j != i:
            w *= N - B[j]
    return w


def eff_product(N: int, B: list[int], x: list[int]) -> int:
    p = 1
    for i in range(len(B)):
        p *= eff_weight(N, B, i) ** x[i]
    return p


def compositions(N: int, k: int):
    """Positive integer vectors of length k summing to N."""
    if k == 1:
        yield (N,)
        return
    for first in range(1, N - k + 2):
        for rest in compositions(N - first, k - 1):
            yield (first,) + rest


def support(B: list[int]) -> list[int]:
    return [i for i in range(len(B)) if B[i] > 0]


def dominates_pointwise(N: int, A: list[int], B: list[int]) -> bool:
    """`∀ e ∈ supp A, effB e ≤ effA e`."""
    S = support(A)
    return all(eff_weight(N, B, i) <= eff_weight(N, A, i) for i in S)


def zero_on_support(N: int, A: list[int], B: list[int]) -> bool:
    S = support(A)
    return any(eff_weight(N, B, i) == 0 for i in S)


def is_maximizer(N: int, A: list[int], F: list[list[int]]) -> bool:
    """Covered-sample maximizer over `F`, decided by the merged #259 iff."""
    for B in F:
        if zero_on_support(N, A, B) or dominates_pointwise(N, A, B):
            continue
        return False
    return True


# ---------------------------------------------------------------------------
# Part A: necessity lemma
# ---------------------------------------------------------------------------


def part_a() -> int:
    checks = 0
    # exhaustive small cases
    for N in range(2, 13):
        for k in range(2, min(N, 5) + 1):
            comps = list(compositions(N, k))
            for A in comps:
                eA = [eff_weight(N, A, i) for i in range(k)]
                for B in comps:
                    if A == B:
                        continue
                    eB = [eff_weight(N, B, i) for i in range(k)]
                    checks += 1
                    if all(eB[i] <= eA[i] for i in range(k)):
                        raise AssertionError(
                            f"necessity lemma violated: N={N} A={A} B={B}")
    # randomized larger cases
    random.seed(259)
    for _ in range(40000):
        k = random.randint(2, 8)
        N = random.randint(k, 250)
        A = _rand_comp(N, k)
        B = _rand_comp(N, k)
        if A == B:
            continue
        checks += 1
        eA = [eff_weight(N, A, i) for i in range(k)]
        eB = [eff_weight(N, B, i) for i in range(k)]
        if all(eB[i] <= eA[i] for i in range(k)):
            raise AssertionError(f"necessity lemma violated: N={N} A={A} B={B}")
    return checks


def _rand_comp(N: int, k: int) -> list[int]:
    cuts = sorted(random.sample(range(1, N), k - 1))
    return [b - a for a, b in zip([0] + cuts, cuts + [N])]


# ---------------------------------------------------------------------------
# Part B: weighted log-ratio identity and KL nonnegativity
# ---------------------------------------------------------------------------


def part_b() -> int:
    checks = 0
    random.seed(260)
    for _ in range(20000):
        k = random.randint(2, 7)
        N = random.randint(k, 120)
        A = _rand_comp(N, k)
        B = _rand_comp(N, k)
        D = 0.0
        KL1 = 0.0
        KL2 = 0.0
        for i in range(k):
            eb = eff_weight(N, B, i)
            ea = eff_weight(N, A, i)
            D += B[i] * math.log(eb / ea)
            KL1 += B[i] * math.log(B[i] / A[i])
            KL2 += (N - B[i]) * math.log((N - B[i]) / (N - A[i]))
        tol = 1e-6 * max(1.0, abs(D))
        if abs(D - (KL1 + KL2)) > tol:
            raise AssertionError(f"identity failed: N={N} A={A} B={B} {D} {KL1+KL2}")
        if KL1 + KL2 < -1e-9:
            raise AssertionError(f"KL negative: N={N} A={A} B={B} {KL1+KL2}")
        checks += 1
    return checks


# ---------------------------------------------------------------------------
# Part C: robust_iff_unique classification battery
# ---------------------------------------------------------------------------


def part_c() -> int:
    checks = 0
    random.seed(261)
    for N in range(2, 11):
        for k in range(2, min(N, 4) + 1):
            comps = [list(c) for c in compositions(N, k)]
            for A in comps:
                # candidate sets F = a random subset of positive vectors total N
                for _ in range(6):
                    pool = [B for B in comps if B != A]
                    size = random.randint(0, min(len(pool), 4))
                    F = [A] + random.sample(pool, size)
                    maximizer = is_maximizer(N, A, F)
                    unique = (len(F) == 1)
                    checks += 1
                    if maximizer != unique:
                        raise AssertionError(
                            f"robust_iff_unique mismatch: N={N} A={A} F={F} "
                            f"maximizer={maximizer} unique={unique}")
    return checks


# ---------------------------------------------------------------------------
# Part D: sufficiency failure (rigid but not maximal) + census
# ---------------------------------------------------------------------------

U2 = [(a, b) for a in (0, 1) for b in (0, 1)]  # (00,01,10,11)


def spectrum(s, L):
    G = len(s)
    c = defaultdict(int)
    for i in range(G):
        c[tuple(s[(i + t) % G] for t in range(L))] += 1
    return c


def spec_vector(s, L, U):
    c = spectrum(s, L)
    return [c.get(w, 0) for w in U]


def necklaces(G):
    seen = set()
    for bits in itertools.product((0, 1), repeat=G):
        if bits in seen:
            continue
        seen.update(bits[k:] + bits[:k] for k in range(G))
        yield bits


def positive_circulations(A, U, L, G):
    edges = [w for w, a in zip(U, A) if a > 0]
    nodes = {}
    for w in edges:
        nodes.setdefault(w[:-1], len(nodes))
        nodes.setdefault(w[1:], len(nodes))
    inc = [(nodes[w[:-1]], nodes[w[1:]]) for w in edges]
    m, n = len(edges), len(nodes)
    if m == 0:
        return []
    out = []
    vals = [1] * m

    def rec(i, remaining):
        if i == m:
            if remaining != 0:
                return
            bal = [0] * n
            for e in range(m):
                u, v = inc[e]
                bal[u] += vals[e]
                bal[v] -= vals[e]
            if all(b == 0 for b in bal):
                out.append(tuple(vals))
            return
        for val in range(1, remaining - (m - i - 1) + 1):
            vals[i] = val
            rec(i + 1, remaining - val)
        vals[i] = 1

    rec(0, G)
    return out


def part_d() -> tuple[int, int, int]:
    # Smallest explicit witness: A = 0001 -> (2,1,1,0); B = 0011 -> (1,1,1,1).
    A = [2, 1, 1, 0]
    B = [1, 1, 1, 1]
    assert spec_vector((0, 0, 0, 1), 2, U2) == A
    assert spec_vector((0, 0, 1, 1), 2, U2) == B
    assert not zero_on_support(4, A, B), "B has no zero weight on supp A"
    assert not dominates_pointwise(4, A, B), "B must beat A pointwise somewhere"
    assert not is_maximizer(4, A, [A, B]), "A must not be maximal against B"
    # A is rigid: unique positive circulation of total 4 on supp(A).
    circs = positive_circulations(A, U2, 2, 4)
    assert circs == [(2, 1, 1)], f"unexpected circulations {circs}"

    # Bounded census over binary necklaces.
    counts = {"rigid_max": 0, "rigid_notmax": 0, "nonrigid_max": 0, "nonrigid_notmax": 0}
    for L in (2, 3, 4):
        U = list(itertools.product((0, 1), repeat=L))
        for G in range(L, 13):
            items = {}
            for s in necklaces(G):
                key = tuple(spec_vector(s, L, U))
                items.setdefault(key, s)
            specs = list(items.items())
            for keyA, sA in specs:
                A2 = list(keyA)
                if any(eff_weight(G, A2, i) == 0 for i in support(A2)):
                    continue
                circs = positive_circulations(A2, U, L, G)
                rigid = (len(circs) == 1)
                maximal = True
                for keyB, _ in specs:
                    if keyB == keyA:
                        continue
                    B2 = list(keyB)
                    if not zero_on_support(G, A2, B2) and not dominates_pointwise(G, A2, B2):
                        maximal = False
                        break
                if rigid and maximal:
                    counts["rigid_max"] += 1
                elif rigid and not maximal:
                    counts["rigid_notmax"] += 1
                elif (not rigid) and maximal:
                    counts["nonrigid_max"] += 1
                else:
                    counts["nonrigid_notmax"] += 1
    return counts["nonrigid_max"], counts["rigid_notmax"], sum(counts.values())


def main() -> int:
    a = part_a()
    b = part_b()
    c = part_c()
    nonrigid_max, rigid_notmax, total = part_d()
    print("verify_product_binomial_rigidity_259.py")
    print(f"  A necessity lemma: {a} (N,k) pairs, 0 domination-by-distinct-pair")
    print(f"  B log-ratio identity + KL nonneg: {b} random cases, 0 mismatches")
    print(f"  C robust_iff_unique battery: {c} (A,F) cases, maximizer == unique")
    print(f"  D sufficiency failure: smallest rigid-but-beaten A=(2,1,1,0) vs B=(1,1,1,1)")
    print(f"  D census (binary necklaces L in 2..4, G <= 12): "
          f"nonrigid&maximal={nonrigid_max} (necessity holds), "
          f"rigid&NOT-maximal={rigid_notmax} (sufficiency fails), "
          f"distinct truth spectra={total}")
    if nonrigid_max != 0:
        raise AssertionError("necessity counterexample found")
    if rigid_notmax != 257:
        raise AssertionError(f"expected 257 rigid-not-maximal, got {rigid_notmax}")
    print("OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
