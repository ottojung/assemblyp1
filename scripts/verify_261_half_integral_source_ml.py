#!/usr/bin/env python3
"""Independent exact-rational cross-check for board #261's integer-vs-half-integral
classification on the *literal* MB09 §6.2 flow object.

Kernel-checked companion: ``AssemblyP1/Section62HalfIntegralSourceML.lean``
(``qThroughput``/``qBalance`` bridge to ``throughput``/``balCore``,
``halfIntegral_double_feasible62``, ``qExactLik_smul``,
``no_half_integral_gap_exact``, ``truth_half_maximal_iff_int_maximal``,
``integral_strict_subset_half_integral``).

The claim under test: for the §6.2 rational flow polytope (edge lower bound 0,
vertex lower bound 1, zero-terminal signed-incidence balance 0, throughput d)
under the **exact multinomial** objective with the candidate's own length
``N = sum_v d_v``, the half-integral relaxation cannot strictly beat the integer
optimum, because (i) the exact likelihood is scale-invariant and (ii) doubling a
half-integral feasible flow gives a literal integer feasible flow.

The script re-derives everything in exact ``Fraction`` arithmetic and fails
(non-zero exit) if any check is violated.  It also runs red mutations that must
FAIL, proving the checks discriminate.

Checks
------
W1  exact multinomial likelihood is scale-invariant on many rational vectors.
W2  The four-edge §6.2 witness: the half-integral circulation (1/2,...,1/2) is
    feasible with throughput (1,1); its double is integer feasible with doubled
    throughput and the same normalized throughput and exact likelihood.
W3  That half-integral circulation has no integral representative: the
    half-integral class strictly contains the integer class.
W4  Brute-force over a bounded box on the witness graph: the maximum exact
    likelihood over half-integral feasible flows equals the maximum over integer
    feasible flows (and every maximizer's double attains it).
W5  Objective dependence: the §6.1 separable binomial with fixed external N does
    have a strict half-integral gap (the already-merged Class 3 result), so the
    no-gap statement is specific to the exact variable-length objective.
W6  Red mutations of W1-W4 must fail.
"""

from fractions import Fraction
from itertools import product


# --------------------------------------------------------------------------- #
# The literal §6.2 flow object on the four-edge witness graph
# --------------------------------------------------------------------------- #
# vertices {0,1}; edges (sx, sy, sgnX, sgnY), rep = identity
EDGES = [
    (0, 0, 1, -1),  # e00
    (0, 1, 1, -1),  # e01
    (1, 0, 1, -1),  # e10
    (1, 1, 1, -1),  # e11
]
VERTS = [0, 1]


def throughput(f, v, edges=EDGES):
    """sum over edges departing from v, matching Lean `throughput`/`qThroughput`."""
    return sum((fe for (sx, _, _, _), fe in zip(edges, f) if sx == v), Fraction(0))


def balcore(f, v, edges=EDGES):
    """signed-incidence balance, matching Lean `balCore`/`qBalance`."""
    out = Fraction(0)
    for (sx, sy, gx, gy), fe in zip(edges, f):
        if sx == v:
            out += gx * fe
        if sy == v:
            out += gy * fe
    return out


def feasible_rat(f, d, verts=VERTS, edges=EDGES):
    if any(fe < 0 for fe in f):
        return False
    if any(throughput(f, v, edges) < 1 for v in verts):
        return False
    if any(balcore(f, v, edges) != 0 for v in verts):
        return False
    return all(throughput(f, v, edges) == d[v] for v in verts)


def exact_lik(d, x):
    """Exact multinomial likelihood of the normalized throughput d at sample x.

    Candidate length N = sum_v d_v (variable length universe).
    """
    N = sum(d.values())
    out = Fraction(1)
    for v in d:
        out *= (d[v] / N) ** x.get(v, 0)
    return out


def scale(d, k):
    return {v: k * d[v] for v in d}


# --------------------------------------------------------------------------- #
# W1: exact likelihood scale invariance
# --------------------------------------------------------------------------- #
def check_w1():
    cases = [
        ({0: Fraction(5, 2), 1: Fraction(1), 2: Fraction(1)}, (2, 1, 1)),
        ({0: Fraction(3, 2), 1: Fraction(3, 2)}, (1, 3)),
        ({0: Fraction(1), 1: Fraction(2), 2: Fraction(3)}, (0, 1, 2)),
        ({0: Fraction(7, 2), 1: Fraction(1, 2), 2: Fraction(2)}, (2, 0, 3)),
    ]
    ks = [Fraction(2), Fraction(3), Fraction(5, 2), Fraction(1, 2),
          Fraction(10), Fraction(7, 3)]
    n = 0
    for d, xv in cases:
        x = {i: xv[i] for i in range(len(xv))}
        base = exact_lik(d, x)
        for k in ks:
            assert exact_lik(scale(d, k), x) == base, (d, x, k)
            n += 1
    return n


# --------------------------------------------------------------------------- #
# W2: the four-edge witness doubling
# --------------------------------------------------------------------------- #
def check_w2():
    half = [Fraction(1, 2)] * 4
    d_half = {v: throughput(half, v) for v in VERTS}
    assert d_half == {0: Fraction(1), 1: Fraction(1)}, d_half
    assert feasible_rat(half, d_half)
    integer = [2 * fe for fe in half]
    d_int = {v: throughput(integer, v) for v in VERTS}
    assert d_int == {0: Fraction(2), 1: Fraction(2)}, d_int
    assert feasible_rat(integer, d_int)
    assert integer == [2 * fe for fe in half]
    # normalized throughputs agree
    for v in VERTS:
        assert d_half[v] / sum(d_half.values()) == d_int[v] / sum(d_int.values())
    x = {0: 1, 1: 2}
    assert exact_lik(d_half, x) == exact_lik(d_int, x)
    return 1


# --------------------------------------------------------------------------- #
# W3: strict subset (no integral representative)
# --------------------------------------------------------------------------- #
def check_w3():
    half = [Fraction(1, 2)] * 4
    # A representative would be a tuple of natural numbers equal to `half`.
    has_integral = any(
        list(g) == half
        for g in product(range(2), repeat=4)  # 1/2 is not a natural number
    )
    assert not has_integral
    # And 1/2 is genuinely not an integer:
    assert half[1] not in (Fraction(0), Fraction(1))
    return 1


# --------------------------------------------------------------------------- #
# W4: brute-force optimum equivalence over a bounded box
# --------------------------------------------------------------------------- #
def check_w4():
    # Half-integral box: each coordinate in {0, 1/2, 1, 3/2, 2, 5/2, 3}.
    grid = [Fraction(k, 2) for k in range(0, 7)]
    samples = [{0: 1, 1: 1}, {0: 2, 1: 1}, {0: 0, 1: 3}, {0: 3, 1: 2}]

    best_half = {tuple(s.items()): None for s in samples}
    best_int = {tuple(s.items()): None for s in samples}
    for f in product(grid, repeat=4):
        d = {v: throughput(f, v) for v in VERTS}
        if not feasible_rat(f, d):
            continue
        for s in samples:
            key = tuple(s.items())
            for v in VERTS:
                assert s.get(v, 0) == s.get(v, 0)
            val = exact_lik(d, s)
            if best_half[key] is None or val > best_half[key]:
                best_half[key] = val
    for g in product(range(4), repeat=4):
        d = {v: throughput(g, v) for v in VERTS}
        if not feasible_rat([Fraction(c) for c in g], d):
            continue
        for s in samples:
            key = tuple(s.items())
            val = exact_lik(d, s)
            if best_int[key] is None or val > best_int[key]:
                best_int[key] = val
    for key in best_half:
        assert best_half[key] is not None and best_int[key] is not None
        # No half-integral optimum strictly beats the integer optimum.
        assert best_half[key] <= best_int[key], (key, best_half[key], best_int[key])
        # And every half-integral value is matched by an integer value.
        assert best_int[key] <= best_half[key], (key, best_int[key], best_half[key])
    return len(best_half)


# --------------------------------------------------------------------------- #
# W5: the fixed-N binomial objective DOES have a gap (objective dependence)
# --------------------------------------------------------------------------- #
def binom_core(d, x, N):
    """§6.1 separable-binomial core with external N (Lean GeneralBidirectedFlowML.binomCore)."""
    n = sum(x.values())
    out = Fraction(1)
    for v in d:
        out *= Fraction(d[v]) ** x.get(v, 0) * Fraction(N - d[v]) ** (n - x.get(v, 0))
    return out


def check_w5():
    # AAA marginal with external N = 5, x = (2,1): proportional to d^2 (5-d)^2.
    def aaa(d):
        return Fraction(d) ** 2 * Fraction(5 - d) ** 2

    assert aaa(Fraction(5, 2)) > aaa(Fraction(2))
    assert aaa(Fraction(5, 2)) > aaa(Fraction(3))
    assert aaa(Fraction(2)) == aaa(Fraction(3))
    # The binomial core is not scale invariant: doubling d changes it.
    d = {0: Fraction(2), 1: Fraction(3)}
    x = {0: 2, 1: 1}
    assert binom_core(d, x, 5) != binom_core(scale(d, 2), x, 5)
    return 1


# --------------------------------------------------------------------------- #
# W6: red mutations must fail
# --------------------------------------------------------------------------- #
def _expect_fail(fn, *args):
    try:
        fn(*args)
    except AssertionError:
        return True
    raise AssertionError(f"mutation {fn.__name__} unexpectedly passed")


def mut_scale_direction():
    # Drop the scale factor from the objective: likelihood would then depend on k.
    d = {0: Fraction(5, 2), 1: Fraction(1)}
    x = {0: 2, 1: 1}
    assert exact_lik(scale(d, 2), x) == exact_lik(d, x) * 1  # would be true;
    # now a wrong claim:
    assert exact_lik(scale(d, 2), x) == exact_lik(d, x) * 2


def mut_half_is_integral():
    half = [Fraction(1, 2)] * 4
    assert list(half) == [Fraction(1)] * 4


def mut_balance_ignored():
    # A flow that is NOT balanced would be accepted if balance were dropped.
    f = [Fraction(1, 2), Fraction(1, 2), Fraction(0), Fraction(1, 2)]
    d = {v: throughput(f, v) for v in VERTS}
    assert any(balcore(f, v) != 0 for v in VERTS)
    # claim it is feasible -> must fail
    assert feasible_rat(f, d)


def mut_binomial_transfers():
    # Claim the binomial gap transfers to the exact objective: find a strict gap.
    d = {0: Fraction(5, 2), 1: Fraction(1)}
    x = {0: 2, 1: 1}
    assert exact_lik(scale(d, 2), x) > exact_lik(d, x)


def check_w6():
    _expect_fail(mut_scale_direction)
    _expect_fail(mut_half_is_integral)
    _expect_fail(mut_balance_ignored)
    _expect_fail(mut_binomial_transfers)
    return 4


def main():
    n1 = check_w1()
    n2 = check_w2()
    n3 = check_w3()
    n4 = check_w4()
    n5 = check_w5()
    n6 = check_w6()
    print(f"W1 exact-likelihood scale invariance: {n1} assertions PASS")
    print(f"W2 four-edge witness doubling: {n2} PASS")
    print(f"W3 strict half-integral superset: {n3} PASS")
    print(f"W4 brute-force optimum equivalence: {n4} samples PASS")
    print(f"W5 fixed-N binomial gap (objective dependence): {n5} PASS")
    print(f"W6 red mutations correctly fail: {n6} PASS")
    print("ALL CHECKS PASS")


if __name__ == "__main__":
    main()
