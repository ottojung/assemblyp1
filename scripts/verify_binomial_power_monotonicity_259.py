#!/usr/bin/env python3
"""Independent exact-rational verification for board issue #259.

This script does not import Lean.  It independently recomputes

* the oriented circular two-read counts of the two explicit circular genomes
  `A = 0^51 1^49` and `B = 0^50 1^18 (01)^16` from their literal definitions,
* the exact iid/multinomial likelihood and the full-alphabet MB09 §6.1
  product-of-marginal-binomials surrogate for `n` identical `00` reads, and
* the sharpness counterexamples of `CoveredBinomialWeightsIffSharpness`.

It then checks the kernel-checked statements of
`AssemblyP1/Section62BinomialPowerMonotonicity.lean` and
`AssemblyP1/CoveredBinomialWeightsIffSharpness.lean` with exact integer and
`Fraction` arithmetic:

* for every `n >= 1` up to a bound, the exact iid likelihood favors `A`
  (`(50/100)^n > (49/100)^n`) while the §6.1 surrogate favors `B`
  (`(25482600/100^4)^n < (28017563/100^4)^n`);
* the generic covered-sample iff of
  `CoveredBinomialWeightsIff.covered_product_le_iff_zero_or_pointwise` fails
  when either disjunct is dropped.

Exit code 0 means every check passed; any mismatch raises AssertionError.
"""

from __future__ import annotations

import itertools
from fractions import Fraction


# ---------------------------------------------------------------------------
# 1. Independent circular two-read counts
# ---------------------------------------------------------------------------


def circular_two_count(genome: list[int], a: int, b: int) -> int:
    """Count starts of the circular word whose oriented 2-read is (a, b)."""
    length = len(genome)
    return sum(
        1
        for i in range(length)
        if genome[i] == a and genome[(i + 1) % length] == b
    )


def check_genome_counts() -> tuple[list[int], list[int]]:
    genome_a = [0] * 51 + [1] * 49
    genome_b = [0] * 50 + [1] * 18 + [0, 1] * 16
    assert len(genome_a) == 100
    assert len(genome_b) == 100
    counts_a = [circular_two_count(genome_a, a, b)
                for a in (0, 1) for b in (0, 1)]
    counts_b = [circular_two_count(genome_b, a, b)
                for a in (0, 1) for b in (0, 1)]
    assert counts_a == [50, 1, 1, 48], counts_a
    assert counts_b == [49, 17, 17, 17], counts_b
    # each circular genome has exactly length-many start positions
    assert sum(counts_a) == 100
    assert sum(counts_b) == 100
    return counts_a, counts_b


# ---------------------------------------------------------------------------
# 2. Exact iid/multinomial and §6.1 product-binomial scores for (n,0,0,0)
# ---------------------------------------------------------------------------


def exact_iid(counts: list[int], n: int) -> Fraction:
    """P(counts): exact joint law of `n` identical reads of the first type.

    For the single-type count vector `(n, 0, 0, 0)` the joint multinomial
    probability equals the iid product `p_00 ^ n` with `p_00 = counts[0] / N`.
    """
    assert counts[0] + counts[1] + counts[2] + counts[3] == 100
    return Fraction(counts[0], 100) ** n


def surrogate(counts: list[int], n: int) -> Fraction:
    """Full-alphabet MB09 §6.1 product of marginal binomials for (n,0,0,0).

    Each read contributes the `00` factor `p_00` and the three zero-count
    factors `(1 - p_i)`, so the score is the `n`-th power of the single-read
    score, retaining every `(1 - d_i / N)` factor.
    """
    total = sum(counts)
    assert total == 100
    p = [Fraction(c, total) for c in counts]
    single = p[0] * (1 - p[1]) * (1 - p[2]) * (1 - p[3])
    return single ** n


def check_base_values() -> None:
    counts_a, counts_b = check_genome_counts()
    # exact one-read numerators over denominator 100
    assert exact_iid(counts_a, 1) == Fraction(50, 100)
    assert exact_iid(counts_b, 1) == Fraction(49, 100)
    # §6.1 one-read numerators over denominator 100^4, all four factors
    assert surrogate(counts_a, 1) == Fraction(50 * 99 * 99 * 52, 100 ** 4)
    assert surrogate(counts_b, 1) == Fraction(49 * 83 ** 3, 100 ** 4)
    assert 50 * 99 * 99 * 52 == 25482600
    assert 49 * 83 ** 3 == 28017563
    assert 100 ** 4 == 100000000
    # the merged base inequalities
    assert exact_iid(counts_b, 1) < exact_iid(counts_a, 1)
    assert surrogate(counts_a, 1) < surrogate(counts_b, 1)


def check_power_monotonicity(bound: int = 64) -> int:
    counts_a, counts_b = check_genome_counts()
    checked = 0
    for n in range(1, bound + 1):
        exact_a, exact_b = exact_iid(counts_a, n), exact_iid(counts_b, n)
        surr_a, surr_b = surrogate(counts_a, n), surrogate(counts_b, n)
        assert exact_b < exact_a, (n, exact_a, exact_b)
        assert surr_a < surr_b, (n, surr_a, surr_b)
        # exact ratio is (50/49)^n > 1
        assert exact_a / exact_b == Fraction(50, 49) ** n
        # the common integer numerators are the merged ones
        assert exact_a == Fraction(50 ** n, 100 ** n)
        assert exact_b == Fraction(49 ** n, 100 ** n)
        assert surr_a == Fraction(25482600 ** n, 100 ** (4 * n))
        assert surr_b == Fraction(28017563 ** n, 100 ** (4 * n))
        checked += 1
    return checked


# ---------------------------------------------------------------------------
# 3. Sharpness of the generic covered-sample iff
# ---------------------------------------------------------------------------


def prod(weights: list[int], counts: list[int]) -> int:
    result = 1
    for w, c in zip(weights, counts):
        result *= w ** c
    return result


def covered_lhs(q_a: list[int], q_b: list[int], a: list[int],
                bound: int) -> bool:
    """Check the LHS over a bounded box of covered count vectors."""
    for counts in itertools.product(range(bound + 1), repeat=len(a)):
        if all(counts[i] >= a[i] for i in range(len(a))):
            if prod(q_b, counts) > prod(q_a, counts):
                return False
    return True


def check_sharpness() -> None:
    # Zero-weight disjunct is indispensable: qA=(1,1), qB=(0,5), a=(1,1).
    q_a, q_b, a = [1, 1], [0, 5], [1, 1]
    assert all(w > 0 for w in q_a) and all(v > 0 for v in a)
    assert covered_lhs(q_a, q_b, a, bound=6)
    # pointwise inequality fails: qB[1] = 5 > 1 = qA[1]
    assert not all(q_b[i] <= q_a[i] for i in range(2))
    # so `LHS <-> pointwise` is false
    assert covered_lhs(q_a, q_b, a, bound=6) != all(
        q_b[i] <= q_a[i] for i in range(2))

    # Pointwise disjunct is indispensable: qA = qB = (1,1), a = (1,1).
    q_a2, q_b2, a2 = [1, 1], [1, 1], [1, 1]
    assert covered_lhs(q_a2, q_b2, a2, bound=6)
    assert not any(w == 0 for w in q_b2)
    # so `LHS <-> (exists zero)` is false
    assert covered_lhs(q_a2, q_b2, a2, bound=6) != any(w == 0 for w in q_b2)


def main() -> int:
    check_base_values()
    n = check_power_monotonicity()
    check_sharpness()
    print(
        "verify_binomial_power_monotonicity_259: OK "
        f"({n} sample sizes; base values, circular counts, and sharpness checked)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
