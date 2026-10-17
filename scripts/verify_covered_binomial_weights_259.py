#!/usr/bin/env python3
"""Independent exact-integer verification for board issue #259.

This does not import Lean.  It checks the finite weight-level classification
`covered_product_le_iff_zero_or_pointwise` and the ambient new-support
examples from `AssemblyP1/CoveredBinomialWeightsIff.lean` with exact integer
arithmetic, plus the flooding inequality used in the necessity direction.

Exit code 0 means every check passed; any mismatch raises AssertionError.
"""

from __future__ import annotations

import itertools
from typing import Callable

# ---------------------------------------------------------------------------
# 1. Generic finite-weight criterion
# ---------------------------------------------------------------------------


def prod(weights: list[int], counts: list[int]) -> int:
    result = 1
    for w, c in zip(weights, counts):
        result *= w ** c
    return result


def covered_product_le(qA: list[int], qB: list[int], a: list[int],
                       bound: int) -> bool:
    """`True` iff every covered `x` with `x_i <= bound` satisfies the bound."""
    for counts in itertools.product(range(bound + 1), repeat=len(a)):
        if all(counts[i] >= a[i] for i in range(len(a))):
            if prod(qB, counts) > prod(qA, counts):
                return False
    return True


def rhs(qA: list[int], qB: list[int]) -> bool:
    return any(w == 0 for w in qB) or all(
        qB[i] <= qA[i] for i in range(len(qA)))


def flooding_witness(qA: list[int], qB: list[int], a: list[int]):
    """Return an explicit covered `x` on which `qB` beats `qA`, when one exists.

    Only valid when no `qB` is zero and some `qA e0 < qB e0`.
    """
    n = len(qA)
    e0 = next(i for i in range(n) if qA[i] < qB[i])
    Q = 1
    for i in range(n):
        if i != e0:
            Q *= qA[i] ** a[i]
    t0 = (Q - 1) * qA[e0] + 1
    x = list(a)
    x[e0] = a[e0] + t0
    return x


def census() -> int:
    """Verify both directions of the iff on small finite instances.

    * If the right-hand side holds, every covered vector (a bounded subset is
      checked) must satisfy the product bound: sufficiency.
    * If the right-hand side fails, the explicit flooding witness must be a
      genuine covered counterexample: necessity.  The witness is unbounded, so
      it is constructed directly rather than searched for inside a box.
    """
    checked = 0
    sizes = [1, 2, 3]
    value_range = [0, 1, 2, 3]
    base_range = [1, 2, 3]
    bound = 4
    for size in sizes:
        for qA in itertools.product(value_range, repeat=size):
            if any(w == 0 for w in qA):
                # truth weights are required positive
                continue
            for qB in itertools.product(value_range, repeat=size):
                for a in itertools.product(base_range, repeat=size):
                    r = rhs(list(qA), list(qB))
                    if r:
                        assert covered_product_le(
                            list(qA), list(qB), list(a), bound), (
                            f"sufficiency failed: qA={qA} qB={qB} a={a}")
                    else:
                        x = flooding_witness(list(qA), list(qB), list(a))
                        assert all(x[i] >= a[i] for i in range(size))
                        assert prod(list(qB), x) > prod(list(qA), x), (
                            f"flooding witness failed: qA={qA} qB={qB} "
                            f"a={a} x={x}")
                    checked += 1
    return checked


# ---------------------------------------------------------------------------
# 2. Fixed-N effective weights (MB09 6.1 surrogate)
# ---------------------------------------------------------------------------


def effective_weight(N: int, B: list[int], i: int) -> int:
    w = B[i]
    for j in range(len(B)):
        if j != i:
            w *= N - B[j]
    return w


def effective_product(N: int, B: list[int], x: list[int]) -> int:
    result = 1
    for i in range(len(B)):
        result *= effective_weight(N, B, i) ** x[i]
    return result


def check_newsupport() -> None:
    # U = Fin 2, A = (2, 0), B = (1, 1), N = 4: dominated.
    A = [2, 0]
    B = [1, 1]
    N = 4
    assert effective_weight(N, A, 0) == 8
    assert effective_weight(N, B, 0) == 3
    assert effective_weight(N, B, 0) <= effective_weight(N, A, 0)
    assert not (0 < A[0] and effective_weight(N, B, 0) == 0)

    # U = Fin 2, A = (2, 0), B = (3, 1), N = 4: defeats.
    B2 = [3, 1]
    assert effective_weight(N, A, 0) == 8
    assert effective_weight(N, B2, 0) == 9
    assert effective_weight(N, B2, 0) > effective_weight(N, A, 0)
    assert not (0 < A[0] and effective_weight(N, B2, 0) == 0)

    # The unobserved class-1 factor is essential.
    # Without it, B=(1,1) would give q_0 = 1 (still dominated), but B=(3,1)
    # would give q_0 = 3 (dominated), hiding the defeat at q_0 = 9.
    assert effective_weight(N, B2, 0) == B2[0] * (N - B2[1])


def check_ambient_example_defeat_sample() -> None:
    """The ambient defeat example really fails on a covered sample."""
    A = [2, 0]
    B = [3, 1]
    N = 4
    # covered sample: x_0 = A_0 + 1 = 3, x_1 = 0 (supported on A's support)
    x = [3, 0]
    assert all(x[i] >= A[i] for i in range(2))
    assert all(A[j] != 0 or x[j] == 0 for j in range(2))
    assert effective_product(N, B, x) > effective_product(N, A, x)


def main() -> int:
    n = census()
    check_newsupport()
    check_ambient_example_defeat_sample()
    print(f"verify_covered_binomial_weights_259: OK ({n} generic iff cases)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
