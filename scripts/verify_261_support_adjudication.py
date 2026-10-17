#!/usr/bin/env python3
"""Independent exact-integer audit for the #261 unobserved-support adjudication.

This checks the *count-vector* bookkeeping only; it is not a proof that any
abstract vector is realizable by the historical reduced bidirected flow graph.
It re-derives, in exact integer arithmetic, the identities kernel-checked in
`AssemblyP1/Section62BinomialSupportAdjudication.lean`:

  * the §6.1 core over the full class universe equals the observed-qFac product;
  * the exact support splitting
      K(d;x) = (prod_{j notin I}(N-d_j))^n * prod_{i in I} d_i^x_i (N-d_i)^(n-x_i)
    for x supported on I with n = sum(x);
  * the effective weight split q_i(d) = d_i * (prod_{j notin I}(N-d_j))
    * (prod_{j in I, j != i}(N-d_j));
  * the unobserved witness (agree on I, differ off I, score 600 vs 384);
  * the observed-only shortcut refutation (observed-only dominance holds while
    the candidate strictly beats the truth, 24 vs 600);
  * the unobserved-factor ratio identity.
"""

from __future__ import annotations

from itertools import product
from math import prod

FAILURES: list[str] = []


def core(d: tuple[int, ...], x: tuple[int, ...], n_ext: int) -> int:
    n = sum(x)
    return prod(
        d[i] ** x[i] * (n_ext - d[i]) ** (n - x[i]) for i in range(len(d))
    )


def qfac(d: tuple[int, ...], n_ext: int) -> tuple[int, ...]:
    return tuple(
        d[i] * prod(n_ext - d[j] for j in range(len(d)) if j != i)
        for i in range(len(d))
    )


def qobs(d: tuple[int, ...], i: int, n_ext: int, I: tuple[int, ...]) -> int:
    return d[i] * prod(n_ext - d[j] for j in I if j != i)


def check(cond: bool, msg: str) -> None:
    if not cond:
        FAILURES.append(msg)


def audit_qfac_identity() -> None:
    """K(d;x) = prod_i q_i(d)^{x_i} over all classes, including zeros."""
    for n_ext in range(1, 5):
        for m in range(1, 4):
            for d in product(range(n_ext + 1), repeat=m):
                for x in product(range(3), repeat=m):
                    q = qfac(d, n_ext)
                    check(
                        core(d, x, n_ext) == prod(q[i] ** x[i] for i in range(m)),
                        f"qfac identity failed N={n_ext} d={d} x={x}",
                    )


def audit_support_split() -> None:
    """Exact support splitting for samples supported on I."""
    for n_ext in range(1, 5):
        for m in range(1, 4):
            for I in [tuple(c for c in range(m) if bits >> c & 1) for bits in range(1, 2 ** m)]:
                for d in product(range(n_ext + 1), repeat=m):
                    for vals in product(range(1, 4), repeat=len(I)):
                        x = [0] * m
                        for i, v in zip(I, vals):
                            x[i] = v
                        x = tuple(x)
                        n = sum(x)
                        observed = prod(
                            d[i] ** x[i] * (n_ext - d[i]) ** (n - x[i]) for i in I
                        )
                        unobserved = prod(
                            (n_ext - d[j]) for j in range(m) if j not in I
                        )
                        check(
                            core(d, x, n_ext) == unobserved ** n * observed,
                            f"support split failed N={n_ext} d={d} I={I} x={x}",
                        )


def audit_qfac_split() -> None:
    """q_i(d) = d_i * (prod_{j notin I}(N-d_j)) * (prod_{j in I, j!=i}(N-d_j))."""
    for n_ext in range(1, 5):
        for m in range(1, 4):
            for I in [tuple(c for c in range(m) if bits >> c & 1) for bits in range(1, 2 ** m)]:
                for i in I:
                    for d in product(range(n_ext + 1), repeat=m):
                        rhs = (
                            d[i]
                            * prod(n_ext - d[j] for j in range(m) if j not in I)
                            * prod(n_ext - d[j] for j in I if j != i)
                        )
                        check(
                            qfac(d, n_ext)[i] == rhs,
                            f"qfac split failed N={n_ext} d={d} I={I} i={i}",
                        )


def audit_unobserved_witness() -> None:
    """wd and wd' agree on the observed support but score differently."""
    wI = (0, 1)
    wx = (1, 1, 0)
    wd = (2, 1, 0)
    wd2 = (2, 1, 1)
    check(all(wd[i] == wd2[i] for i in wI), "unobserved witness: observed differ")
    check(wd[2] != wd2[2], "unobserved witness: unobserved equal")
    check(core(wd, wx, 5) == 600, "unobserved witness: wd score != 600")
    check(core(wd2, wx, 5) == 384, "unobserved witness: wd' score != 384")
    check(
        core(wd, wx, 5) * (5 - wd2[2]) ** 2 == core(wd2, wx, 5) * (5 - wd[2]) ** 2,
        "unobserved witness: ratio identity failed",
    )


def audit_observed_only_refutation() -> None:
    """Observed-only dominance holds yet the candidate strictly beats truth."""
    oI = (0, 1)
    ox = (1, 1, 0)
    oA = (2, 1, 4)
    oB = (2, 1, 0)
    check(
        all(qobs(oB, i, 5, oI) <= qobs(oA, i, 5, oI) for i in oI),
        "observed-only dominance should hold",
    )
    check(core(oA, ox, 5) == 24, "observed-only: oA score != 24")
    check(core(oB, ox, 5) == 600, "observed-only: oB score != 600")
    check(core(oA, ox, 5) < core(oB, ox, 5), "observed-only: candidate does not beat")
    qA, qB = qfac(oA, 5), qfac(oB, 5)
    check(prod(qB[i] for i in oI) != 0, "observed-only: candidate product is zero")
    check(
        not all(qB[i] <= qA[i] for i in oI),
        "observed-only: full qFac domination unexpectedly holds",
    )


def audit_ratio_identity() -> None:
    """Two vectors agreeing on I have scores differing by the unobserved factors."""
    for n_ext in range(1, 5):
        for m in range(1, 4):
            for I in [tuple(c for c in range(m) if bits >> c & 1) for bits in range(1, 2 ** m)]:
                comp = tuple(j for j in range(m) if j not in I)
                for d in product(range(n_ext + 1), repeat=m):
                    for d2_vals in product(range(n_ext + 1), repeat=len(comp)):
                        d2 = list(d)
                        for j, v in zip(comp, d2_vals):
                            d2[j] = v
                        d2 = tuple(d2)
                        for vals in product(range(1, 4), repeat=len(I)):
                            x = [0] * m
                            for i, v in zip(I, vals):
                                x[i] = v
                            x = tuple(x)
                            n = sum(x)
                            lhs = core(d, x, n_ext) * prod(
                                n_ext - d2[j] for j in comp
                            ) ** n
                            rhs = core(d2, x, n_ext) * prod(
                                n_ext - d[j] for j in comp
                            ) ** n
                            check(
                                lhs == rhs,
                                f"ratio identity failed N={n_ext} d={d} d'={d2} I={I} x={x}",
                            )


def main() -> int:
    audit_qfac_identity()
    audit_support_split()
    audit_qfac_split()
    audit_unobserved_witness()
    audit_observed_only_refutation()
    audit_ratio_identity()
    if FAILURES:
        for f in FAILURES[:20]:
            print(f"FAIL: {f}")
        print(f"{len(FAILURES)} failure(s)")
        return 1
    print("verify_261_support_adjudication: all exact-integer checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
