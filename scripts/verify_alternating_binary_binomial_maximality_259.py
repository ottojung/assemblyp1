#!/usr/bin/env python3
"""Infinite alternating-word family for board issue #259.

Proves, with exact integer arithmetic (no Lean import, no floats), that the
alternating binary words ``(01)^k`` (k >= 2) are full-class-beaten yet
realizable-maximal under the MB09 section 6.1 fixed-external-N
product-binomial surrogate.  This promotes the observed census pattern
(``docs/realizable-transfer-gap-259.md`` on branch
``agent/rv8MkAfF-issue259-review``: gap cases at k = 2, 3, 4, 5) to a theorem
in k.

Conventions (identical to ``verify_realizable_transfer_gap_259.py``):
  universe E = {00, 01, 10, 11} (indices 0..3), truth A_k = (0,k,k,0),
  total N = 2k, effective weight q_i(B) = B[i] * prod_{j != i} (N - B[j]),
  effective product F_B(x) = prod_i q_i(B)^x[i].
  Covered sample: x >= A coordinatewise on supp A, x = 0 off support.
  beats(A, B) <=> q(B) > 0 on supp A and not pointwise dominated there
  (the merged #259 covered-sample iff; the full-class transfer beater is
  additionally cross-checked by an exact integer F-comparison).

Checks (exit code 0 means every check passed):
  Part 1 -- necklace spectra have #01 == #10 (exhaustive over even G <= 12),
            so every realizable B of length 2k is (a,m,m,d), a+2m+d = 2k.
  Part 2 -- parametric domination inequality, exact integers, for every
            2 <= k <= KMAX and every (a,m,d) with a+2m+d = 2k, m >= 1:
              m*(2k-a)*(2k-m)*(2k-d) <= 4*k^4,
            with equality iff (a,m,d) = (0,k,0), i.e. B = A_k.
            Proof encoded alongside: with s = a+d = 2k-2m,
              (2k-a)(2k-d) = 4k^2-2ks+ad <= (k+m)^2   [ad <= (s/2)^2],
              then m(2k-m)(k+m)^2 <= 4k^4 because
              g(u) = u(2-u)(1+u)^2 is strictly increasing on (0,1]
              (g'(u) = -4u^3+6u+2 = -2(u+1)(2u^2-2u-1) > 0 there,
              since 2u^2-2u-1 < 0 on (0,1]), so g(m/k) <= g(1) = 4.
            The script checks the inequality directly; the doc carries the proof.
  Part 3 -- exact full-class beating witness for every 2 <= k <= KMAX:
            Bs = (0,k-1,k+1,0) is unbalanced (hence unrealizable), and at the
            covered sample x = (0,k,2k,0),
              F_Bs(x) / F_A(x) = [((k-1)(k+1)^2)^2 / k^6]^k > 1
            as exact integers, since (k-1)(k+1)^2 - k^3 = k^2-k-1 >= 1.
  Part 4 -- controls: k = 1 is {0,1}-valued hence full-class maximal (no gap);
            the unrealizable beater Bs violates the Part-2 bound on its
            flooding coordinate (q_10(Bs) = 4k^2(k+1)^2 > 4k^4), showing the
            bound genuinely separates realizable from unrealizable.

Scope: binary alphabet, L = 2, alternating truths only.  Ternary/alphabets >= 4
and non-alternating realizable truths remain open; #260/#261 flows untouched.
"""

from __future__ import annotations

import itertools
import sys
from collections import defaultdict
from fractions import Fraction

KMAX = 200


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


def necklaces(G: int):
    seen = set()
    for bits in itertools.product((0, 1), repeat=G):
        if bits in seen:
            continue
        seen.update(bits[k:] + bits[:k] for k in range(G))
        yield bits


def spec2(s) -> list[int]:
    U = [(0, 0), (0, 1), (1, 0), (1, 1)]
    c = defaultdict(int)
    for i in range(len(s)):
        c[(s[i], s[(i + 1) % len(s)])] += 1
    return [c.get(w, 0) for w in U]


def part1_necklace_balance() -> None:
    checked = 0
    for G in (2, 4, 6, 8, 10, 12):
        for s in necklaces(G):
            v = spec2(s)
            assert v[1] == v[2], f"unbalanced necklace spectrum {s} -> {v}"
            checked += 1
    print(f"  Part 1: {checked} necklaces (even G <= 12) all satisfy #01 == #10")


def part2_parametric_inequality() -> None:
    n_cases = 0
    n_eq = 0
    for k in range(2, KMAX + 1):
        N = 2 * k
        rhs = 4 * k**4
        for m in range(1, k + 1):
            s = 2 * k - 2 * m
            for a in range(0, s + 1):
                d = s - a
                lhs = m * (N - a) * (N - m) * (N - d)
                assert lhs <= rhs, f"inequality fails at k={k} (a,m,d)={(a, m, d)}"
                n_cases += 1
                if lhs == rhs:
                    n_eq += 1
                    assert (a, m, d) == (0, k, 0), (
                        f"unexpected equality at k={k} (a,m,d)={(a, m, d)}"
                    )
                # cross-check the (k+m)^2 majorant used in the doc proof
                assert (N - a) * (N - d) <= (k + m) ** 2
    assert n_eq == KMAX - 1, f"expected equality exactly at B=A_k, got {n_eq}"
    print(
        f"  Part 2: {n_cases} (k,a,m,d) triples (2 <= k <= {KMAX}) satisfy "
        f"m(2k-a)(2k-m)(2k-d) <= 4k^4, equality only at B = A_k ({n_eq}x)"
    )


def part3_beating_witness() -> None:
    for k in range(2, KMAX + 1):
        N = 2 * k
        A = [0, k, k, 0]
        Bs = [0, k - 1, k + 1, 0]
        assert Bs[1] != Bs[2], "beater must be unbalanced (unrealizable)"
        x = [0, k, 2 * k, 0]
        assert all(x[i] >= A[i] for i in (1, 2)) and x[0] == x[3] == 0
        fa = eff_product(N, A, x)
        fb = eff_product(N, Bs, x)
        assert fa > 0 and fb > fa, f"witness fails at k={k}"
        # analytic cross-check: ratio^1/k as exact Fraction
        ratio_kth = Fraction((k - 1) ** 2 * (k + 1) ** 4, k**6)
        assert ratio_kth > 1, f"analytic ratio fails at k={k}"
        assert fb == fa * ratio_kth**k, f"ratio identity fails at k={k}"
    print(
        f"  Part 3: exact F_Bs(x) > F_A(x) at covered x=(0,k,2k,0) "
        f"for all 2 <= k <= {KMAX}; analytic ratio ((k-1)(k+1)^2/k^3)^{{2k}} > 1"
    )


def part4_controls() -> None:
    # k = 1: A = (0,1,1,0) is {0,1}-valued, hence full-class maximal: no gap.
    A1 = [0, 1, 1, 0]
    assert all(a <= 1 for a in A1), "k=1 truth must be {0,1}-valued"
    # beater control: the unrealizable Bs violates the Part-2 bound on the
    # flooding coordinate, so the bound genuinely separates the classes.
    for k in range(2, 30):
        N = 2 * k
        Bs = [0, k - 1, k + 1, 0]
        assert eff_weight(N, Bs, 2) == 4 * k**2 * (k + 1) ** 2 > 4 * k**4
    print(
        "  Part 4: k=1 truth is {0,1}-valued (full-class maximal, no gap); "
        "unrealizable beater violates the domination bound on its flooding "
        "coordinate (control)"
    )


def main() -> int:
    print("verify_alternating_binary_binomial_maximality_259.py")
    part1_necklace_balance()
    part2_parametric_inequality()
    part3_beating_witness()
    part4_controls()
    print("verify_alternating_binary_binomial_maximality_259: ALL OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
