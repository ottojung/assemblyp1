#!/usr/bin/env python3
"""Independent numeric check for the #271 fixed-x link (Goal 4).

Reuses (does not re-prove or fork) the kernel-checked #258 AAABBB instance in
``AssemblyP1/FixedXExactML.lean``:

* spectra B1..B4 over the four length-2 words (AA, AB, BB, BA);
* integer score ``likProduct E B x = prod_w B[w] ** x[w]``;
* three fixed samples: xWin = B1, xTie = all-ones, xLose = B4.

Verifies, with exact integer arithmetic:
1. xWin: truth B1 is the UNIQUE maximizer (16 > 9, 9, 4);
2. xTie: truth ties B4 at top (4 = 4 > 3, 3);
3. xLose: truth STRICTLY LOSES to B4 (4 < 16) even though xLose = B4 is
   supported entirely on the truth's windows -- so sampling realizability /
   support-type necessary conditions do not guarantee (B) at fixed x.
4. Tautology check: the rational likelihood comparison
   ``Lik(B;x) <= Lik(A;x)`` with the candidate-independent denominator
   ``G^n`` divided out is exactly the integer-product comparison
   (``fixedX_classification_iff``); the structural content is the
   feasible-set census (``feasibleSpectrum_iff_258``) plus the three-status
   instance, not the score restatement.
"""

from __future__ import annotations

from fractions import Fraction

# Order: AA, AB, BB, BA.
B1 = (2, 1, 2, 1)
B2 = (1, 1, 3, 1)
B3 = (3, 1, 1, 1)
B4 = (1, 2, 1, 2)
FEASIBLE = {"B1": B1, "B2": B2, "B3": B3, "B4": B4}

XWIN = B1
XTIE = (1, 1, 1, 1)
XLOSE = B4

G = 6


def lik_product(b: tuple[int, ...], x: tuple[int, ...]) -> int:
    p = 1
    for bi, xi in zip(b, x):
        p *= bi**xi
    return p


def spectrum_lik_factor(b: tuple[int, ...], x: tuple[int, ...]) -> Fraction:
    f = Fraction(1, 1)
    for bi, xi in zip(b, x):
        f *= Fraction(bi, G) ** xi
    return f


def main() -> int:
    # 1. Unique maximizer at xWin.
    win = {k: lik_product(b, XWIN) for k, b in FEASIBLE.items()}
    assert win == {"B1": 16, "B2": 9, "B3": 9, "B4": 4}, win
    assert all(v < win["B1"] for k, v in win.items() if k != "B1")

    # 2. Tie at top at xTie.
    tie = {k: lik_product(b, XTIE) for k, b in FEASIBLE.items()}
    assert tie == {"B1": 4, "B2": 3, "B3": 3, "B4": 4}, tie

    # 3. Strict loss at xLose (supported on truth windows, realizable: xLose
    #    is exactly the spectrum B4 spelled by genome S4_258 = AABABB).
    lose = {k: lik_product(b, XLOSE) for k, b in FEASIBLE.items()}
    assert lose == {"B1": 4, "B2": 3, "B3": 3, "B4": 16}, lose
    assert lose["B1"] < lose["B4"]

    # 4. Tautology check: rational-factor ranking agrees with integer ranking
    #    at all three samples (denominator G^n cancels).
    for x in (XWIN, XTIE, XLOSE):
        n = sum(x)
        denom = G**n
        for b in FEASIBLE.values():
            assert spectrum_lik_factor(b, x) == Fraction(lik_product(b, x), denom)
        order_int = sorted(FEASIBLE, key=lambda k: lik_product(FEASIBLE[k], x))
        order_rat = sorted(FEASIBLE, key=lambda k: spectrum_lik_factor(FEASIBLE[k], x))
        assert order_int == order_rat

    print("271 fixed-x link checks passed:")
    print(f"  xWin products (A,B2,B3,B4): {win['B1']}, {win['B2']}, {win['B3']}, {win['B4']} (truth unique max)")
    print(f"  xTie products (A,B2,B3,B4): {tie['B1']}, {tie['B2']}, {tie['B3']}, {tie['B4']} (tie at top)")
    print(f"  xLose products (A,B2,B3,B4): {lose['B1']}, {lose['B2']}, {lose['B3']}, {lose['B4']} (truth strict loss)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
