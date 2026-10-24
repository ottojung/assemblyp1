#!/usr/bin/env python3
"""Independent exact-rational check for issue #255 (fixed-x objective equivalence).

Mirrors `AssemblyP1.MaximizerOrderTransform` without Lean: for a FIXED observed
count vector x, the exact-multinomial likelihood and any strictly monotone
reparameterization of it share the same maximizer set over any candidate set,
while a strictly antitone reparameterization swaps max/min.

Everything here is EXACT: Python Fractions only, no floating point. The
monotone maps used (q -> q^3, q -> q/(1+q)) are strictly increasing on the
nonnegative rationals and the antitone maps (q -> -q, q -> 1/(1+q)) strictly
decreasing there, so the comparison is faithful to the Lean iff lemmas
(isMaxOn_comp_iff / isMinOn_comp_iff / isMinOn_comp_iff_of_strictAnti /
isMaxOn_comp_iff_of_strictAnti) on a concrete finite candidate set.

Frozen axes: oriented molecule types, exact multinomial objective with the
multinomial coefficient kept (it is constant at fixed x), fixed sample x.
"""

from fractions import Fraction
from math import factorial

# Fixed observed counts over three molecule types.
X = (2, 1, 1)
N = sum(X)
MULTINOMIAL_COEFF = factorial(N) // (
    factorial(X[0]) * factorial(X[1]) * factorial(X[2])
)


def likelihood(p):
    """Exact multinomial likelihood of the fixed sample x under pmf p."""
    num = Fraction(MULTINOMIAL_COEFF, 1)
    for xi, pi in zip(X, p):
        num *= pi**xi
    return num


# Candidate pmfs (exact rationals summing to 1), including a tie at the top
# and a zero-support candidate (likelihood 0).
CANDIDATES = {
    "truth": (Fraction(1, 2), Fraction(1, 4), Fraction(1, 4)),
    "tie": (Fraction(1, 2), Fraction(1, 4), Fraction(1, 4)),
    "alt": (Fraction(1, 3), Fraction(1, 3), Fraction(1, 3)),
    "skew": (Fraction(3, 4), Fraction(1, 8), Fraction(1, 8)),
    "degenerate": (Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)),
}


def argmax(names, score):
    best = max(score(n) for n in names)
    return {n for n in names if score(n) == best}


def argmin(names, score):
    worst = min(score(n) for n in names)
    return {n for n in names if score(n) == worst}


def main():
    names = list(CANDIDATES)
    like = {n: likelihood(CANDIDATES[n]) for n in names}
    assert like["truth"] == like["tie"], "tie candidate must match truth"
    assert like["degenerate"] == 0, "zero-support candidate has likelihood 0"
    # truth/tie likelihood: 12 * (1/2)^2 (1/4) (1/4) = 12/64 = 3/16.
    assert like["truth"] == Fraction(3, 16), like["truth"]

    max_like = argmax(names, like.get)
    min_like = argmin(names, like.get)
    assert max_like == {"truth", "tie"}, max_like

    # Strictly monotone reparameterizations share the maximizer AND minimizer set.
    mono_maps = {
        "cube": lambda q: q**3,
        "bounded": lambda q: q / (1 + q),
    }
    for label, g in mono_maps.items():
        g_like = {n: g(v) for n, v in like.items()}
        assert argmax(names, g_like.get) == max_like, label
        assert argmin(names, g_like.get) == min_like, label

    # Strictly antitone reparameterizations swap max and min.
    anti_maps = {
        "neg": lambda q: -q,
        "inv": lambda q: 1 / (1 + q),
    }
    for label, g in anti_maps.items():
        g_like = {n: g(v) for n, v in like.items()}
        assert argmax(names, g_like.get) == min_like, label
        assert argmin(names, g_like.get) == max_like, label

    print("order-transform checks passed:")
    print(f"  sample x={X} N={N} coeff={MULTINOMIAL_COEFF}")
    print(f"  maximizers: {sorted(max_like)}, minimizers: {sorted(min_like)}")
    print(f"  monotone maps: {sorted(mono_maps)}, antitone maps: {sorted(anti_maps)}")


if __name__ == "__main__":
    main()
