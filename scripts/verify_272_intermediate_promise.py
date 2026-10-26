#!/usr/bin/env python3
"""Exact-rational witness for strictly intermediate supplied information.

Three equally likely truth classes emit the same read. Supplying the proper
promise that the truth belongs to {g0,g1} raises each remaining posterior from
1/3 to 1/2 but does not identify the truth. Supplying the stronger promise
that it is g0 makes the posterior certain. The event is used only when its
truth is actually observed true.
"""

from fractions import Fraction


G = (0, 1, 2)
R = ("r",)
prior = {g: Fraction(1, 3) for g in G}
likelihood = {(g, r): Fraction(1) for g in G for r in R}


def posterior(g, r, supplied_event):
    numerator = prior[g] * likelihood[g, r] * int(supplied_event(g, r))
    denominator = sum(
        prior[h] * likelihood[h, r] * int(supplied_event(h, r)) for h in G
    )
    assert denominator > 0, "conditioning observation must have positive mass"
    return numerator / denominator


def test_proper_promise_is_strictly_intermediate():
    read_only = lambda _g, _r: True
    proper_promise = lambda g, _r: g in (0, 1)
    identifying_promise = lambda g, _r: g == 0

    assert posterior(0, "r", read_only) == Fraction(1, 3)
    assert posterior(1, "r", read_only) == Fraction(1, 3)
    assert posterior(2, "r", read_only) == Fraction(1, 3)

    # The proper promise excludes a positive-support competitor, but leaves
    # two supported truth classes and hence is not sufficient for certainty.
    assert proper_promise(0, "r")
    assert posterior(0, "r", proper_promise) == Fraction(1, 2)
    assert posterior(1, "r", proper_promise) == Fraction(1, 2)
    assert posterior(2, "r", proper_promise) == 0

    # A strictly stronger supplied promise leaves exactly one supported class.
    assert identifying_promise(0, "r")
    assert posterior(0, "r", identifying_promise) == 1
    assert posterior(1, "r", identifying_promise) == 0
    assert posterior(2, "r", identifying_promise) == 0

    # Merely having the promise true at the actual truth is not conditioning.
    assert posterior(0, "r", read_only) == Fraction(1, 3)


if __name__ == "__main__":
    test_proper_promise_is_strictly_intermediate()
    print("proper supplied promise: PASS (posterior 1/2, not certain)")
    print("strictly stronger supplied promise: PASS (posterior 1)")
