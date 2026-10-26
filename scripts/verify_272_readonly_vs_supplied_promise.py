#!/usr/bin/env python3
"""Exact finite witness: read-only uncertainty versus supplied truth promise.

Two equally likely truth orbits both deterministically emit the same read r.
Without an auxiliary observation, every decoder errs on one truth. If the
external promise E(g,r) := (g = 0) is actually supplied and observed true,
conditioning the joint law on E leaves only orbit 0. Merely knowing that E
happens to hold at the true world is not an observation and does not change the
read-only posterior.
"""

from fractions import Fraction


G = (0, 1)
R = ("r",)
prior = {g: Fraction(1, 2) for g in G}
likelihood = {(g, r): Fraction(1) for g in G for r in R}


def joint_mass(g, r, supplied_event):
    return prior[g] * likelihood[g, r] * Fraction(int(supplied_event(g, r)))


def posterior(g, r, supplied_event):
    numerator = joint_mass(g, r, supplied_event)
    denominator = sum(joint_mass(h, r, supplied_event) for h in G)
    assert denominator > 0, "conditioning observation must have positive mass"
    return numerator / denominator


def test_read_only_decoder_cannot_be_certain():
    # Both truths produce r; any deterministic read-only output names one orbit.
    read_only = {r: 0 for r in R}
    assert posterior(0, "r", lambda _g, _r: True) == Fraction(1, 2)
    assert posterior(1, "r", lambda _g, _r: True) == Fraction(1, 2)
    assert any(read_only["r"] != g for g in G)


def test_supplied_promise_is_certain_only_after_conditioning():
    promise = lambda g, _r: g == 0
    assert promise(0, "r")  # Truth satisfies it, by itself no update:
    assert posterior(0, "r", lambda _g, _r: True) == Fraction(1, 2)
    # Supplied observation E=true changes both prior and likelihood jointly:
    assert posterior(0, "r", promise) == 1
    assert joint_mass(1, "r", promise) == 0


if __name__ == "__main__":
    test_read_only_decoder_cannot_be_certain()
    print("read-only ambiguous read: PASS (posterior 1/2; no decoder is certain)")
    test_supplied_promise_is_certain_only_after_conditioning()
    print("supplied truth-dependent promise: PASS (posterior 1 after E=true)")
