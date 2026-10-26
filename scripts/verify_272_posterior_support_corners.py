#!/usr/bin/env python3
"""Exact-rational support-corner checks for finite Bayesian conditioning.

Posterior certainty is a statement about the supported truth fibre, and only
for observations with positive predictive mass. This tiny example checks the
positive-prior/positive-likelihood qualifiers and the zero-denominator case.
"""

from fractions import Fraction


G = ("truth", "zero-prior", "zero-likelihood", "competitor")
R = ("r",)
prior = {
    "truth": Fraction(1, 2),
    "zero-prior": Fraction(0),
    "zero-likelihood": Fraction(1, 4),
    "competitor": Fraction(1, 4),
}
likelihood = {
    ("truth", "r"): Fraction(1),
    ("zero-prior", "r"): Fraction(1),
    ("zero-likelihood", "r"): Fraction(0),
    ("competitor", "r"): Fraction(1),
}


def joint_mass(g, r, event):
    return prior[g] * likelihood[g, r] * Fraction(int(event(g, r)))


def predictive_mass(r, event):
    return sum(joint_mass(g, r, event) for g in G)


def posterior_mass(g, r, event):
    denominator = predictive_mass(r, event)
    assert denominator > 0
    return joint_mass(g, r, event) / denominator


def main():
    # An observable promise excludes the only positive-support competitor.
    event = lambda g, _r: g != "competitor"
    assert predictive_mass("r", event) == Fraction(1, 2)
    assert posterior_mass("truth", "r", event) == 1
    # Zero prior and zero likelihood do not enter the supported truth fibre.
    assert posterior_mass("zero-prior", "r", event) == 0
    assert posterior_mass("zero-likelihood", "r", event) == 0

    # Excluding all positive mass makes conditioning undefined, not certain.
    impossible = lambda _g, _r: False
    assert predictive_mass("r", impossible) == 0
    try:
        posterior_mass("truth", "r", impossible)
    except AssertionError:
        pass
    else:
        raise AssertionError("zero-mass observation must not have a posterior")
    print("positive-mass support and zero-support corners: PASS")


if __name__ == "__main__":
    main()
