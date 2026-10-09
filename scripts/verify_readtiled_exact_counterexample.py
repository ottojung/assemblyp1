#!/usr/bin/env python3
"""Reproduce the read-tiled exact-multinomial counterexample of issue #217.

Row R4 of `docs/source-notes/interpretation-matrix-217.md` cites, without an
observation or an artifact, the pair

    S = AAABCBC   (G = 7)
    D = AAAAABC   (G = 7)     same length
    L = 3
    realized starts (0, 0, 0, 1, 2, 5, 6)   ->  n = 7 reads
    exact multinomial ratio  L_E(D|x) / L_E(S|x) = 27

This script pins that instance down exactly and checks every clause of the
source bridging predicate `I_s` on it, so the row can be read as a reviewed
exact counterexample rather than an unbacked table entry.

Sharing the implementation: the `I_s` predicate (coverage, all-bridged maximal
triple repeats, bridged interleaved pairs, single-lift straddle semantics) is
imported from `scripts/uniform_strand_semantics_search.py` instead of being
re-derived here.  Re-implementing it would create a second definition of the
bridging predicate, which is exactly the source-fidelity risk this repository
tries to avoid.

Exit status is non-zero on any failed check.
"""

from __future__ import annotations

import os
import sys
from collections import Counter
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import uniform_strand_semantics_search as us  # noqa: E402

TRUTH = list("AAABCBC")
COMPETITOR = list("AAAAABC")
READ_LEN = 3
STARTS = [0, 0, 0, 1, 2, 5, 6]


def main() -> int:
    G = len(TRUTH)
    assert len(COMPETITOR) == G, "the witness must be a same-length pair"
    alphabet = us.alphabet_for(2)

    spec_S = us.spectrum(TRUTH, READ_LEN, alphabet, False)
    spec_D = us.spectrum(COMPETITOR, READ_LEN, alphabet, False)
    observed = us.observed(TRUTH, STARTS, READ_LEN, alphabet, False)
    n = len(STARTS)

    failures: list[str] = []

    def check(name: str, condition: bool, detail: str = "") -> None:
        print(f"  {'ok  ' if condition else 'FAIL'} {name}{(': ' + detail) if detail else ''}")
        if not condition:
            failures.append(name)

    print("read-tiled exact-multinomial counterexample (issue #217, row R4)")
    print(f"  truth S = {''.join(TRUTH)}   competitor D = {''.join(COMPETITOR)}")
    print(f"  G = {G}  L = {READ_LEN}  n = {n}  realized starts = {STARTS}")
    print(f"  spec_{READ_LEN}(S) = {dict(spec_S)}")
    print(f"  spec_{READ_LEN}(D) = {dict(spec_D)}")
    print(f"  observed x       = {dict(observed)}")

    # ---- the bridging predicate I_s, clause by clause -------------------
    triples = us.triple_repeats(TRUTH)
    interleaved = us.interleaved_pairs(TRUTH)
    covers = us.covers(TRUTH, STARTS, READ_LEN)
    triple_all_bridged = all(
        us.copy_bridged(TRUTH, t, ell, STARTS, READ_LEN) for ell, tri in triples for t in tri
    )
    interleaved_ok = all(
        any(us.copy_bridged(TRUTH, t, ell, STARTS, READ_LEN) for t in p1)
        or any(us.copy_bridged(TRUTH, t, ell2, STARTS, READ_LEN) for t in p2)
        for (ell, p1), (ell2, p2) in interleaved
    )

    print("  bridging predicate I_s:")
    check("clause 1: realized reads cover every genome position", covers)
    check(
        "clause 2: every maximal triple repeat is all-bridged",
        triple_all_bridged,
        f"triple repeats = {triples}",
    )
    check(
        "clause 3: every interleaved maximal-repeat pair is bridged",
        interleaved_ok,
        f"interleaved pairs = {interleaved}"
        + (" (vacuously: none)" if not interleaved else ""),
    )
    check(
        "the triple-repeat clause is non-vacuous (the bridging rule is exercised)",
        bool(triples),
        f"maximal triple repeats {triples}",
    )

    # ---- the exact multinomial ratio -----------------------------------
    ratio = us.exact_ratio(spec_S, spec_D, observed, G, G)
    # The observation-only multinomial coefficient n! / prod_i x_i! is common
    # to both candidates (sum_i x_i = n), so it cancels in the ratio; it is
    # computed here only to print the two likelihoods.
    factorial = 1
    for k in range(2, n + 1):
        factorial *= k
    denom = 1
    for xc in observed.values():
        f = 1
        for k in range(2, xc + 1):
            f *= k
        denom *= f
    multinomial_coefficient = Fraction(factorial, denom)

    lik_S = multinomial_coefficient
    lik_D = multinomial_coefficient
    for w, xc in observed.items():
        lik_S *= Fraction(spec_S.get(w, 0), G) ** xc
        lik_D *= Fraction(spec_D.get(w, 0), G) ** xc

    print("  exact objective (candidate-intrinsic N(D) = G = 7):")
    print(f"    multinomial coefficient = {multinomial_coefficient}")
    print(f"    L_E(S|x) = {lik_S}")
    print(f"    L_E(D|x) = {lik_D}")
    check("L_E(D|x) > L_E(S|x)", lik_D > lik_S)
    check("L_E(D|x) / L_E(S|x) == 27", ratio == Fraction(27), f"ratio = {ratio}")
    check(
        "the ratio equals the direct product form",
        ratio == Fraction(lik_D, lik_S),
    )

    print("  domain of the §6.1 fixed-N binomial at N = G = 7:")
    check(
        "every competitor multiplicity is < N",
        all(d < G for d in spec_D.values()),
        f"max d_D = {max(spec_D.values())}",
    )

    if failures:
        print(f"FAILED: {failures}")
        return 1
    print("all checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
