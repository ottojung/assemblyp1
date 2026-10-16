#!/usr/bin/env python3
"""Independent exact validation of the #269 §6.2 / genome-likelihood separation.

Scope: `AssemblyP1/Section62FlowGenomeSeparation.lean` (Antonina #269).  That Lean
module proves that the MB09 §6.2 feasible-flow objective (which factors through
the molecule-class throughput vector, by the merged
`AssemblyP1.Section62FlowCountVectorAdapter`) cannot equal the source-faithful
circular-oriented-genome likelihood of `AssemblyP1.GenomeOrbitAdapter`.

The witness is the two length-`2` circular binary genomes

    S0 = 00        (oriented windows: 00, 00)
    S1 = 11        (oriented windows: 11, 11)

which are reverse complements, hence have the *same* §6.2 molecule-class visit
vector (both visit the class {00,11} twice), while the exact oriented likelihood
of the one-read sample (00) is 1 under S0 and 0 under S1.

This script recomputes, from scratch with exact rational arithmetic and no trust
in the Lean output:

  * the oriented window multiplicities of S0 and S1;
  * the molecule-class visit vector (the §6.2 throughput) of S0 and S1, and that
    they are equal;
  * the exact oriented uniform-start read pmf and the sample likelihoods;
  * the non-factorization: no function of the visit vector can reproduce the
    likelihood, because S0 and S1 share a visit vector but differ in likelihood.

It is deterministic and exits non-zero on any failed assertion.  It shares no
code with the Lean module.
"""
from fractions import Fraction
from pathlib import Path
import re

# --- binary alphabet {0,1}, Watson-Crick complement 0 <-> 1 ----------------
COMP = {0: 1, 1: 0}


def rc(w):
    return tuple(COMP[c] for c in reversed(w))


def rep(w):
    """Molecule-class representative (MB09 §4.1): the RC-canonical length-2 word."""
    return w if w <= rc(w) else rc(w)


def windows(genome, length):
    """All oriented length-`length` circular windows of `genome`, in start order."""
    n = len(genome)
    return [tuple(genome[(s + d) % n] for d in range(length)) for s in range(n)]


def multiplicity(genome, length, w):
    return sum(1 for v in windows(genome, length) if v == w)


def visit_vector(genome, length):
    """The §6.2 molecule-class visit vector: class -> number of starts whose
    window lies in that class.  This is `Spelling.visits` of the window walk."""
    counts = {}
    for v in windows(genome, length):
        counts[rep(v)] = counts.get(rep(v), 0) + 1
    return counts


def read_pmf(genome, length, w):
    """Exact oriented uniform-start read pmf p_S(w) = multiplicity_S(w)/|G|."""
    return Fraction(multiplicity(genome, length, w), len(genome))


def likelihood(genome, length, sample):
    """Exact iid product likelihood of an ordered sample of oriented windows."""
    p = Fraction(1)
    for w in sample:
        p *= read_pmf(genome, length, w)
    return p


def check_witness():
    L = 2
    S0 = (0, 0)
    S1 = (1, 1)

    # Reverse complements.
    assert rc(S0) == S1 and rc(S1) == S0, (rc(S0), rc(S1))

    # Oriented window multiplicities.
    assert multiplicity(S0, L, (0, 0)) == 2, multiplicity(S0, L, (0, 0))
    assert multiplicity(S1, L, (0, 0)) == 0, multiplicity(S1, L, (0, 0))
    assert multiplicity(S1, L, (1, 1)) == 2, multiplicity(S1, L, (1, 1))

    # §6.2 molecule-class visit vectors coincide.
    v0 = visit_vector(S0, L)
    v1 = visit_vector(S1, L)
    assert v0 == v1, (v0, v1)
    assert v0 == {(0, 0): 2}, v0  # the class {00,11} is represented by 00

    # Exact oriented likelihoods of the one-read sample (00).
    sample = [(0, 0)]
    l0 = likelihood(S0, L, sample)
    l1 = likelihood(S1, L, sample)
    assert l0 == Fraction(1), l0
    assert l1 == Fraction(0), l1
    assert l0 != l1, (l0, l1)

    # Non-factorization: any map phi of the visit vector would give
    # phi(v0) = l0 and phi(v1) = l1, but v0 = v1 forces l0 = l1.
    assert v0 == v1 and l0 != l1, "witness must share visit vector and differ in likelihood"
    print("witness: S0=00, S1=11 share §6.2 visit vector but differ in oriented likelihood: OK")


def check_rc_invariance_of_visit_vector():
    """The §6.2 throughput is a molecule-class quantity, hence RC-invariant."""
    for genome in [(0, 0), (0, 1), (1, 0), (1, 1), (0, 0, 1), (0, 1, 1, 0)]:
        assert visit_vector(genome, 2) == visit_vector(rc(genome), 2), genome
    print("RC-invariance of the §6.2 molecule-class visit vector: OK")


def check_oriented_likelihood_not_rc_invariant():
    """The exact oriented likelihood is not RC-invariant in general."""
    L = 2
    sample = [(0, 0)]
    assert likelihood((0, 0), L, sample) != likelihood(rc((0, 0)), L, sample)
    print("non-RC-invariance of the oriented likelihood: OK")


def check_lean_witness_consistency():
    """Text-level guard that the Lean witness matches the Python instance."""
    src = (Path(__file__).resolve().parents[1] /
           "AssemblyP1/Section62FlowGenomeSeparation.lean").read_text()
    compact = re.sub(r"\s+", "", src)
    for fragment in [
        "defS0:ZMod2→A2:=fun_=>0",
        "defS1:ZMod2→A2:=fun_=>1",
        "defrep2(w:Word2):Word2:=ifw=w11thenw00elsew",
        "classCountS0=classCountS1:=bydecide",
    ]:
        assert fragment in compact, f"Lean witness diverged from Python: {fragment}"
    print("Lean witness matches Python instance: OK")


def main():
    check_lean_witness_consistency()
    check_witness()
    check_rc_invariance_of_visit_vector()
    check_oriented_likelihood_not_rc_invariant()
    print("verify_269_flow_genome_separation: PASS")


if __name__ == "__main__":
    main()
