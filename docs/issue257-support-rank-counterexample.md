# Issue #257: augmented-kernel rank does not decide rigidity

## Definitions

For a finite directed support graph `D=(V,E)`, let `M` be its signed
vertex-edge incidence matrix (`+1` at the tail and `-1` at the head), and put
`C = [M; 1^T]`. For connected support, `rank_Z ker(C) = |E|-|V|`; this is the
number of independent integral circulation perturbations that preserve both
balance and total mass. It depends only on support topology. Given positive
edge multiplicities `A`, rigidity asks whether there is any nonzero
`delta in ker_Z(C)` with `delta_e >= 1-A_e` for every edge. Thus rank counts
available directions but does not encode how far `A` lies from the positivity
boundary in each direction.

## Counterexample to a topology-only rank criterion

Take the same strongly connected support in both cases, with vertices `A,B`
and ordered edges `AA, AT, TA, TT` (loops `A->A`, `T->T` and arcs `A->T`,
`T->A`). It has `|E|=4`, `|V|=2`, and augmented-kernel rank `2`.

* `AATT`, `L=2`, has multiplicities `(1,1,1,1)`, total `G=4`. It is rigid:
  each edge is at least one and the four values sum to four, forcing the
  spectrum to be exactly `(1,1,1,1)`.
* `AATATT`, `L=2`, has multiplicities `(1,2,2,1)`, total `G=6`. It is
  non-rigid: `(2,1,1,2)` is a distinct positive balanced circulation of total
  six. The difference is the nonzero zero-sum circulation
  `delta=(1,-1,-1,1)`, and `delta >= 1-(1,2,2,1)=(0,-1,-1,0)`.

Both multiplicity vectors are circular-genome-realizable spectra on exactly
the same oriented support. The augmented-kernel rank (and indeed any invariant
of support topology alone) therefore cannot be an iff criterion for the
instance rigidity question. This formalizes the obstruction to a topology-only
classification; multiplicity/slack data must enter. The exact bounded
circulation criterion and Lean finite decider remain the current general iff.

## Reproduction

From the issue branch, run:

```sh
python3 -c 'import sys; sys.path.insert(0,"scratch257"); from rigidity import is_rigid; E=[(0,0),(0,1),(1,0),(1,1)]; A=(1,2,2,1); B=(1,1,1,1); print("AATATT:", is_rigid(2,E,A)); print("AATT:", is_rigid(2,E,B))'
```

Expected: `AATATT` is non-rigid (a witness is `(2,1,1,2)`); `AATT` is
rigid. This is an exact finite brute-force cross-check. The rigidity proof for
the unit vector is also immediate from the total-mass lower bound above.

## Scope

This refutes support-only rank as a complete decision invariant. It does not
improve the worst-case exponential finite decider, establish a polynomial
algorithm, or close the arbitrary-support structural characterization.
