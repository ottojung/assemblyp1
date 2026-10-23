# Issue #257: Lean-checked endpoint examples

This increment independently records the concrete `AATATT`, `L = 2` example
in the finite rigidity model used by
`AssemblyP1.FiniteRigidityDecider`. The support edges are ordered
`AA, AT, TA, TT`, with truth multiplicities `(1, 2, 2, 1)` and total `6`.
The alternative `(2, 1, 1, 2)` is also positive, balanced, and has total `6`,
so `aatatt_nonrigid` kernel-checks this non-rigidity claim using the existing
finite decider. The corresponding prior Python artifact additionally gives
the explicit perturbation `(1, -1, -1, 1)`.

For comparison, `atatat_rigid` kernel-checks the repetitive `ATATAT`, `L = 3`
example: its support is a directed 2-cycle, so balance forces both edge values
equal, and total `6` fixes each at `3`. This rigidity despite triple
`(L-1)`-mer occurrences refutes necessity of the simple no-triple repeat
condition.

## Claim status

**PROVED:** The general algebraic iff criterion
`ExactRigidityCriterion.nonrigid_iff_exists_delta` is kernel-checked, as is an
exact finite decider in `FiniteRigidityDecider.rigid_iff_decider`. The decider
enumerates `(G + 1)^|E|` candidate vectors and is therefore a checkable finite
certificate, not a polynomial-time complexity claim. The `AATATT` and
`ATATAT` endpoints are kernel-checked in the named model.

**OPEN:** A more structural characterization or better complexity bound for
arbitrary oriented read-support graphs is not established by these endpoints.
Existing family-specific criteria do not imply a universal topology-only
condition; multiplicities matter. No claim is made that the simple repeat
restriction is necessary-and-sufficient.

## Validation

* `lake build --wfail AssemblyP1.Rigidity257EndpointAudit` — passed.
* `LEAN_NUM_THREADS=1 lake env leanchecker AssemblyP1.FiniteRigidityDecider` —
  passed.
* `#print axioms` for both endpoint examples — only
  `propext`, `Classical.choice`, and `Quot.sound`.
* `python3 scripts/check-research-docs.py` — passed.
