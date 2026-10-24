# Issue #257: exact per-support criterion for the AATATT/AATT support

## Result

`AssemblyP1.RigidityAatattSlack.aatatt_rigid_iff`: for every feasible
circulation `A` of total `G` on the `AA, AT, TA, TT` support,

> `Rigid A G ↔ G = 4` (equivalently, `A = (1,1,1,1)`).

Supporting lemmas:

* `rigid_of_total_eq_card` (general, any support): `G = |E|` forces the
  all-ones vector, hence rigidity. Proof: `∑ (B e - 1) = 0` with nonnegative
  terms.
* `aatatt_balanced_iff`: balance on this support is exactly `AT = TA`.
* `aatatt_ge_four`: `G ≥ 4` always.
* Three parametric non-rigidity witnesses covering all `G > 4`:
  `aatatt_loop_swap_nonrigid` (asymmetric loops: swap them),
  `aatatt_shift_nonrigid` (`AT = TA ≥ 2`: `δ = (1,-1,-1,1)`),
  `aatatt_shift_rev_nonrigid` (loops `≥ 2`: `δ = (-1,1,1,-1)`).

## Why this matters

This is the first *fully parametric* exact criterion for a
genome-realizable support with a 2-dimensional circulation kernel: topology
alone (augmented-kernel rank 2, cf. `docs/issue257-support-rank-counterexample.md`)
cannot decide rigidity, but topology *plus total mass* can here. It is a
template for per-support exact criteria: collapse balance to independent
equations, then case-split on where the slack sits.

## Scope

Per-support only; arbitrary-support structural characterization and
complexity remain open. No repeat-bounds iff claimed.
