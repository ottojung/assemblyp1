# Augmented throughput is determined by the edge displacement (issue #263)

This note documents the kernel-checked Lean artifact
[`AssemblyP1/AugmentedThroughputDetermined263.lean`](../AssemblyP1/AugmentedThroughputDetermined263.lean),
its axiom audit
[`AssemblyP1/AugmentedThroughputDetermined263Audit.lean`](../AssemblyP1/AugmentedThroughputDetermined263Audit.lean),
and the exact integer verifier
[`scripts/verify_263_augmented_throughput_determined.py`](../scripts/verify_263_augmented_throughput_determined.py).

## What is proved

A standalone bookkeeping cell for the augmented `[A 0; -T I]` system of the
[edge-flow / vertex-throughput Graver bridge](issue263-graver-throughput-bridge.md):
for additive `T`, two augmented-feasible points over the same right-hand side
differ in throughput coordinates exactly by `T` applied to the edge-coordinate
difference.

* `augFeas_throughput_determined` — `y (inr v) - x (inr v) = T (edge y - edge x) v`.
* `augDisp_throughput` — the feasible-displacement form
  `(y - x) (inr v) = T (fun e => (y - x) (inl e)) v`.
* `augDisp_throughput_zero_of_annihilated` — when `T` annihilates the edge
  displacement (the hypothesis `hT` of `hasGraverDecomposition_aug`), every
  feasible displacement has zero throughput coordinates. This is the exact
  corollary consumed inline by `hasGraverDecomposition_aug`, isolated here so a
  successor can build on it without re-deriving the coupling arithmetic.

## Scope

This cell does **not** prove the general `T`-sign-compatible conformal Graver
decomposition (obstructed in general: see the
[throughput sign-clash example](issue263-throughput-sign-clash-example.md)),
the extended-real boundary treatment, or the direct #261 historical signed-graph
adapter, all of which remain open. The verifier checks the determinedness
identity on the sign-clash instance's feasible pair and confirms the individual
lifted moves keep opposite throughput signs at vertex zero.
