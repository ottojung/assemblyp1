# §6.2 the window box is not sharpened to equality by observed-window designation (#284)

This note records the **refutation** of the remaining sharpness question on
#284: whether an explicit *observed-window designation* hypothesis turns the
reduction-invariant window-box upper bound into an equality with the exact
physical feasible-throughput image.

## The two objects

Fix a read length `L` and a spelled candidate word `W`.

* The **physical feasible-throughput image** `PhysImage L W` is the set of count
  vectors `d` realized by a genuine walk of length-`L` reads spelling `W`:

  ```
  PhysImage L W d  ↔  ∃ vs ovs,
      GenuineWalk L vs ovs ∧ spellWalk vs ovs = W ∧ d = throughputOf vs.
  ```

* The **window box** `WindowBox L W` is the merged reduction-invariant upper
  bound (`AssemblyP1.Section62VisitWindowBridge`):

  ```
  WindowBox L W d  ↔  ∀ u, d u ≤ windowCount L u W.
  ```

`physImage_subset_windowBox` records `PhysImage L W ⊆ WindowBox L W`
(a restatement of the merged transport bound `visitCount_le_windowCount`, not a
reproof).  `AssemblyP1.Section62VisitTransport` shows the inclusion is strict.
The question here is whether *designating observed windows* closes the gap.

## Verdict: no

The obstruction is structural, not a missing designation.  A walk spelling `W`
carries two constraints that are **not** functions of the window multiset and
**not** functions of any set of designated observed windows:

* **read-count / length**: a walk with `k` reads spells at most `k · L` symbols
  (`genuineWalk_spell_length_le`), so `k ≥ |W| / L`;
* **connectivity**: consecutive reads sit at window distance at most `L`.

The window box forgets both, and no support/observation designation can restore
them.

### Refutation 1: the prefix `delta` (general)

`delta_prefix_not_mem_image` (kernel-checked): for every word `W` with
`L < |W|`, the count vector concentrated on the **prefix window** `W.take L` is

* in the box (`prefix_delta_mem_box`: the prefix window is the length-`L` window
  at position `0`, so its multiplicity is at least `1`), and
* **not** in the image: a walk realizing it would have all reads equal to
  `W.take L` (`mem_throughputOf_pos`, `countP_eq_length_of_all_eq`), hence exactly
  one read, which spells only `W.take L ≠ W`.

This single vector already refutes every *support/observation* designation: the
prefix window is observed (it is the occurrence at position `0`), so any
hypothesis whose only constraint is "the support of `d` lies in the designated
observed windows/occurrences" accepts it.  This is stated generally as
`no_prefix_support_designation_sharpens`: for **any** predicate `H` with
`H (delta (W.take L))`, `WindowBox L W ∩ H ≠ PhysImage L W`.

### Refutation 2: endpoint designation (prefix = suffix)

The strongest natural designation names the first and last reads
(`EndpointDesignated L W d ↔ d (W.take L) ≥ 1 ∧ d (W.drop (|W| − L)) ≥ 1`).
For `W = 012301`, `L = 2` the prefix and suffix windows coincide (`01`), so the
prefix `delta` **is** endpoint-designated — and still not in the image
(`endpoint_prefix_refuted`).

### Refutation 3: endpoint designation (generic case)

For `W = 01200`, `L = 2` the prefix window `01` and suffix window `00` differ.
The two-endpoint vector `δ_{01} + δ_{00}` is endpoint-designated and in the box,
yet not in the image (`endpoint_pair_refuted`): a walk realizing it has all
reads in `{01, 00}` with one of each (`length_eq_countP_pair`), hence exactly two
reads, and two reads spell at most `2L = 4 < 5 = |W|` symbols.  This is the
read-count obstruction in its generic form.

## What survives: the schedule

The exact image is characterized by the **schedule** — the strictly increasing
list of start positions of the walk's reads, with endpoints `0` and `|W| − L`
and consecutive gaps in `1..L` (`IsSchedule`).  The schedule is exactly the
connectivity data the window multiset and any observed-window designation
forget; recovering it from a designation would be recovering the walk itself,
making the "equality" tautological.  This is the graph model handed to
#261/#262: the box is the correct reduction-invariant **upper bound**, but the
exact feasible set is the schedule-realizable set, not a box.

## Scope

* `physImage_subset_windowBox`, `genuineWalk_spell_length_le`,
  `prefix_delta_mem_box`, `delta_prefix_not_mem_image`,
  `no_prefix_support_designation_sharpens`, `endpoint_prefix_refuted`,
  `endpoint_pair_refuted` are genuine, kernel-checked, self-contained
  (Lean core only) results.
* This module does **not** redefine `isReducibleB`, `transitivelyReduced`,
  `SpelledFeasible62`, or `StepsSurviveReduction`; it does not reprove the merged
  window-multiset invariance or the merged transport bound; and it does not touch
  the #261 ML-maximality classification or the #263 Graver scope.
* The exact ML-likelihood transport to §6.2 feasible flows remains **OPEN**: the
  box is a reduction-invariant upper bound, and this note shows no
  observed-window designation can sharpen it to the exact image.

## Verification

* `lake build --wfail` of the whole library: exit 0.
* `lake env leanchecker AssemblyP1.Section62WindowBoxSharpness`: exit 0.
* Every `#print axioms` endpoint depends only on `{}` or
  `{propext, Classical.choice, Quot.sound}`; no `sorryAx`.
* `scripts/verify_284_window_box_sharpness.py`: exit 0 (independent re-derivation
  of the refutations plus a finite sweep over all words over `{0,1,2}` up to
  length 5 and all proper `L`, checked against an explicit enumeration of every
  genuine walk).
