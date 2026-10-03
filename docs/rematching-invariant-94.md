# `#94`, front B94-REM-2600: the surviving configuration in the rematching language

Committed on branch `board/94-replacement` together with section 5 of
`AssemblyP1/BBTReplacementInvariant.lean`. Nothing is pushed.

## What the previous front left

`selectedInterleaved_crux_or_triple` reduces the `(I)` clause of
`SupportDichotomy` to: two **distinct** interleaved fibres, both rematched,
one of them preceding-blocked at its two selected starts.  It then proposed to
close the case by forcing a maximal triple repeat of length `≥ L-1`, i.e. by
the three-way simultaneous extension that `BBTMaximalExtension` does not
provide.

## Three findings of this front

### 1. `P2` and `¬ LongObstruction` are the same hypothesis

`longObstruction_iff_not_P2` (with `ukkonen_imp_P2`): at `2 ≤ L`,
`LongObstruction hG L S ↔ ¬ P2 hG L S`.

Consequences.

* The `P2` clause and the `¬ LongObstruction` clause of
  `BadSelectedInterleavingRemaining` are **mutually redundant**: the
  obligation is worth exactly as much as its `¬ LongObstruction` clause.
* In particular the genome-side hypothesis can be dropped entirely, and no
  strength is lost by keeping it.  The reduced obligation is
  `InterleavingObstructionNeeded` (§5.4 of the module):

  ```text
  bad θ  ∧  ¬ SelectedTriple θ  ∧  SelectedInterleaved θ   ⟹  LongObstruction
  ```

  for *any* genome and any `2 ≤ L`, with no `P2` assumed.
  `not_remaining_of_interleavingObstruction` proves that this settles the
  previous front's obligation.

### 2. The badness lives in one permutation: `ρ = nextPos⁻¹ ∘ θ`

New in the module: `rematch θ x = prevPos hG (θ x)`, the shift classes
`shiftClass v = prevPos (fibre v)`, and

* `rematch_injective`: `ρ` is injective when `θ` is;
* `mem_rematch_shiftClass`: `ρ` preserves every shift class (this uses
  `FibrePreserving`);
* `selects_iff_rematch`: `Selects v` **is** nontriviality of `ρ` on `fibre v`.

So a rematching at `v` is a permutation of the starts of `v`, and the shift
classes are the sets on which `ρ` is allowed to act.  This is the first
description of a *bad* `θ` that does not mention interleaving.

### 3. At `¬ SelectedTriple` the two constituents have multiplicity exactly 2

`selectedInterleaving_fibreSize`: from `SelectedInterleaved` with four
pairwise distinct starts and `¬ SelectedTriple`, the two constituents are
**distinct** vertices and each has fibre cardinality exactly `2`
(`2 ≤ card` from two distinct members, `card ≤ 2` from `¬ SelectedTriple`).

`crux_rematchShape` combines rungs 1–3 with the above and states the whole
surviving configuration in one place: two distinct interleaved fibres, each of
multiplicity `2`, one preceding-blocked, and `ρ` moving at least one of the
four selected starts.

## What is *not* proved

`BadSelectedInterleavingRemaining` / `InterleavingObstructionNeeded` remain
open.  No `axiom`, no `sorry`, no `admit`, no `native_decide`; `#print axioms`
on all new theorems reports `[propext, Classical.choice, Quot.sound]`.

## A falsification attempt that did not happen (by instruction)

No witness hunt was run.  Reasoned checks only, and they are recorded as
evidence, not as results:

* the surviving configuration is **realised** at `S = 001011`, `L = 3`,
  `θ = T6` (`selectedInterleaved_T6`, `bad_001011`), so the case split is not
  vacuous;
* `T6` fails `P2` (`not_P2_001011_L3`), i.e. it sits exactly where
  `LongObstruction` holds, so it is not a counterexample;
* for `S = 00101` and `001011`, `L = 3, 4`, a Python scan of all bijective,
  fibre-preserving, one-cycle `θ` finds **no** `θ` with `ρ = nextPos⁻¹ ∘ θ` the
  identity and `θ` bad — consistent with the hypothesis that badness is
  carried by `ρ` — and it finds one `θ` that is good with `ρ ≠ id`
  (`00101`, `L = 3`), which is the known harmless crossing.  Hence
  `bad ⟹ ρ ≠ id` is the only direction available, and it is what a
  proof of the endgame can use.  This is a Python count; its completeness is
  not proved.