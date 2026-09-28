import AssemblyP1.BBTCrossingCoalesce

/-!
# `Issue89GapMap`: exactly what stands between §5 and an inhabitant of
# `CrossingChordsCoalesce`

This module is a **gap map**, not a proof.  It is the deliverable of board
issue 94 for the crossing-chords front.  Its job is to make the §5 five-step
reduction of `AssemblyP1.BBTCrossingCoalesce` (§5, docstring of
`InterleaveUntilCollision`, lines 217-282 of that file) explicit as a list of
separate statements, to say for each which are **already proved** in the
library (cited by name and file:line, never restated), which are **proved
here**, and which are **open** --- and, for the open ones, to state the exact
remaining goal in Lean-shaped terms.

It proves **nothing** about `CrossingChordsCoalesce`.  Both of the two
`Prop`s the reduction is built on remain without inhabitants.  (Correction,
board-94 front: the step-3 `Prop` `Step3_slides_meet_no_foreign_chord` *is*
now inhabited --- see `step3_slides_meet_no_foreign_chord`, commit `1fc4e81`.
The step-1 and step-5 `Prop`s are still without inhabitants.)

## The headline result: both §5 `Prop`s are **false as stated**

This is the single most important thing in the file, and it is
kernel-checked, not asserted:

* **§1. `SlidePreservesInterleaved` is refuted.**  At `K = 6`, `L = 2`, the
  word `w6b = 010101` and the quadruple `(a, b, c, d) = (0, 3, 2, 5)`,
  the two pairs `{0, 3}` and `{2, 5}` do each carry a common `1`-mer and do
  interleave, and none of the four stated guards fails; yet the conclusion
  `Interleaved (rotAdd 5 0) (rotAdd 5 3) 2 5` is **false**, because
  `rotAdd 5 3 = 2 = c`, so the four "distinct" endpoints are not distinct.
  See `SlidePreservesInterleaved_refuted`.

  The statement slides the **wrong** pair.  It rotates `a, b` left while
  holding `c, d` fixed, and the guards only exclude collisions of the
  *rotated* `c, d` with the *unrotated* `a, b`.  The proof plan in §5 needs the
  opposite: it slides the chord `c, d` down its backward list while `a, b`
  stay fixed.  With the pair swapped --- `c, d` slides, four guards --- every
  quadruple of `Fin K` satisfies the statement for `K ≤ 5` and for
  `K = 6, 8, 10` (`AllSlid_6`, `AllSlid_8_10`); with **all eight** guards it
  also holds at `K = 6, 8, 10` (`AllSlid8_6`, `AllSlid8_8_10`).  This is
  bounded evidence: the completeness of the search is not proved, and no claim
  is made about `K > 10`.  The four-guard shape `Slid` was later **proved
  outright** for every `K` and every quadruple, by `Issue94IterSlide.slide_one`
  (commit `0806303`), so the searches below are now history rather than the
  current state of the art.  The eight-guard shape `Slid8` is still, as far as
  this file records, evidence only.  §6 below is written against named commits
  rather than against a date, so that each entry can be re-checked
  independently.

  So the §5 `Prop` is not merely unproved: it is a **mis-statement** whose
  correction is plausible.  This is a real, small, checkable piece of progress:
  the reduction is blocked on a lemma that is false, not on a hard lemma.

* **§2. `ShiftLeftPersistence` is refuted.**  It is stated for a *plain*
  shift `t` with only `t ≤ K`, and the library itself already records the
  counterexample in a comment (`P2RepeatResidual.lean`: §5a, "`S = 001`,
  `L = 2`, `a = 0`, `b = 1` ... at `t = 1` they read `vtx 2 = 1` and
  `vtx 0 = 0`").  `ShiftLeftPersistence_refuted` below makes that
  comment kernel-checked.  The **correct** statement --- with the side
  condition `t ≤ pairBack a b` --- is already **proved** in the library as
  `P2RepeatResidual.chord_shift_left` (line 497).  So this half of the §5
  reduction is not open at all: it is discharged, and the `Prop` that
  `§5` lists as missing is a weaker-but-wrong restatement of a theorem the
  library already has.

  Note the consequence for the "visibility obstacle" docstring of
  `ShiftLeftPersistence` (`BBTCrossingCoalesce.lean`:284-298), which says the
  lemma "belongs next to `pairBack`, in that file" because `backAgree` is
  `private`.  That is true of the *naive* statement, and the corrected
  statement is indeed in that file --- as `chord_shift_left`.  The obstacle
  was real for the statement chosen and does not survive the correction.

## What is genuinely left

This paragraph was written when step 2's combinatorial half and step 4 were
both open.  **As of the commits named below that is no longer true**, and the
rest of this file has been corrected to match:

* the combinatorial half of step 2 is **proved** ---
  `Issue94Step2Path.step2_components_are_paths_proved` (commit `ee61190`);
* step 4 in the shape §5 means --- the *conjunction*-shaped guard, which is
  what `Issue94IterSlide.SlideGuards` means --- is **proved** ---
  `Issue94Step4Prop.step4_guarded` (commit `7cd813e`);
* `Step4_slide_iterates` **as written in this file** is not open but
  **refuted**, because its guard clause is an implication chain and not a
  conjunction --- `Issue94Step4Prop.not_Step4_slide_iterates_1` (commit
  `7cd813e`).

What was left was the `vtx_maxPairStart` question of §4, whose only remaining
input was `Step5_heads_interleave` --- the claim that the heads of the two
backward orbits interleave.  That claim is now **refuted**, at commit
`a033fe4`, by `not_Step5_heads_interleave_3` in
`AssemblyP1/Issue94Step5Heads.lean`.  What is left instead is
`Issue94Step5Heads.head_dichotomy` at `L = K`, the same commit: the two
interleaving chords either have `SameExtension` or their four heads interleave.
It is **not proved**.  See the `Step*` `Prop`s below and the classification
comments, each of which names the commit that settles it.

## Status of every declaration here

Every theorem in this file is `#print axioms`-clean and kernel-checked; the
`Prop`s with no inhabitant are marked as such.  No `sorry`, no `admit`, no new
`axiom`, no `native_decide`, no `unsafe`, no linter suppression, no weakened
restatement of any existing theorem.
-/

namespace AssemblyP1.Issue89GapMap

open AssemblyP1.SourceFaithfulIs
open AssemblyP1.PopulationReduction
open AssemblyP1
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.OrientedRigidity
open AssemblyP1.BBTChords
open AssemblyP1.P2RepeatResidual
open AssemblyP1.BBTLadder
open AssemblyP1.BBTCrossingCoalesce

set_option maxHeartbeats 800000

/-! ## 0. The `vtx`-free layer: a decidable `Interleaved`

`Interleaved` is a `Prop` over a `Genome`, and `Decidable` instances for it
are awkward to get out of the library definition (the `Genome` wrapper hides
the length behind a structure projection).  The definitions below spell the
*same* predicate on the bare length `K`, which is what makes the exhaustive
checks of §1 possible at all.  They are the *only* purpose of this section;
nothing downstream of §2 uses them. -/

/-- `Interleaved` for a circle of `K` positions, spelled out on `K`.
This is `SourceFaithfulIs.Interleaved` at `Genome.len = K`, i.e.
`BBTUniqueEulerian.interleavedStarts_iff`'s `InArc` coordinate. -/
def InterK (K : ℕ) [NeZero K] (a b c d : Fin K) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    ((0 < (c.val + K - a.val) % K ∧ (c.val + K - a.val) % K < (b.val + K - a.val) % K) ↔
      ¬(0 < (d.val + K - a.val) % K ∧ (d.val + K - a.val) % K < (b.val + K - a.val) % K))

instance instInterK (K : ℕ) [NeZero K] (a b c d : Fin K) : Decidable (InterK K a b c d) := by
  unfold InterK; infer_instance

/-- The four stated collision guards of `SlidePreservesInterleaved`, collected. -/
def Guards (K : ℕ) (hK : 0 < K) [NeZero K] (a b c d : Fin K) : Prop :=
  rotAdd hK (K - 1) c ≠ a ∧ rotAdd hK (K - 1) c ≠ b ∧
  rotAdd hK (K - 1) d ≠ a ∧ rotAdd hK (K - 1) d ≠ b

/-- The four *reverse* collision guards: the rotated `a, b` also avoid `c, d`. -/
def GuardsR (K : ℕ) (hK : 0 < K) [NeZero K] (a b c d : Fin K) : Prop :=
  rotAdd hK (K - 1) a ≠ c ∧ rotAdd hK (K - 1) a ≠ d ∧
  rotAdd hK (K - 1) b ≠ c ∧ rotAdd hK (K - 1) b ≠ d

instance instGuards (K : ℕ) (hK : 0 < K) [NeZero K] (a b c d : Fin K) : Decidable (Guards K hK a b c d) := by
  unfold Guards; infer_instance
instance instGuardsR (K : ℕ) (hK : 0 < K) [NeZero K] (a b c d : Fin K) : Decidable (GuardsR K hK a b c d) := by
  unfold GuardsR; infer_instance

/-! ## 1. `SlidePreservesInterleaved` is **false as stated**

Three shapes, all pure cyclic-order statements mentioning no word.  `Stated`
is verbatim the cyclic content of `BBTCrossingCoalesce.SlidePreservesInterleaved`
(`BBTCrossingCoalesce.lean`:316-324); `Slid` is the shape the §5 plan
actually needs (`c, d` slides, `a, b` fixed); `Slid8` adds the four reverse
guards. -/

/-- **Verbatim the cyclic content of `SlidePreservesInterleaved`.**  This is
the shape that is refuted below. -/
def Stated (K : ℕ) (hK : 0 < K) [NeZero K] (a b c d : Fin K) : Prop :=
  InterK K a b c d → Guards K hK a b c d →
    InterK K (rotAdd hK (K - 1) a) (rotAdd hK (K - 1) b) c d

/-- **The shape the §5 plan needs**: the *second* pair slides, with the same
four guards.  Bounded evidence at `K ≤ 5` and at `K = 6, 8, 10` when written;
since proved outright for every `K` as `Issue94IterSlide.slide_one` (commit
`0806303`), so this is now a proved theorem, not a conjecture. -/
def Slid (K : ℕ) (hK : 0 < K) [NeZero K] (a b c d : Fin K) : Prop :=
  InterK K a b c d → Guards K hK a b c d →
    InterK K a b (rotAdd hK (K - 1) c) (rotAdd hK (K - 1) d)

/-- **`Slid` with all eight guards.**  No counterexample found for `K ≤ 5` or
at `K = 6, 8, 10`; as far as this file records, still bounded evidence only.
`slide_one` is proved with four guards, so it does not settle this. -/
def Slid8 (K : ℕ) (hK : 0 < K) [NeZero K] (a b c d : Fin K) : Prop :=
  InterK K a b c d → Guards K hK a b c d → GuardsR K hK a b c d →
    InterK K a b (rotAdd hK (K - 1) c) (rotAdd hK (K - 1) d)

instance instStated (K : ℕ) (hK : 0 < K) [NeZero K] (a b c d : Fin K) : Decidable (Stated K hK a b c d) := by
  unfold Stated; infer_instance
instance instSlid (K : ℕ) (hK : 0 < K) [NeZero K] (a b c d : Fin K) : Decidable (Slid K hK a b c d) := by
  unfold Slid; infer_instance
instance instSlid8 (K : ℕ) (hK : 0 < K) [NeZero K] (a b c d : Fin K) : Decidable (Slid8 K hK a b c d) := by
  unfold Slid8; infer_instance

def AllStated (K : ℕ) (hK : 0 < K) [NeZero K] : Prop := ∀ a b c d : Fin K, Stated K hK a b c d
def AllSlid (K : ℕ) (hK : 0 < K) [NeZero K] : Prop := ∀ a b c d : Fin K, Slid K hK a b c d
def AllSlid8 (K : ℕ) (hK : 0 < K) [NeZero K] : Prop := ∀ a b c d : Fin K, Slid8 K hK a b c d

instance instAllStated (K : ℕ) (hK : 0 < K) [NeZero K] : Decidable (AllStated K hK) := by
  unfold AllStated; infer_instance
instance instAllSlid (K : ℕ) (hK : 0 < K) [NeZero K] : Decidable (AllSlid K hK) := by
  unfold AllSlid; infer_instance
instance instAllSlid8 (K : ℕ) (hK : 0 < K) [NeZero K] : Decidable (AllSlid8 K hK) := by
  unfold AllSlid8; infer_instance

/-- **`Stated` holds at `K = 3, 4, 5`.**  Bounded evidence, *not* a proof at any
`K`; in particular it is *not* a proof that `Stated` holds for all `K < 6`. -/
theorem AllStated_small :
    AllStated 3 (by norm_num) ∧ AllStated 4 (by norm_num) ∧ AllStated 5 (by norm_num) :=
  ⟨by decide, by decide, by decide⟩

/-- **`Stated` fails at `K = 6`.**  The stated shape is false. -/
theorem not_AllStated_6 : ¬ AllStated 6 (by norm_num) := by decide

/-- **The explicit `K = 6` counterexample to `Stated`**:
`InterK 6 0 3 2 5` and all four guards hold, but the conclusion fails. -/
theorem Stated_counterexample_6 :
    InterK 6 0 3 2 5 ∧
    Guards 6 (by norm_num : 0 < 6) 0 3 2 5 ∧
    ¬ InterK 6 (rotAdd (by norm_num : 0 < 6) 5 0) (rotAdd (by norm_num : 0 < 6) 5 3) 2 5 :=
  ⟨by decide, by decide, by decide⟩

/-- **`Slid` holds at `K = 6`.**  Bounded evidence only. -/
theorem AllSlid_6 : AllSlid 6 (by norm_num) := by decide

/-- **`Slid` holds at `K = 8` and `K = 10`.**  Bounded evidence only: this
checks every quadruple of `Fin 8` and of `Fin 10` and nothing larger.  The
completeness of such a search is *not* proved, so this is evidence and not a
statement about all `K`. -/
theorem AllSlid_8_10 : AllSlid 8 (by norm_num) ∧ AllSlid 10 (by norm_num) :=
  ⟨by decide, by decide⟩

/-- **`Slid8` holds at `K = 6`.**  Bounded evidence only. -/
theorem AllSlid8_6 : AllSlid8 6 (by norm_num) := by decide

/-- **`Slid8` holds at `K = 8` and `K = 10`.**  Bounded evidence only, on the
same terms as `AllSlid_8_10`. -/
theorem AllSlid8_8_10 : AllSlid8 8 (by norm_num) ∧ AllSlid8 10 (by norm_num) :=
  ⟨by decide, by decide⟩

/-- **`SlidePreservesInterleaved` is refuted**, as a statement about words:
at `L = 2`, `K = 6`, the word `w6b` below and the quadruple `(0, 3, 2, 5)`,
every hypothesis of the library `Prop` holds and its conclusion fails.

`w6b = 010101` is read at `L = 2`, so the `(L-1)`-mers are single symbols and
`vtx a = vtx b` holds for every pair of starts of equal parity --- in
particular for `(0, 3)` (`0, 1`) and for `(2, 5)` (`0, 1`).  The two chords
`{0, 3}` and `{2, 5}` interleave on the six-cycle.  The four guards hold
because `rotAdd 5 2 = 1 ∉ {0, 3}` and `rotAdd 5 5 = 4 ∉ {0, 3}`.  But
`rotAdd 5 3 = 2 = c`, so the conclusion asks for the four points
`5, 2, 2, 5` to be pairwise distinct, which they are not. -/
theorem six : 0 < 6 := by norm_num



def w6b : Fin 6 → Bin
  | 0 => Bin.A | 1 => Bin.B | 2 => Bin.A | 3 => Bin.A | 4 => Bin.B | _ => Bin.A

/-- the six-cycle carrying the counterexample -/
abbrev g6 : SourceFaithfulIs.Genome Bin := ⟨6, six, w6b⟩

/-- the two `vtx` hypotheses at `(0,3)` and `(2,5)` -/
theorem w6b_vtx03 : vtx six 2 w6b 0 = vtx six 2 w6b 3 := by decide
theorem w6b_vtx25 : vtx six 2 w6b 2 = vtx six 2 w6b 5 := by decide
theorem w6b_interleaved : Interleaved g6 (0:Fin 6) (3:Fin 6) (2:Fin 6) (5:Fin 6) := by decide
theorem w6b_g1 : rotAdd six 5 2 ≠ (0 : Fin 6) := by decide
theorem w6b_g2 : rotAdd six 5 2 ≠ (3 : Fin 6) := by decide
theorem w6b_g3 : rotAdd six 5 5 ≠ (0 : Fin 6) := by decide
theorem w6b_g4 : rotAdd six 5 5 ≠ (3 : Fin 6) := by decide
theorem w6b_not_interleaved_slid : ¬ Interleaved g6 (rotAdd six 5 (0:Fin 6)) (rotAdd six 5 (3:Fin 6)) (2:Fin 6) (5:Fin 6) := by decide

theorem SlidePreservesInterleaved_refuted :
    ¬ (∀ (K : ℕ) (hK : 0 < K) (S : Fin K → Bin) (a b c d : Fin K),
      a ≠ b → c ≠ d →
      vtx hK 2 S a = vtx hK 2 S b → vtx hK 2 S c = vtx hK 2 S d →
      Interleaved (mkGenome hK S) a b c d →
      rotAdd hK (K - 1) c ≠ a → rotAdd hK (K - 1) c ≠ b →
      rotAdd hK (K - 1) d ≠ a → rotAdd hK (K - 1) d ≠ b →
      Interleaved (mkGenome hK S) (rotAdd hK (K - 1) a) (rotAdd hK (K - 1) b) c d) := by
  intro h
  have hres := h 6 six w6b (0 : Fin 6) (3 : Fin 6) (2 : Fin 6) (5 : Fin 6)
    (by decide) (by decide) w6b_vtx03 w6b_vtx25 w6b_interleaved
    w6b_g1 w6b_g2 w6b_g3 w6b_g4
  exact w6b_not_interleaved_slid (by simpa [mkGenome, g6] using hres)

/-! ## 2. `ShiftLeftPersistence` is refuted; the corrected form is **already proved** -/

/-- **`ShiftLeftPersistence` is refuted**, at `L = 2`, `K = 3`, the word
`S = (0, 0, 1)`, `a = 0`, `b = 1`, `t = 1`.  `vtx 0 = vtx 1 = (0)`, but
`vtx (rotAdd 2 0) = vtx 2 = (1)` while `vtx (rotAdd 2 1) = vtx 0 = (0)`.
This is exactly the counterexample recorded in the comment above
`P2RepeatResidual.chord_shift_left` (`P2RepeatResidual.lean`:465-471); here it
is kernel-checked. -/
theorem three : 0 < 3 := by norm_num

def w3 : Fin 3 → Bin
  | 0 => Bin.A | 1 => Bin.A | _ => Bin.B

theorem w3_vtx01 : vtx three 2 w3 0 = vtx three 2 w3 1 := by decide
theorem w3_broken : vtx three 2 w3 (rotAdd three 2 0) ≠ vtx three 2 w3 (rotAdd three 2 1) := by decide

theorem ShiftLeftPersistence_refuted :
    ¬ (∀ (K : ℕ) (hK : 0 < K) (S : Fin K → Bin) {a b : Fin K} (t : ℕ),
      t ≤ K →
      vtx hK 2 S a = vtx hK 2 S b →
      vtx hK 2 S (rotAdd hK (K - t) a) = vtx hK 2 S (rotAdd hK (K - t) b)) := by
  intro h
  exact w3_broken (h 3 three w3 1 (by decide) w3_vtx01)

/-- **The corrected form of `ShiftLeftPersistence`, restated here with the
side condition `t ≤ pairBack a b` that makes it true, and *proved* by
re-deriving it from the library's `P2RepeatResidual.chord_shift_left`.**

This is the only theorem in this file that discharges a §5 step, and it
discharges it by **citation**, not by new mathematics: the corrected lemma is
`P2RepeatResidual.chord_shift_left` (`P2RepeatResidual.lean`:497), already
kernel-checked in the library.  The point of restating it is to record that
§5 step 2 ("`ShiftLeftPersistence` keeps `C_j` a chord") is **not open**. -/
theorem shift_left_persistence_corrected {G _L : ℕ} (hG : 0 < G) (S : Fin G → Bin)
    {a b : Fin G} (ℓ t : ℕ)
    (hag : ∀ d : Fin ℓ, cyc hG S (a.val + d.val) = cyc hG S (b.val + d.val))
    (ht : t ≤ pairBack hG S a.val b.val) :
    ∀ d : Fin ℓ, cyc hG S ((a.val + G - t) % G + d.val)
        = cyc hG S ((b.val + G - t) % G + d.val) :=
  P2RepeatResidual.chord_shift_left hG S a b ℓ t hag ht

/-! ## 3. The five-step reduction, step by step

Step numbering follows `BBTCrossingCoalesce.lean`:249-277 verbatim.

**Step 1. Fibres have size two.**  *Proved.*  `P2.imp_nodeCount_le_two`
(`P2RepeatResidual.lean`:381) gives `nodeCount ≤ 2`; the form the collision
step needs is `BBTCrossingCoalesce.three_starts_ne` (`:133`) and
`BBTCrossingCoalesce.collision_forces_pair` (`:169`).  Nothing to do.  The
`Step1_fibre_le_two` `Prop` below is a faithful restatement *for the record*;
its inhabitant is `step1_proved`, which is pure citation.

**Step 2. The canonical extension is constant along a component.**  *Split into
two sub-steps.*  The word-level half is **proved** (by citation to
`chord_shift_left`, and to `P2RepeatResidual.pairBack_shift` `:540` and
`BBTLadder.maxPairStart_eq` `:151` / `maxPairStart_rotAdd` `:167`, which give
that the head of the backward list is exactly the pair of extension starts).
The combinatorial half --- that the truncated backward orbit of a chord is a
**path** and does not revisit itself --- was recorded here as **open**.  It is
now **proved**: `Issue94Step2Path.step2_components_are_paths_proved`
(commit `ee61190`) derives it from primitivity alone, for every `K`, every
genome and every `L`.  The two ways the orbit could return to `{a, b}` are
each excluded: `j ≡ 0 (mod K)` by `pairBack_lt_G`, and `2 * j ≡ 0 (mod K)`,
i.e. `K = 2 * j`, by observing that the circle is then literally `T ++ T` with
`|T| = K / 2 < K`, contradicting `IsPrimitive`.  The `Prop` itself is
unchanged and still lives in this file; its inhabitant lives in
`Issue94Step2Path`.  §5 below records why the naive reading of §5 step 2 (as a
statement about the *word*) was not what step 4 needs, and what the gap
actually was.

**Step 3. Slides do not meet a chord of another component.**  *Proved*, by
`collision_forces_pair` and `three_starts_ne`: if `C_j` shared an endpoint with
`D` then by step 1 `C_j = D`, so `D` is in `C`'s component.  Restated for the
record as `Step3_slides_meet_no_foreign_chord`; **now given an inhabitant**
by `step3_slides_meet_no_foreign_chord` (commit `1fc4e81`).  The earlier text
here said no inhabitant was given "because writing that proof requires naming
the component relation, which the library does not define"; that was false,
since the `Prop` ranges over quadruples of starts, and it is corrected at the
`Prop` itself.

**Step 3 does not deliver the guard that step 5 actually needs.**  With the
refutation of `Step5_heads_interleave` at commit `a033fe4` in hand, the
diagnosis is sharp.  `heads_of_one_chord_ne` (commit `a033fe4`) proves that
*within one chord* the two extension starts are distinct.  So the four heads of
`Step5_heads_interleave` can fail to be pairwise distinct **only** by a
**cross-chord** collision:
`maxPairStart a b = maxPairStart c d` or `maxPairStart a b = maxPairStart d c`.
The guard step 5 needed is a statement about *heads*, i.e. about
`maxPairStart` applied to two different chords.
`Step3_slides_meet_no_foreign_chord` is quantifier-mismatched against exactly
that need: it talks about chords and their *components* (`(a = c ∧ b = d) ∨
(a = d ∧ b = c) ∨ all-four-distinct`), and it constrains only the input starts
`a b c d`, never the heads.  It therefore delivers **no head-level guard at
all** --- which is why it does not block the counterexample, whose chords are
already distinct at the input starts and whose failure happens downstream at
`maxPairStart`.  The *pair*-level content of step 3 is now discharged outright,
in the same file, by `step3_slides_meet_no_foreign_chord` (commit `1fc4e81`);
what is still missing is the head-level restatement, on which the refutation of
`Step5_heads_interleave` and any replacement of it now turn.  So the diagnosis
below survives the inhabitant: discharging the `Prop` as phrased does not move
step 5.  This is recorded here, beside the step entries,
because it is the diagnosis a later front needs, not a claim that the step-3
`Prop` is wrong.

**Step 4. A slide preserves interleaving.**  *The `§5` statement of it is
false as written (§1 above) and the corrected one-step shape is proved.*
`Step4_slide_preserves` below is the one-step `Slid` shape with the word
carried along; its cyclic content is `Issue94IterSlide.slide_one` (commit
`0806303`), proved for every `K`, and it remains without an inhabitant here
only because the word-level spelling has not been written up in that module.

The shape the reduction *iterates* is `Step4_slide_iterates` ("applied
repeatedly along the backward list").  That `Prop` is **not open and not
proved: it is refuted** (`Issue94Step4Prop.not_Step4_slide_iterates_1`, commit
`7cd813e`), because Lean reads its guard clause
`∀ j ≤ t, A → B → C → D` as an implication *chain*, which is vacuously
satisfied precisely at the `j` where the slid pair has collided with `a` or
`b` --- the collisions the guard exists to exclude.  The guard §5 means is the
*conjunction* `∀ j ≤ t, A ∧ B ∧ C ∧ D`, which is
`Issue94IterSlide.SlideGuards` (`slide = rotAdd (K - j)` definitionally).
In that shape step 4 is **proved outright**, for every `L` and every `K`, with
no primitivity and no `P2` hypothesis: `Issue94Step4Prop.step4_guarded`
(commit `7cd813e`), whose statement is
`Issue94Step4Prop.Step4_slide_iterates_guarded`.  Both `Prop`s are kept here;
the gap map's job is to say which proposition is true, not to delete the
false one.

**Step 5. Contradiction.**  *Proved* as far as it can be: the ingredients
`P2.imp_ExtCrossing` (`P2RepeatResidual.lean`:903) and
`BBTCrossingCoalesce.vtx_maxPairStart` (`:190`) are both in the library, and
§4 below shows precisely what they do and do not give.  What step 5 needs on
top of them --- that the two heads **cross** --- is the content of step 4. -/

/-- **Step 1, restated**: every `(L-1)`-mer is spelled at most twice.
*Proved*: this is `P2.imp_nodeCount_le_two` (`P2RepeatResidual.lean`:381),
specialised at each `k`.  Restated only to give the step a name. -/
def Step1_fibre_le_two (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → Bin) (_hP2 : P2 hK L S)
    (_hprim : RepeatAdapter.IsPrimitive hK S), 2 ≤ L → L ≤ K →
    ∀ k : Fin (L - 1) → Bin, nodeCount (L := L) hK S k ≤ 2

/-- **Step 1, inhabited by citation.**  No new mathematics. -/
theorem step1_proved (L : ℕ) : Step1_fibre_le_two L :=
  fun _K hK S hP2 hprim hL hLG k =>
    P2.imp_nodeCount_le_two hK hL hLG S hprim hP2 k

/-- **Step 2, combinatorial half (PROVED, in `Issue94Step2Path`).**  The
truncated backward orbit of a chord `{a, b}`, namely
`{{a - j, b - j} : j ≤ pairBack a b}`, visits no chord twice: there is no
`0 < j ≤ pairBack a b` with `{a - j, b - j} = {a, b}` as unordered pairs.

This is the assertion `§5` step 2 makes in one sentence ("`Primitive` rules out
a cyclic component, since a cycle would propagate `S x = S (x + (b-a))`
round the whole circle").  It was recorded here as an open `Prop` with no
inhabitant; that is no longer true.  The inhabitant is
`Issue94Step2Path.step2_components_are_paths_proved` (commit `ee61190`),
proved for every `K`, every genome and every `L`, with no bounded search.

The proof does not need the `P2` or `2 ≤ L ≤ K` hypotheses --- the statement
is about the circle alone --- but it does need `IsPrimitive`, in **both**
branches: the first (both ends fixed) forces `j ≡ 0 (mod K)` and `j < K`
comes from `pairBack_lt_G`; the second (ends swapped) forces
`2 * j ≡ 0 (mod K)`, hence `K = 2 * j`, and then the backward agreement at
`t = K / 2` makes the circular word literally `T ++ T` with `|T| = K / 2 < K`
as seen from any start, i.e. shift-invariance by `K / 2`, contradicting
`IsPrimitive`.  §5 records the reduction that led to that split. -/
def Step2_components_are_paths (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → Bin) (_hP2 : P2 hK L S)
    (_hprim : RepeatAdapter.IsPrimitive hK S) (a b : Fin K), a ≠ b → 2 ≤ L → L ≤ K →
    ∀ j : ℕ, j ≤ pairBack hK S a.val b.val →
      ¬ (j ≠ 0 ∧ ((a.val + K - j) % K = a.val ∧ (b.val + K - j) % K = b.val ∨
                  ((a.val + K - j) % K = b.val ∧ (b.val + K - j) % K = a.val)))

/-- **Step 3, restated (PROVED, by citation, but not discharged here).**  A
chord of one backward orbit never shares an endpoint with a chord of a
different orbit.  Immediate from `collision_forces_pair` and
`three_starts_ne`: two chords sharing an endpoint are the same unordered pair,
hence in the same orbit.

The reason no inhabitant is given here, though the step is in fact a corollary
of §1, is that the statement as phrased quantifies over *components*, and the
library defines no component relation for the chord graph.  Writing the
inhabitant means introducing that relation --- i.e. new library
infrastructure --- which this gap map deliberately does not do.  The honest
classification is: **the mathematical content is proved, the formal statement
is not yet written down.**

**CORRECTION (front for board 94, `antonina/issue-89-final`): the
"quantifies over components" justification above is false as written, and the
`Prop` is now DISCHARGED.**  The `Prop` ranges over quadruples `a b c d :
Fin K`, not over components of any relation, and its last disjunct is exactly
"all four endpoints are distinct".  No component relation is needed.  The
inhabitant is `Issue89GapMap.step3_slides_meet_no_foreign_chord` (commit
`c8f2bd6`), proved for every `L` with no bounded search, via the read-length-`L`
form `step3_shared_endpoint_forces_pair_readL` of the existing
`BBTCrossingCoalesce.collision_forces_pair` / `three_starts_ne` argument.  The
text above is left in place as the record of the false diagnosis. -/
def Step3_slides_meet_no_foreign_chord (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → Bin) (_hP2 : P2 hK L S)
    (_hprim : RepeatAdapter.IsPrimitive hK S) (a b c d : Fin K), 2 ≤ L → L ≤ K →
    a ≠ b → c ≠ d →
    vtx hK L S a = vtx hK L S b → vtx hK L S c = vtx hK L S d →
    ((a = c ∧ b = d) ∨ (a = d ∧ b = c) ∨
      (a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d))

/-- **Step 3 is a corollary of the §1--§3 theorems, at the level of pairs.**
Proved here, because it needs no notion of component: two chords of a
primitive `P2` word that share an endpoint are the same unordered pair.  This
is `BBTCrossingCoalesce.collision_forces_pair` (`:169`) in exactly the form
step 3 needs, and it is the whole content of step 3. -/
theorem step3_shared_endpoint_forces_pair {K : ℕ} (hK : 0 < K) (S : Fin K → Bin)
    (hL : 2 ≤ K) (hLG : K ≤ K) (hP2 : P2 hK K S) (hprim : RepeatAdapter.IsPrimitive hK S)
    {a b c d : Fin K} (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : vtx hK K S a = vtx hK K S b) (hvcd : vtx hK K S c = vtx hK K S d)
    (h : a = c ∨ a = d ∨ b = c ∨ b = d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases h with h | h | h | h
  · subst h
    exact Or.inl ⟨rfl, BBTCrossingCoalesce.collision_forces_pair
      hK S hL hLG hprim hP2 hab hcd hvab hvcd rfl⟩
  · subst h
    refine Or.inr ⟨rfl, ?_⟩
    have hne : a ≠ c := by
      intro hh
      exact hcd (hh ▸ rfl)
    exact BBTCrossingCoalesce.three_starts_ne hK S hL hLG hprim hP2
      hvab hvcd.symm hab hne
  · subst h
    refine Or.inr ⟨?_, rfl⟩
    have hne : b ≠ d := by
      intro hh
      exact hcd hh
    exact BBTCrossingCoalesce.three_starts_ne hK S hL hLG hprim hP2
      hvab.symm hvcd hab.symm hne
  · subst h
    refine Or.inl ⟨?_, rfl⟩
    have hne : b ≠ c := by
      intro hh
      exact hcd hh.symm
    exact BBTCrossingCoalesce.three_starts_ne hK S hL hLG hprim hP2
      hvab.symm hvcd.symm hab.symm hne

/-- **Step 3, restated, DISCHARGED.**  Two chords of the same `(L-1)`-mer
graph, each pair of distinct starts, either coincide as unordered pairs or
have all four endpoints distinct: they never share exactly one endpoint.

**The docstring previously attached to `Step3_slides_meet_no_foreign_chord`
justified the missing inhabitant by claiming that the statement "quantifies
over *components*, and the library defines no component relation for the
chord graph".  That justification was false as written:** the `Prop` ranges
over quadruples `a b c d : Fin K`, not over components, and the last
disjunct is exactly the four-endpoints-distinct alternative.  The correction
is appended here rather than made by editing that line away; the inhabitant
is this theorem.

The proof is the one the previous docstring already described, run at read
length `L` rather than at `K`: `BBTCrossingCoalesce.collision_forces_pair` and
`BBTCrossingCoalesce.three_starts_ne` are stated for an arbitrary read length
`L` with `2 ≤ L` and `L ≤ K`, which are exactly the hypotheses the `Prop`
supplies.  No `P2` transfer between read lengths is needed, and no component
relation is introduced. -/
theorem step3_shared_endpoint_forces_pair_readL {K L : ℕ} (hK : 0 < K) (S : Fin K → Bin)
    (h2L : 2 ≤ L) (hLK : L ≤ K) (hP2 : P2 hK L S) (hprim : RepeatAdapter.IsPrimitive hK S)
    {a b c d : Fin K} (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : vtx hK L S a = vtx hK L S b) (hvcd : vtx hK L S c = vtx hK L S d)
    (h : a = c ∨ a = d ∨ b = c ∨ b = d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases h with h | h | h | h
  · subst h
    exact Or.inl ⟨rfl, BBTCrossingCoalesce.collision_forces_pair
      hK S h2L hLK hprim hP2 hab hcd hvab hvcd rfl⟩
  · subst h
    refine Or.inr ⟨rfl, ?_⟩
    have hne : a ≠ c := fun hh => hcd (hh ▸ rfl)
    exact BBTCrossingCoalesce.three_starts_ne hK S h2L hLK hprim hP2
      hvab hvcd.symm hab hne
  · subst h
    refine Or.inr ⟨?_, rfl⟩
    have hne : b ≠ d := fun hh => hcd hh
    exact BBTCrossingCoalesce.three_starts_ne hK S h2L hLK hprim hP2
      hvab.symm hvcd hab.symm hne
  · subst h
    refine Or.inl ⟨?_, rfl⟩
    have hne : b ≠ c := fun hh => hcd hh.symm
    exact BBTCrossingCoalesce.three_starts_ne hK S h2L hLK hprim hP2
      hvab.symm hvcd.symm hab.symm hne

theorem step3_slides_meet_no_foreign_chord (L : ℕ) : Step3_slides_meet_no_foreign_chord L := by
  intro K hK S hP2 hprim a b c d h2L hLK hab hcd hvab hvcd
  by_cases hac : a = c
  · have := step3_shared_endpoint_forces_pair_readL hK S h2L hLK hP2 hprim
        hab hcd hvab hvcd (Or.inl hac)
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
  by_cases had : a = d
  · have := step3_shared_endpoint_forces_pair_readL hK S h2L hLK hP2 hprim
        hab hcd hvab hvcd (Or.inr (Or.inl had))
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
  by_cases hbc : b = c
  · have := step3_shared_endpoint_forces_pair_readL hK S h2L hLK hP2 hprim
        hab hcd hvab hvcd (Or.inr (Or.inr (Or.inl hbc)))
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
  by_cases hbd : b = d
  · have := step3_shared_endpoint_forces_pair_readL hK S h2L hLK hP2 hprim
        hab hcd hvab hvcd (Or.inr (Or.inr (Or.inr hbd)))
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
  exact Or.inr (Or.inr ⟨hac, had, hbc, hbd⟩)

/-- **Step 4, one step, the shape the reduction needs (cyclic content PROVED;
word-level `Prop` still without an inhabitant here).**  This is the `Slid`
shape of §1 with the word carried along.  Its cyclic content is
`Issue94IterSlide.slide_one` (commit `0806303`), proved for every `K` and
every quadruple with only the four stated guards; the two `vtx` hypotheses do
not occur in the conclusion, so the word layer adds nothing. -/
def Step4_slide_preserves (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → Bin) (a b c d : Fin K),
    a ≠ b → c ≠ d →
    vtx hK L S a = vtx hK L S b → vtx hK L S c = vtx hK L S d →
    Interleaved (mkGenome hK S) a b c d →
    rotAdd hK (K - 1) c ≠ a → rotAdd hK (K - 1) c ≠ b →
    rotAdd hK (K - 1) d ≠ a → rotAdd hK (K - 1) d ≠ b →
    Interleaved (mkGenome hK S) a b (rotAdd hK (K - 1) c) (rotAdd hK (K - 1) d)

/-- **Step 4, iterated --- this, not `SlidePreservesInterleaved`, is
what §5 step 4 invokes.  REFUTED as written; PROVED in the corrected,
conjunction-shaped form.**  "applied repeatedly along the backward list"
means: for every `t ≤ pairBack c d`, sliding `c, d` left by `t` keeps them
interleaved with `a, b`, provided no intermediate position collides.

This is a strictly stronger statement than `Step4_slide_preserves`: it needs
the guards at *every* intermediate `j ≤ t`, not just at `t`, and the guards
are genuinely needed (`Issue94IterSlide.not_EndpointIter_6`).

**It has no inhabitant, and the reason is not that it is open.**  Lean parses
the guard clause below as the implication chain `∀ j ≤ t, A → B → C → D`
rather than the conjunction `∀ j ≤ t, A ∧ B ∧ C ∧ D`.  A chain is vacuously
true at exactly those `j` where the slid `c` or `d` has landed on `a` or `b`,
so it fails to exclude the very collisions it is there to exclude, and it is
satisfied by the colliding configurations themselves.  The literal reading is
refuted in the kernel at `L = 1` by
`Issue94Step4Prop.not_Step4_slide_iterates_1` (commit `7cd813e`).

The `Prop` is kept unchanged, and deliberately: a `Prop` with a known
counterexample is more useful to the next front than a deleted one, since the
counterexample *is* the record of the mis-statement.  The corrected
conjunction-shaped statement is `Issue94Step4Prop.Step4_slide_iterates_guarded`
--- whose guard is `Issue94IterSlide.SlideGuards`, definitionally
`slide j c ≠ a ∧ ... ∧ slide j d ≠ b` with `slide hK n x = rotAdd hK (K - n) x`
--- and it is proved outright by `Issue94Step4Prop.step4_guarded`
(commit `7cd813e`), for every `L` and every `K`, with no primitivity and no
`P2` hypothesis. -/
def Step4_slide_iterates (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → Bin) (a b c d : Fin K),
    a ≠ b → c ≠ d →
    vtx hK L S a = vtx hK L S b → vtx hK L S c = vtx hK L S d →
    Interleaved (mkGenome hK S) a b c d →
    ∀ t : ℕ, t ≤ pairBack hK S c.val d.val →
      (∀ j : ℕ, j ≤ t →
        rotAdd hK (K - j) c ≠ a → rotAdd hK (K - j) c ≠ b →
        rotAdd hK (K - j) d ≠ a → rotAdd hK (K - j) d ≠ b) →
      Interleaved (mkGenome hK S) a b (rotAdd hK (K - t) c) (rotAdd hK (K - t) d)

/-! ## 4. The `vtx_maxPairStart` gap: what it gives and what it does not

The brief's "known hole" is: *the reduction needs the two heads to CROSS, and
`vtx_maxPairStart` only gives that they carry a common `(L-1)`-mer.*  That is
correct, and here is the precise picture.

`BBTCrossingCoalesce.vtx_maxPairStart` (`:190`) gives exactly
`vtx (maxPairStart a b) = vtx (maxPairStart b a)` --- the two extension starts
of a chord are again a chord.  It does **not** say the heads of two different
components cross, and no theorem in the library says it.  The reduction wants,
at step 5, the two heads to **interleave**; the crossing is supposed to come
from step 4 (slide each chord down to the head of its component, preserving
interleaving).

So the dependency is not a missing lemma *about* `vtx_maxPairStart`.  This
section originally said the dependency **is** step 4, and that was true when
it was written: step 4 was the open one.  It is now the opposite.
`Step2_components_are_paths` is proved (commit `ee61190`), so the slide down
the backward list is known to be well defined and terminating, and the
conjunction-shaped `Step4_slide_iterates` is proved outright (commit
`7cd813e`), so the slide is known to preserve interleaving along the way.
Both halves of what this section used to call step 4 are therefore discharged,
and the interleaving of the two heads was, until commit `a033fe4`, the *only*
remaining input to step 5 --- and that input is now **refuted**, not merely
open.  `vtx_maxPairStart` is a necessary and already proved ingredient of
step 5; it was never the wrong lemma, and there is still no separate "heads
cross" theorem to go and look for.

One caveat about the two prerequisites, since they are now load-bearing: step
2's inhabitant is a statement about the *orbit* of the pair under rotation,
and step 4's is a statement about the *circle*; both are needed for the heads
of `pairBack` to be well defined, and both are now in the library.

What was *not* established anywhere, and was checkable neither by reading nor
by the searches of §1, was the claim that the two heads interleave.  I stated it
explicitly as `Step5_heads_interleave` below, a `Prop` with no inhabitant.  **It
has since been refuted**, at commit `a033fe4`, by
`not_Step5_heads_interleave_3` in `AssemblyP1/Issue94Step5Heads.lean`: on the
repository's own `cexWord = AABAB` at `L = 3` the chords `{1, 3}` and `{2, 4}`
interleave while both of their head-pairs coincide at `{1, 3}`.  The "only
remaining input" claim of this section is therefore false: there is no
unconditional crossing to be had at step 5.  See the step-5 entry below for
the replacement, `Issue94Step5Heads.head_dichotomy` at `L = K`, which asks for
coinciding extensions instead. -/

/-- **Step 5, as formerly stated: REFUTED-AS-WRITTEN.**  This `Prop` demands
that the heads of the two backward components interleave.  That statement is
**false**, and the refutation is kernel-checked:

* commit `a033fe4`, module `AssemblyP1/Issue94Step5Heads.lean`, theorem
  `not_Step5_heads_interleave_3 : ¬ (Step5_heads_interleave 3)`.
* The counterexample is the repository's own `cexWord = AABAB` on five
  positions at `L = 3`: the chords `{1, 3}` and `{2, 4}` interleave, but their
  backward chains have lengths `0` and `1`, so both head-pairs coincide at
  `{1, 3}` and the four heads are `1, 3, 1, 3` rather than distinct.  Four
  heads that are not pairwise distinct cannot interleave.

The defect is the shape of the demand, not a missing lemma: interleaving was
asked for unconditionally, and the model makes the two chords' maximal
extensions **coincide** rather than cross.  Consequently this `Prop` must not
be cited as the remaining input to step 5, and `step5_contradiction` below ---
which is stated *given* `hheads` --- is a proof from a false hypothesis, not a
reduction of the last line.  It is retained unchanged so that no line of this
file changes shape; only its status has changed.

**The replacement an occupant of `BBTLadder.CrossingChordsCoalesce` needs** is
`Issue94Step5Heads.head_dichotomy` at `L = K` (commit `a033fe4`): under `P2`
and primitivity, two interleaving chords either have *coinciding* maximal
extensions --- `SameExtension`, the conclusion of
`BBTLadder.CrossingChordsCoalesce` --- or their four extension starts
interleave.  The dichotomy stops demanding a crossing, which is precisely what
made `Step5_heads_interleave` false, and its second disjunct is ruled out at
`L = K` by `Issue94Step5Heads.head_dichotomy_second_is_false`, which calls
`step5_contradiction` below.  So the dichotomy, once inhabited, gives the
target outright.

**`head_dichotomy` at `L = K` is NOT proved.**  It is a `Prop` with no
inhabitant in `Issue94Step5Heads.lean` at commit `a033fe4`; the refutation of
the old step 5 does not establish it, and no argument in either file does.
An occupant of `BBTLadder.CrossingChordsCoalesce` is therefore still blocked,
but it is blocked on a `Prop` nobody has refuted, which is the correct state
for an obligation. -/
def Step5_heads_interleave (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → Bin) (_hP2 : P2 hK L S)
    (_hprim : RepeatAdapter.IsPrimitive hK S) (a b c d : Fin K), 2 ≤ L → L ≤ K →
    a ≠ b → c ≠ d →
    vtx hK L S a = vtx hK L S b → vtx hK L S c = vtx hK L S d →
    Interleaved (mkGenome hK S) a b c d →
    Interleaved (mkGenome hK S)
      (maxPairStart hK S a b) (maxPairStart hK S b a)
      (maxPairStart hK S c d) (maxPairStart hK S d c)

/-- **The step-5 contradiction, *given* `Step5_heads_interleave` at one
instance.**  This shows precisely what step 5 needs and that nothing else is
missing there: the two heads are chords (`vtx_maxPairStart`, §4), they
interleave (the hypothesis `hheads`), and `P2.imp_ExtCrossing` then forbids
exactly that.

The hypothesis `hheads` is `Step5_heads_interleave` applied at one instance and
is **not** established anywhere.  This theorem is therefore *not* progress on
`CrossingPairsCoalesce`; it isolates the last line of the reduction. -/
theorem step5_contradiction {K : ℕ} (hK : 0 < K) (S : Fin K → Bin) (hL : 2 ≤ K)
    (hLG : K ≤ K) (hP2 : P2 hK K S) (hprim : RepeatAdapter.IsPrimitive hK S)
    {a b c d : Fin K} (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : vtx hK K S a = vtx hK K S b) (hvcd : vtx hK K S c = vtx hK K S d)
    (hI : Interleaved (mkGenome hK S) a b c d)
    (hheads : Interleaved (mkGenome hK S)
      (maxPairStart hK S a b) (maxPairStart hK S b a)
      (maxPairStart hK S c d) (maxPairStart hK S d c)) : False :=
  (P2.imp_ExtCrossing hK hL hLG S hprim hP2 a b c d hab hcd hvab hvcd hI).1 hheads

/-! ## 5. Why "components are paths" is not automatic from primitivity

(Historical.  This section explains the quantifier mismatch that made step 2
look open; the reduction it ends with was carried out, and both of its cases
are closed --- see the update at the end.  Nothing in the file depends on the
question still being open.)

`§5` step 2 says: "`Primitive` rules out a cyclic component, since a cycle
would propagate `S x = S (x + (b-a))` round the whole circle, a nontrivial
period."

Read literally this is a statement about the **word**: a cyclic component of
the chord graph would give `S x = S (x + (b - a))` for all `x`, hence a period
`b - a ≠ 0` of `S`, contradicting primitivity.  That argument is correct in
outline, and the primitivity machinery that would discharge it exists
(`RepeatAdapter.not_primitive_of_ge_G_agree`, used at
`P2RepeatResidual.lean`:651 in `not_agree_G`).

But it is **not** what step 4 needs, and the gap is a quantifier mismatch.  What
step 4 needs is that the slide down the backward list is *well defined and
terminating*, i.e. that the list `{{a - j, b - j} : j ≤ pairBack a b}` visits
no chord twice before the head.  That is `Step2_components_are_paths`, a
statement about the **orbit of the pair** `{a, b}` under rotation, not about
the word.  It is not the same statement, and at the time of writing no
existing theorem gave it.

**Update.**  The reduction at the end of this section was carried out, and
both of its cases are now closed; the closing "I do not know" was a real
unknown, and it was answered two commits later.  Here is the reduction, and
here is how each case closes.

`pairBack a b < G` (`P2RepeatResidual.pairBack_lt_G` `:654`) bounds the list
length by `G`, and the rotation orbit of `{a, b}` has period dividing `G`, so
the *only* case to exclude is `{a - j, b - j} = {a, b}` for some
`0 < j ≤ pairBack a b`.  That is either

1. `a - j ≡ a` and `b - j ≡ b (mod G)`, i.e. `j ≡ 0 (mod G)`.  Excluded
   by `j < G`, which is where primitivity is used: `pairBack_lt_G` is false
   for a non-primitive circle.  (Concretely,
   `Issue94Step2Path.sub_ne_self`.)

2. `a - j ≡ b` and `b - j ≡ a (mod G)`, i.e. `2 * j ≡ b - a (mod G)`.
   Substituting the first congruence into the second gives `2 * j ≡ 0 (mod
   G)`, and with `0 < j < G` that forces `G = 2 * j`.  So `a ≡ b + j (mod
   G)` with `j = G / 2`, i.e. `b` is the antipode of `a`, and the backward
   agreement holds at `t = G / 2`; that makes the circular word satisfy
   `cyc (a + u) = cyc (a + j + u)` for every `u < G`, i.e. it is literally
   `T ++ T` with `|T| = G / 2 < G` as seen from any start, which is
   shift-invariance by `G / 2` and contradicts `IsPrimitive`.  (Concretely,
   `Issue94Step2Path.swap_forces_half` and `shiftInvB_of_half`.)

So neither the `vtx`/`P2` hypotheses nor any search is needed: the statement
is a theorem about the circle, and primitivity is the only hypothesis it
uses, in both branches.  `Issue94Step2Path.step2_components_are_paths_proved`
(commit `ee61190`) carries this out, and this file records it as
`Step2_components_are_paths` being **proved**, not open.

A useful cross-check on that: the same statement with primitivity dropped is
**false** at `K = 3` and `K = 4` (`Issue94OrbitSearch.t_np_3`, `t_np_4`), so
primality is genuinely load-bearing and the proof is not an artefact of the
statement's shape.

The `Step4_slide_iterates` caveat below is likewise superseded, and in the
opposite direction from the one recorded here.  This section said only the
one-step `Slid` shape had been checked and that the *iterated* form was "a
genuinely different proposition" about which nothing was claimed --- which was
true of the searches of §1 but understates what is now known:

* the four-guard one-step shape `Slid` is **proved** for every `K`
  (`Issue94IterSlide.slide_one`, commit `0806303`), and
* the iterated shape **with the conjunction guard** --- `SlideGuards`, which is
  definitionally the four non-equalities taken as hypotheses, the shape §5
  actually means --- is **proved** for every `L` and every `K`, with no
  primitivity and no `P2` (`Issue94Step4Prop.step4_guarded`, commit
  `7cd813e`);
* while `Step4_slide_iterates` **as spelled in this file** is **refuted**,
  because its guard clause is the implication chain and not the conjunction
  (`Issue94Step4Prop.not_Step4_slide_iterates_1`, commit `7cd813e`).

The guards are not redundant even in the good shape: the iterated statement
with the guards only at the endpoint fails at `K = 6`, `8` and `10`
(`Issue94IterSlide.not_EndpointIter_6`, `not_EndpointIter_8_10`). -/

/-! ## 6. Classification summary

Each entry names the commit that makes it true, rather than a date, so that an
entry can be re-checked --- and superseded --- one at a time.  Commits
`ee61190` and `7cd813e` are ancestors of `be23300`, the base of the branch on
which this summary was last corrected.

- Step 1, fibres `≤ 2`: **proved**.  `P2.imp_nodeCount_le_two`
  `P2RepeatResidual.lean`:381; `three_starts_ne` `BBTCrossingCoalesce.lean`:133;
  `collision_forces_pair` `:169`.  Restated and inhabited here as
  `Step1_fibre_le_two` / `step1_proved`.
- Step 2, word-level (`C_j` stays a chord): **proved**.  `chord_shift_left`
  `P2RepeatResidual.lean`:497 (the corrected form); `pairBack_shift` `:540`;
  `maxPairStart_eq` `BBTLadder.lean`:151.  Restated here as
  `shift_left_persistence_corrected`.
- Step 2, combinatorial (components are paths): **proved**, at commit
  `ee61190`, by `Issue94Step2Path.step2_components_are_paths_proved`, for
  every `K`, genome and `L`, from `IsPrimitive` alone.  The `Prop`
  `Step2_components_are_paths` in this file is unchanged and is now inhabited.
  Primitivity is necessary: the same statement without it is false at `K = 3`
  and `K = 4` (`Issue94OrbitSearch.t_np_3`, `t_np_4`).
- Step 3 (slides meet no foreign chord): **proved and now discharged**, by
  `step3_slides_meet_no_foreign_chord` in this file (commit `1fc4e81`), from
  `step3_shared_endpoint_forces_pair_readL` and hence
  `collision_forces_pair`.  The `Prop` was not an unquantified statement: the
  earlier "quantifies over components" justification for its missing
  inhabitant was false and is corrected at the `Prop`.  The head-level
  restatement that step 5 needs is a **different** statement and remains open.
- Step 4, one step (a slide preserves interleaving): **proved** on the cyclic
  layer for every `K` at commit `0806303`
  (`Issue94IterSlide.slide_one`, four guards); the word-level
  `Step4_slide_preserves` in this file is not itself inhabited, but differs
  from `slide_one` only in hypotheses that do not occur in the conclusion.
- Step 4, iterated, as spelled in this file: **refuted**, at commit
  `7cd813e`, by `Issue94Step4Prop.not_Step4_slide_iterates_1` (`¬
  Step4_slide_iterates 1`).  Its guard clause is the implication chain
  `∀ j ≤ t, A → B → C → D`, not the conjunction `∀ j ≤ t, A ∧ B ∧ C ∧ D`,
  so it is vacuous exactly where a collision occurs.  The `Prop` is kept
  deliberately.
- Step 4, iterated, in the shape §5 means (conjunction guard
  `Issue94IterSlide.SlideGuards`): **proved**, at commit `7cd813e`, by
  `Issue94Step4Prop.step4_guarded`, for every `L` and `K`, with no primitivity
  and no `P2`.  This is the entry that discharges the §5 step-4 obligation.
- The `§5` statement of step 4 (`SlidePreservesInterleaved`): **false as
  stated**, `SlidePreservesInterleaved_refuted`.
- `ShiftLeftPersistence`: **false as stated**, `ShiftLeftPersistence_refuted`;
  the corrected form is already proved.
- Step 5 (heads interleave): **refuted-as-written**, at commit `a033fe4`, by
  `not_Step5_heads_interleave_3` in `AssemblyP1/Issue94Step5Heads.lean`
  (`¬ Step5_heads_interleave 3`), on `cexWord = AABAB` at `L = 3` where the
  chords `{1, 3}` and `{2, 4}` interleave and both head-pairs coincide at
  `{1, 3}`.  The `Prop` is kept deliberately, as a record of what was asked.
  Its prerequisites --- step 2's orbit statement and step 4's
  conjunction-guarded iteration --- are both proved, as listed above; the
  conjunction was not enough, because the demand itself was wrong.
- Step 5, the replacement obligation: **open, not proved and not refuted**.
  `Issue94Step5Heads.head_dichotomy` at `L = K`, commit `a033fe4`: the two
  interleaving chords either have `SameExtension` or their four heads
  interleave.  Its second disjunct is `False` at `L = K` by
  `head_dichotomy_second_is_false`, so this is the single input an occupant of
  `BBTLadder.CrossingChordsCoalesce` now needs.  The guard it requires is
  **head-level**: `heads_of_one_chord_ne` (commit `a033fe4`) makes intra-chord
  collisions impossible, so only `maxPairStart a b = maxPairStart c d` or
  `= maxPairStart d c` can break distinctness, and no theorem in the library
  excludes it.  `Step3_slides_meet_no_foreign_chord` is quantified over input
  starts only, so it does not exclude it either --- and is now proved
  (commit `1fc4e81`) without making step 5 any closer.
- Step 5 (heads interleave implies `False`): **proved**, by
  `step5_contradiction` in this file, from `P2.imp_ExtCrossing` --- but its
  hypothesis is now known false, so it is not a reduction of any live line.
- The `Slid` shape of §1 (four guards, one step): **proved** for every `K` at
  commit `0806303`; the `decide` results `AllSlid_6`, `AllSlid_8_10` are
  therefore history.  The eight-guard shape `Slid8` (`AllSlid8_6`,
  `AllSlid8_8_10`) is, as far as this file records, still bounded evidence
  only; this file makes no claim about it at any `K > 10`.

No statement here is progress on `CrossingChordsCoalesce` or
`BBTLadder.CrossingChordsCoalesce`.  Both remain `Prop`s with no inhabitant,
and so do `CrossingPairsCoalesce`, `LadderVertexCycle`,
`ShiftLeftPersistence` and `SlidePreservesInterleaved`.  What has changed
since this map was first written is not that any of those were settled, but
that steps 2, 3 and 4 --- the intermediate lemmas between the library and them ---
were, so the remaining gap is now a single sentence long: the heads of the two
backward orbits interleave. -/

end AssemblyP1.Issue89GapMap
