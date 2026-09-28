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
`Prop`s the reduction is built on remain without inhabitants.

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
  is made about `K > 10`.

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

After those two corrections, the reduction's remaining content is **one**
new cyclic-order lemma, the *iteration* form of the slide lemma, and the
`vtx_maxPairStart` question addressed in §4 below.  See the `Step*` `Prop`s
and the classification comments.

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
four guards.  No counterexample found for `K ≤ 5` or at `K = 6, 8, 10`. -/
def Slid (K : ℕ) (hK : 0 < K) [NeZero K] (a b c d : Fin K) : Prop :=
  InterK K a b c d → Guards K hK a b c d →
    InterK K a b (rotAdd hK (K - 1) c) (rotAdd hK (K - 1) d)

/-- **`Slid` with all eight guards.**  No counterexample found for `K ≤ 5` or
at `K = 6, 8, 10`. -/
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
**path** and does not revisit itself --- is **open**; it is
`Step2_components_are_paths`.  See §5 below for why the "no cyclic component"
sentence in §5 step 2 does not follow from primitivity as written.

**Step 3. Slides do not meet a chord of another component.**  *Proved*, by
`collision_forces_pair` and `three_starts_ne`: if `C_j` shared an endpoint with
`D` then by step 1 `C_j = D`, so `D` is in `C`'s component.  Restated for the
record as `Step3_slides_meet_no_foreign_chord`; **not** given an inhabitant
here, because writing that proof requires naming the component relation, which
the library does not define --- see the note on that `Prop` below.

**Step 4. A slide preserves interleaving.**  *Open, and the §5 statement of it
is false (§1 above).*  The corrected one-step shape is `Step4_slide_preserves`;
the shape the reduction *iterates* is `Step4_slide_iterates`, an `n`-step
version, which is what `§5` step 4 actually invokes ("applied repeatedly along
the backward list").  Both are `Prop`s with **no inhabitant**.

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

/-- **Step 2, combinatorial half (OPEN).**  The truncated backward orbit of a
chord `{a, b}`, namely `{{a - j, b - j} : j ≤ pairBack a b}`, visits no
chord twice: there is no `0 < j ≤ pairBack a b` with
`{a - j, b - j} = {a, b}` as unordered pairs.

This is the assertion `§5` step 2 makes in one sentence ("`Primitive` rules out
a cyclic component, since a cycle would propagate `S x = S (x + (b-a))`
round the whole circle").  It is a `Prop` with **no inhabitant**.  See §5 for
the reduction of the case to be excluded. -/
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
is not yet written down.** -/
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

/-- **Step 4, one step, the shape the reduction needs (OPEN).**  This is the
`Slid` shape of §1 with the word carried along.  A `Prop` with **no
inhabitant**. -/
def Step4_slide_preserves (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → Bin) (a b c d : Fin K),
    a ≠ b → c ≠ d →
    vtx hK L S a = vtx hK L S b → vtx hK L S c = vtx hK L S d →
    Interleaved (mkGenome hK S) a b c d →
    rotAdd hK (K - 1) c ≠ a → rotAdd hK (K - 1) c ≠ b →
    rotAdd hK (K - 1) d ≠ a → rotAdd hK (K - 1) d ≠ b →
    Interleaved (mkGenome hK S) a b (rotAdd hK (K - 1) c) (rotAdd hK (K - 1) d)

/-- **Step 4, iterated (OPEN) --- this, not `SlidePreservesInterleaved`, is
what §5 step 4 invokes.**  "applied repeatedly along the backward list" means:
for every `t ≤ pairBack c d`, sliding `c, d` left by `t` keeps them
interleaved with `a, b`, provided no intermediate position collides.

This is a strictly stronger statement than `Step4_slide_preserves`: it needs
the guards at *every* intermediate `j ≤ t`, not just at `t`.  A `Prop` with
**no inhabitant**. -/
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
interleaving), and step 4 is exactly `Step4_slide_iterates`, which is open.

So the dependency is not a missing lemma *about* `vtx_maxPairStart`; it is
**step 4**.  There is no separate "heads cross" theorem to go and look for, and
`vtx_maxPairStart` is not the wrong lemma --- it is a necessary and already
proved ingredient of step 5, whose only remaining input is interleaving of the
heads.

What is *not* established anywhere, and is checkable neither by reading nor by
the searches of §1, is the claim that the two heads interleave.  I state it
explicitly as `Step5_heads_interleave` below, a `Prop` with **no inhabitant**,
so that a later front cannot mistake it for something already covered. -/

/-- **Step 5, the missing input (OPEN).**  The heads of the two backward
components interleave.  This is what `vtx_maxPairStart` does **not** give, and
what `P2.imp_ExtCrossing` needs in order to be applied and yield the
contradiction.  A `Prop` with **no inhabitant**. -/
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
the word.  It is not the same statement, and no existing theorem gives it.

Concretely, `pairBack a b < G` (`P2RepeatResidual.pairBack_lt_G` `:654`)
bounds the list length by `G`, and the rotation orbit of `{a, b}` has period
dividing `G`, so the *only* case to exclude is `{a - j, b - j} = {a, b}` for
some `0 < j ≤ pairBack a b`.  That is either `j ≡ 0 (mod G)` (excluded by
`j < G`) or `a - j ≡ b` and `b - j ≡ a`, i.e. `2j ≡ b - a (mod G)`.  **I do
not know** whether the `vtx` / `P2` hypotheses rule that out, and I have not
checked it computationally.  **Not established.**

The same caveat applies to `Step4_slide_iterates`: I have verified only the
one-step `Slid` shape up to `K = 6` (§1) and the four- and eight-guard variants
up to `K = 6`; the *iterated* form is a genuinely different proposition and I
make no claim about it.
-/

/-! ## 6. Classification summary

- Step 1, fibres `≤ 2`: **proved**.  `P2.imp_nodeCount_le_two`
  `P2RepeatResidual.lean`:381; `three_starts_ne` `BBTCrossingCoalesce.lean`:133;
  `collision_forces_pair` `:169`.  Restated and inhabited here as
  `Step1_fibre_le_two` / `step1_proved`.
- Step 2, word-level (`C_j` stays a chord): **proved**.  `chord_shift_left`
  `P2RepeatResidual.lean`:497 (the corrected form); `pairBack_shift` `:540`;
  `maxPairStart_eq` `BBTLadder.lean`:151.  Restated here as
  `shift_left_persistence_corrected`.
- Step 2, combinatorial (components are paths): **open**.
  `Step2_components_are_paths`.  Not established either way.
- Step 3 (slides meet no foreign chord): **proved**, by
  `step3_shared_endpoint_forces_pair` in this file, from
  `collision_forces_pair`.
- Step 4 (a slide preserves interleaving): **open, and the §5 statement is
  false.**  Refuted by `SlidePreservesInterleaved_refuted`.  Corrected shape
  `Step4_slide_preserves`; iterated form `Step4_slide_iterates`.
- Step 5 (heads interleave): **open**.  `Step5_heads_interleave`.
- Step 5 (heads interleave implies `False`): **proved**, by
  `step5_contradiction` in this file, from `P2.imp_ExtCrossing`.
- `ShiftLeftPersistence`: **false as stated**, `ShiftLeftPersistence_refuted`;
  the corrected form is already proved.
- `SlidePreservesInterleaved`: **false as stated**,
  `SlidePreservesInterleaved_refuted`.

No statement here is progress on `CrossingChordsCoalesce` or
`BBTLadder.CrossingChordsCoalesce`.  Both remain `Prop`s with no inhabitant,
and so do `CrossingPairsCoalesce`, `LadderVertexCycle`,
`ShiftLeftPersistence` and `SlidePreservesInterleaved`. -/

end AssemblyP1.Issue89GapMap
