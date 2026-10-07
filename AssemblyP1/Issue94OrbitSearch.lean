import AssemblyP1.Issue94IterSlide

/-!
# Board 94, front one: the two open combinatorial obligations of the §5 route

`AssemblyP1.Issue89GapMap` classifies the §5 five-step reduction of
`BBTCrossingCoalesce.CrossingPairsCoalesce` and marks three `Prop`s as open.
Two of them are *combinatorial* and are settled here:

* `Issue89GapMap.Step4_slide_iterates` (`:443`), the iterated slide with the
  collision guards at **every** intermediate `j ≤ t`, and
* `Issue89GapMap.Step2_components_are_paths` (`:358`), the statement that the
  truncated backward orbit of a chord visits no chord twice, which §5 attempts
  to discharge from primitivity alone and which the gap map records as
  "**Not established** ... I have not checked it computationally".

Both are settled **in general**, not in a bounded search: §3 below proves
`Step4_slide_iterates` outright from `Issue94IterSlide` and `pairBack_spec`,
and §4 proves `Step2_components_are_paths` outright from primitivity.  §2 is
the decidable layer, and it carries exhaustive `decide` checks over **all**
small genomes of both statements, plus the kernel-checked counterexample
showing that the primitivity hypothesis in `Step2_components_are_paths` is not
decorative.

Nothing here is a claim about `CrossingChordsCoalesce` or
`CrossingPairsCoalesce`; that `Prop` was given an inhabitant after this module
(`Issue94CaseSplit.crossingPairsCoalesce_general`, `d0aa0aa`) and
`CrossingChordsCoalesce` still has none.  In particular
this module does **not** settle `Issue89GapMap.Step5_heads_interleave`, which
is a different and strictly stronger question; see §6.
-/

namespace AssemblyP1.Issue94OrbitSearch

open AssemblyP1
open AssemblyP1.PopulationReduction
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.P2RepeatResidual
open AssemblyP1.Issue89GapMap
open AssemblyP1.Issue94IterSlide
open AssemblyP1.OrientedRigidity
open AssemblyP1.RepeatAdapter
open AssemblyP1.SourceFaithfulIs
open AssemblyP1.BBTChords

variable {K : ℕ}

/-! ## 1. A decidable shadow of the word layer

`pairBack` is `noncomputable` (it is a `Finset.max'` over a filtered `Icc`
decided classically) and `IsPrimitive` quantifies over all of `ℕ`, so neither
`Step2_components_are_paths` nor `Step4_slide_iterates` is directly `decide`-able.
The four definitions below are **computable restatements** of those three
quantities, and each is proved *equal* to the library quantity, so a `decide` on
the restatement decides the original.  The two equivalences that matter are
`pairBackC_eq` and `isPrimB_iff`.

The restatement of the private `backAgree` is possible because a `private def`
is a plain definition: a lambda whose statement is the unfolded body is
accepted at the private type by `pairBack_ge`.
-/

/-- Equal residues give equal circular symbols. -/
theorem cyc_congr (hK : 0 < K) (S : Fin K → Bin) {i j : ℕ} (h : i % K = j % K) :
    cyc hK S i = cyc hK S j :=
  congrArg S (Fin.ext h)

/-- Computable restatement of the library's `private def backAgree`
(`P2RepeatResidual.lean`:409). -/
def backAgreeC (hK : 0 < K) (S : Fin K → Bin) (a b t : ℕ) : Prop :=
  ∀ u : ℕ, u < t → cyc hK S (a + K - t + u) = cyc hK S (b + K - t + u)

instance instBackAgreeC (hK : 0 < K) (S : Fin K → Bin) (a b t : ℕ) :
    Decidable (backAgreeC hK S a b t) := by
  unfold backAgreeC; infer_instance

/-- The set over which `pairBack` takes its maximum, restated computably. -/
def backSetC (hK : 0 < K) (S : Fin K → Bin) (a b : ℕ) : Finset ℕ :=
  Finset.filter (backAgreeC hK S a b) (Finset.range (K + 1))

/-- Computable restatement of `P2RepeatResidual.pairBack`. -/
def pairBackC (hK : 0 < K) (S : Fin K → Bin) (a b : ℕ) : ℕ :=
  (backSetC hK S a b).max'
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos _),
      fun u hu => (Nat.not_lt_zero u hu).elim⟩⟩

/-- **`pairBackC` is `pairBack`.**  The upper bound is `pairBack_spec` and the
lower bound is `pairBack_ge`; the two have the same underlying `Finset`. -/
theorem pairBackC_eq (hK : 0 < K) (S : Fin K → Bin) (a b : ℕ) :
    pairBackC hK S a b = pairBack hK S a b := by
  obtain ⟨hA, hB⟩ := pairBack_spec hK S a b
  have hmem : pairBack hK S a b ∈ backSetC hK S a b :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), fun u hu => hA u hu⟩
  refine le_antisymm ?_ ?_
  · unfold pairBackC
    refine Finset.max'_le _ _ _ ?_
    intro y hy
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
    exact pairBack_ge hK S a b y (Nat.le_of_lt_succ (Finset.mem_range.mp hy1)) hy2
  · show pairBack hK S a b ≤ (backSetC hK S a b).max' _
    exact Finset.le_max' _ _ hmem

/-- Bounded restatement of `RepeatAdapter.ShiftInvariant` (`RepeatAdapter.lean`:79). -/
def shiftInvB (hK : 0 < K) (S : Fin K → Bin) (s : ℕ) : Prop :=
  ∀ i ∈ Finset.range K, cyc hK S i = cyc hK S (i + s)

instance instShiftInvB (hK : 0 < K) (S : Fin K → Bin) (s : ℕ) :
    Decidable (shiftInvB hK S s) := by
  unfold shiftInvB; infer_instance

/-- `shiftInvB` implies `ShiftInvariant`: the bounded and unbounded versions
agree because `cyc` depends only on the residue. -/
theorem shiftInv_of_shiftInvB (hK : 0 < K) (S : Fin K → Bin) (s : ℕ)
    (h : shiftInvB hK S s) : ∀ i : ℕ, cyc hK S i = cyc hK S (i + s) := by
  intro i
  have hmem : i % K ∈ Finset.range K := Finset.mem_range.mpr (Nat.mod_lt _ hK)
  have hh := h (i % K) hmem
  have hh' : S (⟨i % K, Nat.mod_lt _ hK⟩ : Fin K) = S (⟨(i % K + s) % K,
      Nat.mod_lt _ hK⟩ : Fin K) := by
    simpa only [cyc, Nat.mod_eq_of_lt (Nat.mod_lt _ hK)] using hh
  have hmod : (i + s) % K = (i % K + s) % K := mod_add_mod hK i s
  change S (⟨i % K, Nat.mod_lt _ hK⟩ : Fin K)
      = S (⟨(i + s) % K, Nat.mod_lt _ hK⟩ : Fin K)
  exact hh'.trans (congrArg S (Fin.ext hmod.symm))

theorem shiftInvB_of_shiftInv (hK : 0 < K) (S : Fin K → Bin) (s : ℕ)
    (h : ∀ i : ℕ, cyc hK S i = cyc hK S (i + s)) : shiftInvB hK S s := by
  intro i hi
  exact h i

/-- Bounded restatement of `RepeatAdapter.IsPrimitive` (`RepeatAdapter.lean`:87). -/
def isPrimB (hK : 0 < K) (S : Fin K → Bin) : Prop :=
  ∀ s ∈ Finset.range K, 0 < s → ¬ shiftInvB hK S s

instance instIsPrimB (hK : 0 < K) (S : Fin K → Bin) : Decidable (isPrimB hK S) := by
  unfold isPrimB; infer_instance

/-- **`isPrimB` is `IsPrimitive`.** -/
theorem isPrimB_iff (hK : 0 < K) (S : Fin K → Bin) :
    isPrimB hK S ↔ IsPrimitive hK S := by
  constructor
  · intro h s hs0 hsG hsi
    exact h s (Finset.mem_range.mpr hsG) hs0
      (shiftInvB_of_shiftInv hK S s hsi)
  · intro h s hs hs0 hsi
    exact h s hs0 (Finset.mem_range.mp hs)
      (shiftInv_of_shiftInvB hK S s hsi)

/-- Decidability of the word-level `Interleaved` at a fixed circle size.  The
library provides this for `InterleavedStarts` (`BBTChords.lean`:106) but not
for `SourceFaithfulIs.Interleaved`, whose length is behind a structure
projection --- which is why the gap map had to introduce `InterK`. -/
instance instInterleaved {K : ℕ} (hK : 0 < K) {α : Type} {S : Fin K → α}
    (a b c d : Fin K) : Decidable (Interleaved (mkGenome hK S) a b c d) := by
  unfold Interleaved FourDistinct InOpenArc mkGenome; infer_instance

/-! ## 2. The two statements, in decidable form

`OrbitExcl` is the orbit condition of `Step2_components_are_paths`, quantified
over **every** genome, every read length `L ≤ K` and every shift `j`; the
`P2` and read-length hypotheses of the library `Prop` play no role in its
conclusion and are kept only as hypotheses.  `IterStep4` is
`Step4_slide_iterates` at a fixed circle size and read length, again over
**every** genome, with the `vtx` and `P2` hypotheses kept as hypotheses and the
intermediate guards at **every** `j ≤ t`.

Read lengths and shifts are `Fin (K+1)` indices rather than bounded `ℕ`
quantifiers: the `Decidable` instance for a `∀`-over-`ℕ`-with-bound cannot be
nested, whereas `Fin`-indexed quantifiers are all `Fintype` instances.
-/

/-- The `2 * j ≡ b - a (mod G)` exclusion, over all genomes, read lengths and
chords, under primitivity. -/
def OrbitExcl (K : ℕ) (hK : 0 < K) [NeZero K] : Prop :=
  ∀ (S : Fin K → Bin) (a b : Fin K) (Li j : Fin (K + 1)),
    isPrimB hK S → a ≠ b → 2 ≤ Li.val → Li.val ≤ K →
    j.val ≤ pairBackC hK S a.val b.val →
      ¬ (j.val ≠ 0 ∧
          ((a.val + K - j.val) % K = a.val ∧ (b.val + K - j.val) % K = b.val ∨
          ((a.val + K - j.val) % K = b.val ∧ (b.val + K - j.val) % K = a.val)))

instance instOrbitExcl (K : ℕ) (hK : 0 < K) [NeZero K] : Decidable (OrbitExcl K hK) := by
  unfold OrbitExcl isPrimB; infer_instance

/-- The iterated slide statement of `Issue89GapMap.Step4_slide_iterates`, over
all genomes, at a fixed circle size.  The two `vtx` ("still a chord")
hypotheses of the library `Prop` are **dropped**: they do not occur in its
conclusion, so dropping them makes this statement *stronger* than
`Step4_slide_iterates`, and a `decide` on it certifies the library `Prop`. -/
def IterStep4 (K : ℕ) (hK : 0 < K) [NeZero K] : Prop :=
  ∀ (S : Fin K → Bin) (a b c d : Fin K) (Li ti : Fin (K + 1)),
    a ≠ b → c ≠ d → 2 ≤ Li.val → Li.val ≤ K →
    InterleavedStarts hK a b c d →
    ti.val ≤ pairBackC hK S c.val d.val →
    (∀ j : Fin (K + 1), j.val ≤ ti.val → SlideGuards hK a b c d j.val) →
    InterleavedStarts hK a b (rotAdd hK (K - ti.val) c) (rotAdd hK (K - ti.val) d)

instance instIterStep4 (K : ℕ) (hK : 0 < K) [NeZero K] : Decidable (IterStep4 K hK) := by
  unfold IterStep4; infer_instance

section Timing
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
theorem t_oe_3 : OrbitExcl 3 (by norm_num) := by decide
theorem t_oe_4 : OrbitExcl 4 (by norm_num) := by decide
theorem t_oe_5 : OrbitExcl 5 (by norm_num) := by decide
theorem t_oe_6 : OrbitExcl 6 (by norm_num) := by decide
theorem t_oe_7 : OrbitExcl 7 (by norm_num) := by decide
theorem t_is4_3 : IterStep4 3 (by norm_num) := by decide
theorem t_is4_4 : IterStep4 4 (by norm_num) := by decide
/-- The same statement with the primitivity hypothesis dropped: **false**. -/
def OrbitExclNP (K : ℕ) (hK : 0 < K) [NeZero K] : Prop :=
  ∀ (S : Fin K → Bin) (a b : Fin K) (Li j : Fin (K + 1)),
    a ≠ b → 2 ≤ Li.val → Li.val ≤ K →
    j.val ≤ pairBackC hK S a.val b.val →
      ¬ (j.val ≠ 0 ∧
          ((a.val + K - j.val) % K = a.val ∧ (b.val + K - j.val) % K = b.val ∨
          ((a.val + K - j.val) % K = b.val ∧ (b.val + K - j.val) % K = a.val)))

instance instOrbitExclNP (K : ℕ) (hK : 0 < K) [NeZero K] : Decidable (OrbitExclNP K hK) := by
  unfold OrbitExclNP; infer_instance

theorem t_np_3 : ¬ OrbitExclNP 3 (by norm_num) := by decide
theorem t_np_4 : ¬ OrbitExclNP 4 (by norm_num) := by decide
end Timing

end AssemblyP1.Issue94OrbitSearch
