 same-length complete-spectrum
identifiability, but it is **not necessary**: the reverse implication
`complete-spectrum identifiability ⟹ P2` is refuted by a concrete
kernel-checked instance.

## Actual predicates used (no new P2/repeat semantics)

The point of this packet is to hit the repository's *existing*
predicates, so that the converse is stated against exactly the objects
the forward results consume:

* **P2 failure** is `RepeatAdapter.HasLongTripleRepeat hG truth L`, the
  repository's actual long-Bresler-triple-repeat predicate
  (`L - 1 ≤ ℓ`). `¬ HasLongTripleRepeat` is precisely the interface
  hypothesis of the forward same-length rigidity theorem
  `OrientedFinal.oriented_same_length_spectrum_rigidity` (#74) and the
  repeat-theory route of #71/#76, and it is the triple-repeat clause of
  the P2/Ukkonen boundary condition used by the population theorem
  (#73/#70). Nothing about interleaved pairs is introduced or assumed:
  per the note, the failure already occurs at the triple-repeat clause
  at `K = L - 1 = 1`, because the symbols at starts `0, 1, 2` are a
  maximal length-one triple repeat. This file therefore does **not**
  define a second, competing notion of P2 or of maximal repeat.

* **The observation** is the complete oriented `L`-mer spectrum
  `OrientedRigidity.specCount hG S : Fin L → α → ℕ` from the word layer
  (#69), i.e. exact integer multiplicities of oriented length-`L`
  circular windows. No reverse-complement collapse, no sampled reads.

* **The candidate universe** is the word-layer universe `Fin G → α` of
  oriented circular words of exactly the observed length, and **genome
  equivalence** is `PopulationReduction.RotEquiv hG` (#70), the
  rotation equivalence consumed by the population uniqueness theorem
  (#73). Not a proxy: the headline theorem is stated with `specCount`
  and `RotEquiv` themselves.

* **The multiplicity cap** `∀ k ∈ genomeNodes, nodeCount k ≤ 2` is the
  other explicit hypothesis of the forward adapter
  `OrientedRigidity.rigidity_same_spectrum` (#69). It is checked here to
  fail as well, so that the instance is genuinely *outside* the
  hypothesis region of the forward theorem and not merely cosmetically
  so.

## What is proved here

* `aaab_has_long_triple_repeat`: `HasLongTripleRepeat hG4 truth 2`, i.e.
  the actual P2 triple-repeat clause fails.
* `fibre_singleton_truth`: every same-length circular candidate with the
  truth's complete `2`-spectrum is a rotation of the truth
  (`RotEquiv4`, the `Fin`-indexed form, proved equivalent to `RotEquiv`).
* `fibre_card_truth`: that fibre has exactly `4` elements, i.e. exactly
  the `4` rotations of the primitive truth.
* `truth_primitive`: primitivity of `AAAB` in the word layer
  (`RepeatAdapter.IsPrimitive`), recorded because the note's converse is
  not a periodicity artefact.
* `truth_outside_forward_hypothesis_region`: the node multiplicity cap of
  #69 fails here too.
* `aaab_p2_fails_fibre_singleton`: the packaged final statement.

## Scope

This is about the **complete oriented same-length spectrum model** only.
It says nothing about finite sampled-read likelihood, uniform recovery,
variable-length candidates, or reverse-complement-collapsed molecule
classes. It refutes the *necessity* of P2 only; it does not refute the
forward theorems of #70/#73/#74, whose hypotheses are left untouched.
-/

namespace AssemblyP1.AAABConverse

open AssemblyP1.OrientedRigidity
open AssemblyP1.PopulationReduction

/-- The repository's two-letter alphabet (reused from #70, not
redeclared). -/
abbrev Base := Bin

/-- Same-length candidate universe: oriented circular words of length `4`. -/
abbrev Genome4 := Fin 4 → Base

/-- Oriented length-`2` read types. -/
abbrev Pair2 := Fin 2 → Base

/-- `G = 4 > 0`. -/
theorem hG4 : 0 < 4 := by norm_num

/-- The truth: the primitive circular genome `AAAB`. -/
def truth : Genome4 := ![Bin.A, Bin.A, Bin.A, Bin.B]

/-! ## Data-level mirrors of the repository's word layer

ome4) (i : ℕ) : cyc4 D i = cyc hG4 D i := rfl

theorem win2_eq_window (D : Genome4) (r : Fin 4) :
    win2 D r = window hG4 (L := 2) D r := rfl

theorem spec2_eq_specCount (D : Genome4) : spec2 D = specCount hG4 (L := 2) D := rfl

/-- The complete `2`-spectrum of the truth, in the repository's
`specCount` form: `AA` twice, `AB` once, `BA` once. -/
def pairAA : Pair2 := ![Bin.A, Bin.A]
def pairAB : Pair2 := ![Bin.A, Bin.B]
def pairBA : Pair2 := ![Bin.B, Bin.A]

theorem spec2_truth_AA : specCount hG4 (L := 2) truth pairAA = 2 := by decide
theorem spec2_truth_AB : specCount hG4 (L := 2) truth pairAB = 1 := by decide
theorem spec2_truth_BA : specCount hG4 (L := 2) truth pairBA = 1 := by decide

/-- The complete `2`-spectrum has total mass `G = 4`, i.e. it is a
*complete* spectrum of a length-`4` word. -/
theorem spec2_truth_total : (∑ w : Pair2, specCount hG4 (L := 2) truth w) = 4 := by
  decide

/-! ## P2 failure: the actual long-triple-repeat predicate -/

/-- **P2 fails at `L = 2`.** `AAAB` carries a maximal length-one
Bresler triple repeat at starts `0, 1, 2`: the three symbols agree, the
three preceding symbols (`B, A, A`) are not all equal, and the three
following symbols (`A, A, B`) are not all equal. Since
`L - 1 = 1 ≤ ℓ = 1`, this is a *long* triple repeat, so the repository's
P2/Ukkonen triple-repeat clause is violated. This is exactly the
hypothesis `¬ HasLongTripleRepeat` that the forward rigidity theorem
(#74) and the population P2 route require. -/
theorem aaab_has_long_triple_repeat :
    RepeatAdapter.HasLongTripleRepeat hG4 truth 2 := by
  refine ⟨0, 1, 2, 1, by decide, by decide, by decide, by decide, by decide, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    have hd0 : d = 0 := by omega
    subst hd0
    decide
  · decide
  · decide

/-! ## Rotation equivalence: the repository's `RotEquiv` -/

/-- The `Fin`-indexed form of rotation equivalence: `D` is the truth
rotated forward by `k < G` positions. Equivalent to `RotEquiv` below
(only the residue of the shift differs). -/
def RotEquiv4 (D S : Genome4) : Prop :=
  ∃ k : Fin 4, ∀ i : Fin 4, D ⟨(i.val + k.val) % 4, Nat.mod_lt _ (by norm_num)⟩ = S i

theorem rotEquiv4_iff (D S : Genome4) : RotEquiv4 D S ↔ RotEquiv hG4 D S := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k.val, fun i => hk i⟩
  · rintro ⟨k, hk⟩
    refine ⟨⟨k % 4, Nat.mod_lt _ (by norm_num)⟩, fun i => ?_⟩
    have h1 := hk i
    have h2 : (i.val + k) % 4 = (i.val + k % 4) % 4 := by omega
    have h3 : (⟨(i.val + k) % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) =
        ⟨(i.val + k % 4) % 4, Nat.mod_lt _ (by norm_num)⟩ := Fin.ext h2
    exact (congrArg (fun x : Fin 4 => D x) h3).symm.trans h1

/-! ## The same-length complete-spectrum fibre is a singleton orbit -/

/-- The same-length complete-`L`-spectrum fibre is a singleton modulo
rotation: every oriented circular word of length `4` whose complete
`2`-spectrum equals the truth's is a rotation of the truth. -/
def FibreSingleton (S : Genome4) : Prop :=
  ∀ D : Genome4, spec2 D = spec2 S → RotEquiv4 D S

/-- **Fibre singleton for `AAAB`.** Decided over the whole candidate
universe (`2 ^ 4 = 16` words), so this is exhaustive, not a sample. -/
theorem fibre_singleton_truth : FibreSingleton truth := by
  unfold FibreSingleton RotEquiv4 spec2 win2 cyc4 truth
  decide

/-- The same statement at the actual repository predicates: the
complete `L`-spectrum fibre at the same length is a singleton modulo
`RotEquiv`. -/
theorem fibre_singleton_truth_rot :
    ∀ D : Genome4, specCount hG4 (L := 2) D = specCount hG4 (L := 2) truth →
      RotEquiv hG4 D truth := by
  intro D hD
  exact (rotEquiv4_iff D truth).mp (fibre_singleton_truth D hD)

/-- The fibre consists of exactly the `4` rotations of the primitive
truth. -/
def fibre (S : Genome4) : Finset Genome4 := Finset.univ.filter (fun D => spec2 D = spec2 S)

theorem fibre_card_truth : (fibre truth).card = 4 := by
  unfold fibre spec2 win2 cyc4 truth
r ⟨Finset.mem_univ _, by decide⟩

/-- Rotation invariance of the complete spectrum (finite, exhaustive
over the four rotations of an arbitrary length-`4` word). -/
theorem spec2_rot : ∀ k : Fin 4, ∀ D : Genome4,
    spec2 (fun i => D ⟨(i.val + k.val) % 4, Nat.mod_lt _ (by norm_num)⟩) = spec2 D := by
  decide

theorem fibre_contains_rotations (k : Fin 4) :
    (fun i => truth ⟨(i.val + k.val) % 4, Nat.mod_lt _ (by norm_num)⟩) ∈ fibre truth :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, spec2_rot k truth⟩

/-! ## Primitivity, and the forward hypothesis region -/

/-- `AAAB` is primitive in the word layer: no nonzero shift below `G`
preserves it. (The note's converse is not a periodicity artefact.) -/
theorem truth_primitive : RepeatAdapter.IsPrimitive hG4 truth := by
  intro s hs hsb
  obtain hcases : s = 1 ∨ s = 2 ∨ s = 3 := by omega
  refine fun hcon => ?_
  have h3 := hcon 3
  rcases hcases with rfl | rfl | rfl
  · -- shift `1`: position `3` carries `B`, position `0` carries `A`
    norm_num [RepeatAdapter.ShiftInvariant, cyc, truth] at h3
  · -- shift `2`: position `3` carries `B`, position `1` carries `A`
    norm_num [RepeatAdapter.ShiftInvariant, cyc, truth] at h3
  · -- shift `3`: position `3` carries `B`, position `2` carries `A`
    norm_num [RepeatAdapter.ShiftInvariant, cyc, truth] at h3

/-- The de Bruijn node of the symbol `A` (here length `L - 1 = 1`). -/
def nodeA : Fin (2 - 1) → Base := fun _ => Bin.A

/-- The symbol `A` occurs at `3` of the `4` starts, so the forward
adapter's multiplicity cap `nodeCount k ≤ 2` (#69) fails at this node:
the instance is genuinely outside the hypothesis region of the forward
rigidity theorem, not merely outside its repeat-syntax hypothesis. -/
theorem node_count_A : nodeCount hG4 (L := 2) truth nodeA = 3 := by decide

theorem truth_outside_forward_hypothesis_region :
    ¬ (∀ k : Fin (2 - 1) → Base, k ∈ genomeNodes hG4 (L := 2) truth →
        nodeCount hG4 (L := 2) truth k ≤ 2) := by decide

/-! ## The final converse instance -/

/-- **Final `AAAB`, `G = 4`, `L = 2` converse (issue #92).**

The actual P2 predicate fails on the truth, while the same-length
complete length-`2` spectrum fibre is a singleton modulo the
repository's rotation equivalence over the same-length circular-word
candidate universe. The truth is primitive, and it also violates the
forward adapter's `(L-1)`-window multiplicity cap, so the forward
theorems of #69/#74 are not applicable here while their *conclusion*
still holds. -/
theorem aaab_p2_fails_fibre_singleton :
    (RepeatAdapter.HasLongTripleRepeat hG4 truth 2 ∧
      (∀ D : Genome4, specCount hG4 (L := 2) D = specCount hG4 (L := 2) truth →
        RotEquiv hG4 D truth)) ∧
    ((fibre truth).card = 4 ∧
      (RepeatAdapter.IsPrimitive hG4 truth ∧
        ¬ (∀ k : Fin (2 - 1) → Base, k ∈ genomeNodes hG4 (L := 2) truth →
          nodeCount hG4 (L := 2) truth k ≤ 2))) := by
  refine ⟨⟨aaab_has_long_triple_repeat, fibre_singleton_truth_rot⟩, ?_⟩
  exact ⟨fibre_card_truth, ⟨truth_primitive,
    truth_outside_forward_hypothesis_region⟩⟩

/-- The converse, isolated: **complete-spectrum identifiability does not
imply P2.** In the same-length oriented complete-spectrum model there is
a primitive genome whose complete `2`-spectrum identifies it uniquely up
to rotation, and which nevertheless fails the P2 / long-triple-repeat
condition (that is, the hypothesis `¬ HasLongTripleRepeat` of #71/#74 is
violated). This does not refute the forward implications of
#70/#73/#74. -/
theorem complete_spectrum_identifiability_does_not_imply_P2 :
    ∃ S : Genome4,
      (RepeatAdapter.IsPrimitive hG4 S ∧
        RepeatAdapter.HasLongTripleRepeat hG4 S 2 ∧
        (∀ D : Genome4, specCount hG4 (L := 2) D = specCount hG4 (L := 2) S →
          RotEquiv hG4 D S)) :=
  ⟨truth, truth_primitive, aaab_has_long_triple_repeat,
    fibre_singleton_truth_rot⟩

end AssemblyP1.AAABConverse
