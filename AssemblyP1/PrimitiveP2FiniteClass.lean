import AssemblyP1.P2RepeatResidual
import AssemblyP1.FiniteReadRecoveryP2Complete

/-!
# Finiteness of the primitive-P2 admissible class, and the unconditional
  finite-read ML recovery theorem (issue #281)

`AssemblyP1.FiniteReadRecoveryP2Complete.finite_primitiveP2_ML_confidence`
proved the exact iid maximum-likelihood error decay against a *hypothesised*
finite family `C` of primitive-P2 admissible non-rotational competitors.
The family had to be supplied by the caller, so the theorem never said that
such a family *exists*: the whole admissible class ranges over all positive
genome lengths, and nothing bounded the lengths. This module closes exactly
that gap and removes the finite-family premise.

## The bound

For a finite alphabet `α` of cardinal `q`, read length `L ≥ 2` and
`K = L - 1`, every primitive circular word satisfying the triple-repeat
clause of P2 has

    G ≤ 2 * q ^ K,

and the bound is tight: at `q = 2`, `K = 1` the circular word `1100` is
primitive, satisfies P2 at `L = 2`, and attains `G = 4 = 2 * 2 ^ 1`.

The crux is that **P2 alone does not bound the multiplicity of a `K`-window**:
it forbids *maximal* triple repeats, not arbitrary triples of equal windows.
Three occurrences of one `K`-window become a contradiction only after the
window is extended maximally on both sides. That extension is the shared
engine of `RepeatAdapter`, and its primitive branch
`RepeatAdapter.primitive_nodeCount_le_two` already yields

    `P2RepeatResidual.P2.imp_nodeCount_le_two` :
      primitive + `P2 hG L S` + `L ≤ G` ⟹ every `(L - 1)`-window occurs at
      most twice.

So no maximal-extension argument is repeated here. What this module adds is
everything else:

* `nodeWindow_injective_of_short`: the **wrap-around regime**. A window of
  length `K ≥ G` sees the whole circle, so two occurrences at distinct starts
  make the word shift-invariant, hence non-primitive. Multiplicity is then
  `1`, not `2`. This case is invisible to a count that only sees windows of
  length below `G`, and it is the reason `L ≥ 2` genuinely matters: at `L = 1`
  the bound `G ≤ 2 * q ^ 0 = 2` is false (a primitive word with all-distinct
  symbols of length `3` over a `3`-letter alphabet satisfies P2 vacuously).
* `primitive_P2_len_le`: the fiber count of `nodeWindow` that turns the
  multiplicity cap into `G ≤ 2 * q ^ K`, plus the injective branch above.
* `primitiveP2Candidates` / `mem_primitiveP2Candidates_iff`: the finite family
  constructed from that bound, with an exact membership characterization.
* `nonRotationalCandidates`: the family with the truth's rotations removed.
* `all_primitiveP2_ML_confidence`: the endpoint with no finite-family premise.

## What is imported rather than re-proved

* `P2RepeatResidual.isTripleRepeat_of_maximalTriple` — the translation of the
  repeat-theory maximal triple repeat into the source-faithful
  `SourceFaithfulIs.Genome.IsTripleRepeat`.
* `P2RepeatResidual.P2.imp_noLongTripleRepeat` — `P2 hg L S` implies
  `¬ RepeatAdapter.HasLongTripleRepeat hg S L`.
* `P2RepeatResidual.P2.imp_nodeCount_le_two` — the `(L - 1)`-window
  multiplicity cap from primitivity and P2.
* `RepeatAdapter.primitive_nodeCount_le_two`, `RepeatAdapter.not_primitive_of_ge_G_agree`
  — the two-sided maximal-extension engine and the period escape.
* `P2RepeatResidual.IsPrimitive.shiftPrimitive` — the bridge from
  `PopulationReduction.IsPrimitive` ("not an exact nontrivial power") to
  `RepeatAdapter.IsPrimitive` ("minimal period `G`").
* `FiniteReadRecoveryGenome.circular_exists_n_for_confidence` — the
  union-bound / Hellinger affinity engine. No likelihood proof is duplicated:
  the only new content here is the finite family that makes it applicable to
  the whole admissible class.

## Epistemic status, and what is classical

Everything stated here is kernel-checked. Axiom audits
(`AssemblyP1/PrimitiveP2FiniteClassAudit.lean`) report only `propext`,
`Classical.choice` and `Quot.sound` for every endpoint. No `axiom`, `sorry`
or `admit` is introduced. No definition is changed.

The two finite sets are built with explicit classical decidability
(`Classical.dec` for `DecidableEq (Genome α)` and for the membership
predicates), so they are not computable programs; the mathematical content is
the finiteness and the membership characterization, both stated as theorems
and both proved. `Classical.choice` enters through that construction and
through Mathlib, and nowhere else.
-/

namespace AssemblyP1.PrimitiveP2FiniteClass

open AssemblyP1.OrientedRigidity
open AssemblyP1.SourceFaithfulIs
open AssemblyP1.RepeatAdapter
open AssemblyP1.FiniteReadRecoveryGenome
open scoped Classical

variable {α : Type} [DecidableEq α] [Fintype α]

/-- Decidable equality of circular genomes.

`Genome α` is a structure with a proof field (`len_pos`), so Lean derives no
`DecidableEq` for it; without one, `Finset (Genome α)` cannot be built by
`image`. Genome equality *is* decidable — the data fields `len` and `sym` are
decidable and the proof field is a `Prop`, hence irrelevant — but the
construction is classical and therefore not executable. Only the finite
candidate family below needs it, and every membership statement about that
family is stated as a theorem rather than relied on computationally.
-/
noncomputable def genomeDecEq : DecidableEq (Genome α) :=
  fun x y => Classical.dec (x = y)

noncomputable instance : DecidableEq (Genome α) := genomeDecEq

/-! ## 1. The wrap-around regime: a genome shorter than the read length -/

omit [Fintype α] in
/-- **A genome shorter than the read length has pairwise distinct
`(L - 1)`-windows, by primitivity alone.**

A window of length at least `G` sees the whole circle, so two occurrences of
one at distinct starts would make the word shift-invariant — which is exactly
non-primitivity (`RepeatAdapter.not_primitive_of_ge_G_agree`, whose escape is
primitivity via `P2RepeatResidual.IsPrimitive.shiftPrimitive`).

This is the case that a count over windows of length `< G` cannot see: with
`K ≥ G` the multiplicity of a `K`-window is `1`, not `2`. It is also the
reason `L ≥ 2` is a real hypothesis of the length bound and not a convenience:
at `L = 1` the assertion `G ≤ 2 * q ^ 0` is false.
-/
theorem nodeWindow_injective_of_short {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (hshort : G ≤ L - 1) (hprim : PopulationReduction.IsPrimitive S)
    (a b : Fin G)
    (hEq : nodeWindow (L := L) hG S a = nodeWindow (L := L) hG S b) : a = b := by
  by_contra hne
  have hab : ((a : ℕ) % G) ≠ ((b : ℕ) % G) := by
    intro h
    have ha' : ((a : ℕ) % G) = (a : ℕ) := Nat.mod_eq_of_lt a.isLt
    have hb' : ((b : ℕ) % G) = (b : ℕ) := Nat.mod_eq_of_lt b.isLt
    rw [ha', hb'] at h
    exact hne (Fin.ext h)
  have hagr : ∀ d : ℕ, d < L - 1 →
      cyc hG S (a.val + d) = cyc hG S (b.val + d) := by
    intro d hd
    exact congrFun hEq ⟨d, hd⟩
  exact (not_primitive_of_ge_G_agree hG S a.val b.val (L - 1) hab (by omega) hagr)
    (AssemblyP1.P2RepeatResidual.IsPrimitive.shiftPrimitive hG hprim)

/-! ## 2. The length bound -/

/-- The number of length-`k` words over a `q`-letter alphabet. -/
private theorem card_word {α : Type} [Fintype α] (k : ℕ) :
    Fintype.card (Fin k → α) = Fintype.card α ^ k := by
  rw [Fintype.card_pi]
  simp [Finset.prod_const]

/-- **Finiteness of the primitive-P2 class: the length bound.**

A primitive circular word over a `q`-letter alphabet whose read length is
`L ≥ 2` and which has no maximal triple repeat of length `≥ L - 1` satisfies

    G ≤ 2 * q ^ (L - 1).

Short genomes (`G < L`) are bounded by the injectivity of the `(L - 1)`-window
map, since every such window is then unique. Longer genomes are bounded by the
multiplicity cap `P2RepeatResidual.P2.imp_nodeCount_le_two` and a fiber count
over `nodeWindow`. Either way the admissible class over all positive lengths
is finite.

The `2 ≤ L` hypothesis is essential: at `L = 1` the bound would read
`G ≤ 2 * q ^ 0 = 2`, while a primitive word with all-distinct symbols of
length `3` over a `3`-letter alphabet satisfies P2 vacuously.
-/
theorem primitive_P2_len_le {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (hL : 2 ≤ L) (hprim : PopulationReduction.IsPrimitive S)
    (hP2 : AssemblyP1.P2 hG L S) : G ≤ 2 * Fintype.card α ^ (L - 1) := by
  by_cases hLG : L ≤ G
  · -- the multiplicity cap plus a fiber count over the (L-1)-windows
    have hfib : ∀ b : Fin (L - 1) → α,
        ((Finset.univ : Finset (Fin G)).filter
          (fun a => nodeWindow (L := L) hG S a = b)).card ≤ 2 := by
      intro b
      exact AssemblyP1.P2RepeatResidual.P2.imp_nodeCount_le_two hG hL hLG S
        (AssemblyP1.P2RepeatResidual.IsPrimitive.shiftPrimitive hG hprim) hP2 b
    have hcount := Finset.card_le_mul_card_image
      (s := (Finset.univ : Finset (Fin G))) (n := 2)
      (fun b _ => hfib b)
    have hle : (Finset.univ.image (nodeWindow (L := L) hG S)).card
        ≤ Fintype.card α ^ (L - 1) := by
      have h2 : (Finset.univ.image (nodeWindow (L := L) hG S)).card
          ≤ Fintype.card (Fin (L - 1) → α) := Finset.card_le_univ _
      exact h2.trans_eq (card_word (L - 1))
    have hLen : (Finset.univ : Finset (Fin G)).card = G := by simp
    calc G = (Finset.univ : Finset (Fin G)).card := hLen.symm
      _ ≤ 2 * (Finset.univ.image (nodeWindow (L := L) hG S)).card := hcount
      _ ≤ 2 * (Fintype.card α ^ (L - 1)) := by exact Nat.mul_le_mul_left _ hle
  · -- the wrap-around regime: every (L-1)-window is unique
    have hinj : Function.Injective (nodeWindow (L := L) hG S) := by
      intro a b hEq
      exact nodeWindow_injective_of_short hG S (by omega) hprim a b hEq
    have hcard : Fintype.card (Fin G) ≤ Fintype.card (Fin (L - 1) → α) :=
      Fintype.card_le_of_injective _ hinj
    have hGcard : Fintype.card (Fin G) = G := Fintype.card_fin _
    have hW : Fintype.card (Fin (L - 1) → α) = Fintype.card α ^ (L - 1) :=
      card_word (L - 1)
    omega

/-! ## 3. The finite candidate class -/

/-- The total length bound over `α` at read length `L`: every primitive-P2
admissible circular genome over `α` has length at most this number, so the
admissible class is finite for every `L ≥ 2`. -/
def maxLen (L : ℕ) : ℕ := 2 * Fintype.card α ^ (L - 1)

/-- The finite σ-type of words of known length over `α`, read as a genome. -/
private def wordGenome (m : ℕ) (p : Σ n : Fin m, Fin (n.val + 1) → α) :
    Genome α :=
  ⟨p.1.val + 1, (by omega), p.2⟩

/-- **All circular genomes over `α` of length at most `m`**, as a finite set.

The source type is the finite σ-type of words of known length, which is a
`Fintype` for every `m`, and `Finset.image` is the only set operation applied
to `Genome α` itself. -/
noncomputable def shortGenomes (m : ℕ) : Finset (Genome α) :=
  (Finset.univ : Finset (Σ n : Fin m, Fin (n.val + 1) → α)).image (wordGenome m)

omit [DecidableEq α] in
/-- Membership in `shortGenomes` is exactly the length bound. -/
theorem mem_shortGenomes (m : ℕ) (D : Genome α) :
    D ∈ shortGenomes m ↔ D.len ≤ m := by
  classical
  constructor
  · intro hD
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hD
    have hp := p.1.isLt
    show ↑p.1 + 1 ≤ m
    omega
  · intro h
    obtain ⟨G, hG, S⟩ := D
    have hGm : G ≤ m := h
    have hn : G - 1 < m := by omega
    have hn' : (⟨G - 1, hn⟩ : Fin m).val = G - 1 := rfl
    have hIdx : G = (⟨G - 1, hn⟩ : Fin m).val + 1 := by rw [hn']; omega
    have hT : (Fin G → α) = (Fin ((⟨G - 1, hn⟩ : Fin m).val + 1) → α) :=
      congrArg (fun n => (Fin n → α)) hIdx
    refine Finset.mem_image.mpr
      ⟨⟨⟨G - 1, hn⟩, cast hT S⟩, Finset.mem_univ _, ?_⟩
    have hW : wordGenome m ⟨⟨G - 1, hn⟩, cast hT S⟩
        = ⟨(⟨G - 1, hn⟩ : Fin m).val + 1, (by omega), cast hT S⟩ := rfl
    rw [hW, Genome.mk.injEq]
    exact ⟨hIdx.symm, cast_heq hT S⟩

/-- **The finite class of all primitive-P2 admissible circular genomes over
`α` at read length `L`.**

Every admissible genome is a member (`mem_primitiveP2Candidates`), and every
member is admissible. This is the object whose existence the finite-family
version of the ML recovery theorem had to assume.
-/
noncomputable def primitiveP2Candidates (L : ℕ) : Finset (Genome α) := by
  letI : DecidablePred (fun (D : Genome α) =>
      AssemblyP1.PopulationUniqueness.AdmClass L D.len_pos D.sym) :=
    fun (D : Genome α) => Classical.dec
      (AssemblyP1.PopulationUniqueness.AdmClass L D.len_pos D.sym)
  exact (shortGenomes (maxLen (α := α) L)).filter
    (fun (D : Genome α) =>
      AssemblyP1.PopulationUniqueness.AdmClass L D.len_pos D.sym)

set_option linter.style.haveILetI false in
/-- Membership is exactly admissibility. -/
theorem mem_primitiveP2Candidates_iff {L : ℕ} (hL : 2 ≤ L) (D : Genome α) :
    D ∈ primitiveP2Candidates L ↔
      AssemblyP1.PopulationUniqueness.AdmClass L D.len_pos D.sym := by
  letI : DecidablePred (fun (D : Genome α) =>
      AssemblyP1.PopulationUniqueness.AdmClass L D.len_pos D.sym) :=
    fun (D : Genome α) => Classical.dec
      (AssemblyP1.PopulationUniqueness.AdmClass L D.len_pos D.sym)
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨mem_shortGenomes _ D |>.mpr
      (primitive_P2_len_le D.len_pos D.sym hL h.1 h.2), h⟩

/-- Every primitive-P2 admissible genome of any positive length belongs to the
finite candidate class. -/
theorem mem_primitiveP2Candidates {L : ℕ} (hL : 2 ≤ L) (D : Genome α)
    (hAdm : AssemblyP1.PopulationUniqueness.AdmClass L D.len_pos D.sym) :
    D ∈ primitiveP2Candidates L :=
  mem_primitiveP2Candidates_iff hL D |>.mpr hAdm

/-- **The primitive-P2 admissible class over all positive genome lengths is
finite.** This is the finiteness statement the candidate-family premise of
the finite-read recovery theorem used to stand in for. -/
theorem primitiveP2Class_finite (L : ℕ) (hL : 2 ≤ L) : Set.Finite
    {D : Genome α | AssemblyP1.PopulationUniqueness.AdmClass L D.len_pos D.sym} :=
  ((primitiveP2Candidates L).finite_toSet).subset
    (fun D hD => mem_primitiveP2Candidates_iff hL D |>.mpr hD)

/-! ## 4. The candidate family with the rotations of the truth removed -/

/-- **All primitive-P2 admissible genomes that are not a rotation of the true
genome `S`.**

Rotations of the truth share its read law, so keeping them in the competitor
family would make the "wrong candidate wins" event certain. They are removed
here, exactly as the finite-family theorem's `hNotRot` premise demands, so
the target of the ML statement is *constructed* rather than hypothesised.
-/
noncomputable def nonRotationalCandidates (L : ℕ) (S : Genome α) :
    Finset (Genome α) := by
  letI : DecidablePred (fun (D : Genome α) =>
      ¬ ∃ h : S.len = D.len,
        AssemblyP1.PopulationReduction.RotEquiv S.len_pos (h ▸ D.sym) S.sym) :=
    fun (D : Genome α) => Classical.dec
      (¬ ∃ h : S.len = D.len,
        AssemblyP1.PopulationReduction.RotEquiv S.len_pos (h ▸ D.sym) S.sym)
  exact (primitiveP2Candidates L).filter (fun (D : Genome α) =>
    ¬ ∃ h : S.len = D.len,
      AssemblyP1.PopulationReduction.RotEquiv S.len_pos (h ▸ D.sym) S.sym)

set_option linter.style.haveILetI false in
/-- Membership in `nonRotationalCandidates` is exactly admissibility together
with non-rotation. -/
theorem mem_nonRotationalCandidates_iff (L : ℕ) (hL : 2 ≤ L) (S D : Genome α) :
    D ∈ nonRotationalCandidates L S ↔
      (AssemblyP1.PopulationUniqueness.AdmClass L D.len_pos D.sym ∧
        ¬ ∃ h : S.len = D.len,
          AssemblyP1.PopulationReduction.RotEquiv S.len_pos (h ▸ D.sym) S.sym) := by
  letI : DecidablePred (fun (D : Genome α) =>
      ¬ ∃ h : S.len = D.len,
        AssemblyP1.PopulationReduction.RotEquiv S.len_pos (h ▸ D.sym) S.sym) :=
    fun (D : Genome α) => Classical.dec
      (¬ ∃ h : S.len = D.len,
        AssemblyP1.PopulationReduction.RotEquiv S.len_pos (h ▸ D.sym) S.sym)
  constructor
  · intro h
    obtain ⟨hc, hnr⟩ := Finset.mem_filter.mp h
    exact ⟨mem_primitiveP2Candidates_iff hL D |>.mp hc, hnr⟩
  · intro h
    exact Finset.mem_filter.mpr
      ⟨mem_primitiveP2Candidates_iff hL D |>.mpr h.1, h.2⟩

/-- Members are admissible. -/
theorem mem_nonRotationalCandidates_adm (L : ℕ) (hL : 2 ≤ L) (S D : Genome α)
    (hD : D ∈ nonRotationalCandidates L S) :
    AssemblyP1.PopulationUniqueness.AdmClass L D.len_pos D.sym :=
  (mem_nonRotationalCandidates_iff L hL S D).mp hD |>.1

/-- Members are not rotations of the truth. -/
theorem mem_nonRotationalCandidates_notRot (L : ℕ) (hL : 2 ≤ L) (S D : Genome α)
    (hD : D ∈ nonRotationalCandidates L S) :
    ¬ ∃ h : S.len = D.len,
        AssemblyP1.PopulationReduction.RotEquiv S.len_pos (h ▸ D.sym) S.sym :=
  (mem_nonRotationalCandidates_iff L hL S D).mp hD |>.2

/-! ## 5. The endpoint: ML reliability with no finite-family premise -/

/-- **Finite-read ML reliability over the entire primitive-P2 class.**

`AssemblyP1.FiniteReadRecoveryP2Complete.finite_primitiveP2_ML_confidence`
required the caller to hand over a finite family `C` of admissible
non-rotational competitors. Here that premise is gone: the competitor family
is `nonRotationalCandidates L S`, a finite set built from the length bound
`primitive_P2_len_le`, which holds for **every** primitive P2-admissible
genome of **every** positive length. The hypotheses are therefore only

* `L ≥ 2`;
* the true genome `S` is primitive and P2 (the actual `def:P1P2`), at the
  source-faithful level; and
* a tolerance `δ > 0`.

The conclusion is the exact Hellinger/Bhattacharyya iid decay: after `n ≥ N`
uniformly oriented circular reads from `S`, the probability that *some*
admissible non-rotational candidate ties or beats `S`'s exact likelihood is
at most `δ`. Ties are counted as failures, so no tie-breaking convention is
assumed. The read model is the actual data-only `circularReadPMF`; no
truth-feasibility oracle and no small-multiplicity assumption appears.
-/
theorem all_primitiveP2_ML_confidence (L : ℕ) (hL : 2 ≤ L) (S : Genome α)
    (hPrimS : PopulationReduction.IsPrimitive S.sym)
    (hP2S : AssemblyP1.P2 S.len_pos L S.sym)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      AssemblyP1.FiniteReadRecovery.eventProb
        (circularReadPMF S L) n
        (AssemblyP1.FiniteReadRecovery.wrongEvent
          (circularReadPMF S L)
          (readLawFamily (nonRotationalCandidates L S) L) n) ≤ δ :=
  AssemblyP1.FiniteReadRecoveryP2Complete.finite_primitiveP2_ML_confidence S
    (nonRotationalCandidates L S) L hL hPrimS hP2S
    (fun D hD => mem_nonRotationalCandidates_adm L hL S D hD)
    (fun D hD => mem_nonRotationalCandidates_notRot L hL S D hD) δ hδ

/-! ## Axiom audit -/

-- The kernel axioms used by the finiteness chain. `propext`,
-- `Classical.choice` and `Quot.sound` are the three standard Lean/Mathlib
-- axioms; `Classical.choice` enters only through the classical decidability
-- of the constructed finite families and through Mathlib.
#print axioms primitive_P2_len_le
#print axioms primitiveP2Candidates
#print axioms mem_primitiveP2Candidates
#print axioms primitiveP2Class_finite
#print axioms all_primitiveP2_ML_confidence

end AssemblyP1.PrimitiveP2FiniteClass
