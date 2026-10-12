import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic

/-!
# Finite read-confusability and deterministic side labels (#272)

This is a SUPPORT-ONLY abstraction, not a proof that a specific genome
assembly reconstruction theorem supplies the auxiliary label. If the prior is
positive on every candidate and each supported read has positive likelihood,
the supported fibre of the joint observation (read,label) is the positive
posterior support.

A truthful deterministic side label c : Genome -> Label achieves pointwise
certainty precisely when it separates every pair of distinct candidates that
can generate a common observation (proper coloring of the confusability graph).

A four-candidate two-observation model exhibits two minimum-cardinality
two-label side channels that are incomparable in information content. There is
no coarsest sufficient deterministic truth-only label partition.
-/

namespace AssemblyP1.FiniteSideInformationColoring

variable {Genome Obs Label : Type*}

def CertainGivenLabel (S : Genome → Obs → Prop) (c : Genome → Label) : Prop :=
  ∀ g h y, S g y → S h y → c g = c h → g = h

def ProperConfusabilityColoring (S : Genome → Obs → Prop)
    (c : Genome → Label) : Prop :=
  ∀ g h, g ≠ h → (∃ y, S g y ∧ S h y) → c g ≠ c h

theorem certain_iff_proper (S : Genome → Obs → Prop) (c : Genome → Label) :
    CertainGivenLabel S c ↔ ProperConfusabilityColoring S c := by
  constructor
  · intro hc g h hne ⟨y, hg, hh⟩ heq
    exact hne (hc g h y hg hh heq)
  · intro hp g h y hg hh heq
    by_contra hne
    exact hp g h hne ⟨y, hg, hh⟩ heq

/-- c2 reveals no more distinctions than c1: every c1-class lies in a
single c2-class. This is the usual partition refinement partial order. -/
def FactorsThrough {G C D : Type*} (c1 : G → C) (c2 : G → D) : Prop :=
  ∀ g h, c1 g = c1 h → c2 g = c2 h

namespace FourCandidates

def S (g : Fin 4) (y : Fin 2) : Prop :=
  ((g = 0 ∨ g = 1) ∧ y = 0) ∨ ((g = 2 ∨ g = 3) ∧ y = 1)

def labelA (g : Fin 4) : Bool := (g == 1) || (g == 3)
def labelB (g : Fin 4) : Bool := (g == 1) || (g == 2)

theorem labelA_certain : CertainGivenLabel S labelA := by
  unfold CertainGivenLabel S labelA
  decide
theorem labelB_certain : CertainGivenLabel S labelB := by
  unfold CertainGivenLabel S labelB
  decide

/-- One possible label cannot distinguish candidates 0 and 1, which
can produce the same observation. Thus the minimum label count is at least 2. -/
theorem no_subsingleton_label {C : Type*} [Subsingleton C] (c : Fin 4 → C) :
    ¬ CertainGivenLabel S c := by
  intro hc
  have h : (0 : Fin 4) = 1 := hc 0 1 0 (by simp [S]) (by simp [S])
    (Subsingleton.elim _ _)
  exact (by decide : (0 : Fin 4) ≠ 1) h

theorem labelA_not_refines_labelB : ¬ FactorsThrough labelA labelB := by
  unfold FactorsThrough labelA labelB
  decide
theorem labelB_not_refines_labelA : ¬ FactorsThrough labelB labelA := by
  unfold FactorsThrough labelB labelA
  decide

/-- Even though A and B each give certain recovery with two possible labels,
no deterministic side label coarser than both can be sufficient. -/
theorem no_common_coarsest {C : Type*} (c : Fin 4 → C)
    (hA : FactorsThrough labelA c) (hB : FactorsThrough labelB c) :
    ¬ CertainGivenLabel S c := by
  intro hc
  have h02 : c 0 = c 2 := hA 0 2 (by decide)
  have h12 : c 1 = c 2 := hB 1 2 (by decide)
  have h01 : c 0 = c 1 := h02.trans h12.symm
  have hbad : (0 : Fin 4) = 1 := hc 0 1 0 (by simp [S]) (by simp [S]) h01
  exact (by decide : (0 : Fin 4) ≠ 1) hbad

end FourCandidates

end AssemblyP1.FiniteSideInformationColoring
