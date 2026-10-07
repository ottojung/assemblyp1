import AssemblyP1.Issue94NoCollision
import AssemblyP1.Issue94InterlaceParity
import AssemblyP1.BBTLadder

namespace AssemblyP1.Issue94PhysicalChord

open SourceFaithfulIs
open AssemblyP1
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTLadder
open AssemblyP1.BBTEulerian
open AssemblyP1.Issue94NoCollision

variable {α : Type} [DecidableEq α] {K : ℕ}

/-- Canonical lower endpoints of the nontrivial AltF transpositions. -/
def altFChordSet (hK : 0 < K) (sigma : Fin K ≃ Fin K) : Finset (Fin K) :=
  Finset.univ.filter (fun a => a.val < (AltF hK sigma a).val)

/-- One physical AltF transposition, represented by its lower-valued endpoint. -/
abbrev AltFChord (hK : 0 < K) (sigma : Fin K ≃ Fin K) :=
  {a : Fin K // a ∈ altFChordSet hK sigma}

@[simp] theorem mem_altFChordSet
    (hK : 0 < K) (sigma : Fin K ≃ Fin K) (a : Fin K) :
    a ∈ altFChordSet hK sigma ↔ a.val < (AltF hK sigma a).val := by
  simp [altFChordSet]

theorem chord_lower
    (hK : 0 < K) (sigma : Fin K ≃ Fin K)
    (c : AltFChord hK sigma) :
    c.1.val < (AltF hK sigma c.1).val := by
  exact (mem_altFChordSet hK sigma c.1).mp c.2

@[simp] theorem chord_ne_image
    (hK : 0 < K) (sigma : Fin K ≃ Fin K)
    (c : AltFChord hK sigma) :
    c.1 ≠ AltF hK sigma c.1 := by
  intro h
  have hv := congrArg Fin.val h
  exact (Nat.ne_of_lt (chord_lower hK sigma c)) hv

/-- Interlacement graph on physical AltF transpositions, counted once each. -/
def altFInterlaceGraph
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K) :
    SimpleGraph (AltFChord hK sigma) where
  Adj c d :=
    Interleaved (mkGenome hK S)
      c.1 (AltF hK sigma c.1)
      d.1 (AltF hK sigma d.1)
  symm := Std.Symm.mk (by
    intro c d h
    exact interleaved_pair_swap hK _ _ _ _ h)
  loopless := Std.Irrefl.mk (by
    intro c h
    exact h.1.2.1 rfl)

@[simp] theorem altFInterlaceGraph_adj
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (c d : AltFChord hK sigma) :
    (altFInterlaceGraph hK S sigma).Adj c d ↔
      Interleaved (mkGenome hK S)
        c.1 (AltF hK sigma c.1)
        d.1 (AltF hK sigma d.1) := Iff.rfl

#print axioms AssemblyP1.Issue94PhysicalChord.chord_ne_image
#print axioms AssemblyP1.Issue94PhysicalChord.altFInterlaceGraph_adj

theorem exists_physical_chord_of_support
    {L : ℕ}
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    {a : Fin K} (hne : AltF hK sigma a ≠ a) :
    ∃ c : AltFChord hK sigma,
      ({c.1, AltF hK sigma c.1} : Finset (Fin K)) =
        {a, AltF hK sigma a} := by
  have hsq : AltF hK sigma (AltF hK sigma a) = a :=
    AltF_sq hK S hEul hL hLK hprim hP2 a
  by_cases hlt : a.val < (AltF hK sigma a).val
  · let c : AltFChord hK sigma :=
      ⟨a, (mem_altFChordSet hK sigma a).2 hlt⟩
    exact ⟨c, rfl⟩
  · have hvals : a.val ≠ (AltF hK sigma a).val := by
      intro hv
      apply hne
      apply Fin.ext
      exact hv.symm
    have hgt : (AltF hK sigma a).val < a.val := by omega
    have hmem : AltF hK sigma a ∈ altFChordSet hK sigma := by
      apply (mem_altFChordSet hK sigma _).2
      simpa [hsq] using hgt
    let c : AltFChord hK sigma := ⟨AltF hK sigma a, hmem⟩
    refine ⟨c, ?_⟩
    apply Finset.ext
    intro x
    simp [c, hsq, or_comm]

#print axioms AssemblyP1.Issue94PhysicalChord.exists_physical_chord_of_support

end AssemblyP1.Issue94PhysicalChord
