import AssemblyP1.Issue94ComponentCoordinates
import AssemblyP1.Issue94InvolutionSplit

namespace AssemblyP1.Issue94ComponentEndpoints

open AssemblyP1
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTLadder
open AssemblyP1.Issue94PhysicalChord
open AssemblyP1.Issue94CLEDeletion

variable {α : Type} [DecidableEq α] {K L : ℕ}

noncomputable def componentEndpoints
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (c : AltFChord hK sigma) : Finset (Fin K) := by
  classical
  exact (componentFinset (altFInterlaceGraph hK S sigma) c).biUnion
    (fun d => {d.1, AltF hK sigma d.1})

theorem mem_componentEndpoints
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (c : AltFChord hK sigma) (x : Fin K) :
    x ∈ componentEndpoints hK S sigma c ↔
      ∃ d : AltFChord hK sigma,
        d ∈ componentFinset (altFInterlaceGraph hK S sigma) c ∧
          (x = d.1 ∨ x = AltF hK sigma d.1) := by
  classical
  simp [componentEndpoints, or_comm]

theorem componentEndpoints_nonempty
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (c : AltFChord hK sigma) :
    (componentEndpoints hK S sigma c).Nonempty := by
  classical
  refine ⟨c.1, ?_⟩
  apply (mem_componentEndpoints hK S sigma c c.1).2
  refine ⟨c, ?_, Or.inl rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

theorem componentEndpoints_closed
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (c : AltFChord hK sigma) (x : Fin K) :
    x ∈ componentEndpoints hK S sigma c ↔
      AltF hK sigma x ∈ componentEndpoints hK S sigma c := by
  classical
  have hsq : ∀ y : Fin K, AltF hK sigma (AltF hK sigma y) = y :=
    AltF_sq hK S hEul hL hLK hprim hP2
  have hforward : ∀ y : Fin K, y ∈ componentEndpoints hK S sigma c →
      AltF hK sigma y ∈ componentEndpoints hK S sigma c := by
    intro y hy
    rcases (mem_componentEndpoints hK S sigma c y).1 hy with ⟨d, hd, hdy | hdy⟩
    · subst y
      apply (mem_componentEndpoints hK S sigma c _).2
      exact ⟨d, hd, Or.inr rfl⟩
    · subst y
      rw [hsq d.1]
      apply (mem_componentEndpoints hK S sigma c _).2
      exact ⟨d, hd, Or.inl rfl⟩
  constructor
  · exact hforward x
  · intro hx
    have h := hforward (AltF hK sigma x) hx
    simpa only [hsq x] using h

theorem componentEndpoints_moved
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (c : AltFChord hK sigma) :
    ∀ x : Fin K, x ∈ componentEndpoints hK S sigma c →
      AltF hK sigma x ≠ x := by
  classical
  intro x hx
  rcases (mem_componentEndpoints hK S sigma c x).1 hx with ⟨d, hd, rfl | rfl⟩
  · exact (chord_ne_image hK sigma d).symm
  · have hsq := AltF_sq hK S hEul hL hLK hprim hP2 d.1
    rw [hsq]
    exact chord_ne_image hK sigma d

end AssemblyP1.Issue94ComponentEndpoints
