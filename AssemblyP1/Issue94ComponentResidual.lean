import AssemblyP1.Issue94ComponentEndpoints
import AssemblyP1.Issue94InvolutionSplit


namespace AssemblyP1.Issue94ComponentResidual

open AssemblyP1
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTLadder
open AssemblyP1.Issue94PhysicalChord
open AssemblyP1.Issue94ComponentEndpoints
open AssemblyP1.Issue94InvolutionSplit
open AssemblyP1.Issue94SupportDescent

variable {α : Type} [DecidableEq α] {K L : ℕ}

noncomputable def componentSwitch
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (c : AltFChord hK sigma) : Fin K ≃ Fin K :=
  onSetEquiv (AltF hK sigma) (componentEndpoints hK S sigma c)
    (AltF_sq hK S hEul hL hLK hprim hP2)
    (componentEndpoints_closed hK S sigma hEul hL hLK hprim hP2 c)

noncomputable def componentResidual
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (c : AltFChord hK sigma) : Fin K ≃ Fin K :=
  offSetEquiv (AltF hK sigma) (componentEndpoints hK S sigma c)
    (AltF_sq hK S hEul hL hLK hprim hP2)
    (componentEndpoints_closed hK S sigma hEul hL hLK hprim hP2 c)

theorem altF_eq_switch_residual
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (c : AltFChord hK sigma) :
    ∀ x : Fin K,
      AltF hK sigma x =
        componentSwitch hK S sigma hEul hL hLK hprim hP2 c
          (componentResidual hK S sigma hEul hL hLK hprim hP2 c x) := by
  intro x
  exact split_apply (AltF hK sigma) (componentEndpoints hK S sigma c)
    (AltF_sq hK S hEul hL hLK hprim hP2)
    (componentEndpoints_closed hK S sigma hEul hL hLK hprim hP2 c) x

theorem switch_residual_commute
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (c : AltFChord hK sigma) :
    ∀ x : Fin K,
      componentSwitch hK S sigma hEul hL hLK hprim hP2 c
          (componentResidual hK S sigma hEul hL hLK hprim hP2 c x) =
        componentResidual hK S sigma hEul hL hLK hprim hP2 c
          (componentSwitch hK S sigma hEul hL hLK hprim hP2 c x) := by
  intro x
  exact commute_apply (AltF hK sigma) (componentEndpoints hK S sigma c)
    (AltF_sq hK S hEul hL hLK hprim hP2)
    (componentEndpoints_closed hK S sigma hEul hL hLK hprim hP2 c) x

theorem switch_preserves_vtx
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (c : AltFChord hK sigma) :
    ∀ x : Fin K,
      vtx hK L S
          (componentSwitch hK S sigma hEul hL hLK hprim hP2 c x) =
        vtx hK L S x := by
  exact onSet_preserves (vtx hK L S) (AltF hK sigma)
    (componentEndpoints hK S sigma c)
    (AltF_sq hK S hEul hL hLK hprim hP2)
    (componentEndpoints_closed hK S sigma hEul hL hLK hprim hP2 c)
    (fun x => AltF_vtx' (hG := hK) (S := S) hEul x)

theorem residual_preserves_vtx
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (c : AltFChord hK sigma) :
    ∀ x : Fin K,
      vtx hK L S
          (componentResidual hK S sigma hEul hL hLK hprim hP2 c x) =
        vtx hK L S x := by
  exact offSet_preserves (vtx hK L S) (AltF hK sigma)
    (componentEndpoints hK S sigma c)
    (AltF_sq hK S hEul hL hLK hprim hP2)
    (componentEndpoints_closed hK S sigma hEul hL hLK hprim hP2 c)
    (fun x => AltF_vtx' (hG := hK) (S := S) hEul x)

theorem residual_support_lt
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (c : AltFChord hK sigma) :
    (Support (componentResidual hK S sigma hEul hL hLK hprim hP2 c)).card <
      supportMeasure hK sigma := by
  change (Support (componentResidual hK S sigma hEul hL hLK hprim hP2 c)).card <
    (Support (AltF hK sigma)).card
  apply support_card_lt_of_delete
  · exact componentEndpoints_nonempty hK S sigma c
  · intro x hx
    exact offSet_fixes (AltF hK sigma) (componentEndpoints hK S sigma c)
      (AltF_sq hK S hEul hL hLK hprim hP2)
      (componentEndpoints_closed hK S sigma hEul hL hLK hprim hP2 c) hx
  · intro x hx
    exact offSet_agrees (AltF hK sigma) (componentEndpoints hK S sigma c)
      (AltF_sq hK S hEul hL hLK hprim hP2)
      (componentEndpoints_closed hK S sigma hEul hL hLK hprim hP2 c) hx
  · exact componentEndpoints_moved hK S sigma hEul hL hLK hprim hP2 c

theorem switch_nontrivial
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (c : AltFChord hK sigma) :
    ∃ x : Fin K,
      componentSwitch hK S sigma hEul hL hLK hprim hP2 c x ≠ x := by
  classical
  refine ⟨c.1, ?_⟩
  have hcmem : c.1 ∈ componentEndpoints hK S sigma c := by
    apply (mem_componentEndpoints hK S sigma c c.1).2
    refine ⟨c, ?_, Or.inl rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  change onSet (AltF hK sigma) (componentEndpoints hK S sigma c) c.1 ≠ c.1
  simp only [onSet, hcmem, ite_true]
  exact (chord_ne_image hK sigma c).symm

end AssemblyP1.Issue94ComponentResidual
