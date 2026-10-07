import AssemblyP1.Issue94ComponentResidual
import AssemblyP1.Issue94SwapBridge
import AssemblyP1.Issue94EvenPairing
import Mathlib.GroupTheory.Perm.Support

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace AssemblyP1.Issue94ComponentSwitchProduct

open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTLadder
open AssemblyP1.P2RepeatResidual
open AssemblyP1.Issue94PhysicalChord
open AssemblyP1.Issue94PhysicalComponent
open AssemblyP1.Issue94InterlaceComponents
open AssemblyP1.Issue94ComponentCoordinates
open AssemblyP1.Issue94ComponentEndpoints
open AssemblyP1.Issue94ComponentResidual
open AssemblyP1.Issue94InvolutionSplit
open AssemblyP1.Issue94SwapBridge
open AssemblyP1.Issue94Antiderivative
open AssemblyP1.Issue94EvenPairing
open AssemblyP1.Issue94AlignedPairs

variable {α : Type} [DecidableEq α] {K L : ℕ}

theorem alignedSwap_disjoint_of_ne_coordinate
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K)
    (S : Fin K → α) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hUkk : Ukkonen hK L S)
    (sigma : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S sigma)
    (c : AltFChord hK sigma) {i j : ℕ}
    (hi : i ∈ componentCoordinates hK S sigma c)
    (hj : j ∈ componentCoordinates hK S sigma c)
    (hij : i ≠ j) :
    Equiv.Perm.Disjoint
      (alignedSwap hK
        (maxPairStart hK S c.1 (AltF hK sigma c.1))
        (maxPairStart hK S (AltF hK sigma c.1) c.1) i)
      (alignedSwap hK
        (maxPairStart hK S c.1 (AltF hK sigma c.1))
        (maxPairStart hK S (AltF hK sigma c.1) c.1) j) := by
  classical
  obtain ⟨_, d, hd, hdi, _⟩ :=
    componentCoordinate_mem_data hK hL hLK S hP2 hprim hUkk sigma hEul c hi
  obtain ⟨_, e, he, hej, _⟩ :=
    componentCoordinate_mem_data hK hL hLK S hP2 hprim hUkk sigma hEul c hj
  have hcompd :
      (altFInterlaceGraph hK S sigma).connectedComponentMk c =
        (altFInterlaceGraph hK S sigma).connectedComponentMk d := by
    exact ((Finset.mem_filter.mp hd).2).symm
  have hcompe :
      (altFInterlaceGraph hK S sigma).connectedComponentMk c =
        (altFInterlaceGraph hK S sigma).connectedComponentMk e := by
    exact ((Finset.mem_filter.mp he).2).symm
  have hsd := swap_bridge_of_component hK hL hLK S hP2 hprim hUkk sigma hEul hcompd
  have hse := swap_bridge_of_component hK hL hLK S hP2 hprim hUkk sigma hEul hcompe
  rw [hdi] at hsd
  rw [hej] at hse
  rw [← hsd, ← hse]
  rw [Equiv.Perm.disjoint_iff_disjoint_support]
  rw [Equiv.Perm.support_swap (chord_ne_image hK sigma d)]
  rw [Equiv.Perm.support_swap (chord_ne_image hK sigma e)]
  rw [Finset.disjoint_left]
  intro x hxd hxe
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxd hxe
  have hshare :
      d.1 = e.1 ∨ d.1 = AltF hK sigma e.1 ∨
      AltF hK sigma d.1 = e.1 ∨
      AltF hK sigma d.1 = AltF hK sigma e.1 := by
    rcases hxd with rfl | rfl <;> rcases hxe with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hvd : vtx hK L S d.1 = vtx hK L S (AltF hK sigma d.1) :=
    (AltF_vtx' hK S hEul d.1).symm
  have hve : vtx hK L S e.1 = vtx hK L S (AltF hK sigma e.1) :=
    (AltF_vtx' hK S hEul e.1).symm
  have hpair := pair_eq_of_shared_endpoint hK S hL hLK hprim hP2
    (chord_ne_image hK sigma d) (chord_ne_image hK sigma e) hvd hve hshare
  have hde : d = e := physical_chord_eq_of_pair_eq hK sigma hpair
  apply hij
  calc
    i = chordCoordinate hK S sigma d := hdi.symm
    _ = chordCoordinate hK S sigma e := by rw [hde]
    _ = j := hej


theorem pairEndpoints_prod {Γ : Type*} [Group Γ] (s : ℕ → Γ) :
    ∀ ps : List (ℕ × ℕ),
      (ps.map (fun p => s p.1 * s p.2)).prod =
        ((pairEndpoints ps).map s).prod
  | [] => by simp [pairEndpoints]
  | (a, b) :: rest => by
      simp [pairEndpoints, pairEndpoints_prod s rest, mul_assoc]

theorem coordinatePairs_boundary_eq_sorted {Γ : Type*} [Group Γ]
    (B : Finset ℕ) (hEven : Even B.card) (s : ℕ → Γ) :
    ((coordinatePairs B).map (fun p => s p.1 * s p.2)).prod =
      ((B.sort (· ≤ ·)).map s).prod := by
  rw [pairEndpoints_prod]
  have hlen : (B.sort (· ≤ ·)).length % 2 = 0 := by
    rw [Finset.length_sort]
    exact Nat.even_iff.mp hEven
  have hflat :=
    pairEndpoints_pairConsecutive_of_even (B.sort (· ≤ ·)) hlen
  simpa [coordinatePairs] using congrArg (fun xs => (xs.map s).prod) hflat

theorem sorted_componentSwaps_pairwise_disjoint
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K)
    (S : Fin K → α) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hUkk : Ukkonen hK L S)
    (sigma : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S sigma)
    (c : AltFChord hK sigma) :
    (((componentCoordinates hK S sigma c).sort (· ≤ ·)).map
      (fun i => alignedSwap hK
        (maxPairStart hK S c.1 (AltF hK sigma c.1))
        (maxPairStart hK S (AltF hK sigma c.1) c.1) i)).Pairwise
      Equiv.Perm.Disjoint := by
  rw [List.pairwise_map]
  apply (Finset.sort_nodup (componentCoordinates hK S sigma c) (· ≤ ·)).pairwise_of_forall_ne
  intro i hi j hj hij
  apply alignedSwap_disjoint_of_ne_coordinate hK hL hLK S hP2 hprim hUkk sigma hEul c
  · exact (Finset.mem_sort (· ≤ ·)).1 hi
  · exact (Finset.mem_sort (· ≤ ·)).1 hj
  · exact hij


theorem listProd_apply_eq_self_of_forall {β : Type*}
    (xs : List (Equiv.Perm β)) (x : β)
    (hfix : ∀ g ∈ xs, g x = x) :
    xs.prod x = x := by
  induction xs with
  | nil => simp
  | cons g gs ih =>
      rw [List.prod_cons, Equiv.Perm.mul_apply, ih]
      · exact hfix g (by simp)
      · intro h hh
        exact hfix h (by simp [hh])

theorem sorted_componentSwaps_eq_componentSwitch
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K)
    (S : Fin K → α) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hUkk : Ukkonen hK L S)
    (sigma : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S sigma)
    (c : AltFChord hK sigma) :
    (((componentCoordinates hK S sigma c).sort (· ≤ ·)).map
      (fun i => alignedSwap hK
        (maxPairStart hK S c.1 (AltF hK sigma c.1))
        (maxPairStart hK S (AltF hK sigma c.1) c.1) i)).prod =
      componentSwitch hK S sigma hEul hL hLK hprim hP2 c := by
  classical
  let xs : List (Equiv.Perm (Fin K)) :=
    ((componentCoordinates hK S sigma c).sort (· ≤ ·)).map
      (fun i => alignedSwap hK
        (maxPairStart hK S c.1 (AltF hK sigma c.1))
        (maxPairStart hK S (AltF hK sigma c.1) c.1) i)
  have hpw : xs.Pairwise Equiv.Perm.Disjoint := by
    simpa [xs] using
      sorted_componentSwaps_pairwise_disjoint hK hL hLK S hP2 hprim hUkk sigma hEul c
  change xs.prod = componentSwitch hK S sigma hEul hL hLK hprim hP2 c
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ componentEndpoints hK S sigma c
  · rcases (mem_componentEndpoints hK S sigma c x).1 hx with
      ⟨d, hd, hxd | hxd⟩
    · subst x
      let ell := chordCoordinate hK S sigma d
      have hell : ell ∈ componentCoordinates hK S sigma c := by
        unfold componentCoordinates
        exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
      have hcomp :
          (altFInterlaceGraph hK S sigma).connectedComponentMk c =
            (altFInterlaceGraph hK S sigma).connectedComponentMk d := by
        exact ((Finset.mem_filter.mp hd).2).symm
      have hswap := swap_bridge_of_component hK hL hLK S hP2 hprim hUkk sigma hEul hcomp
      have hswap' :
          Equiv.swap d.1 (AltF hK sigma d.1) =
            alignedSwap hK
              (maxPairStart hK S c.1 (AltF hK sigma c.1))
              (maxPairStart hK S (AltF hK sigma c.1) c.1) ell := by
        simpa [ell] using hswap
      have hmem :
          alignedSwap hK
              (maxPairStart hK S c.1 (AltF hK sigma c.1))
              (maxPairStart hK S (AltF hK sigma c.1) c.1) ell ∈ xs := by
        apply List.mem_map.mpr
        refine ⟨ell, ?_, rfl⟩
        exact (Finset.mem_sort (· ≤ ·)).2 hell
      have hsupp :
          d.1 ∈
            (alignedSwap hK
              (maxPairStart hK S c.1 (AltF hK sigma c.1))
              (maxPairStart hK S (AltF hK sigma c.1) c.1) ell).support := by
        rw [← hswap', Equiv.Perm.support_swap (chord_ne_image hK sigma d)]
        simp
      have hprod :=
        Equiv.Perm.eq_on_support_mem_disjoint hmem hpw d.1 hsupp
      have hdD : d.1 ∈ componentEndpoints hK S sigma c :=
        (mem_componentEndpoints hK S sigma c d.1).2 ⟨d, hd, Or.inl rfl⟩
      calc
        xs.prod d.1 =
            alignedSwap hK
              (maxPairStart hK S c.1 (AltF hK sigma c.1))
              (maxPairStart hK S (AltF hK sigma c.1) c.1) ell d.1 := hprod.symm
        _ = AltF hK sigma d.1 := by
          rw [← hswap']
          simp [chord_ne_image hK sigma d]
        _ = componentSwitch hK S sigma hEul hL hLK hprim hP2 c d.1 := by
          symm
          simp [componentSwitch, Issue94InvolutionSplit.onSet, hdD]
    · subst x
      let ell := chordCoordinate hK S sigma d
      have hell : ell ∈ componentCoordinates hK S sigma c := by
        unfold componentCoordinates
        exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
      have hcomp :
          (altFInterlaceGraph hK S sigma).connectedComponentMk c =
            (altFInterlaceGraph hK S sigma).connectedComponentMk d := by
        exact ((Finset.mem_filter.mp hd).2).symm
      have hswap := swap_bridge_of_component hK hL hLK S hP2 hprim hUkk sigma hEul hcomp
      have hswap' :
          Equiv.swap d.1 (AltF hK sigma d.1) =
            alignedSwap hK
              (maxPairStart hK S c.1 (AltF hK sigma c.1))
              (maxPairStart hK S (AltF hK sigma c.1) c.1) ell := by
        simpa [ell] using hswap
      have hmem :
          alignedSwap hK
              (maxPairStart hK S c.1 (AltF hK sigma c.1))
              (maxPairStart hK S (AltF hK sigma c.1) c.1) ell ∈ xs := by
        apply List.mem_map.mpr
        refine ⟨ell, ?_, rfl⟩
        exact (Finset.mem_sort (· ≤ ·)).2 hell
      have hsupp :
          AltF hK sigma d.1 ∈
            (alignedSwap hK
              (maxPairStart hK S c.1 (AltF hK sigma c.1))
              (maxPairStart hK S (AltF hK sigma c.1) c.1) ell).support := by
        rw [← hswap', Equiv.Perm.support_swap (chord_ne_image hK sigma d)]
        simp
      have hprod :=
        Equiv.Perm.eq_on_support_mem_disjoint hmem hpw (AltF hK sigma d.1) hsupp
      have hfdD : AltF hK sigma d.1 ∈ componentEndpoints hK S sigma c :=
        (mem_componentEndpoints hK S sigma c (AltF hK sigma d.1)).2
          ⟨d, hd, Or.inr rfl⟩
      have hsq : AltF hK sigma (AltF hK sigma d.1) = d.1 :=
        AltF_sq hK S hEul hL hLK hprim hP2 d.1
      calc
        xs.prod (AltF hK sigma d.1) =
            alignedSwap hK
              (maxPairStart hK S c.1 (AltF hK sigma c.1))
              (maxPairStart hK S (AltF hK sigma c.1) c.1) ell
              (AltF hK sigma d.1) := hprod.symm
        _ = d.1 := by
          rw [← hswap']
          simp [chord_ne_image hK sigma d]
        _ = componentSwitch hK S sigma hEul hL hLK hprim hP2 c
              (AltF hK sigma d.1) := by
          symm
          simp [componentSwitch, Issue94InvolutionSplit.onSet, hfdD, hsq]
  · have hfix :
        ∀ g ∈ xs, g x = x := by
      intro g hg
      rcases List.mem_map.mp hg with ⟨ell, hellsort, rfl⟩
      have hell : ell ∈ componentCoordinates hK S sigma c :=
        (Finset.mem_sort (· ≤ ·)).1 hellsort
      obtain ⟨_, d, hd, hdi, _⟩ :=
        componentCoordinate_mem_data hK hL hLK S hP2 hprim hUkk sigma hEul c hell
      have hcomp :
          (altFInterlaceGraph hK S sigma).connectedComponentMk c =
            (altFInterlaceGraph hK S sigma).connectedComponentMk d := by
        exact ((Finset.mem_filter.mp hd).2).symm
      have hswap := swap_bridge_of_component hK hL hLK S hP2 hprim hUkk sigma hEul hcomp
      rw [hdi] at hswap
      rw [← hswap]
      apply Equiv.swap_apply_of_ne_of_ne
      · intro hxeq
        apply hx
        rw [hxeq]
        exact (mem_componentEndpoints hK S sigma c d.1).2
          ⟨d, hd, Or.inl rfl⟩
      · intro hxeq
        apply hx
        rw [hxeq]
        exact (mem_componentEndpoints hK S sigma c (AltF hK sigma d.1)).2
          ⟨d, hd, Or.inr rfl⟩
    have hprod : xs.prod x = x :=
      listProd_apply_eq_self_of_forall xs x hfix
    calc
      xs.prod x = x := hprod
      _ = componentSwitch hK S sigma hEul hL hLK hprim hP2 c x := by
        symm
        simp [componentSwitch, Issue94InvolutionSplit.onSet, hx]

theorem coordinatePairs_boundary_eq_componentSwitch
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K)
    (S : Fin K → α) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hUkk : Ukkonen hK L S)
    (sigma : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S sigma)
    (c : AltFChord hK sigma) :
    ((coordinatePairs (componentCoordinates hK S sigma c)).map
      (fun p =>
        alignedSwap hK
          (maxPairStart hK S c.1 (AltF hK sigma c.1))
          (maxPairStart hK S (AltF hK sigma c.1) c.1) p.1 *
        alignedSwap hK
          (maxPairStart hK S c.1 (AltF hK sigma c.1))
          (maxPairStart hK S (AltF hK sigma c.1) c.1) p.2)).prod =
      componentSwitch hK S sigma hEul hL hLK hprim hP2 c := by
  have hEven :=
    componentCoordinates_even hK hL hLK S hP2 hprim hUkk sigma hEul c
  exact
    (coordinatePairs_boundary_eq_sorted
      (componentCoordinates hK S sigma c) hEven
      (fun i => alignedSwap hK
        (maxPairStart hK S c.1 (AltF hK sigma c.1))
        (maxPairStart hK S (AltF hK sigma c.1) c.1) i)).trans
      (sorted_componentSwaps_eq_componentSwitch
        hK hL hLK S hP2 hprim hUkk sigma hEul c)

#print axioms AssemblyP1.Issue94ComponentSwitchProduct.coordinatePairs_boundary_eq_componentSwitch

end AssemblyP1.Issue94ComponentSwitchProduct
