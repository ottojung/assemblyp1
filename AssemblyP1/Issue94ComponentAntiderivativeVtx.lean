import AssemblyP1.Issue94AntiderivativeInterval
import AssemblyP1.Issue94ComponentCoordinates
import AssemblyP1.Issue94EvenPairing
import AssemblyP1.Issue94PhysicalChord

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace AssemblyP1.Issue94ComponentAntiderivativeVtx

open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTLadder
open AssemblyP1.P2RepeatResidual
open AssemblyP1.Issue94PhysicalChord
open AssemblyP1.Issue94Antiderivative
open AssemblyP1.Issue94IntervalCore
open AssemblyP1.Issue94AntiderivativeInterval
open AssemblyP1.Issue94EvenPairing
open AssemblyP1.Issue94ComponentCoordinates

variable {α : Type} [DecidableEq α] {K L : ℕ}

theorem vtxPreserving_mul
    (hK : 0 < K) (S : Fin K → α)
    {g h : Equiv.Perm (Fin K)}
    (hg : ∀ x : Fin K, vtx hK L S (g x) = vtx hK L S x)
    (hh : ∀ x : Fin K, vtx hK L S (h x) = vtx hK L S x) :
    ∀ x : Fin K, vtx hK L S ((g * h) x) = vtx hK L S x := by
  intro x
  rw [Equiv.Perm.mul_apply]
  exact (hg (h x)).trans (hh x)

theorem intervalProd_preserves_vtx
    (hK : 0 < K) (S : Fin K → α)
    (s : ℕ → Equiv.Perm (Fin K)) {a n : ℕ}
    (hs : ∀ i, a ≤ i → i < a + n →
      ∀ x : Fin K, vtx hK L S (s i x) = vtx hK L S x) :
    ∀ x : Fin K, vtx hK L S (intervalProd s a n x) = vtx hK L S x := by
  induction n generalizing a with
  | zero =>
      intro x
      simp [intervalProd]
  | succ n ih =>
      rw [intervalProd]
      apply vtxPreserving_mul hK S
      · exact hs a (by omega) (by omega)
      · apply ih
        intro i hi1 hi2
        exact hs i (by omega) (by omega)

theorem listProd_preserves_vtx
    (hK : 0 < K) (S : Fin K → α)
    (xs : List (Equiv.Perm (Fin K)))
    (hxs : ∀ g ∈ xs, ∀ x : Fin K, vtx hK L S (g x) = vtx hK L S x) :
    ∀ x : Fin K, vtx hK L S (xs.prod x) = vtx hK L S x := by
  induction xs with
  | nil =>
      intro x
      simp
  | cons g gs ih =>
      rw [List.prod_cons]
      apply vtxPreserving_mul hK S
      · exact hxs g (by simp)
      · apply ih
        intro h hh
        exact hxs h (by simp [hh])

theorem coordinatePairs_antiderivative_preserves_vtx
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : EulerianCycle hK L S sigma) (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (hUkk : Ukkonen hK L S) (c : AltFChord hK sigma) :
    ∀ x : Fin K,
      vtx hK L S
        (((coordinatePairs (componentCoordinates hK S sigma c)).map
          (fun p => intervalProd
            (alignedSwap hK
              (maxPairStart hK S c.1 (AltF hK sigma c.1))
              (maxPairStart hK S (AltF hK sigma c.1) c.1))
            p.1 (p.2 - p.1))).prod x)
        = vtx hK L S x := by
  apply listProd_preserves_vtx hK S
  intro g hg
  rcases List.mem_map.mp hg with ⟨q, hq, rfl⟩
  have hEven : Even (componentCoordinates hK S sigma c).card :=
    componentCoordinates_even hK hL hLK S hP2 hprim hUkk sigma hEul c
  have hq2 : q.2 ∈ componentCoordinates hK S sigma c :=
    coordinatePairs_snd_mem _ hEven hq
  have hle : q.1 ≤ q.2 := coordinatePairs_le _ q hq
  obtain ⟨hlen2, _⟩ :=
    componentCoordinate_mem_data hK hL hLK S hP2 hprim hUkk sigma hEul c hq2
  apply intervalProd_preserves_vtx hK S
  intro i hi1 hi2
  have hib : i + (L - 1) ≤ maxPairLen hK S c.1 (AltF hK sigma c.1) := by
    have hsum : q.1 + (q.2 - q.1) = q.2 := by omega
    omega
  exact alignedSwap_preserves_vtx_of_support_chord hK hL hLK S hprim hP2
    hEul (chord_ne_image hK sigma c) rfl hib

#print axioms AssemblyP1.Issue94ComponentAntiderivativeVtx.coordinatePairs_antiderivative_preserves_vtx

end AssemblyP1.Issue94ComponentAntiderivativeVtx
