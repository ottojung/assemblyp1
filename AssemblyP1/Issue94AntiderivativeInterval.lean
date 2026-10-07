import AssemblyP1.Issue94Antiderivative
import AssemblyP1.Issue94IntervalCore
import AssemblyP1.Issue94LadderAligned

namespace AssemblyP1.Issue94AntiderivativeInterval

open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTLadder
open AssemblyP1.P2RepeatResidual
open AssemblyP1.Issue94LadderAligned
open AssemblyP1.Issue94IntervalCore
open AssemblyP1.Issue94Antiderivative

variable {α : Type} [DecidableEq α] {K L : ℕ}

theorem alignedSwap_preserves_vtx_of_support_chord
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K) (S : Fin K → α)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    {σ : Fin K ≃ Fin K} (hEul : EulerianCycle hK L S σ)
    {a b : Fin K} (hab : a ≠ b) (hfx : AltF hK σ a = b)
    {i : ℕ} (hi : i + (L - 1) ≤ maxPairLen hK S a b) :
    ∀ x : Fin K,
      vtx hK L S
        (alignedSwap hK (maxPairStart hK S a b)
          (maxPairStart hK S b a) i x) =
      vtx hK L S x := by
  intro x
  let p := rotAdd hK i (maxPairStart hK S a b)
  let q := rotAdd hK i (maxPairStart hK S b a)
  have hpq : vtx hK L S p = vtx hK L S q :=
    aligned_vtx_of_support_chord hK hL hLK S hprim hP2 hEul hab hfx hi
  by_cases hxp : x = p
  · subst x
    simp [alignedSwap, p, q, hpq]
  by_cases hxq : x = q
  · subst x
    simp [alignedSwap, p, q, hpq]
  · have hs : Equiv.swap p q x = x :=
      Equiv.swap_apply_of_ne_of_ne hxp hxq
    simpa [alignedSwap, p, q] using congrArg (vtx hK L S) hs

theorem alignedSwaps_commute_of_support_chord
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K) (S : Fin K → α)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    {σ : Fin K ≃ Fin K} (hEul : EulerianCycle hK L S σ)
    {a b : Fin K} (hab : a ≠ b) (hfx : AltF hK σ a = b)
    {i j : ℕ}
    (hi : i + (L - 1) ≤ maxPairLen hK S a b)
    (hj : j + (L - 1) ≤ maxPairLen hK S a b) :
    Commute
      (alignedSwap hK (maxPairStart hK S a b) (maxPairStart hK S b a) i)
      (alignedSwap hK (maxPairStart hK S a b) (maxPairStart hK S b a) j) := by
  let pi := rotAdd hK i (maxPairStart hK S a b)
  let qi := rotAdd hK i (maxPairStart hK S b a)
  let sj := alignedSwap hK (maxPairStart hK S a b) (maxPairStart hK S b a) j
  by_cases hne : pi ≠ qi
  · have hne' :
        rotAdd hK i (maxPairStart hK S a b) ≠
          rotAdd hK i (maxPairStart hK S b a) := by
      simpa [pi, qi] using hne
    have ht := aligned_swap_commutes hK hL hLK S hprim hP2 hEul hab hfx hi hne'
        sj (alignedSwap_preserves_vtx_of_support_chord hK hL hLK S hprim hP2
          hEul hab hfx hj)
    change
      alignedSwap hK (maxPairStart hK S a b) (maxPairStart hK S b a) i * sj =
        sj * alignedSwap hK (maxPairStart hK S a b) (maxPairStart hK S b a) i
    exact ht
  · have heq : pi = qi := not_ne_iff.mp hne
    have hsid :
        alignedSwap hK (maxPairStart hK S a b) (maxPairStart hK S b a) i =
          1 := by
      ext x
      simp [alignedSwap, pi, qi, heq]
    rw [hsid]
    exact Commute.one_left sj

theorem alignedSwap_sq
    (hK : 0 < K) (p q : Fin K) (i : ℕ) :
    alignedSwap hK p q i * alignedSwap hK p q i = 1 := by
  simp [alignedSwap]

theorem rho_shift_alignedSwap_mul
    (hK : 0 < K) (p q : Fin K) (i : ℕ) :
    rhoEquiv hK * alignedSwap hK p q i * (rhoEquiv hK)⁻¹ =
      alignedSwap hK p q (i + 1) := by
  change
    ((rhoEquiv hK).symm.trans (alignedSwap hK p q i)).trans (rhoEquiv hK) =
      alignedSwap hK p q (i + 1)
  exact rho_conj_alignedSwap hK p q i

theorem aligned_interval_commutator
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K) (S : Fin K → α)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    {σ : Fin K ≃ Fin K} (hEul : EulerianCycle hK L S σ)
    {u v : Fin K} (huv : u ≠ v) (hfx : AltF hK σ u = v)
    {a n : ℕ}
    (hvalid : a + n + (L - 1) ≤ maxPairLen hK S u v) :
    let p := maxPairStart hK S u v
    let q := maxPairStart hK S v u
    let g := intervalProd (alignedSwap hK p q) a n
    g⁻¹ * rhoEquiv hK * g * (rhoEquiv hK)⁻¹ =
      alignedSwap hK p q a * alignedSwap hK p q (a + n) := by
  dsimp
  apply intervalProd_commutator_local
  · intro i j hi1 hi2 hj1 hj2
    apply alignedSwaps_commute_of_support_chord hK hL hLK S hprim hP2 hEul huv hfx
    · omega
    · omega
  · intro i hi1 hi2
    exact alignedSwap_sq hK _ _ i
  · intro i hi1 hi2
    exact rho_shift_alignedSwap_mul hK _ _ i

#print axioms aligned_interval_commutator
