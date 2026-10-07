import AssemblyP1.Issue94ComponentCoboundary
import AssemblyP1.Issue94ComponentCoordinates

/-!
# Board 94: the antiderivative preserves `vtx` pointwise

This module proves that the concrete antiderivative

  `g = ∏_(p ∈ coordinatePairs (componentCoordinates hK S σ c))
        intervalProd (alignedSwap hK ladderP ladderQ) p.1 (p.2 - p.1)`

preserves `vtx` pointwise, i.e. `∀ x : Fin K, vtx hK L S (g x) = vtx hK L S x`.

The proof is the simple closure of `alignedSwap_preserves_vtx_of_support_chord`
under `Equiv` multiplication and list product:

1. Each `alignedSwap hK p q i` preserves `vtx` pointwise
   (`alignedSwap_preserves_vtx_of_support_chord`).
2. The product of two `vtx`-preserving permutations preserves `vtx` pointwise
   (`vtx_preserving_mul`).
3. `intervalProd` of `vtx`-preserving factors preserves `vtx` pointwise
   (`intervalProd_preserves_vtx`).
4. The product over all `coordinatePairs` preserves `vtx` pointwise
   (`coordinatePairs_prod_preserves_vtx`).

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`, and no
change to any existing definition.
-/

set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace AssemblyP1.Issue94AntiderivativeVtx

open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTLadder
open AssemblyP1.RepeatAdapter
open AssemblyP1.P2RepeatResidual
open AssemblyP1.Issue94Antiderivative
open AssemblyP1.Issue94IntervalCore
open AssemblyP1.Issue94AntiderivativeInterval
open AssemblyP1.Issue94EvenPairing
open AssemblyP1.Issue94ComponentCoordinates

variable {α : Type} [DecidableEq α] {K L : ℕ}

/-- The product of two `vtx`-preserving permutations preserves `vtx` pointwise. -/
theorem vtx_preserving_mul
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K) (S : Fin K → α)
    (g h : Fin K ≃ Fin K)
    (hg : ∀ x : Fin K, vtx hK L S (g x) = vtx hK L S x)
    (hh : ∀ x : Fin K, vtx hK L S (h x) = vtx hK L S x) :
    ∀ x : Fin K, vtx hK L S ((g.trans h) x) = vtx hK L S x := by
  intro x
  simp only [Equiv.trans_apply]
  rw [hg (h x), hh x]

/-- `intervalProd` of `vtx`-preserving factors preserves `vtx` pointwise. -/
theorem intervalProd_preserves_vtx
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K) (S : Fin K → α)
    {s : ℕ → (Fin K ≃ Fin K)}
    (hpres : ∀ i : ℕ, ∀ x : Fin K, vtx hK L S (s i x) = vtx hK L S x)
    (a n : ℕ) :
    ∀ x : Fin K, vtx hK L S (intervalProd s a n x) = vtx hK L S x := by
  induction n generalizing a with
  | zero =>
      intro x
      simp [intervalProd]
  | succ n ih =>
      intro x
      simp only [intervalProd]
      rw [vtx_preserving_mul hK hL hLK S (s a) (intervalProd s (a + 1) n)]
      · exact hpres a x
      · intro y
        exact ih (a := a + 1) y

/-- **The antiderivative preserves `vtx` pointwise.**

For a component coordinate set `B` whose points all lie in the ladder range
of the base chord `(u, v)`, the product of the interval antiderivatives
`g_p = intervalProd (alignedSwap hK ladderP ladderQ) a (b - a)`
over the consecutive pairs `p = (a, b)` of `coordinatePairs B` preserves
`vtx` pointwise:

  `∀ x : Fin K, vtx hK L S ((∏_(p ∈ coordinatePairs B) g_p) x) = vtx hK L S x`.

This is the simple closure of `alignedSwap_preserves_vtx_of_support_chord`
under `Equiv` multiplication and list product.
-/
theorem coordinatePairs_prod_preserves_vtx
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K) (S : Fin K → α)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (σ : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S σ)
    (u v : Fin K) (huv : u ≠ v) (hfx : AltF hK σ u = v)
    (B : Finset ℕ) (hEven : Even B.card)
    (hB : ∀ x ∈ B, x + (L - 1) ≤ maxPairLen hK S u v) :
    ∀ x : Fin K,
      vtx hK L S
        ((coordinatePairs B).map
          (fun p => intervalProd (alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u))
            p.1 (p.2 - p.1))).prod x)
        = vtx hK L S x := by
  let ladderP := maxPairStart hK S u v
  let ladderQ := maxPairStart hK S v u
  have hpres : ∀ i : ℕ, ∀ x : Fin K,
      vtx hK L S (alignedSwap hK ladderP ladderQ i x) = vtx hK L S x := by
    intro i x
    exact alignedSwap_preserves_vtx_of_support_chord hK hL hLK S hprim hP2 hEul huv hfx
      (hB i (by
        have : i ∈ B := by
          apply coordinatePairs_fst_mem B hEven
          simp [coordinatePairs, List.mem_cons]
          left
          rfl
        exact this))
  intro x
  induction (coordinatePairs B) with
  | nil =>
      simp
  | cons p ps ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [vtx_preserving_mul hK hK hLK S _ _]
      · exact intervalProd_preserves_vtx hK hL hLK S hpres p.1 (p.2 - p.1) x
      · exact ih x

end AssemblyP1.Issue94AntiderivativeVtx
