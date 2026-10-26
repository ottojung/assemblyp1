import AssemblyP1.GraverThroughputBridge

set_option autoImplicit false

/-!
# Augmented throughput is determined by the edge displacement (#263)

Small conditional transfer cell for the edge-flow / vertex-throughput Graver
bridge (`AssemblyP1.GraverThroughputBridge`).

For the augmented `[A 0; -T I]` system, the throughput coordinates of any two
feasible points differ exactly by `T` applied to the edge-coordinate
difference.  In particular a feasible *displacement* `y - z` has throughput
coordinates `T` of its edge displacement.  When `T` annihilates the edge
lattice `L₀` (the hypothesis `hT` of
`AssemblyP1.GraverThroughputBridge.hasGraverDecomposition_aug`), every feasible
displacement has *zero* throughput coordinates, which is the fact used inline
there; here it is isolated as a standalone lemma.

This lemma does **not** prove the general `T`-sign-compatible conformal Graver
decomposition (which is obstructed in general: see
`AssemblyP1.ThroughputSignClash263`), nor the #261 historical signed-graph
adapter.  It records the exact bookkeeping on which any such transfer must
build.
-/

namespace AssemblyP1.AugmentedThroughputDetermined263

open AssemblyP1.GraverThroughputBridge
open AssemblyP1.SeparableConvexGraver

variable {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype E] [Fintype V]

/-- For additive `T`, two augmented-feasible points over the same right-hand
side differ in throughput coordinates exactly by `T` of the edge difference. -/
theorem augFeas_throughput_determined (tail head : E → V)
    (T : (E → ℤ) → (V → ℤ))
    (hT_add : ∀ x y, T (x + y) = T x + T y)
    (b : (V ⊕ Unit) ⊕ V → ℤ) (l u : E ⊕ V → ℤ)
    {x y : E ⊕ V → ℤ}
    (hx : Feasible (augLin tail head T) b l u x)
    (hy : Feasible (augLin tail head T) b l u y) :
    ∀ v, y (Sum.inr v) - x (Sum.inr v)
      = T ((fun e => y (Sum.inl e)) - (fun e => x (Sum.inl e))) v := by
  intro v
  have hxv := congrFun hx.1 (Sum.inr v)
  have hyv := congrFun hy.1 (Sum.inr v)
  simp only [augLin, Sum.elim_inr] at hxv hyv
  have hsub := congrFun (T_sub T hT_add
    (fun e => y (Sum.inl e)) (fun e => x (Sum.inl e))) v
  simp only [Pi.sub_apply] at hsub
  omega

/-- Feasible displacements of the augmented system have throughput coordinates
given by `T` of the edge displacement. -/
theorem augDisp_throughput (tail head : E → V)
    (T : (E → ℤ) → (V → ℤ))
    (hT_add : ∀ x y, T (x + y) = T x + T y)
    (b : (V ⊕ Unit) ⊕ V → ℤ) (l u : E ⊕ V → ℤ)
    {x y : E ⊕ V → ℤ}
    (hx : Feasible (augLin tail head T) b l u x)
    (hy : Feasible (augLin tail head T) b l u y) :
    ∀ v, (y - x) (Sum.inr v)
      = T (fun e => (y - x) (Sum.inl e)) v := by
  intro v
  have h := augFeas_throughput_determined tail head T hT_add b l u hx hy v
  have hedge : (fun e => (y - x) (Sum.inl e))
      = (fun e => y (Sum.inl e)) - (fun e => x (Sum.inl e)) := rfl
  rw [hedge]
  simp only [Pi.sub_apply]
  omega

/-- When `T` annihilates the edge lattice displacement, every augmented
feasible displacement has zero throughput coordinates.  This is the exact
corollary consumed (inline) by
`AssemblyP1.GraverThroughputBridge.hasGraverDecomposition_aug`. -/
theorem augDisp_throughput_zero_of_annihilated (tail head : E → V)
    (T : (E → ℤ) → (V → ℤ))
    (hT_add : ∀ x y, T (x + y) = T x + T y)
    (b : (V ⊕ Unit) ⊕ V → ℤ) (l u : E ⊕ V → ℤ)
    {x y : E ⊕ V → ℤ}
    (hx : Feasible (augLin tail head T) b l u x)
    (hy : Feasible (augLin tail head T) b l u y)
    (hT0 : T ((fun e => y (Sum.inl e)) - (fun e => x (Sum.inl e))) = 0) :
    ∀ v, (y - x) (Sum.inr v) = 0 := by
  intro v
  have h := augDisp_throughput tail head T hT_add b l u hx hy v
  have hedge : (fun e => (y - x) (Sum.inl e))
      = (fun e => y (Sum.inl e)) - (fun e => x (Sum.inl e)) := rfl
  rw [hedge, hT0] at h
  simpa using h

end AssemblyP1.AugmentedThroughputDetermined263
