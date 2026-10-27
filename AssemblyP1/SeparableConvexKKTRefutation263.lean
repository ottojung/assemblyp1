import Mathlib

set_option autoImplicit false

/-!
# Unconstrained KKT non-stationarity at the discrete multinomial MLE (issue #263)

This file is the final analytic piece of the separable-convex Graver optimality
certificate front (#263).  It does **not** duplicate the integer-kernel
conformal-minimal existence proof of #257 (`AssemblyP1.GraverRigidity`), the
likelihood maximizers of #259/#261, or the historical signed-graph adapter
(deliberately left OPEN).  It proves, in elementary real analysis, the precise
sense in which the discrete certificate
`AssemblyP1.SeparableConvexGraver.graver_optimal_iff_no_improving` is
**necessary and sufficient** while continuous KKT stationarity is **false**:

* For the fixed-total multinomial negative-log cost
  `F(d) = -x * log (d / G)` in one candidate copy count `d` (with read count
  `x > 0` and total `G ≠ 0`), the unconstrained partial derivative at *every*
  interior point is `-x / d < 0` (`mlCost_slope_neg`), hence **never zero**
  (`mlCost_slope_ne_zero`).  In particular the unconstrained gradient does not
  vanish at the discrete optimum: naive "gradient = 0" stationarity fails on a
  discrete lattice, exactly as the board #259 discussion observes.
* The *constrained* (fixed-total) stationarity **does** hold at `d = x`: every
  coordinate slope equals `-1` (`mlCost_slope_at_truth`), i.e. all partial
  derivatives agree up to the single simplex multiplier.  This separates the
  true constrained KKT condition from the false unconstrained one.
* The concrete four-class instance uses the AAABBB `L = 2` truth spectrum
  `B1 = [2, 1, 2, 1]` proved feasible in `AssemblyP1.FixedXExactML` (with total
  `G = 6`): every coordinate slope at the truth is `-1`
  (`truth_coord_slope`), so the unconstrained gradient `(-1, -1, -1, -1)` is
  nonzero (`truth_gradient_ne_zero`) although the truth is the discrete
  maximizer.  The general lemmas cover any positive read counts, including the
  board's `x = [3, 1, 2, 1]` instance shape.

## Sources

* The separable-convex certificate and its multinomial instantiation
  (`multinomialTerm_discConvOn`) in `AssemblyP1.SeparableConvexGraver`;
  the cost below is its real-analytic continuation in one coordinate.
* Board #259 comment: the AAABBB `G = 6` truth is the discrete unique maximizer
  but the continuous KKT gradient is not zero.
-/

namespace AssemblyP1.KKTRefutation263

/-- Fixed-total multinomial negative-log cost in one candidate copy count `d`:
read count `x`, fixed total `G`.  This is the real-analytic continuation of one
summand of the separable objective certified discretely convex on the positive
interior by `AssemblyP1.SeparableConvexGraver.multinomialTerm_discConvOn`. -/
noncomputable def mlCost (x G : ℝ) (d : ℝ) : ℝ := -x * Real.log (d / G)

/-- The partial derivative of the one-coordinate multinomial cost is `-x / d`. -/
theorem hasDerivAt_mlCost {x G d : ℝ} (hd : d ≠ 0) (hG : G ≠ 0) :
    HasDerivAt (mlCost x G) (-x / d) d := by
  have hdiv : HasDerivAt (fun d : ℝ => d / G) (1 / G) d :=
    (hasDerivAt_id d).div_const G
  have h := (hdiv.log (div_ne_zero hd hG)).const_mul (-x)
  have heq : -x * ((1 / G) / (d / G)) = -x / d := by
    field_simp [hd, hG]
    ring
  rw [heq] at h
  exact h

/-- `deriv` form of the coordinate slope. -/
theorem deriv_mlCost_eq {x G d : ℝ} (hd : d ≠ 0) (hG : G ≠ 0) :
    deriv (mlCost x G) d = -x / d :=
  (hasDerivAt_mlCost hd hG).deriv

/-- At every interior point with positive read count, the unconstrained
coordinate slope is strictly negative. -/
theorem mlCost_slope_neg {x G d : ℝ} (hx : 0 < x) (hd : 0 < d) (hG : G ≠ 0) :
    deriv (mlCost x G) d < 0 := by
  rw [deriv_mlCost_eq hd.ne' hG]
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hx) hd

/-- **No false KKT stationarity.**  The unconstrained coordinate slope never
vanishes at any interior point with positive read count — in particular not at
a discrete optimum. -/
theorem mlCost_slope_ne_zero {x G d : ℝ} (hx : 0 < x) (hd : 0 < d)
    (hG : G ≠ 0) : deriv (mlCost x G) d ≠ 0 :=
  ne_of_lt (mlCost_slope_neg hx hd hG)

/-- **True constrained stationarity.**  At `d = x` every coordinate slope equals
`-1`: all partial derivatives agree, i.e. the fixed-total KKT condition holds
with the single simplex multiplier. -/
theorem mlCost_slope_at_truth {x G : ℝ} (hx : x ≠ 0) (hG : G ≠ 0) :
    deriv (mlCost x G) x = -1 := by
  rw [deriv_mlCost_eq hx hG, neg_div_self hx]

/-- Read-count vector of the AAABBB `L = 2` truth spectrum (`B1` in
`AssemblyP1.FixedXExactML`, proved feasible there). -/
def truthCounts : Fin 4 → ℝ := ![2, 1, 2, 1]

/-- The four truth read counts, by kernel computation. -/
theorem truthCounts_zero : truthCounts 0 = 2 := rfl

/-- The four truth read counts, by kernel computation. -/
theorem truthCounts_one : truthCounts 1 = 1 := rfl

/-- The four truth read counts, by kernel computation. -/
theorem truthCounts_two : truthCounts 2 = 2 := rfl

/-- The four truth read counts, by kernel computation. -/
theorem truthCounts_three : truthCounts 3 = 1 := rfl

/-- Every truth read count is positive. -/
theorem truthCounts_pos (i : Fin 4) : 0 < truthCounts i := by
  fin_cases i
  · show (0:ℝ) < 2; norm_num
  · show (0:ℝ) < 1; norm_num
  · show (0:ℝ) < 2; norm_num
  · show (0:ℝ) < 1; norm_num

/-- At the truth, every coordinate slope of the `G = 6` multinomial cost is
`-1`: constrained stationarity holds while the unconstrained gradient
`(-1, -1, -1, -1)` is nonzero. -/
theorem truth_coord_slope (i : Fin 4) :
    deriv (mlCost (truthCounts i) 6) (truthCounts i) = -1 := by
  apply mlCost_slope_at_truth
  · exact ne_of_gt (truthCounts_pos i)
  · norm_num

/-- **The discrete maximizer is not an unconstrained stationary point.**
Some coordinate slope at the truth is nonzero (indeed every one equals `-1`). -/
theorem truth_gradient_ne_zero :
    ∃ i : Fin 4, deriv (mlCost (truthCounts i) 6) (truthCounts i) ≠ 0 := by
  exact ⟨0, by rw [truth_coord_slope]; norm_num⟩

end AssemblyP1.KKTRefutation263
