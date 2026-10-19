import AssemblyP1.ExactMLOptimizerTransfer
import AssemblyP1.SeparableConvexGraver

/-!
# Optimizer-preserving exact support-restricted Graver certificate (#263)

This module closes the **optimizer-preservation gap** left open by the merged
`AssemblyP1.ExactMLOptimizerTransfer` (PR #357).  There, the merged separable
convex Graver certificate is transferred from the finite secant-slope affine
tail *surrogate* to the genuine extended-real maximum-likelihood objective only
under the explicit hypothesis that the certified minimizer lies in the positive
interior of the box.  That hypothesis is not established there, and the
one-dimensional witness `N = 3, n = 2, x = 1` shows that the affine surrogate
over-admits boundary minimizers (it is constant on `{0,1,2,3}` while the true
ML maximizers are `{1,2}`).

The genuinely new content here is the **exact** treatment of the zero-support
boundary, which needs no finite surrogate at all:

* The **support-restricted admissible box** is
  `lowOf x e ≤ z e ≤ highOf N n x e` where
  `lowOf x e = 1` when `0 < x e` and `0` otherwise, and
  `highOf N n x e = N e - 1` when `0 < n e - x e` and `N e` otherwise.
  It is exactly the set of candidates whose binomial marginal likelihood is
  strictly positive (a zero-likelihood candidate has `z e ≤ 0` with `x e > 0`,
  or `N e ≤ z e` with `n e - x e > 0`).

* **T1 (excluded candidates cannot minimize).**  If a feasible candidate
  violates the support restriction then its exact extended-real objective is
  `⊤` (`+∞` negative log), while any admissible candidate has a finite
  objective.  Hence an excluded candidate is never a global exact-ML
  minimizer, given at least one admissible candidate exists.

* **T2 (optimizer preservation).**  On the admissible box the exact
  extended-real objective agrees with the honest finite interior cost
  `binomCost` (resp. `multinomialCost`); consequently the exact-ML minimizer
  over the admissible box coincides with the minimizer of the finite cost over
  the same box.  Moreover that finite cost is **discretely convex on the
  admissible box** (all four sign patterns of `x` and `n - x` handled
  separately), so the already-merged interior discrete-convex Graver criterion
  `graver_optimal_iff_no_improving` applies **without** the affine surrogate.

* The endpoint `binom_exact_optimal_admissible` /
  `multinomial_exact_optimal_admissible` combine T2 with the merged
  conditional Graver certificate to give a necessary-and-sufficient exact-ML
  optimality certificate on the support-restricted integer fiber.

## Anti-duplication

* The exact extended-real costs `binomExact` / `multinomialExact`, the finite
  interior costs `binomCost` / `multinomialCost`, and `exactObj` are **reused**
  verbatim from `AssemblyP1.ExactMLOptimizerTransfer`; the finite convex
  interior instantiations `binomTerm_discConvOn`, `multinomialTerm_discConvOn`,
  `negLog_discConvOn`, `negLog_sub_discConvOn`, the closure lemmas
  `DiscConvOn.{add,const_mul,const,congr,comp_sub}`, and the abstract
  certificate `graver_optimal_iff_no_improving` are reused verbatim from
  `AssemblyP1.SeparableConvexGraver`.  No theorem of those modules is
  restated, and no definition is changed.
* The positive-observations-require-positive-multiplicity fact is **not**
  re-proved here; it is the elementary `binomExact = ⊤` boundary clause
  already present in `AssemblyP1.ExactMLOptimizerTransfer` and
  `AssemblyP1.Section62BinomialCriterion`.
* The affine-tail surrogate `binomExt` / `multinomialExt` is **never** used as
  if exact: the certificate below is stated for `binomExact` / `multinomialExact`
  directly.

No `axiom`, `sorry`, `admit`, or `native_decide` is used.
-/

set_option autoImplicit false

namespace AssemblyP1.ExactSupportRestrictedGraver

open AssemblyP1.SeparableConvexGraver
open AssemblyP1.ExactMLOptimizerTransfer

variable {E : Type} [Fintype E]

/-! ## The support-restricted admissible box -/

/-- Lower bound of the support-restricted admissible box: `1` where the observed
count is positive (a positive observation forces a positive copy count), `0`
otherwise. -/
def lowOf (x : E → ℤ) (e : E) : ℤ := if 0 < x e then 1 else 0

/-- Upper bound of the support-restricted admissible box: `N - 1` where the
missing count `n - x` is positive (an unobserved copy forces a non-full count),
`N` otherwise. -/
def highOf (N n x : E → ℤ) (e : E) : ℤ := if 0 < n e - x e then N e - 1 else N e

omit [Fintype E] in
theorem lowOf_pos {x : E → ℤ} {e : E} (h : 0 < x e) : lowOf x e = 1 := by
  rw [lowOf]; exact ite_eq_left h

omit [Fintype E] in
theorem lowOf_zero {x : E → ℤ} {e : E} (h : x e ≤ 0) : lowOf x e = 0 := by
  rw [lowOf]; exact ite_eq_right (not_lt.mpr h)

omit [Fintype E] in
theorem highOf_pos {N n x : E → ℤ} {e : E} (h : 0 < n e - x e) :
    highOf N n x e = N e - 1 := by
  rw [highOf]; exact ite_eq_left h

omit [Fintype E] in
theorem highOf_zero {N n x : E → ℤ} {e : E} (h : n e - x e ≤ 0) :
    highOf N n x e = N e := by
  rw [highOf]; exact ite_eq_right (not_lt.mpr h)

/-- The admissible box sits inside the ambient box `[0, N]`. -/
omit [Fintype E] in
theorem lowOf_nonneg {x : E → ℤ} {e : E} : 0 ≤ lowOf x e := by
  rw [lowOf]; split_ifs <;> omega

/-- The admissible box sits inside the ambient box `[0, N]`. -/
omit [Fintype E] in
theorem highOf_le {N n x : E → ℤ} {e : E} : highOf N n x e ≤ N e := by
  rw [highOf]; split_ifs <;> omega

/-! ## T2: the exact objective equals the finite interior cost on the box -/

/-- **T2 (product-binomial).**  On the support-restricted admissible box the
exact extended-real product-binomial objective agrees with the honest finite
interior cost, so `exactObj` is the coercion of `sepObj binomCost`. -/
theorem admissible_binomExact_eq_coe {N x n : E → ℤ} {z : E → ℤ}
    (hz : ∀ e, lowOf x e ≤ z e ∧ z e ≤ highOf N n x e) :
    exactObj (fun e => binomExact (N e) (x e) (n e)) z =
      ((sepObj (fun e => binomCost (N e) (x e) (n e)) z : ℝ) : WithTop ℝ) := by
  unfold exactObj sepObj
  rw [WithTop.coe_sum]
  apply Finset.sum_congr rfl
  intro e _
  have hnot : ¬ ((z e ≤ 0 ∧ 0 < x e) ∨ (N e ≤ z e ∧ 0 < n e - x e)) := by
    have hze : lowOf x e ≤ z e ∧ z e ≤ highOf N n x e := hz e
    by_cases hx : 0 < x e
    · by_cases hnx : 0 < n e - x e
      · rw [lowOf_pos hx, highOf_pos hnx] at hze; omega
      · rw [lowOf_pos hx, highOf_zero (by omega)] at hze; omega
    · by_cases hnx : 0 < n e - x e
      · rw [lowOf_zero (by omega), highOf_pos hnx] at hze; omega
      · rw [lowOf_zero (by omega), highOf_zero (by omega)] at hze; omega
  unfold binomExact
  dsimp only
  rw [ite_eq_right hnot]

/-- **T2 (product-binomial, comparison form).**  Two admissible candidates are
ordered by the exact objective exactly when they are ordered by the finite
interior cost. -/
theorem admissible_binom_exact_le_iff_cost_le {N x n : E → ℤ} {z w : E → ℤ}
    (hz : ∀ e, lowOf x e ≤ z e ∧ z e ≤ highOf N n x e)
    (hw : ∀ e, lowOf x e ≤ w e ∧ w e ≤ highOf N n x e) :
    exactObj (fun e => binomExact (N e) (x e) (n e)) z ≤
        exactObj (fun e => binomExact (N e) (x e) (n e)) w ↔
      sepObj (fun e => binomCost (N e) (x e) (n e)) z ≤
        sepObj (fun e => binomCost (N e) (x e) (n e)) w := by
  rw [admissible_binomExact_eq_coe (N := N) (x := x) (n := n) hz,
    admissible_binomExact_eq_coe (N := N) (x := x) (n := n) hw]
  exact WithTop.coe_le_coe

/-- **T2 (multinomial).**  On the support-restricted admissible box the exact
extended-real multinomial objective agrees with the honest finite cost. -/
theorem admissible_multinomialExact_eq_coe {G x : E → ℤ} {z : E → ℤ}
    (hz : ∀ e, lowOf x e ≤ z e ∧ z e ≤ G e) :
    exactObj (fun e => multinomialExact (G e) (x e)) z =
      ((sepObj (fun e => multinomialCost (G e) (x e)) z : ℝ) : WithTop ℝ) := by
  unfold exactObj sepObj
  rw [WithTop.coe_sum]
  apply Finset.sum_congr rfl
  intro e _
  have hnot : ¬ (z e ≤ 0 ∧ 0 < x e) := by
    have hze : lowOf x e ≤ z e ∧ z e ≤ G e := hz e
    by_cases hx : 0 < x e
    · rw [lowOf_pos hx] at hze; omega
    · omega
  unfold multinomialExact
  dsimp only
  rw [ite_eq_right hnot]

/-- **T2 (multinomial, comparison form).** -/
theorem admissible_multinomial_exact_le_iff_cost_le {G x : E → ℤ} {z w : E → ℤ}
    (hz : ∀ e, lowOf x e ≤ z e ∧ z e ≤ G e)
    (hw : ∀ e, lowOf x e ≤ w e ∧ w e ≤ G e) :
    exactObj (fun e => multinomialExact (G e) (x e)) z ≤
        exactObj (fun e => multinomialExact (G e) (x e)) w ↔
      sepObj (fun e => multinomialCost (G e) (x e)) z ≤
        sepObj (fun e => multinomialCost (G e) (x e)) w := by
  rw [admissible_multinomialExact_eq_coe (G := G) (x := x) hz,
    admissible_multinomialExact_eq_coe (G := G) (x := x) hw]
  exact WithTop.coe_le_coe

/-! ## T1: excluded (zero-likelihood) candidates cannot minimize -/

/-- **T1 (product-binomial).**  A candidate that is not in the admissible box
has a zero-likelihood marginal, hence exact objective `⊤`. -/
theorem excluded_binom_exact_eq_top {N x n : E → ℤ} {z : E → ℤ}
    (hexcl : ∃ e, (0 < x e ∧ z e ≤ 0) ∨ (0 < n e - x e ∧ N e ≤ z e)) :
    exactObj (fun e => binomExact (N e) (x e) (n e)) z = ⊤ := by
  unfold exactObj
  rw [WithTop.sum_eq_top]
  obtain ⟨e, he⟩ := hexcl
  exact ⟨e, Finset.mem_univ e, by
    unfold binomExact
    dsimp only
    rcases he with ⟨hx, hz0⟩ | ⟨hnx, hzN⟩
    · rw [ite_eq_left (Or.inl ⟨hz0, hx⟩)]
    · rw [ite_eq_left (Or.inr ⟨hzN, hnx⟩)]⟩

/-- **T1 (product-binomial, minimizer form).**  Given an admissible candidate,
an excluded candidate is strictly worse, so it is not a global exact-ML
minimizer. -/
theorem excluded_binom_not_minimizer {V : Type}
    (N x n : E → ℤ) (lin : (E → ℤ) → (V → ℤ)) (b : V → ℤ)
    {z : E → ℤ} (hz : Feasible lin b (fun _ => 0) (fun e => N e) z)
    (hexcl : ∃ e, (0 < x e ∧ z e ≤ 0) ∨ (0 < n e - x e ∧ N e ≤ z e))
    {w : E → ℤ} (_hw : Feasible lin b (fun _ => 0) (fun e => N e) w)
    (hwadm : ∀ e, lowOf x e ≤ w e ∧ w e ≤ highOf N n x e) :
    exactObj (fun e => binomExact (N e) (x e) (n e)) w <
      exactObj (fun e => binomExact (N e) (x e) (n e)) z := by
  rw [excluded_binom_exact_eq_top (N := N) (x := x) (n := n) hexcl]
  have hwfin : exactObj (fun e => binomExact (N e) (x e) (n e)) w ≠ ⊤ := by
    rw [admissible_binomExact_eq_coe (N := N) (x := x) (n := n) hwadm]
    exact WithTop.lt_top_iff_ne_top.mp
      (WithTop.coe_lt_top (sepObj (fun e => binomCost (N e) (x e) (n e)) w))
  exact WithTop.lt_top_iff_ne_top.mpr hwfin

/-- **T1 (multinomial).**  A candidate with a zero copy count at a positive
observation has exact objective `⊤`. -/
theorem excluded_multinomial_exact_eq_top {G x : E → ℤ} {z : E → ℤ}
    (hexcl : ∃ e, 0 < x e ∧ z e ≤ 0) :
    exactObj (fun e => multinomialExact (G e) (x e)) z = ⊤ := by
  unfold exactObj
  rw [WithTop.sum_eq_top]
  obtain ⟨e, he⟩ := hexcl
  exact ⟨e, Finset.mem_univ e, by
    unfold multinomialExact
    dsimp only
    rw [ite_eq_left (And.comm.mp he)]⟩

/-- **T1 (multinomial, minimizer form).** -/
theorem excluded_multinomial_not_minimizer {V : Type}
    (G x : E → ℤ) (lin : (E → ℤ) → (V → ℤ)) (b : V → ℤ)
    {z : E → ℤ} (hz : Feasible lin b (fun _ => 0) (fun e => G e) z)
    (hexcl : ∃ e, 0 < x e ∧ z e ≤ 0)
    {w : E → ℤ} (_hw : Feasible lin b (fun _ => 0) (fun e => G e) w)
    (hwadm : ∀ e, lowOf x e ≤ w e ∧ w e ≤ G e) :
    exactObj (fun e => multinomialExact (G e) (x e)) w <
      exactObj (fun e => multinomialExact (G e) (x e)) z := by
  rw [excluded_multinomial_exact_eq_top (G := G) (x := x) hexcl]
  have hwfin : exactObj (fun e => multinomialExact (G e) (x e)) w ≠ ⊤ := by
    rw [admissible_multinomialExact_eq_coe (G := G) (x := x) hwadm]
    exact WithTop.lt_top_iff_ne_top.mp
      (WithTop.coe_lt_top (sepObj (fun e => multinomialCost (G e) (x e)) w))
  exact WithTop.lt_top_iff_ne_top.mpr hwfin

/-! ## T2 (convexity): the finite interior cost is discretely convex on the box -/

/-- `d ↦ -log (N - d)` is discretely convex on `[0, N-1]` (the left endpoint is
honest because `N - d > 0` there). -/
omit [Fintype E] in
theorem negLog_sub_discConvOn_zero (N : ℤ) :
    DiscConvOn (fun d : ℤ => -Real.log ((N : ℝ) - (d : ℝ))) 0 (N - 1) := by
  have h := (negLog_discConvOn N).comp_sub (c := N)
  have hNN : (N : ℤ) - N = 0 := by ring
  rw [hNN] at h
  simpa only [Int.cast_sub] using h

/-- **T2 (product-binomial convexity on the admissible box).**  The honest
finite product-binomial cost `binomCost N x n` is discretely convex on the
support-restricted admissible box `(lowOf x, highOf N n x)`, in all four sign
patterns of `x` and `n - x`. -/
omit [Fintype E] in
theorem binomCost_admissible_discConvOn (N x n : E → ℤ) (hx : ∀ e, 0 ≤ x e)
    (hxn : ∀ e, x e ≤ n e) :
    ∀ e, DiscConvOn (binomCost (N e) (x e) (n e)) (lowOf x e) (highOf N n x e) := by
  intro e
  have hx_e : 0 ≤ x e := hx e
  have hxn_e : x e ≤ n e := hxn e
  by_cases hx0 : 0 < x e
  · by_cases hnx : 0 < n e - x e
    · -- box [1, N-1]
      rw [lowOf_pos hx0, highOf_pos hnx]
      rcases lt_or_ge (N e) 2 with hN | hN
      · intro a b ha hab hb; omega
      · exact binomTerm_discConvOn (N e) hN (x e) (n e) hx_e hxn_e
    · -- box [1, N]
      rw [lowOf_pos hx0, highOf_zero (by omega)]
      rcases lt_or_ge (N e) 1 with hN | hN
      · intro a b ha hab hb; omega
      · have h1 : DiscConvOn (fun d : ℤ => (x e : ℝ) * -Real.log (d : ℝ)) 1 (N e) :=
          (negLog_discConvOn (N e)).const_mul (c := (x e : ℝ)) (by exact_mod_cast hx e)
        have h2 : DiscConvOn (fun _ : ℤ => (x e : ℝ) * Real.log ((N e : ℝ))) 1 (N e) :=
          DiscConvOn.const
        refine DiscConvOn.congr (g := fun d : ℤ =>
          (x e : ℝ) * -Real.log (d : ℝ) + (x e : ℝ) * Real.log ((N e : ℝ))) ?_ (h1.add h2)
        intro d _ hdN
        have hnx0 : n e - x e = 0 := by omega
        have hN0 : (N e : ℝ) ≠ 0 := by
          have : (0 : ℝ) < (N e : ℝ) := by exact_mod_cast (show 0 < N e by omega)
          exact this.ne'
        have hd0 : (d : ℝ) ≠ 0 := by
          have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
          exact this.ne'
        unfold binomCost
        rw [hnx0]
        simp only [Int.cast_zero, zero_mul, sub_zero, Real.log_div hd0 hN0]
        ring
  · -- x e = 0
    have hx0' : x e = 0 := by omega
    by_cases hnx : 0 < n e - x e
    · -- box [0, N-1]
      rw [lowOf_zero (by omega), highOf_pos hnx]
      rcases lt_or_ge (N e) 1 with hN | hN
      · intro a b ha hab hb; omega
      · have h0 : DiscConvOn (fun d : ℤ => -Real.log ((N e : ℝ) - (d : ℝ))) 0 (N e - 1) :=
          negLog_sub_discConvOn_zero (N e)
        have h1 : DiscConvOn
            (fun d : ℤ => ((n e : ℤ) : ℝ) * -Real.log ((N e : ℝ) - (d : ℝ))) 0 (N e - 1) :=
          h0.const_mul (c := ((n e : ℤ) : ℝ)) (by exact_mod_cast (by omega : 0 ≤ n e))
        have h2 : DiscConvOn (fun _ : ℤ => ((n e : ℤ) : ℝ) * Real.log ((N e : ℝ))) 0 (N e - 1) :=
          DiscConvOn.const
        refine DiscConvOn.congr (g := fun d : ℤ =>
          ((n e : ℤ) : ℝ) * -Real.log ((N e : ℝ) - (d : ℝ))
            + ((n e : ℤ) : ℝ) * Real.log ((N e : ℝ))) ?_ (h1.add h2)
        intro d _ hdN
        have hN0 : (N e : ℝ) ≠ 0 := by
          have : (0 : ℝ) < (N e : ℝ) := by exact_mod_cast (show 0 < N e by omega)
          exact this.ne'
        have hNd : ((N e : ℝ) - (d : ℝ)) ≠ 0 := by
          have : (d : ℝ) < (N e : ℝ) := by exact_mod_cast (show d < N e by omega)
          have : (0 : ℝ) < (N e : ℝ) - (d : ℝ) := by linarith
          exact this.ne'
        unfold binomCost
        rw [hx0']
        simp only [sub_zero, one_sub_div hN0, Real.log_div hNd hN0]
        push_cast
        ring
    · -- box [0, N], the cost is identically 0
      rw [lowOf_zero (by omega), highOf_zero (by omega)]
      have h : DiscConvOn (fun _ : ℤ => (0 : ℝ)) 0 (N e) := DiscConvOn.const
      refine DiscConvOn.congr (g := fun _ : ℤ => (0 : ℝ)) ?_ h
      intro d _ _
      have hx0'' : x e = 0 := by omega
      have hn0 : n e = 0 := by omega
      unfold binomCost
      rw [hx0'', hn0]
      simp

/-- **T2 (multinomial convexity on the admissible box).**  The honest finite
multinomial cost `multinomialCost G x` is discretely convex on
`(lowOf x, G)`. -/
omit [Fintype E] in
theorem multinomialCost_admissible_discConvOn (G x : E → ℤ) (hx : ∀ e, 0 ≤ x e) :
    ∀ e, DiscConvOn (multinomialCost (G e) (x e)) (lowOf x e) (G e) := by
  intro e
  have hx_e : 0 ≤ x e := hx e
  by_cases hx0 : 0 < x e
  · rw [lowOf_pos hx0]
    rcases lt_or_ge (G e) 1 with hG | hG
    · intro a b ha hab hb; omega
    · exact multinomialTerm_discConvOn (G e) hG (x e) hx_e (G e)
  · rw [lowOf_zero (by omega)]
    have h : DiscConvOn (fun _ : ℤ => (0 : ℝ)) 0 (G e) := DiscConvOn.const
    refine DiscConvOn.congr (g := fun _ : ℤ => (0 : ℝ)) ?_ h
    intro d _ _
    have hx0' : x e = 0 := by omega
    unfold multinomialCost
    rw [hx0']
    simp

/-! ## The exact-ML Graver certificate on the support-restricted fiber -/

/-- **Exact product-binomial ML Graver certificate (issue #263, T1+T2).**  On
the support-restricted admissible integer fiber, `z` minimizes the exact
extended-real product-binomial ML objective over the whole admissible box iff no
feasible Graver move strictly improves the honest finite interior cost.  This
uses the merged `graver_optimal_iff_no_improving` with `binomCost` (not the
affine-tail surrogate) and the T2 agreement on the admissible box. -/
theorem binom_exact_optimal_admissible {V : Type}
    (N x n : E → ℤ) (hx : ∀ e, 0 ≤ x e) (hxn : ∀ e, x e ≤ n e)
    (lin : (E → ℤ) → (V → ℤ)) (b : V → ℤ) (Graver : (E → ℤ) → Prop)
    (hlin_add : ∀ p q : E → ℤ, lin (p + q) = lin p + lin q)
    (hker : ∀ g, Graver g → lin g = 0)
    {z : E → ℤ}
    (hz : Feasible lin b (lowOf x) (highOf N n x) z)
    (hdec : HasGraverDecomposition lin b (lowOf x) (highOf N n x) Graver z)
    (hno : ∀ g, Graver g → Feasible lin b (lowOf x) (highOf N n x) (z + g) →
      sepObj (fun e => binomCost (N e) (x e) (n e)) z ≤
        sepObj (fun e => binomCost (N e) (x e) (n e)) (z + g)) :
    ∀ w, Feasible lin b (lowOf x) (highOf N n x) w →
      exactObj (fun e => binomExact (N e) (x e) (n e)) z ≤
        exactObj (fun e => binomExact (N e) (x e) (n e)) w := by
  intro w hw
  have hzbox : ∀ e, lowOf x e ≤ z e ∧ z e ≤ highOf N n x e := fun e => hz.2 e
  have hwbox : ∀ e, lowOf x e ≤ w e ∧ w e ≤ highOf N n x e := fun e => hw.2 e
  rw [admissible_binom_exact_le_iff_cost_le (N := N) (x := x) (n := n) hzbox hwbox]
  exact ((graver_optimal_iff_no_improving lin b (lowOf x) (highOf N n x) Graver
    hlin_add hker (binomCost_admissible_discConvOn N x n hx hxn) hz hdec).mpr hno) w hw

/-- **Exact multinomial ML Graver certificate (issue #263, T1+T2).** -/
theorem multinomial_exact_optimal_admissible {V : Type}
    (G x : E → ℤ) (hx : ∀ e, 0 ≤ x e)
    (lin : (E → ℤ) → (V → ℤ)) (b : V → ℤ) (Graver : (E → ℤ) → Prop)
    (hlin_add : ∀ p q : E → ℤ, lin (p + q) = lin p + lin q)
    (hker : ∀ g, Graver g → lin g = 0)
    {z : E → ℤ}
    (hz : Feasible lin b (lowOf x) (fun e => G e) z)
    (hdec : HasGraverDecomposition lin b (lowOf x) (fun e => G e) Graver z)
    (hno : ∀ g, Graver g → Feasible lin b (lowOf x) (fun e => G e) (z + g) →
      sepObj (fun e => multinomialCost (G e) (x e)) z ≤
        sepObj (fun e => multinomialCost (G e) (x e)) (z + g)) :
    ∀ w, Feasible lin b (lowOf x) (fun e => G e) w →
      exactObj (fun e => multinomialExact (G e) (x e)) z ≤
        exactObj (fun e => multinomialExact (G e) (x e)) w := by
  intro w hw
  have hzbox : ∀ e, lowOf x e ≤ z e ∧ z e ≤ G e := fun e => hz.2 e
  have hwbox : ∀ e, lowOf x e ≤ w e ∧ w e ≤ G e := fun e => hw.2 e
  rw [admissible_multinomial_exact_le_iff_cost_le (G := G) (x := x) hzbox hwbox]
  exact ((graver_optimal_iff_no_improving lin b (lowOf x) (fun e => G e) Graver
    hlin_add hker (multinomialCost_admissible_discConvOn G x hx) hz hdec).mpr hno) w hw

end AssemblyP1.ExactSupportRestrictedGraver
