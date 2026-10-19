import AssemblyP1.SeparableConvexGraver
import AssemblyP1.GraverThroughputBridge

set_option autoImplicit false

/-!
# Exact-ML optimizer preservation for the affine-tail Graver certificate (#263)

The merged separable-convex Graver certificate
`AssemblyP1.SeparableConvexGraver.graver_optimal_iff_no_improving` (PR #305/#331)
and its source-likelihood instantiations `multinomialTerm_ext_discConvOn` /
`binomTerm_ext_discConvOn` certify a minimizer of the **finite secant-slope
affine-tail extension** of the negative-log-likelihood cost on the full
candidate box `[0, G]` resp. `[0, N]`.  That extension is a *regularized
surrogate*: at a zero-probability endpoint (`d = 0` with `x > 0`, or `d = N`
with `n - x > 0`) the genuine extended-real negative log is `+∞`, while
`affineExtend` assigns a finite secant value.  The transfer of optimality from
the extension to the **true extended-real maximum-likelihood objective** was
left explicitly OPEN (see `docs/issue263-separable-convex-graver-certificate.md`,
"Source-fidelity caveat").

This module closes that gap **conditionally**, with a single explicit
optimizer-preservation hypothesis: the certified minimizer lies in the positive
interior of the box.  The transfer is the elementary inequality

```text
exact(w) ≥ extension(w) ≥ extension(z) = exact(z)        (all feasible w),
```

where the second inequality is the merged Graver criterion applied to the
*extension* over the full box, and the first is the honest fact that the
affine extension never exceeds the true extended-real cost (it is `⊤` at
zero-likelihood endpoints, and the secant tail lies below the convex interior
cost at the remaining endpoints).  No `sorry`, `admit`, `axiom`, or
`native_decide` is used, and no definition of the merged modules is changed.

## Model and objective

* `E` a finite type of read classes; `exactObj g z = ∑ e, g e (z e)` is the
  separable extended-real objective with values in `WithTop ℝ`.
* `binomCost N x n d = -x·log(d/N) - (n-x)·log(1 - d/N)` is the finite
  product-binomial negative log on the positive interior `0 < d < N`;
  `binomExt N x n = affineExtend (binomCost N x n) 1 (N-1)` is its secant-slope
  affine-tail extension to all of `ℤ`, already proved discretely convex on
  `[0, N]` (`binomTerm_ext_discConvOn`).
* `binomExact N x n d = ⊤` at a zero-probability endpoint, and
  `↑(binomCost N x n d)` otherwise.  This is the genuine extended-real
  negative log (up to the candidate-independent constant, which does not move
  the minimizer).
* `multinomialCost G x d = -x·log(d/G)` and `multinomialExact G x d` are the
  fixed-total analogues.

## Main results

* `exact_minimizer_of_ext_minimizer` — the generic transfer: if `z` is in the
  box interior, minimizes a finite separable objective `f` over a feasible set
  `P`, and the extended-real objective `g` dominates `↑f` pointwise while
  agreeing with it at interior points, then `z` minimizes `g` over `P`.
* `graver_exact_optimal_of_no_improving` — the same, with "minimizes `f`"
  replaced by "no improving feasible Graver move", using the merged
  `graver_optimal_iff_no_improving`.
* `binomExact_dom_ext`, `binomExact_eq_ext` — the pointwise domination and
  interior agreement for the product-binomial cost.
* `multinomialExact_dom_ext`, `multinomialExact_eq_ext` — the multinomial
  analogues.
* `binom_exact_optimal_flow` — the concrete edge-flow instantiation: the
  merged edge-flow Graver criterion (`GraverThroughputBridge`) yields a true
  minimizer of the exact extended-real product-binomial ML objective whenever
  the certified minimizer is interior.

## Remaining open gap

The hypothesis that the affine-tail minimizer is **interior** is *not*
established here.  The extension may be minimized only at a zero-probability
endpoint, in which case no interior optimizer exists and this transfer does not
apply; conversely an interior extension minimizer is a genuine exact-ML
optimizer by the results below.  Determining when the extension has an interior
minimizer (equivalently, excluding over-admission of boundary minimizers) is a
separate question, deliberately left OPEN.
-/

namespace AssemblyP1.ExactMLOptimizerTransfer

open AssemblyP1.SeparableConvexGraver
open AssemblyP1.GraverThroughputBridge
open AssemblyP1.GraverRigidity

/-! ## Generic optimizer-preservation transfer -/

/-- The separable extended-real objective `∑ e, g e (z e)`, with values in
`WithTop ℝ` (so `⊤` models a `+∞` negative-log cost at a zero-likelihood
candidate). -/
noncomputable def exactObj {E : Type} [Fintype E] (g : E → ℤ → WithTop ℝ)
    (z : E → ℤ) : WithTop ℝ :=
  ∑ e, g e (z e)

/-- **Generic optimizer-preservation transfer.**  Let `P` be a feasible set
contained in the box `l ≤ · ≤ u`, `f` a finite separable objective, and `g` an
extended-real separable objective that dominates `↑f` pointwise on the box and
agrees with it at every interior point of `z`.  If `z` is interior and minimizes
`f` over `P`, then `z` minimizes the extended-real `g` over `P`. -/
theorem exact_minimizer_of_ext_minimizer {E : Type} [Fintype E]
    {l u : E → ℤ} {f : E → ℤ → ℝ} {g : E → ℤ → WithTop ℝ} {z : E → ℤ}
    (P : (E → ℤ) → Prop)
    (hPbox : ∀ w, P w → ∀ e, l e ≤ w e ∧ w e ≤ u e)
    (hdom : ∀ e d, l e ≤ d → d ≤ u e → ((f e d : ℝ) : WithTop ℝ) ≤ g e d)
    (hagree : ∀ e, l e < z e → z e < u e →
      g e (z e) = ((f e (z e) : ℝ) : WithTop ℝ))
    (hzint : ∀ e, l e < z e ∧ z e < u e)
    (hmin : ∀ w, P w → sepObj f z ≤ sepObj f w) :
    ∀ w, P w → exactObj g z ≤ exactObj g w := by
  intro w hw
  have hzcast : exactObj g z = ((sepObj f z : ℝ) : WithTop ℝ) := by
    unfold exactObj sepObj
    rw [WithTop.coe_sum]
    exact Finset.sum_congr rfl (fun e _ => hagree e (hzint e).1 (hzint e).2)
  have hwcast : ((sepObj f w : ℝ) : WithTop ℝ) ≤ exactObj g w := by
    unfold exactObj sepObj
    rw [WithTop.coe_sum]
    exact Finset.sum_le_sum (fun e _ =>
      hdom e (w e) (hPbox w hw e).1 (hPbox w hw e).2)
  calc exactObj g z = ((sepObj f z : ℝ) : WithTop ℝ) := hzcast
    _ ≤ ((sepObj f w : ℝ) : WithTop ℝ) := by
        exact WithTop.coe_le_coe.mpr (hmin w hw)
    _ ≤ exactObj g w := hwcast

/-- **Exact-ML Graver criterion.**  Under the merged conditional Graver
optimality certificate, if `z` is interior and no feasible Graver move improves
the finite separable objective `f`, then `z` minimizes the extended-real
objective `g` over the whole feasible fiber.  This is
`exact_minimizer_of_ext_minimizer` with the "minimizes `f`" hypothesis supplied
by `graver_optimal_iff_no_improving`. -/
theorem graver_exact_optimal_of_no_improving {E V : Type} [Fintype E]
    (lin : (E → ℤ) → (V → ℤ)) (b : V → ℤ) (l u : E → ℤ) (Graver : (E → ℤ) → Prop)
    (hlin_add : ∀ x y : E → ℤ, lin (x + y) = lin x + lin y)
    (hker : ∀ g, Graver g → lin g = 0)
    {f : E → ℤ → ℝ} (hf : ∀ e, DiscConvOn (f e) (l e) (u e))
    {g : E → ℤ → WithTop ℝ}
    (hdom : ∀ e d, l e ≤ d → d ≤ u e → ((f e d : ℝ) : WithTop ℝ) ≤ g e d)
    {z : E → ℤ}
    (hagree : ∀ e, l e < z e → z e < u e →
      g e (z e) = ((f e (z e) : ℝ) : WithTop ℝ))
    (hz : Feasible lin b l u z)
    (hzint : ∀ e, l e < z e ∧ z e < u e)
    (hdec : HasGraverDecomposition lin b l u Graver z)
    (hno : ∀ g', Graver g' → Feasible lin b l u (z + g') →
      sepObj f z ≤ sepObj f (z + g')) :
    ∀ w, Feasible lin b l u w → exactObj g z ≤ exactObj g w :=
  exact_minimizer_of_ext_minimizer (Feasible lin b l u) (fun _ hw => hw.2)
    hdom hagree hzint
    ((graver_optimal_iff_no_improving lin b l u Graver hlin_add hker hf hz hdec).mpr hno)

/-! ## Product-binomial exact extended-real objective -/

/-- The finite fixed-external-`N` product-binomial negative-log term in the
candidate copy count `d`, on the positive interior `0 < d < N` (where the two
logarithms are honest). -/
noncomputable def binomCost (N x n : ℤ) (d : ℤ) : ℝ :=
  -(x : ℝ) * Real.log ((d : ℝ) / (N : ℝ))
    - ((n - x : ℤ) : ℝ) * Real.log (1 - (d : ℝ) / (N : ℝ))

/-- The secant-slope affine-tail extension of `binomCost N x n` from the exact
interval `[1, N-1]` to all of `ℤ`. -/
noncomputable def binomExt (N x n : ℤ) : ℤ → ℝ :=
  affineExtend (binomCost N x n) 1 (N - 1)

/-- The genuine extended-real product-binomial negative log: `⊤` at a
zero-probability endpoint (`d ≤ 0` with `x > 0`, or `N ≤ d` with `n - x > 0`),
and the finite cost otherwise. -/
noncomputable def binomExact (N x n : ℤ) : ℤ → WithTop ℝ :=
  fun d => if (d ≤ 0 ∧ 0 < x) ∨ (N ≤ d ∧ 0 < n - x) then ⊤
    else ((binomCost N x n d : ℝ) : WithTop ℝ)

/-- Discrete convexity of the affine-tail extension on the full box `[0, N]`
(`N ≥ 3`), reused verbatim from the merged `binomTerm_ext_discConvOn`. -/
theorem binomExt_discConvOn (N : ℤ) (hN : 3 ≤ N) (x n : ℤ) (hx : 0 ≤ x)
    (hxn : x ≤ n) :
    DiscConvOn (binomExt N x n) 0 N := by
  unfold binomExt binomCost
  exact binomTerm_ext_discConvOn N hN x n hx hxn

/-- The affine-tail extension is exact on the interior `[1, N-1]`. -/
theorem binomExt_eq_cost_of_interior (N x n : ℤ) {d : ℤ}
    (h1 : 1 ≤ d) (h2 : d ≤ N - 1) :
    binomExt N x n d = binomCost N x n d := by
  unfold binomExt
  rcases eq_or_lt_of_le h1 with h | h
  · rw [← h, affineExtend_of_le (le_refl (1 : ℤ))]
    simp
  · rw [affineExtend_of_le_U h h2]

/-- The extended-real product-binomial objective agrees with the extension on
the interior `[1, N-1]`. -/
theorem binomExact_eq_ext (N x n : ℤ) {d : ℤ} (h1 : 1 ≤ d) (h2 : d ≤ N - 1) :
    binomExact N x n d = ((binomExt N x n d : ℝ) : WithTop ℝ) := by
  have hnot : ¬ ((d ≤ 0 ∧ 0 < x) ∨ (N ≤ d ∧ 0 < n - x)) := by omega
  unfold binomExact
  rw [ite_eq_right hnot, binomExt_eq_cost_of_interior N x n h1 h2]

/-! ### Boundary domination for the product-binomial extension

The affine extension is a *lower* bound for the genuine finite cost at the two
positive-likelihood endpoints.  Both endpoints reduce to the single elementary
logarithm inequality `log(1 - 2/N) ≤ 2·log(1 - 1/N)` for `N ≥ 3`. -/

/-- Elementary logarithm inequality: `log (1 - 2/N) ≤ 2 log (1 - 1/N)` for
`N ≥ 3`.  Equivalent to `1 - 2/N ≤ (1 - 1/N)²`. -/
theorem log_one_sub_two_le (N : ℤ) (hN : 3 ≤ N) :
    Real.log (1 - 2 / (N : ℝ)) ≤ 2 * Real.log (1 - 1 / (N : ℝ)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show (1 : ℤ) < N by omega)
  have hN2 : (2 : ℝ) < (N : ℝ) := by exact_mod_cast (show (2 : ℤ) < N by omega)
  have hpos1 : (0 : ℝ) < 1 - 1 / (N : ℝ) := by
    rw [sub_pos, div_lt_one hNpos]; exact hN1
  have hpos2 : (0 : ℝ) < 1 - 2 / (N : ℝ) := by
    rw [sub_pos, div_lt_one hNpos]; exact hN2
  have hsq : 1 - 2 / (N : ℝ) ≤ (1 - 1 / (N : ℝ)) ^ 2 := by
    have hdiff : (1 - 1 / (N : ℝ)) ^ 2 - (1 - 2 / (N : ℝ)) = (1 / (N : ℝ)) ^ 2 := by ring
    nlinarith [sq_nonneg (1 / (N : ℝ))]
  have h := Real.log_le_log hpos2 hsq
  rwa [Real.log_pow] at h

/-- Value of the extension at the left endpoint `d = 0`, in terms of the first
two interior cost values. -/
theorem binomExt_zero_eq (N x n : ℤ) :
    binomExt N x n 0 = 2 * binomCost N x n 1 - binomCost N x n 2 := by
  unfold binomExt
  rw [affineExtend_of_le (show (0 : ℤ) ≤ 1 by norm_num)]
  push_cast
  ring

/-- Value of the extension at the right endpoint `d = N`, in terms of the last
two interior cost values. -/
theorem binomExt_N_eq (N x n : ℤ) (hN : 2 ≤ N) :
    binomExt N x n N = 2 * binomCost N x n (N - 1) - binomCost N x n (N - 2) := by
  unfold binomExt
  rw [affineExtend_of_ge (by omega) (by omega)]
  push_cast
  ring

/-- At the left endpoint with `x = 0` the extension lies below the genuine
finite cost `binomCost N 0 n 0 = 0`. -/
theorem binomExt_zero_le (N n : ℤ) (hN : 3 ≤ N) (hn : 0 ≤ n) :
    binomExt N 0 n 0 ≤ binomCost N 0 n 0 := by
  have hlog := log_one_sub_two_le N hN
  have hNpos : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    exact this.ne'
  have hc0 : binomCost N 0 n 0 = 0 := by
    unfold binomCost; simp
  have hc1 : binomCost N 0 n 1 = -((n : ℝ) * Real.log (1 - 1 / (N : ℝ))) := by
    unfold binomCost
    have harg : ((1 : ℤ) : ℝ) / (N : ℝ) = 1 / (N : ℝ) := by push_cast; ring
    rw [harg]; push_cast; ring
  have hc2 : binomCost N 0 n 2 = -((n : ℝ) * Real.log (1 - 2 / (N : ℝ))) := by
    unfold binomCost
    have harg : ((2 : ℤ) : ℝ) / (N : ℝ) = 2 / (N : ℝ) := by push_cast; ring
    rw [harg]; push_cast; ring
  rw [binomExt_zero_eq, hc0, hc1, hc2]
  have hprod : (0 : ℝ) ≤ (n : ℝ) * (2 * Real.log (1 - 1 / (N : ℝ)) - Real.log (1 - 2 / (N : ℝ))) :=
    mul_nonneg (by exact_mod_cast hn) (by linarith [hlog])
  nlinarith [hprod]

/-- At the right endpoint with `x = n` the extension lies below the genuine
finite cost `binomCost N n n N = 0`. -/
theorem binomExt_N_le (N x : ℤ) (hN : 3 ≤ N) (hx : 0 ≤ x) :
    binomExt N x x N ≤ binomCost N x x N := by
  have hlog := log_one_sub_two_le N hN
  have hN2 : 2 ≤ N := by omega
  have hNpos : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    exact this.ne'
  have hcN : binomCost N x x N = 0 := by
    unfold binomCost; simp
  have hc1 : binomCost N x x (N - 1)
      = -((x : ℝ) * Real.log (1 - 1 / (N : ℝ))) := by
    unfold binomCost
    have harg : ((N - 1 : ℤ) : ℝ) / (N : ℝ) = 1 - 1 / (N : ℝ) := by
      rw [one_sub_div hNpos]; push_cast; ring
    rw [harg]; push_cast; ring
  have hc2 : binomCost N x x (N - 2)
      = -((x : ℝ) * Real.log (1 - 2 / (N : ℝ))) := by
    unfold binomCost
    have harg : ((N - 2 : ℤ) : ℝ) / (N : ℝ) = 1 - 2 / (N : ℝ) := by
      rw [one_sub_div hNpos]; push_cast; ring
    rw [harg]; push_cast; ring
  rw [binomExt_N_eq N x x hN2, hcN, hc1, hc2]
  have hprod : (0 : ℝ) ≤ (x : ℝ) * (2 * Real.log (1 - 1 / (N : ℝ)) - Real.log (1 - 2 / (N : ℝ))) :=
    mul_nonneg (by exact_mod_cast hx) (by linarith [hlog])
  nlinarith [hprod]

/-- **Pointwise domination.**  On the full box `[0, N]` the affine-tail
extension is dominated (as an extended-real value) by the genuine extended-real
product-binomial cost. -/
theorem binomExact_dom_ext (N x n : ℤ) (hN : 3 ≤ N) (hx : 0 ≤ x) (hxn : x ≤ n) :
    ∀ d, 0 ≤ d → d ≤ N → ((binomExt N x n d : ℝ) : WithTop ℝ) ≤ binomExact N x n d := by
  intro d hd0 hdN
  by_cases hzl : (d ≤ 0 ∧ 0 < x) ∨ (N ≤ d ∧ 0 < n - x)
  · unfold binomExact; rw [ite_eq_left hzl]; exact le_top
  · unfold binomExact; rw [ite_eq_right hzl]
    have hle : binomExt N x n d ≤ binomCost N x n d := by
      rcases lt_or_ge d 1 with hlt | hge
      · have hd_eq : d = 0 := by omega
        subst hd_eq
        have hx0 : x = 0 := by
          by_contra hxne
          exact hzl (Or.inl ⟨le_refl 0, lt_of_le_of_ne hx (Ne.symm hxne)⟩)
        subst hx0
        exact binomExt_zero_le N n hN (by omega)
      · rcases lt_or_ge (N - 1) d with hgt | hle'
        · have hd_eq : d = N := by omega
          rw [hd_eq]
          have hxn' : x = n := by omega
          rw [hxn']
          exact binomExt_N_le N n hN (by omega)
        · exact le_of_eq (binomExt_eq_cost_of_interior N x n hge hle')
    exact WithTop.coe_le_coe.mpr hle

/-! ## Multinomial (fixed total) exact extended-real objective -/

/-- The finite fixed-total multinomial negative-log term `-x·log(d/G)` in the
candidate copy count `d`, honest on `d ≥ 1`. -/
noncomputable def multinomialCost (G x : ℤ) (d : ℤ) : ℝ :=
  -(x : ℝ) * Real.log ((d : ℝ) / (G : ℝ))

/-- The secant-slope affine-tail extension of `multinomialCost G x` from
`[1, G]` to all of `ℤ`. -/
noncomputable def multinomialExt (G x : ℤ) : ℤ → ℝ :=
  affineExtend (multinomialCost G x) 1 G

/-- The genuine extended-real multinomial negative log: `⊤` at `d ≤ 0` with
`x > 0`, and the finite cost otherwise. -/
noncomputable def multinomialExact (G x : ℤ) : ℤ → WithTop ℝ :=
  fun d => if d ≤ 0 ∧ 0 < x then ⊤ else ((multinomialCost G x d : ℝ) : WithTop ℝ)

/-- Discrete convexity of the affine-tail extension on the full box `[0, G]`
(`G ≥ 2`), reused from `multinomialTerm_ext_discConvOn`. -/
theorem multinomialExt_discConvOn (G : ℤ) (hG : 2 ≤ G) (x : ℤ) (hx : 0 ≤ x) :
    DiscConvOn (multinomialExt G x) 0 G := by
  unfold multinomialExt multinomialCost
  exact multinomialTerm_ext_discConvOn G hG x hx

/-- The affine-tail extension is exact on the interior `[1, G]`. -/
theorem multinomialExt_eq_cost (G x : ℤ) {d : ℤ} (h1 : 1 ≤ d) (h2 : d ≤ G) :
    multinomialExt G x d = multinomialCost G x d := by
  unfold multinomialExt
  rcases eq_or_lt_of_le h1 with h | h
  · rw [← h, affineExtend_of_le (le_refl (1 : ℤ))]; simp
  · rcases eq_or_lt_of_le h2 with hG | hG
    · rw [hG, affineExtend_of_ge (by omega) (le_refl G)]; simp
    · rw [affineExtend_of_le_U h (le_of_lt hG)]

/-- The extended-real multinomial objective agrees with the extension on the
interior `[1, G-1]`. -/
theorem multinomialExact_eq_ext (G x : ℤ) {d : ℤ} (h1 : 1 ≤ d) (h2 : d ≤ G - 1) :
    multinomialExact G x d = ((multinomialExt G x d : ℝ) : WithTop ℝ) := by
  have hnot : ¬ (d ≤ 0 ∧ 0 < x) := by omega
  unfold multinomialExact
  rw [ite_eq_right hnot, multinomialExt_eq_cost G x h1 (by omega)]

/-- At `d = 0` with `x = 0` the multinomial extension equals the genuine finite
cost `multinomialCost G 0 0 = 0`. -/
theorem multinomialExt_zero_eq (G : ℤ) :
    multinomialExt G 0 0 = multinomialCost G 0 0 := by
  have h1 : multinomialExt G 0 0
      = 2 * multinomialCost G 0 1 - multinomialCost G 0 2 := by
    unfold multinomialExt
    rw [affineExtend_of_le (show (0 : ℤ) ≤ 1 by norm_num)]
    push_cast; ring
  have e0 : multinomialCost G 0 0 = 0 := by unfold multinomialCost; simp
  have e1 : multinomialCost G 0 1 = 0 := by unfold multinomialCost; simp
  have e2 : multinomialCost G 0 2 = 0 := by unfold multinomialCost; simp
  rw [h1, e0, e1, e2]; ring

/-- **Pointwise domination.**  On the full box `[0, G]` the affine-tail
extension is dominated by the genuine extended-real multinomial cost. -/
theorem multinomialExact_dom_ext (G x : ℤ) (hx : 0 ≤ x) :
    ∀ d, 0 ≤ d → d ≤ G →
      ((multinomialExt G x d : ℝ) : WithTop ℝ) ≤ multinomialExact G x d := by
  intro d hd0 hdG
  by_cases hzl : d ≤ 0 ∧ 0 < x
  · unfold multinomialExact; rw [ite_eq_left hzl]; exact le_top
  · unfold multinomialExact; rw [ite_eq_right hzl]
    have hle : multinomialExt G x d ≤ multinomialCost G x d := by
      rcases lt_or_ge d 1 with hlt | hge
      · have hd_eq : d = 0 := by omega
        subst hd_eq
        have hx0 : x = 0 := by
          by_contra hxne
          exact hzl ⟨le_refl 0, lt_of_le_of_ne hx (Ne.symm hxne)⟩
        subst hx0
        exact le_of_eq (multinomialExt_zero_eq G)
      · exact le_of_eq (multinomialExt_eq_cost G x hge hdG)
    exact WithTop.coe_le_coe.mpr hle

/-! ## Separable exact-ML optimality over the full box -/

/-- **Product-binomial exact-ML optimizer from the merged affine-tail criterion.**
For the fixed-external-`N` product-binomial separable objective, if `z` is in the
positive interior `0 < z e < N e` and no feasible Graver move improves the
affine-tail extension `binomExt`, then `z` minimizes the genuine extended-real
ML objective `binomExact` over the whole feasible fiber. -/
theorem binom_separable_exact_optimal {E V : Type} [Fintype E]
    (N x n : E → ℤ) (hN : ∀ e, 3 ≤ N e) (hx : ∀ e, 0 ≤ x e) (hxn : ∀ e, x e ≤ n e)
    (lin : (E → ℤ) → (V → ℤ)) (b : V → ℤ) (Graver : (E → ℤ) → Prop)
    (hlin_add : ∀ p q : E → ℤ, lin (p + q) = lin p + lin q)
    (hker : ∀ g, Graver g → lin g = 0)
    {z : E → ℤ}
    (hz : Feasible lin b (fun _ => 0) (fun e => N e) z)
    (hzint : ∀ e, 0 < z e ∧ z e < N e)
    (hdec : HasGraverDecomposition lin b (fun _ => 0) (fun e => N e) Graver z)
    (hno : ∀ g, Graver g → Feasible lin b (fun _ => 0) (fun e => N e) (z + g) →
      sepObj (fun e => binomExt (N e) (x e) (n e)) z ≤
      sepObj (fun e => binomExt (N e) (x e) (n e)) (z + g)) :
    ∀ w, Feasible lin b (fun _ => 0) (fun e => N e) w →
      exactObj (fun e => binomExact (N e) (x e) (n e)) z ≤
      exactObj (fun e => binomExact (N e) (x e) (n e)) w := by
  refine graver_exact_optimal_of_no_improving lin b (fun _ => 0) (fun e => N e) Graver
    hlin_add hker ?_ ?_ ?_ hz hzint hdec hno
  · intro e
    exact binomExt_discConvOn (N e) (hN e) (x e) (n e) (hx e) (hxn e)
  · intro e d h0 hN'
    exact binomExact_dom_ext (N e) (x e) (n e) (hN e) (hx e) (hxn e) d h0 hN'
  · intro e h1 h2
    exact binomExact_eq_ext (N e) (x e) (n e) (by omega) (by omega)

/-- **Edge-flow product-binomial exact-ML optimizer.**  The same as
`binom_separable_exact_optimal` with the `HasGraverDecomposition` hypothesis
discharged by the merged `AssemblyP1.GraverThroughputBridge.hasGraverDecomposition_flow`
(#343): the merged edge-flow Graver criterion yields a true minimizer of the
exact extended-real product-binomial ML objective whenever the certified
minimizer is interior. -/
theorem binom_exact_optimal_flow {V E : Type} [DecidableEq V] [DecidableEq E]
    [Fintype E] [Fintype V]
    (tail head : E → V) (N x n : E → ℤ)
    (hN : ∀ e, 3 ≤ N e) (hx : ∀ e, 0 ≤ x e) (hxn : ∀ e, x e ≤ n e)
    (b : V ⊕ Unit → ℤ) {z : E → ℤ}
    (hz : Feasible (flowLin tail head) b (fun _ => 0) (fun e => N e) z)
    (hzint : ∀ e, 0 < z e ∧ z e < N e)
    (hno : ∀ g, Graver tail head Finset.univ g →
      Feasible (flowLin tail head) b (fun _ => 0) (fun e => N e) (z + g) →
      sepObj (fun e => binomExt (N e) (x e) (n e)) z ≤
      sepObj (fun e => binomExt (N e) (x e) (n e)) (z + g)) :
    ∀ w, Feasible (flowLin tail head) b (fun _ => 0) (fun e => N e) w →
      exactObj (fun e => binomExact (N e) (x e) (n e)) z ≤
      exactObj (fun e => binomExact (N e) (x e) (n e)) w :=
  binom_separable_exact_optimal N x n hN hx hxn (flowLin tail head) b
    (Graver tail head Finset.univ) (flowLin_add tail head)
    (fun _ hg => graver_flowLin_eq_zero tail head hg)
    hz hzint (hasGraverDecomposition_flow tail head b (fun _ => 0) (fun e => N e) hz) hno

end AssemblyP1.ExactMLOptimizerTransfer
