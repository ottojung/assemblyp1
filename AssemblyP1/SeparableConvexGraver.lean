import Mathlib

/-!
# Separable-convex Graver optimality certificates (issue #263)

This file formalizes the convex-objective half of the Graver optimality
certificate, as an independent parallel front to the integer-kernel
conformal-minimal existence proof of #257 and the likelihood maximizers of
#259/#261.  It deliberately does **not** prove any Graver *decomposition*
existence theorem; the main result below is explicitly **conditional** on a
conformal Graver decomposition of every feasible difference, exactly as the
issue requires ("may close as conditional core convex theorem even before
#257's Graver decomposition is integrated").

## Mathematical source

* "Near-Optimal Algorithms for Sparse Separable Convex Integer Programs"
  (Mathematical Programming, 2026), Proposition 3 (the Positive Sum
  Property), https://link.springer.com/article/10.1007/s10107-026-02341-5 :
  for a separable convex objective and sign-compatible (conformal) integer
  increments, the total increment dominates the sum of the individual
  increments.
* The standard Graver optimality certificate (Onn; De Loera–Oebelein–Onn):
  for a separable convex objective over an integer program, a feasible point
  is globally optimal iff no Graver basis element gives a strictly improving
  feasible step.

## Model

* `E` a finite type (the edge / read-type / coordinate set).
* An affine integer fiber `lin z = b` with box `l ≤ z ≤ u` (`Feasible`).
* A separable objective `F z = ∑ e, f e (z e)` with each `f e` discrete
  convex on the box interval (`DiscConvOn`: first differences nondecreasing,
  i.e. discrete second differences nonnegative on the interior).
* `Graver`: nonzero kernel elements that are conformally indecomposable.
* `GraverDecomp z`: every feasible difference `y - z` is a sum of mutually
  sign-compatible Graver moves (the conditional hypothesis).

## What is proved

* `inc_le_inc_of_discConvOn` / `dec_le_dec_of_discConvOn`: increment
  monotonicity for positive / negative steps.
* `superadd_1d`: the one-dimensional Positive Sum Property.
* `superadd_separable`: the Positive Sum Property for separable objectives.
* `graver_optimal_iff_no_improving`: the conditional necessary-and-sufficient
  Graver optimality certificate.
* `multiplier_improving`: an improving integer multiple `α * g` of a Graver
  move already improves the unit step `g`.
-/

namespace AssemblyP1.SeparableConvexGraver

/-! ## Discrete convexity on an integer interval -/

/-- Discrete convexity of `f : ℤ → ℝ` on the integer interval `[lo, hi]`:
the first differences `f (k+1) - f k` are nondecreasing in `k` for
`lo ≤ k` with `k + 1 ≤ hi`.  Equivalently the discrete second differences
`f k - 2 * f (k+1) + f (k+2)` are nonnegative on the interior. -/
def DiscConvOn (f : ℤ → ℝ) (lo hi : ℤ) : Prop :=
  ∀ k l, lo ≤ k → k ≤ l → l + 1 ≤ hi → f (k+1) - f k ≤ f (l+1) - f l

/-- First difference of `f` at `k`. -/
def inc (f : ℤ → ℝ) (k : ℤ) : ℝ := f (k+1) - f k

/-- For a discrete-convex `f`, a nonnegative step from a larger base point
does not decrease the increment. -/
theorem inc_le_inc_of_discConvOn {f : ℤ → ℝ} {lo hi : ℤ} (hf : DiscConvOn f lo hi)
    {z w : ℤ} (hz : lo ≤ z) (hw : lo ≤ w) (hzw : z ≤ w) {n : ℕ}
    (hb : z + n ≤ hi) (hbw : w + n ≤ hi) :
    f (z + n) - f z ≤ f (w + n) - f w := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h1 : inc f (z + ↑m) ≤ inc f (w + ↑m) := by
      exact hf (z + ↑m) (w + ↑m) (by omega) (by omega) (by omega)
    have e1 : f (z + ↑(m + 1)) - f (z + ↑m) = inc f (z + ↑m) := rfl
    have e2 : f (w + ↑(m + 1)) - f (w + ↑m) = inc f (w + ↑m) := rfl
    have h2 : f (z + ↑m) - f z ≤ f (w + ↑m) - f w := ih (by omega) (by omega)
    omega

/-- For a discrete-convex `f`, a nonpositive step from a smaller base point
does not increase the decrement. -/
theorem dec_le_dec_of_discConvOn {f : ℤ → ℝ} {lo hi : ℤ} (hf : DiscConvOn f lo hi)
    {z w : ℤ} (hwz : w ≤ z) (hzh : z ≤ hi) (hlo : lo ≤ w) {n : ℕ}
    (hn : lo ≤ w - n) :
    f w - f (w - n) ≤ f z - f (z - n) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h1 : inc f (w - (m + 1)) ≤ inc f (z - (m + 1)) := by
      exact hf (w - (m + 1)) (z - (m + 1)) (by omega) (by omega) (by omega)
    have e1 : f w - f (w - (m + 1))
        = (f w - f (w - m)) + inc f (w - (m + 1)) := by
      show f w - f (w - (m + 1))
          = (f w - f (w - m)) + (f (w - m) - f (w - (m + 1)))
      ring
    have e2 : f z - f (z - (m + 1))
        = (f z - f (z - m)) + inc f (z - (m + 1)) := by
      show f z - f (z - (m + 1))
          = (f z - f (z - m)) + (f (z - m) - f (z - (m + 1)))
      ring
    rw [e1, e2]
    omega

/-! ## The Positive Sum Property -/

/-- **One-dimensional Positive Sum Property.**  For a discrete-convex
`f : ℤ → ℝ` and same-sign integer steps `h₁, …, hₖ` from a base point `z`
whose whole path stays in `[lo, hi]`, the total increment dominates the sum
of the individual increments:

`f (z + ∑ hⱼ) - f z ≥ ∑ⱼ (f (z + hⱼ) - f z)`. -/
theorem superadd_1d {f : ℤ → ℝ} {lo hi : ℤ} (hf : DiscConvOn f lo hi)
    (z : ℤ) (hs : List ℤ)
    (hsign : (∀ h ∈ hs, 0 ≤ h) ∨ (∀ h ∈ hs, h ≤ 0))
    (hz : lo ≤ z) (hzh : z ≤ hi) (hslo : lo ≤ z + hs.sum) (hshi : z + hs.sum ≤ hi) :
    (∑ h ∈ hs, (f (z + h) - f z)) ≤ f (z + hs.sum) - f z := by
  induction hs with
  | nil => simp
  | cons h rest ih =>
    set s : ℤ := rest.sum with hsdef
    have hsum : z + (h :: rest).sum = z + (h + s) := by simp [hsdef]
    have e1 : f (z + (h + s)) - f z
        = (f (z + h + s) - f (z + s)) + (f (z + s) - f z) := by ring
    rw [hsum, e1]
    cases hsign with
    | inl hpos =>
      have hh : 0 ≤ h := hpos h (by simp)
      have hs' : 0 ≤ s := by
        have hpos' : ∀ h' ∈ rest, 0 ≤ h' := fun h' hh' => hpos h' (by simp [hh'])
        have := List.sum_nonneg hpos'
        simpa [hsdef] using this
      have h1 : f (z + h) - f z ≤ f (z + s + h) - f (z + s) := by
        have heq : ((h.natAbs : ℕ) : ℤ) = h := Int.natAbs_of_nonneg hh
        rw [← heq]
        exact inc_le_inc_of_discConvOn hf hz (by omega) (by omega) (by omega) (by omega)
      have h2 : (∑ h' ∈ rest, (f (z + h') - f z)) ≤ f (z + s) - f z := by
        exact ih (Or.inl fun h' hh' => hpos h' (by simp [hh'])) hz hzh (by omega) (by omega)
      have h3 : (∑ h' ∈ h :: rest, (f (z + h') - f z))
          = (f (z + h) - f z) + ∑ h' ∈ rest, (f (z + h') - f z) := by
        simp [List.sum_cons]
      omega
    | inr hneg =>
      have hh : h ≤ 0 := hneg h (by simp)
      have hs' : s ≤ 0 := by
        have hneg' : ∀ h' ∈ rest, h' ≤ 0 := fun h' hh' => hneg h' (by simp [hh'])
        have := List.sum_nonpos hneg'
        simpa [hsdef] using this
      have h1 : f (z + h + s) - f (z + s) ≥ f (z + h) - f z := by
        have heq : ((h.natAbs : ℕ) : ℤ) = -h := Int.natAbs_of_nonpos hh
        rw [← heq]
        have h2' := dec_le_dec_of_discConvOn hf (by omega) hzh (by omega) (by omega)
        have e : f (z + s - h.natAbs) - f (z + s)
            = -(f (z + s) - f (z + s - h.natAbs)) := by ring
        have e2 : f (z - h.natAbs) - f z = -(f z - f (z - h.natAbs)) := by ring
        rw [e, e2] at h2'
        omega
      have h2 : (∑ h' ∈ rest, (f (z + h') - f z)) ≤ f (z + s) - f z := by
        exact ih (Or.inr fun h' hh' => hneg h' (by simp [hh'])) hz hzh (by omega) (by omega)
      have h3 : (∑ h' ∈ h :: rest, (f (z + h') - f z))
          = (f (z + h) - f z) + ∑ h' ∈ rest, (f (z + h') - f z) := by
        simp [List.sum_cons]
      omega

/-! ## Separable objectives -/

/-- A separable objective `F z = ∑ e, f e (z e)`. -/
def sepObj {E : Type} [Fintype E] (f : E → ℤ → ℝ) (z : E → ℤ) : ℝ :=
  ∑ e, f e (z e)

/-- **Positive Sum Property for separable convex objectives.**  If the
increments `g₁, …, gₖ` are coordinatewise sign-compatible and the path from
`z` to `z + ∑ gⱼ` stays in the box, then

`F (z + ∑ gⱼ) - F z ≥ ∑ⱼ (F (z + gⱼ) - F z)`. -/
theorem superadd_separable {E : Type} [Fintype E] {f : E → ℤ → ℝ}
    {lo hi : ℤ} (hf : ∀ e, DiscConvOn (f e) lo hi)
    (z : E → ℤ) (gs : Finset (E → ℤ))
    (hsign : ∀ e, (∀ g ∈ gs, 0 ≤ g e) ∨ (∀ g ∈ gs, g e ≤ 0))
    (hz : ∀ e, lo ≤ z e) (hzh : ∀ e, z e ≤ hi)
    (hslo : ∀ e, lo ≤ (z + ∑ g ∈ gs, g) e) (hshi : ∀ e, (z + ∑ g ∈ gs, g) e ≤ hi) :
    (∑ g ∈ gs, (sepObj f (z + g) - sepObj f z))
      ≤ sepObj f (z + ∑ g ∈ gs, g) - sepObj f z := by
  have hper : ∀ e, (∑ g ∈ gs, (f e (z e + g e) - f e (z e)))
      ≤ f e (z e + (∑ g ∈ gs, g) e) - f e (z e) := by
    intro e
    set gsList : List ℤ := gs.toList.map (fun g => g e) with hdef
    have hsum : (gsList.sum : ℤ) = (∑ g ∈ gs, g) e := by
      simp [hdef, Finset.sum_toList]
    have hsign' : (∀ h ∈ gsList, 0 ≤ h) ∨ (∀ h ∈ gsList, h ≤ 0) := by
      cases hsign e with
      | inl h =>
        exact Or.inl (by
          intro h hh
          rw [List.mem_map] at hh
          obtain ⟨g, hg, rfl⟩ := hh
          exact h g (by simpa [Finset.mem_toList] using hg))
      | inr h =>
        exact Or.inr (by
          intro h hh
          rw [List.mem_map] at hh
          obtain ⟨g, hg, rfl⟩ := hh
          exact h g (by simpa [Finset.mem_toList] using hg))
    have h1 := superadd_1d (hf e) (z e) gsList hsign' (hz e) (hzh e) (by omega) (by omega)
    rwa [hsum] at h1
  have h2 : ∑ g ∈ gs, (sepObj f (z + g) - sepObj f z)
      = ∑ g ∈ gs, ∑ e, (f e (z e + g e) - f e (z e)) := by
    apply Finset.sum_congr rfl
    intro g _
    show sepObj f (z + g) - sepObj f z = ∑ e, (f e (z e + g e) - f e (z e))
    show (∑ e, f e ((z + g) e)) - (∑ e, f e (z e)) = _
    rw [Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    show f e ((z + g) e) - f e (z e) = f e (z e + g e) - f e (z e)
    rw [Pi.add_apply]
  have h3 : ∑ g ∈ gs, ∑ e, (f e (z e + g e) - f e (z e))
      = ∑ e, ∑ g ∈ gs, (f e (z e + g e) - f e (z e)) := Finset.sum_comm
  have h4 : ∑ e, (f e (z e + (∑ g ∈ gs, g) e) - f e (z e))
      = sepObj f (z + ∑ g ∈ gs, g) - sepObj f z := by
    show ∑ e, (f e ((z + ∑ g ∈ gs, g) e)) - (∑ e, f e (z e)) = _
    rw [Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    show f e ((z + ∑ g ∈ gs, g) e) - f e (z e)
        = f e (z e + (∑ g ∈ gs, g) e) - f e (z e)
    rw [Pi.add_apply]
  rw [h2, h3] at hper ⊢
  rw [h4]
  exact Finset.sum_le_sum (fun e _ => hper e)

/-! ## The conditional Graver optimality certificate -/

section Certificate

variable {E V : Type} [Fintype E] [Fintype V]
variable (lin : (E → ℤ) → (V → ℤ)) (b : V → ℤ) (l u : E → ℤ)

/-- The affine integer fiber with box: `lin z = b` and `l ≤ z ≤ u`. -/
def Feasible (z : E → ℤ) : Prop :=
  lin z = b ∧ ∀ e, l e ≤ z e ∧ z e ≤ u e

/-- Positive part of an integer vector. -/
def posPart (f : E → ℤ) : E → ℤ := fun e => max (f e) 0

/-- Negative part of an integer vector. -/
def negPart (f : E → ℤ) : E → ℤ := fun e => max (-(f e)) 0

/-- The conformal (sign-compatible) order on integer vectors: `g₁ ≼ g₂`
iff the positive and negative parts of `g₁` are coordinatewise bounded by
those of `g₂`. -/
def Conformal (g₁ g₂ : E → ℤ) : Prop :=
  ∀ e, negPart g₁ e ≤ negPart g₂ e ∧ posPart g₁ e ≤ posPart g₂ e

/-- The Graver predicate: nonzero, in the integer kernel of `lin`, and
conformally indecomposable. -/
def Graver (g : E → ℤ) : Prop :=
  lin g = 0 ∧ g ≠ 0 ∧ ∀ g₁ g₂ : E → ℤ,
    lin g₁ = 0 → lin g₂ = 0 → g = g₁ + g₂ →
    Conformal g₁ g → Conformal g₂ g → g₁ = 0 ∨ g₂ = 0

/-- The conformal Graver-decomposition hypothesis: every feasible difference
`y - z` is a sum of mutually sign-compatible Graver moves. -/
def GraverDecomp (z : E → ℤ) : Prop :=
  ∀ y, Feasible lin b l u y → ∃ gs : Finset (E → ℤ),
    (∀ g ∈ gs, Graver lin g) ∧
    (∀ e, (∀ g ∈ gs, 0 ≤ g e) ∨ (∀ g ∈ gs, g e ≤ 0)) ∧
    y = z + ∑ g ∈ gs, g

/-- **Conditional Graver optimality certificate (issue #263).**

Under the conformal Graver-decomposition hypothesis, `z` is a global minimum
of the separable convex objective `F` over the feasible set **iff** no
feasible strictly improving Graver step `z + g` exists.  This is the correct
discrete optimality certificate: the forward direction is the classical
necessity of "no improving Graver move"; the conditional superadditivity
argument gives sufficiency.  It avoids the false necessity of continuous
KKT stationarity (see `AssemblyP1.AAABBBGraverCertificate` for a concrete
instance where the unique discrete maximizer is not a continuous KKT point).
-/
theorem graver_optimal_iff_no_improving
    (hlin : ∀ x y : E → ℤ, lin (x + y) = lin x + lin y)
    (hlin0 : lin 0 = 0)
    {f : E → ℤ → ℝ} (hf : ∀ e, DiscConvOn (f e) (l e) (u e))
    {z : E → ℤ} (hz : Feasible lin b l u z)
    (hdec : GraverDecomp lin b l u z) :
    (∀ w, Feasible lin b l u w → sepObj f z ≤ sepObj f w) ↔
    (∀ g, Graver lin g → Feasible lin b l u (z + g) → sepObj f z ≤ sepObj f (z + g)) := by
  constructor
  · exact fun hopt g _ hfeas => hopt (z + g) hfeas
  · intro hw
    intro w hwfeas
    obtain ⟨gs, hgs, hsign, rfl⟩ := hdec w hwfeas
    have hzg : ∀ g ∈ gs, Feasible lin b l u (z + g) := by
      intro g hg
      refine ⟨?_, ?_⟩
      · show lin (z + g) = b
        have h0 : lin g = 0 := (hgs hg).1
        rw [hlin, hz.1, h0]
        exact hlin0
      · intro e
        have hle : min (z e) (z e + (∑ g' ∈ gs, g') e) ≤ (z + g) e := by
          cases hsign e with
          | inl hpos =>
            have h1 : 0 ≤ g e := hpos g hg
            have h2 : g e ≤ (∑ g' ∈ gs, g') e := by
              refine Finset.single_le_sum hg (fun g' _ => hpos g' ?_)
              exact Finset.mem_toList.mp (Finset.mem_toList.mpr (by
                exact Finset.mem_univ g'))
            have h3 : z e + (∑ g' ∈ gs, g') e = z e + (w e - z e) := by
              have := hwfeas
              simp only [Feasible, and_iff_right True] at this
              simp_all
            omega
          | inr hneg =>
            have h1 : g e ≤ 0 := hneg g hg
            have h2 : (∑ g' ∈ gs, g') e ≤ g e := by
              refine Finset.sum_le_sum (fun g' _ => hneg g' ?_)
              exact Finset.mem_toList.mp (Finset.mem_toList.mpr (by
                exact Finset.mem_univ g'))
            have h3 : z e + (∑ g' ∈ gs, g') e = z e + (w e - z e) := by
              have := hwfeas
              simp only [Feasible, and_iff_right True] at this
              simp_all
            omega
        have hge : (z + g) e ≤ max (z e) (z e + (∑ g' ∈ gs, g') e) := by
          cases hsign e with
          | inl hpos =>
            have h1 : 0 ≤ g e := hpos g hg
            have h2 : g e ≤ (∑ g' ∈ gs, g') e := by
              refine Finset.single_le_sum hg (fun g' _ => hpos g' ?_)
              exact Finset.mem_toList.mp (Finset.mem_toList.mpr (by
                exact Finset.mem_univ g'))
            have h3 : z e + (∑ g' ∈ gs, g') e = z e + (w e - z e) := by
              have := hwfeas
              simp only [Feasible, and_iff_right True] at this
              simp_all
            omega
          | inr hneg =>
            have h1 : g e ≤ 0 := hneg g hg
            have h2 : (∑ g' ∈ gs, g') e ≤ g e := by
              refine Finset.sum_le_sum (fun g' _ => hneg g' ?_)
              exact Finset.mem_toList.mp (Finset.mem_toList.mpr (by
                exact Finset.mem_univ g'))
            have h3 : z e + (∑ g' ∈ gs, g') e = z e + (w e - z e) := by
              have := hwfeas
              simp only [Feasible, and_iff_right True] at this
              simp_all
            omega
        refine ⟨hle, hge⟩
    have hs := superadd_separable hf z gs hsign
      (fun e => (hz.2 e).1) (fun e => (hz.2 e).2)
      (fun e => (hwfeas.2 e).1) (fun e => (hwfeas.2 e).2)
    have hterm : ∀ g ∈ gs, sepObj f (z + g) - sepObj f z ≥ 0 := by
      intro g hg
      have := hw g (hgs hg) (hzg g hg)
      omega
    have hfin : ∑ g ∈ gs, (sepObj f (z + g) - sepObj f z) ≥ 0 :=
      Finset.sum_nonneg hterm
    omega

/-! ## The multiplier lemma -/

/-- **One-dimensional multiplier lemma.**  For a discrete-convex `f`, a
same-sign step `h`, and any `α ≥ 0`, the total increment along `α` copies of
the step dominates `α` times the unit increment:

`f (z + α * h) - f z ≥ α * (f (z + h) - f z)`.

Proved by applying the one-dimensional Positive Sum Property (`superadd_1d`)
to the list of `α` copies of `h`. -/
theorem superadd_1d_multi {f : ℤ → ℝ} {lo hi : ℤ} (hf : DiscConvOn f lo hi)
    (z : ℤ) (h : ℤ) (hsign : 0 ≤ h ∨ h ≤ 0) :
    ∀ α : ℕ, lo ≤ z → z ≤ hi → lo ≤ z + α * h → z + α * h ≤ hi →
      α * (f (z + h) - f z) ≤ f (z + α * h) - f z := by
  intro α hz hzh hlo hhi
  have hsum : (List.replicate α h).sum = α * h := by
    induction α with
    | zero => simp
    | succ m ih => simp [ih, Nat.succ_eq_add_one, add_mul, one_mul]
  have hsign' : (∀ x ∈ List.replicate α h, 0 ≤ x) ∨ (∀ x ∈ List.replicate α h, x ≤ 0) := by
    cases hsign with
    | inl hpos => exact Or.inl (by
      intro x hx
      have hex : x = h := (List.mem_replicate.mp hx).2
      rw [hex]; exact hpos)
    | inr hneg => exact Or.inr (by
      intro x hx
      have hex : x = h := (List.mem_replicate.mp hx).2
      rw [hex]; exact hneg)
  have h1 := superadd_1d hf z (List.replicate α h) hsign' hz hzh
    (by rw [hsum]; exact hlo) (by rw [hsum]; exact hhi)
  have h2 : (∑ x ∈ List.replicate α h, (f (z + x) - f z)) = α * (f (z + h) - f z) := by
    induction α with
    | zero => simp
    | succ m ih => simp [ih, Nat.succ_eq_add_one, add_mul, one_mul]
  rw [h2, hsum] at h1
  exact h1

/-- **Multiplier lemma (issue #263).**  For a separable convex objective,
if an integer multiple `α * g` of a Graver move `g` (with `α ≥ 1` and
`z + g` feasible) strictly improves over `z`, then the unit step `g`
already strictly improves.  The box bounds make the whole path
`z, z + g, …, z + α * g` feasible. -/
theorem multiplier_improving {E : Type} [Fintype E] {f : E → ℤ → ℝ}
    {lo hi : ℤ} (hf : ∀ e, DiscConvOn (f e) lo hi)
    {z : E → ℤ} {g : E → ℤ} {α : ℕ} (hα : 1 ≤ α)
    (hz : ∀ e, lo ≤ z e) (hzh : ∀ e, z e ≤ hi)
    (hlo : ∀ e, lo ≤ (z + α * g) e) (hhi : ∀ e, (z + α * g) e ≤ hi) :
    sepObj f (z + α * g) < sepObj f z → sepObj f (z + g) < sepObj f z := by
  intro himp
  have hper : ∀ e, α * (f e (z e + g e) - f e (z e))
      ≤ f e (z e + α * g e) - f e (z e) := by
    intro e
    have hlo' : lo ≤ z e + α * g e := hlo e
    have hhi' : z e + α * g e ≤ hi := hhi e
    cases lt_or_ge (g e) 0 with
    | inl hneg =>
      have hsign : g e ≤ 0 := by omega
      exact superadd_1d_multi (hf e) (z e) (g e) (Or.inr hsign) α
        (hz e) (hzh e) hlo' hhi'
    | inr hpos =>
      have hsign : 0 ≤ g e := by omega
      exact superadd_1d_multi (hf e) (z e) (g e) (Or.inl hsign) α
        (hz e) (hzh e) hlo' hhi'
  have h1 : sepObj f (z + α * g) - sepObj f z
      = ∑ e, (f e (z e + α * g e) - f e (z e)) := by
    show (∑ e, f e ((z + α * g) e)) - (∑ e, f e (z e)) = _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    rfl
  have h2 : α * (sepObj f (z + g) - sepObj f z)
      = ∑ e, α * (f e (z e + g e) - f e (z e)) := by
    show α * ((∑ e, f e ((z + g) e)) - (∑ e, f e (z e))) = _
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    rfl
  have h3 : ∑ e, α * (f e (z e + g e) - f e (z e))
      ≤ ∑ e, (f e (z e + α * g e) - f e (z e)) :=
    Finset.sum_le_sum (fun i _ => hper i)
  have h4 : α * (sepObj f (z + g) - sepObj f z) ≤ sepObj f (z + α * g) - sepObj f z := by
    rw [h1, h2]
    exact h3
  have hneg : sepObj f (z + α * g) - sepObj f z < 0 := by linarith [himp]
  have h6 : α * (sepObj f (z + g) - sepObj f z) < 0 := by linarith [h4, hneg]
  have h7 : sepObj f (z + g) - sepObj f z < 0 := by
    by_contra hcon
    have hcon' : 0 ≤ sepObj f (z + g) - sepObj f z := not_lt.mp hcon
    have h8 : 0 ≤ α * (sepObj f (z + g) - sepObj f z) :=
      mul_nonneg (Nat.cast_nonneg α) hcon'
    linarith [h6, h8]
  linarith [h7]

end Certificate

end AssemblyP1.SeparableConvexGraver
