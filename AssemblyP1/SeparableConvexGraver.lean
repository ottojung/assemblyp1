import Mathlib

set_option autoImplicit false

/-!
# Separable-convex Graver optimality certificate (issue #263)

This file formalizes the **convex-objective half** of the Graver optimality
certificate for a separable convex integer program, as an independent parallel
front to the integer-kernel conformal-minimal existence proof of #257
(`AssemblyP1.GraverRigidity`) and the likelihood maximizers of #259/#261.

The file deliberately does **not** prove any Graver *decomposition* existence
theorem: the main result `graver_optimal_iff_no_improving` is explicitly
**conditional** on a conformal Graver decomposition of every feasible
displacement, exactly as issue #263 permits ("may close as conditional core
convex theorem even before #257's Graver decomposition is integrated").  The
decomposition hypothesis has precisely the shape produced by
`AssemblyP1.GraverRigidity.graver_decomposition`, namely a `List` of Graver
moves that are coordinatewise sign-compatible with the total displacement and
sum to it; using a `List` (rather than a `Finset`) is essential because a
conformal decomposition may repeat a Graver move.

## Mathematical source

* Hunkenschröder, Koutecký, Levin, Vu, *(Near)-Optimal algorithms for sparse
  separable convex integer programs*, Mathematical Programming (2026),
  **Proposition 1** (separable-convex superadditivity for same-orthant
  increments and nonnegative integer coefficients) and **Proposition 3**
  (conformal positive-sum decomposition of integer kernel moves into Graver
  elements), https://link.springer.com/article/10.1007/s10107-026-02341-5 .
* The standard Graver optimality certificate (Onn; De Loera–Oebelein–Onn):
  for a separable convex objective over an integer program, a feasible point
  is globally optimal **iff** no Graver basis element gives a strictly
  improving feasible step.
* Hemmecke, Onn, Weismantel, *A polynomial oracle-time algorithm for convex
  integer minimization*, arXiv:0710.3003, Mathematical Programming 126 (2011).

## Model

* `E` a finite coordinate type (edges / read types).
* An affine integer fiber `lin z = b` with coordinatewise box `l ≤ z ≤ u`
  (`Feasible`).
* A separable objective `sepObj f z = ∑ e, f e (z e)` where each `f e` is
  discrete convex on the box interval `[l e, u e]` (`DiscConvOn`: first
  differences are nondecreasing).
* `Graver` is an abstract predicate on `E → ℤ`; the only structural facts used
  are that its elements lie in the kernel of `lin` (`hker`) and that every
  feasible displacement admits a sign-compatible `List` decomposition into
  Graver moves (`HasGraverDecomposition`).

## Main results

* `inc_mono`: monotonicity of finite differences.
* `quad_pos` / `quad_neg`: the two-step discrete convex quadrangle inequality.
* `superadd_list`: the one-dimensional Positive Sum Property (Prop. 1).
* `superadd_separable_list`: the separable Positive Sum Property.
* `graver_optimal_iff_no_improving`: the conditional necessary-and-sufficient
  Graver optimality certificate (minimization form, `F z ≤ F (z + g)`).
* `multiplier_improving`: an improving integer Graver ray `α • g` forces the
  unit step `g` to improve.
-/

namespace AssemblyP1.SeparableConvexGraver

/-! ## Discrete convexity on an integer interval -/

/-- Forward difference of `f : ℤ → ℝ` at `k`. -/
def inc (f : ℤ → ℝ) (k : ℤ) : ℝ := f (k + 1) - f k

/-- Discrete convexity of `f : ℤ → ℝ` on the integer interval `[lo, hi]`: the
forward differences `inc f` are nondecreasing.  Equivalently the discrete
second differences are nonnegative on the interior. -/
def DiscConvOn (f : ℤ → ℝ) (lo hi : ℤ) : Prop :=
  ∀ a b : ℤ, lo ≤ a → a ≤ b → b + 1 ≤ hi → inc f a ≤ inc f b

/-! ## Monotone finite differences -/

/-- For a discrete-convex `f`, a fixed nonnegative step from a larger base
point has a larger increment. -/
theorem inc_mono {f : ℤ → ℝ} {lo hi : ℤ} (hf : DiscConvOn f lo hi)
    {a b : ℤ} (ha : lo ≤ a) (hab : a ≤ b) {n : ℕ} (hb : b + (n : ℤ) ≤ hi) :
    f (a + (n : ℤ)) - f a ≤ f (b + (n : ℤ)) - f b := by
  have htel_a : f (a + (n : ℤ)) - f a
      = ∑ i ∈ Finset.range n, (f (a + ((i + 1 : ℕ) : ℤ)) - f (a + (i : ℤ))) := by
    have h := Finset.sum_range_sub (fun i : ℕ => f (a + (i : ℤ))) n
    simpa using h.symm
  have htel_b : f (b + (n : ℤ)) - f b
      = ∑ i ∈ Finset.range n, (f (b + ((i + 1 : ℕ) : ℤ)) - f (b + (i : ℤ))) := by
    have h := Finset.sum_range_sub (fun i : ℕ => f (b + (i : ℤ))) n
    simpa using h.symm
  rw [htel_a, htel_b]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i < n := Finset.mem_range.mp hi
  have hstep : inc f (a + (i : ℤ)) ≤ inc f (b + (i : ℤ)) :=
    hf (a + (i : ℤ)) (b + (i : ℤ)) (by omega) (by omega) (by omega)
  simp only [inc] at hstep
  have e1 : a + ((i + 1 : ℕ) : ℤ) = a + (i : ℤ) + 1 := by push_cast; ring
  have e2 : b + ((i + 1 : ℕ) : ℤ) = b + (i : ℤ) + 1 := by push_cast; ring
  rw [e1, e2]
  exact hstep

/-! ## Two-step quadrangle inequality -/

/-- Discrete convex quadrangle inequality for two nonnegative steps. -/
theorem quad_pos {f : ℤ → ℝ} {lo hi : ℤ} (hf : DiscConvOn f lo hi)
    {z a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hzlo : lo ≤ z) (hchi : z + a + b ≤ hi) :
    f (z + a) + f (z + b) ≤ f z + f (z + a + b) := by
  have hbcast : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg hb
  have h := inc_mono hf (a := z) (b := z + a) (ha := hzlo) (hab := by omega)
    (n := b.toNat) (hb := by rw [hbcast]; omega)
  rw [hbcast] at h
  linarith

/-- Reflection preserves discrete convexity (interval `[lo,hi]` maps to
`[-hi,-lo]`). -/
theorem discConvOn_neg {f : ℤ → ℝ} {lo hi : ℤ} (hf : DiscConvOn f lo hi) :
    DiscConvOn (fun t : ℤ => f (-t)) (-hi) (-lo) := by
  intro a b ha hab hb
  have h := hf (-b - 1) (-a - 1) (by omega) (by omega) (by omega)
  simp only [inc] at h ⊢
  ring_nf at h ⊢
  linarith

/-- Discrete convex quadrangle inequality for two nonpositive steps. -/
theorem quad_neg {f : ℤ → ℝ} {lo hi : ℤ} (hf : DiscConvOn f lo hi)
    {z a b : ℤ} (ha : a ≤ 0) (hb : b ≤ 0)
    (hzhi : z ≤ hi) (hclo : lo ≤ z + a + b) :
    f (z + a) + f (z + b) ≤ f z + f (z + a + b) := by
  have h := quad_pos (discConvOn_neg hf) (z := -z) (a := -a) (b := -b)
    (by omega) (by omega) (by omega) (by omega)
  simpa only [neg_add, neg_neg, add_comm, add_left_comm, add_assoc] using h

/-- A nonpositive list of integers has nonpositive sum. -/
theorem list_sum_nonpos_int {l : List ℤ} (h : ∀ x ∈ l, x ≤ 0) : l.sum ≤ 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.sum_cons]
    have ht := ih (fun x hx => h x (by simp [hx]))
    have ha := h a (by simp)
    omega

/-! ## One-dimensional Positive Sum Property -/

/-- The one-dimensional Positive Sum Property (Prop. 1): for a discrete-convex
`f` and a `List` of same-sign integer steps whose path stays in `[lo, hi]`, the
total increment dominates the sum of the individual increments. -/
theorem superadd_list {f : ℤ → ℝ} {lo hi : ℤ} (hf : DiscConvOn f lo hi)
    (z : ℤ) (hs : List ℤ)
    (hsign : (∀ h ∈ hs, 0 ≤ h) ∨ (∀ h ∈ hs, h ≤ 0))
    (hzlo : lo ≤ z) (hzhi : z ≤ hi)
    (hclo : lo ≤ z + hs.sum) (hchi : z + hs.sum ≤ hi) :
    (hs.map (fun h => f (z + h) - f z)).sum ≤ f (z + hs.sum) - f z := by
  induction hs with
  | nil => simp
  | cons h rest ih =>
    rw [List.sum_cons] at hclo hchi
    simp only [List.map_cons, List.sum_cons]
    have hsign_rest : (∀ h' ∈ rest, 0 ≤ h') ∨ (∀ h' ∈ rest, h' ≤ 0) := by
      rcases hsign with hp | hn
      · exact Or.inl (fun h' hh' => hp h' (by simp [hh']))
      · exact Or.inr (fun h' hh' => hn h' (by simp [hh']))
    have hgoal : z + (h + rest.sum) = z + h + rest.sum := by ring
    rw [hgoal]
    rcases hsign with hp | hn
    · have hh : 0 ≤ h := hp h (by simp)
      have hsr : 0 ≤ rest.sum := List.sum_nonneg (fun x hx => hp x (by simp [hx]))
      have hlo_s : lo ≤ z + rest.sum := by omega
      have hhi_s : z + rest.sum ≤ hi := by omega
      have ih' := ih hsign_rest hlo_s hhi_s
      have hquad : f (z + h) + f (z + rest.sum) ≤ f z + f (z + h + rest.sum) :=
        quad_pos hf hh hsr hzlo (by omega)
      linarith
    · have hh : h ≤ 0 := hn h (by simp)
      have hsr : rest.sum ≤ 0 := list_sum_nonpos_int (fun x hx => hn x (by simp [hx]))
      have hlo_s : lo ≤ z + rest.sum := by omega
      have hhi_s : z + rest.sum ≤ hi := by omega
      have ih' := ih hsign_rest hlo_s hhi_s
      have hquad : f (z + h) + f (z + rest.sum) ≤ f z + f (z + h + rest.sum) :=
        quad_neg hf hh hsr hzhi (by omega)
      linarith

/-! ## Separable objectives -/

/-- A separable objective `sepObj f z = ∑ e, f e (z e)`. -/
def sepObj {E : Type} [Fintype E] (f : E → ℤ → ℝ) (z : E → ℤ) : ℝ :=
  ∑ e, f e (z e)

/-- `List.sum` of a pointwise function family is the pointwise sum of the
coordinate values. -/
theorem list_sum_apply {E : Type} (gs : List (E → ℤ)) (e : E) :
    (gs.map (fun g => g e)).sum = (gs.sum) e := by
  induction gs with
  | nil => simp
  | cons g rest ih => simp [List.sum_cons, ih]

/-- Sums over a `List` and a `Finset` commute. -/
theorem list_sum_finset_sum {E : Type} [Fintype E] {M : Type} [AddCommMonoid M]
    (gs : List (E → ℤ)) (φ : (E → ℤ) → E → M) :
    (gs.map (fun g => ∑ e, φ g e)).sum = ∑ e, (gs.map (fun g => φ g e)).sum := by
  induction gs with
  | nil => simp
  | cons g rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, Finset.sum_add_distrib]

/-- If `a` is a member of a nonnegative integer list then `a` is at most the
list sum. -/
theorem list_le_sum_of_mem_int {l : List ℤ} {a : ℤ} (ha : a ∈ l)
    (hnn : ∀ x ∈ l, 0 ≤ x) : a ≤ l.sum := by
  induction l with
  | nil => simp at ha
  | cons b t ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp ha with rfl | ha'
    · have h : 0 ≤ t.sum := List.sum_nonneg (fun x hx => hnn x (by simp [hx]))
      omega
    · have hb : 0 ≤ b := hnn b (by simp)
      have h : a ≤ t.sum := ih ha' (fun x hx => hnn x (by simp [hx]))
      omega

/-- If `a` is a member of a nonpositive integer list then `a` is at least the
list sum. -/
theorem list_sum_le_of_mem_int {l : List ℤ} {a : ℤ} (ha : a ∈ l)
    (hnp : ∀ x ∈ l, x ≤ 0) : l.sum ≤ a := by
  induction l with
  | nil => simp at ha
  | cons b t ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp ha with rfl | ha'
    · have h : t.sum ≤ 0 := list_sum_nonpos_int (fun x hx => hnp x (by simp [hx]))
      omega
    · have hb : b ≤ 0 := hnp b (by simp)
      have h : t.sum ≤ a := ih ha' (fun x hx => hnp x (by simp [hx]))
      omega

/-- The separable Positive Sum Property: if the moves `gs` are coordinatewise
sign-compatible and the path from `z` to `z + gs.sum` stays in the box, then
the total objective increment dominates the sum of the individual increments. -/
theorem superadd_separable_list {E : Type} [Fintype E] {f : E → ℤ → ℝ}
    {l u : E → ℤ} (hf : ∀ e, DiscConvOn (f e) (l e) (u e))
    (z : E → ℤ) (gs : List (E → ℤ))
    (hsign : ∀ e, (∀ g ∈ gs, 0 ≤ g e) ∨ (∀ g ∈ gs, g e ≤ 0))
    (hzlo : ∀ e, l e ≤ z e) (hzhi : ∀ e, z e ≤ u e)
    (hclo : ∀ e, l e ≤ (z + gs.sum) e) (hchi : ∀ e, (z + gs.sum) e ≤ u e) :
    (gs.map (fun g => sepObj f (z + g) - sepObj f z)).sum
      ≤ sepObj f (z + gs.sum) - sepObj f z := by
  have hsep : ∀ g : E → ℤ,
      (∑ e, (f e (z e + g e) - f e (z e))) = sepObj f (z + g) - sepObj f z := by
    intro g
    rw [sepObj, sepObj, Finset.sum_sub_distrib]
    congr 1
  have hcoord : ∀ e,
      (gs.map (fun g => f e (z e + g e) - f e (z e))).sum
        ≤ f e (z e + (gs.sum) e) - f e (z e) := by
    intro e
    have hsign' : (∀ h ∈ gs.map (fun g => g e), 0 ≤ h)
        ∨ (∀ h ∈ gs.map (fun g => g e), h ≤ 0) := by
      rcases hsign e with hp | hn
      · exact Or.inl (fun x hx => by
          rw [List.mem_map] at hx; obtain ⟨g, hg, rfl⟩ := hx; exact hp g hg)
      · exact Or.inr (fun x hx => by
          rw [List.mem_map] at hx; obtain ⟨g, hg, rfl⟩ := hx; exact hn g hg)
    have hzlo_e : l e ≤ z e := hzlo e
    have hzhi_e : z e ≤ u e := hzhi e
    have hclo_e : l e ≤ z e + (gs.map (fun g => g e)).sum := by
      rw [list_sum_apply]; exact hclo e
    have hchi_e : z e + (gs.map (fun g => g e)).sum ≤ u e := by
      rw [list_sum_apply]; exact hchi e
    have h := superadd_list (hf e) (z e) (gs.map (fun g => g e)) hsign'
      hzlo_e hzhi_e hclo_e hchi_e
    simpa [List.map_map, Function.comp_def, list_sum_apply] using h
  have hLHS : (gs.map (fun g => sepObj f (z + g) - sepObj f z)).sum
      = ∑ e, (gs.map (fun g => f e (z e + g e) - f e (z e))).sum := by
    have h1 : (gs.map (fun g => sepObj f (z + g) - sepObj f z)).sum
        = (gs.map (fun g => ∑ e, (f e (z e + g e) - f e (z e)))).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro g _
      exact (hsep g).symm
    rw [h1, list_sum_finset_sum]
  have hRHS : sepObj f (z + gs.sum) - sepObj f z
      = ∑ e, (f e (z e + (gs.sum) e) - f e (z e)) := (hsep gs.sum).symm
  rw [hLHS, hRHS]
  exact Finset.sum_le_sum (fun e _ => hcoord e)

/-! ## The conditional Graver optimality certificate -/

section Certificate

variable {E V : Type} [Fintype E]

/-- The affine integer fiber `lin z = b` with coordinatewise box `l ≤ z ≤ u`. -/
def Feasible (lin : (E → ℤ) → (V → ℤ)) (b : V → ℤ) (l u : E → ℤ)
    (z : E → ℤ) : Prop :=
  lin z = b ∧ ∀ e, l e ≤ z e ∧ z e ≤ u e

/-- A conformal Graver decomposition of the displacement from `z`: every
feasible `y` equals `z` plus a `List` of coordinatewise sign-compatible Graver
moves.  This is exactly the shape returned by
`AssemblyP1.GraverRigidity.graver_decomposition`. -/
def HasGraverDecomposition (lin : (E → ℤ) → (V → ℤ)) (b : V → ℤ) (l u : E → ℤ)
    (Graver : (E → ℤ) → Prop) (z : E → ℤ) : Prop :=
  ∀ y, Feasible lin b l u y → ∃ gs : List (E → ℤ),
    (∀ g ∈ gs, Graver g) ∧
    (∀ e, (∀ g ∈ gs, 0 ≤ g e) ∨ (∀ g ∈ gs, g e ≤ 0)) ∧
    gs.sum = y - z

/-- **Conditional Graver optimality certificate (issue #263).**

Assume a separable discrete-convex objective `F z = ∑ e, f e (z e)` on the box,
a `Graver` predicate whose elements lie in the kernel of `lin`, and a conformal
Graver decomposition of every feasible displacement from `z`.  Then `z` is a
global minimum of `F` over the feasible set **iff** no feasible Graver step
`z + g` strictly improves `F`.  The inequality direction is the minimization
form `F z ≤ F (z + g)`.

This is the correct discrete optimality certificate and avoids the false
continuous KKT stationarity criterion: discrete optimality does not force the
real gradient to vanish. -/
theorem graver_optimal_iff_no_improving
    (lin : (E → ℤ) → (V → ℤ)) (b : V → ℤ) (l u : E → ℤ)
    (Graver : (E → ℤ) → Prop)
    (hlin_add : ∀ x y : E → ℤ, lin (x + y) = lin x + lin y)
    (hker : ∀ g, Graver g → lin g = 0)
    {f : E → ℤ → ℝ} (hf : ∀ e, DiscConvOn (f e) (l e) (u e))
    {z : E → ℤ} (hz : Feasible lin b l u z)
    (hdec : HasGraverDecomposition lin b l u Graver z) :
    (∀ w, Feasible lin b l u w → sepObj f z ≤ sepObj f w) ↔
    (∀ g, Graver g → Feasible lin b l u (z + g) →
      sepObj f z ≤ sepObj f (z + g)) := by
  constructor
  · intro hopt g _ hgfeas
    exact hopt (z + g) hgfeas
  · intro hno w hw
    obtain ⟨gs, hgs, hsign, hsum⟩ := hdec w hw
    have hzg : ∀ g ∈ gs, Feasible lin b l u (z + g) := by
      intro g hg
      refine ⟨?_, ?_⟩
      · rw [hlin_add, hz.1, hker g (hgs g hg), add_zero]
      · intro e
        rw [Pi.add_apply]
        have hsum_e : (gs.sum) e = w e - z e := by
          rw [congrFun hsum e, Pi.sub_apply]
        rcases hsign e with hp | hn
        · have hle : g e ≤ (gs.sum) e := by
            rw [← list_sum_apply]
            exact list_le_sum_of_mem_int (List.mem_map.mpr ⟨g, hg, rfl⟩)
              (fun x hx => by
                rw [List.mem_map] at hx; obtain ⟨g', hg', rfl⟩ := hx; exact hp g' hg')
          have hg0 : 0 ≤ g e := hp g hg
          rw [hsum_e] at hle
          exact ⟨by have := (hz.2 e).1; omega, by have := (hw.2 e).2; omega⟩
        · have hge : (gs.sum) e ≤ g e := by
            rw [← list_sum_apply]
            exact list_sum_le_of_mem_int (List.mem_map.mpr ⟨g, hg, rfl⟩)
              (fun x hx => by
                rw [List.mem_map] at hx; obtain ⟨g', hg', rfl⟩ := hx; exact hn g' hg')
          have hg0 : g e ≤ 0 := hn g hg
          rw [hsum_e] at hge
          exact ⟨by have := (hw.2 e).1; omega, by have := (hz.2 e).2; omega⟩
    have hterm : ∀ g ∈ gs, 0 ≤ sepObj f (z + g) - sepObj f z := by
      intro g hg
      have := hno g (hgs g hg) (hzg g hg)
      linarith
    have hsum_nonneg : 0 ≤ (gs.map (fun g => sepObj f (z + g) - sepObj f z)).sum := by
      apply List.sum_nonneg
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨g, hg, rfl⟩ := hx
      exact hterm g hg
    have hwz : z + gs.sum = w := by
      funext e
      rw [Pi.add_apply, congrFun hsum e, Pi.sub_apply]
      ring
    have hsuper := superadd_separable_list hf z gs hsign
      (fun e => (hz.2 e).1) (fun e => (hz.2 e).2)
      (fun e => by rw [hwz]; exact (hw.2 e).1)
      (fun e => by rw [hwz]; exact (hw.2 e).2)
    rw [hwz] at hsuper
    linarith

end Certificate

/-! ## The multiplier (integer Graver ray) lemma -/

/-- **Multiplier lemma (issue #263).**  For a separable discrete-convex
objective, if the integer Graver ray `α • g` (`α ≥ 1`) strictly improves over
`z` while the whole path `z, z+g, …, z+α•g` stays in the box, then the unit
step `g` already strictly improves.  This is proved by applying the separable
Positive Sum Property to the list of `α` copies of `g`. -/
theorem multiplier_improving {E : Type} [Fintype E] {f : E → ℤ → ℝ}
    {l u : E → ℤ} (hf : ∀ e, DiscConvOn (f e) (l e) (u e))
    {z g : E → ℤ} {α : ℕ} (hα : 1 ≤ α)
    (hzlo : ∀ e, l e ≤ z e) (hzhi : ∀ e, z e ≤ u e)
    (hclo : ∀ e, l e ≤ (z + α • g) e) (hchi : ∀ e, (z + α • g) e ≤ u e) :
    sepObj f (z + α • g) < sepObj f z → sepObj f (z + g) < sepObj f z := by
  intro himp
  have hsum_rep : (List.replicate α g).sum = α • g := List.sum_replicate α g
  have hsign : ∀ e, (∀ h ∈ List.replicate α g, 0 ≤ h e)
      ∨ (∀ h ∈ List.replicate α g, h e ≤ 0) := by
    intro e
    rcases lt_or_ge (g e) 0 with hlt | hge
    · exact Or.inr (fun h hh => by
        obtain ⟨-, rfl⟩ := List.mem_replicate.mp hh; omega)
    · exact Or.inl (fun h hh => by
        obtain ⟨-, rfl⟩ := List.mem_replicate.mp hh; exact hge)
  have hclo' : ∀ e, l e ≤ (z + (List.replicate α g).sum) e := by
    intro e; rw [hsum_rep]; exact hclo e
  have hchi' : ∀ e, (z + (List.replicate α g).sum) e ≤ u e := by
    intro e; rw [hsum_rep]; exact hchi e
  have hsuper := superadd_separable_list hf z (List.replicate α g) hsign
    hzlo hzhi hclo' hchi'
  rw [hsum_rep] at hsuper
  have hmap : (List.replicate α g).map
      (fun g' => sepObj f (z + g') - sepObj f z)
      = List.replicate α (sepObj f (z + g) - sepObj f z) := by
    rw [List.map_replicate]
  rw [hmap, List.sum_replicate] at hsuper
  have hcast : ((α : ℝ)) * (sepObj f (z + g) - sepObj f z)
      ≤ sepObj f (z + α • g) - sepObj f z := by
    simpa using hsuper
  have hαpos : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα
  have hneg : sepObj f (z + α • g) - sepObj f z < 0 := by linarith
  have hlt : (α : ℝ) * (sepObj f (z + g) - sepObj f z) < 0 := by linarith
  have : sepObj f (z + g) - sepObj f z < 0 := by
    by_contra hcon
    have h0 : 0 ≤ sepObj f (z + g) - sepObj f z := le_of_not_gt hcon
    nlinarith [mul_nonneg (le_of_lt hαpos) h0]
  linarith

/-! ## Discrete convexity of the source likelihood costs (candidate copy count)

The following lemmas instantiate the abstract convexity hypothesis on the
source-oriented negative-log likelihood costs, with the optimization variable
being the **candidate copy count** `d` (not the observed read count).  The
domains are restricted to the positive interior so that `Real.log` is honest:
`Real.log 0 = 0` would otherwise give a false finite value at impossible
boundary candidates.

These are the **pure maximum-likelihood** costs.  A penalized solver cost
`F_ML + P` is a different objective: the certificate
`graver_optimal_iff_no_improving` transfers to it only when the *full*
penalized objective is itself discretely convex on the box, a property that
must be verified for the specific penalty `P` (e.g. a separable convex
penalty).  The lemmas above certify the pure ML terms only; they make no
claim about a penalized solver cost whose penalty is not separately shown to
be discretely convex. -/

/-- Discrete convexity is preserved by pointwise addition. -/
theorem DiscConvOn.add {f g : ℤ → ℝ} {lo hi : ℤ} (hf : DiscConvOn f lo hi)
    (hg : DiscConvOn g lo hi) : DiscConvOn (fun d => f d + g d) lo hi := by
  intro a b ha hab hb
  simp only [inc]
  have h1 := hf a b ha hab hb
  have h2 := hg a b ha hab hb
  simp only [inc] at h1 h2
  linarith

/-- Discrete convexity is preserved by nonnegative scaling. -/
theorem DiscConvOn.const_mul {f : ℤ → ℝ} {lo hi : ℤ} (hf : DiscConvOn f lo hi)
    {c : ℝ} (hc : 0 ≤ c) : DiscConvOn (fun d => c * f d) lo hi := by
  intro a b ha hab hb
  simp only [inc]
  have h := hf a b ha hab hb
  simp only [inc] at h
  have h' := mul_le_mul_of_nonneg_left h hc
  ring_nf at h' ⊢
  exact h'

/-- Discrete convexity is preserved by adding a constant. -/
theorem DiscConvOn.const {c : ℝ} {lo hi : ℤ} : DiscConvOn (fun _ => c) lo hi := by
  intro a b ha hab hb
  simp [inc]

/-- Reflection about `c/2` preserves discrete convexity. -/
theorem DiscConvOn.comp_sub {f : ℤ → ℝ} {lo hi c : ℤ} (hf : DiscConvOn f lo hi) :
    DiscConvOn (fun d => f (c - d)) (c - hi) (c - lo) := by
  intro a b ha hab hb
  have h := hf (c - b - 1) (c - a - 1) (by omega) (by omega) (by omega)
  simp only [inc] at h ⊢
  ring_nf at h ⊢
  linarith

/-- Discrete convexity transfers across functions that agree on the interval
(the first differences only probe points inside `[lo, hi]`). -/
theorem DiscConvOn.congr {f g : ℤ → ℝ} {lo hi : ℤ}
    (h : ∀ d, lo ≤ d → d ≤ hi → f d = g d) (hg : DiscConvOn g lo hi) :
    DiscConvOn f lo hi := by
  intro a b ha hab hb
  simp only [inc]
  rw [h (a + 1) (by omega) (by omega), h a (by omega) (by omega),
    h (b + 1) (by omega) (by omega), h b (by omega) (by omega)]
  exact hg a b ha hab hb

/-- `d ↦ -log d` is discretely convex on the positive integers `[1, hi]`. -/
theorem negLog_discConvOn (hi : ℤ) :
    DiscConvOn (fun d : ℤ => -Real.log (d : ℝ)) 1 hi := by
  intro a b ha hab hb
  have ha1 : (0:ℝ) < (a:ℝ) := by exact_mod_cast (show 0 < a by omega)
  have ha2 : (0:ℝ) < (a:ℝ) + 1 := by linarith
  have hb1 : (0:ℝ) < (b:ℝ) := by exact_mod_cast (show 0 < b by omega)
  have hb2 : (0:ℝ) < (b:ℝ) + 1 := by linarith
  have hratio : (a:ℝ) / ((a:ℝ) + 1) ≤ (b:ℝ) / ((b:ℝ) + 1) := by
    rw [div_le_div_iff₀ ha2 hb2]
    nlinarith [show (a:ℝ) ≤ (b:ℝ) by exact_mod_cast hab]
  have hlog := Real.log_le_log (by positivity : 0 < (a:ℝ) / ((a:ℝ) + 1)) hratio
  simp only [inc]
  have e1 : -Real.log (((a + 1 : ℤ)) : ℝ) - -Real.log ((a : ℤ) : ℝ)
      = Real.log ((a:ℝ) / ((a:ℝ) + 1)) := by
    rw [Real.log_div ha1.ne' ha2.ne']
    push_cast
    ring
  have e2 : -Real.log (((b + 1 : ℤ)) : ℝ) - -Real.log ((b : ℤ) : ℝ)
      = Real.log ((b:ℝ) / ((b:ℝ) + 1)) := by
    rw [Real.log_div hb1.ne' hb2.ne']
    push_cast
    ring
  rw [e1, e2]
  exact hlog

/-- `d ↦ -log (N - d)` is discretely convex on `[1, N-1]`. -/
theorem negLog_sub_discConvOn (N : ℤ) (_hN : 2 ≤ N) :
    DiscConvOn (fun d : ℤ => -Real.log ((N:ℝ) - (d:ℝ))) 1 (N - 1) := by
  have h := (negLog_discConvOn (N - 1)).comp_sub (c := N)
  have hlo : (N : ℤ) - (N - 1) = 1 := by ring
  rw [hlo] at h
  simpa only [Int.cast_sub, Int.cast_one] using h

/-- The exact fixed-total multinomial negative-log term
`d ↦ -x · log(d/G)` is discretely convex in the candidate copy count `d` on
the positive interior `[1, hi]`, for `G ≥ 1` and `x ≥ 0`.  On `d ≠ 0` it
equals `x · (-log d) + x · log G`, a nonnegative multiple of `-log d` plus a
constant. -/
theorem multinomialTerm_discConvOn (G : ℤ) (hG : 1 ≤ G) (x : ℤ) (hx : 0 ≤ x)
    (hi : ℤ) :
    DiscConvOn (fun d : ℤ => -(x:ℝ) * Real.log ((d:ℝ) / (G:ℝ))) 1 hi := by
  have hg1 : DiscConvOn (fun d : ℤ => (x:ℝ) * -Real.log (d:ℝ)) 1 hi :=
    (negLog_discConvOn hi).const_mul (c := (x:ℝ)) (by exact_mod_cast hx)
  have hg2 : DiscConvOn (fun _ : ℤ => (x:ℝ) * Real.log (G:ℝ)) 1 hi := DiscConvOn.const
  have hg := hg1.add hg2
  refine DiscConvOn.congr (g := fun d : ℤ =>
    (x:ℝ) * -Real.log (d:ℝ) + (x:ℝ) * Real.log (G:ℝ)) ?_ hg
  intro d hd1 _
  have hd0 : (d:ℝ) ≠ 0 := by
    have : (0:ℝ) < (d:ℝ) := by exact_mod_cast (show 0 < d by omega)
    exact this.ne'
  have hG0 : (G:ℝ) ≠ 0 := by
    have : (0:ℝ) < (G:ℝ) := by exact_mod_cast (show 0 < G by omega)
    exact this.ne'
  rw [Real.log_div hd0 hG0]
  ring

/-- The fixed-external-`N` product-binomial negative-log term
`d ↦ -x · log(d/N) - (n-x) · log(1 - d/N)` is discretely convex in the
candidate copy count `d` on the strict interior `[1, N-1]`, for `N ≥ 2` and
`0 ≤ x ≤ n`.  On `0 < d < N` it equals the nonnegative combination
`x · (-log d) + (n-x) · (-log(N-d)) + n · log N`. -/
theorem binomTerm_discConvOn (N : ℤ) (hN : 2 ≤ N) (x n : ℤ) (hx : 0 ≤ x)
    (hxn : x ≤ n) :
    DiscConvOn (fun d : ℤ => -(x:ℝ) * Real.log ((d:ℝ) / (N:ℝ))
        - ((n - x : ℤ) : ℝ) * Real.log (1 - (d:ℝ) / (N:ℝ))) 1 (N - 1) := by
  have hg1 : DiscConvOn (fun d : ℤ => (x:ℝ) * -Real.log (d:ℝ)) 1 (N - 1) :=
    (negLog_discConvOn (N - 1)).const_mul (c := (x:ℝ)) (by exact_mod_cast hx)
  have hg2 : DiscConvOn (fun d : ℤ => ((n - x : ℤ) : ℝ) * -Real.log ((N:ℝ) - (d:ℝ)))
      1 (N - 1) :=
    (negLog_sub_discConvOn N hN).const_mul (c := ((n - x : ℤ) : ℝ))
      (by exact_mod_cast (by omega : 0 ≤ n - x))
  have hg3 : DiscConvOn (fun _ : ℤ => ((n : ℤ) : ℝ) * Real.log (N:ℝ)) 1 (N - 1) :=
    DiscConvOn.const
  have hg := (hg1.add hg2).add hg3
  refine DiscConvOn.congr (g := fun d : ℤ =>
    (x:ℝ) * -Real.log (d:ℝ) + ((n - x : ℤ) : ℝ) * -Real.log ((N:ℝ) - (d:ℝ))
      + ((n : ℤ) : ℝ) * Real.log (N:ℝ)) ?_ hg
  intro d hd1 hdN
  have hd0 : (d:ℝ) ≠ 0 := by
    have : (0:ℝ) < (d:ℝ) := by exact_mod_cast (show 0 < d by omega)
    exact this.ne'
  have hN0 : (N:ℝ) ≠ 0 := by
    have : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
    exact this.ne'
  have hNd0 : ((N:ℝ) - (d:ℝ)) ≠ 0 := by
    have : (0:ℝ) < (N:ℝ) - (d:ℝ) := by
      have : (d:ℝ) < (N:ℝ) := by exact_mod_cast (show d < N by omega)
      linarith
    exact this.ne'
  have hsub : 1 - (d:ℝ) / (N:ℝ) = ((N:ℝ) - (d:ℝ)) / (N:ℝ) := one_sub_div hN0
  rw [Real.log_div hd0 hN0, hsub, Real.log_div hNd0 hN0]
  push_cast
  ring

end AssemblyP1.SeparableConvexGraver
