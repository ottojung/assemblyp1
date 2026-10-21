import Mathlib
import AssemblyP1.Section62BidirectedFlow

/-!
# Integer vs half-integral relaxation for the exact §6.2 read likelihood (#261)

This module answers one precise question of board issue #261: *can the
half-integral relaxation of the MB09 §6.2 bidirected overlap flow polytope
ever yield a strictly higher **exact** read likelihood than the best integer
flow?*

## The class made precise

* **Candidate set.** Rational flows `f : BdEdge A W → ℚ` on the §6.2
  bidirected overlap graph `edges` over the vertex list `verts`, satisfying the
  §6.2 clauses: edge lower bound `0`, vertex lower bound `1`, zero-terminal
  signed-incidence balance `0`, and throughput vector `d`.  Integer flows are
  those with `∀ e, ∃ n : ℤ, f e = n`; half-integral flows are those with
  `∀ e, ∃ n : ℤ, f e = n / 2` (`IsHalfIntegral`).  The candidate set is
  *flows*, not spelled circuits and not circular genomes.
* **Truth.** Admitted (any feasible flow).
* **Likelihood.** The exact multinomial likelihood of the candidate's normalized
  throughput, with candidate length `N = ∑ᵥ d v` (the variable-length §6.1
  first display, `exactLik`).

## The result

The exact likelihood is homogeneous of degree `0` in the throughput
(`exactLik_smul`), and the §6.2 feasibility clauses are homogeneous, so
doubling a half-integral feasible flow yields an integer feasible flow with the
same normalized throughput (`half_integral_doubling`).  Hence the half-integral
relaxation cannot strictly beat the integer optimum.

This is in sharp contrast to the MB09 §6.1 **separable binomial** objective
(with external `N` fixed), for which the integer constraint *is* binding
(`AssemblyP1.GeneralBidirectedFlowML.half_integral_gap`): the binomial is not
homogeneous, so doubling changes its value, while the exact multinomial is
homogeneous and is not changed.

## Scope

No claim is made about spelled circuits, circular genomes, the fixed-external-`N`
binomial, or the real (non-half-integral) LP relaxation.  No `sorry`, `admit`,
`axiom`, or `native_decide`.
-/

set_option autoImplicit false

namespace AssemblyP1.Section62HalfIntegralExactML

open AssemblyP1.Section62Flow
open Finset

variable {A W : Type} [DecidableEq W]

/-! ## The rational §6.2 flow object -/

/-- A rational flow on the bidirected overlap graph. -/
abbrev QFlow (A : Type) (W : Type) [DecidableEq W] : Type := BdEdge A W → ℚ

/-- The rational throughput of a rational flow: the total flow on the graph
edges that depart from the molecule class of `v`.  This is the `ℚ`-analogue of
`throughput`, written as a `List.sum` so that it counts *edge occurrences*
exactly like the source `List.foldr` (in particular duplicates are counted). -/
def qThroughput (rep : W → W) (f : QFlow A W) (edges : List (BdEdge A W)) (v : W) : ℚ :=
  (edges.map (fun e => if rep e.sx = v then f e else 0)).sum

/-- The rational signed-incidence balance of a rational flow (zero terminals).
This is the `ℚ`-analogue of `balCore`, again counting edge occurrences. -/
def qBalance (rep : W → W) (f : QFlow A W) (edges : List (BdEdge A W)) (v : W) : ℚ :=
  (edges.map (fun e => if rep e.sx = v then (e.sgnX : ℚ) * f e else 0)).sum +
    (edges.map (fun e => if rep e.sy = v then (e.sgnY : ℚ) * f e else 0)).sum

/-! ## Homogeneity of the §6.2 clauses -/

/-- The rational throughput is homogeneous of degree `1`. -/
theorem qThroughput_smul (rep : W → W) (f : QFlow A W) (edges : List (BdEdge A W))
    (v : W) (k : ℚ) :
    qThroughput rep (fun e => k * f e) edges v = k * qThroughput rep f edges v := by
  unfold qThroughput
  induction edges with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      split_ifs <;> ring

/-- The rational balance is homogeneous of degree `1`. -/
theorem qBalance_smul (rep : W → W) (f : QFlow A W) (edges : List (BdEdge A W))
    (v : W) (k : ℚ) :
    qBalance rep (fun e => k * f e) edges v = k * qBalance rep f edges v := by
  unfold qBalance
  have hx : (edges.map (fun e => if rep e.sx = v then (e.sgnX : ℚ) * (k * f e) else 0)).sum
      = k * (edges.map (fun e => if rep e.sx = v then (e.sgnX : ℚ) * f e else 0)).sum := by
    induction edges with
    | nil => simp
    | cons a t ih =>
        simp only [List.map_cons, List.sum_cons, ih]
        split_ifs <;> ring
  have hy : (edges.map (fun e => if rep e.sy = v then (e.sgnY : ℚ) * (k * f e) else 0)).sum
      = k * (edges.map (fun e => if rep e.sy = v then (e.sgnY : ℚ) * f e else 0)).sum := by
    clear hx
    induction edges with
    | nil => simp
    | cons a t ih =>
        simp only [List.map_cons, List.sum_cons, ih]
        split_ifs <;> ring
  rw [hx, hy]
  ring

/-- Rational §6.2 feasibility (zero terminals): edge lower bound `0`, vertex
lower bound `1`, signed-incidence balance `0`, and throughput vector `d`.  This
is the `ℚ`-analogue of the `Feasible62` clauses (with `noTerminals`). -/
def QFeasible62 (rep : W → W) (verts : List W) (edges : List (BdEdge A W))
    (f : QFlow A W) (d : W → ℚ) : Prop :=
  (∀ e ∈ edges, (0 : ℚ) ≤ f e) ∧
    (∀ v ∈ verts, (1 : ℚ) ≤ qThroughput rep f edges v) ∧
    (∀ v ∈ verts, qBalance rep f edges v = 0) ∧
    (∀ v ∈ verts, qThroughput rep f edges v = d v)

/-- **The §6.2 clauses are homogeneous.**  Scaling a feasible rational flow by a
positive factor preserves feasibility (the vertex lower bound stays satisfied
because the scale factor is at least `1`... in fact at least positive and the
throughput scales up). -/
theorem qFeasible62_smul (rep : W → W) (verts : List W) (edges : List (BdEdge A W))
    (f : QFlow A W) (d : W → ℚ) (k : ℚ) (hk : 1 ≤ k)
    (h : QFeasible62 rep verts edges f d) :
    QFeasible62 rep verts edges (fun e => k * f e) (fun v => k * d v) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he
    exact mul_nonneg (le_trans zero_le_one hk) (h1 e he)
  · intro v hv
    rw [qThroughput_smul]
    nlinarith [h2 v hv, hk]
  · intro v hv
    rw [qBalance_smul, h3 v hv]
    ring
  · intro v hv
    rw [qThroughput_smul, h4 v hv]
    try ring

/-! ## The exact multinomial likelihood and its scale invariance -/

/-- The exact multinomial likelihood of a rational throughput vector `d` over
the observed vertex set `verts`, at observed counts `x`, with candidate length
`N = ∑ᵥ d v`: `∏ᵥ (d v / ∑ᵤ d u) ^ (x v)`. -/
noncomputable def exactLik (d : W → ℚ) (x : W → ℕ) (verts : List W) : ℚ :=
  ∏ v ∈ verts.toFinset, (d v / (∑ u ∈ verts.toFinset, d u)) ^ (x v)

/-- **The exact likelihood is scale-invariant.**  Multiplying the throughput by
a positive factor leaves every normalized coordinate `d v / ∑ d` unchanged,
hence leaves the exact likelihood unchanged. -/
theorem exactLik_smul (d : W → ℚ) (x : W → ℕ) (verts : List W) (k : ℚ) (hk : 0 < k)
    (hsum : 0 < ∑ u ∈ verts.toFinset, d u) :
    exactLik (fun v => k * d v) x verts = exactLik d x verts := by
  unfold exactLik
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  have hk0 : k ≠ 0 := ne_of_gt hk
  have hsum0 : (∑ u ∈ verts.toFinset, d u) ≠ 0 := ne_of_gt hsum
  rw [← Finset.mul_sum]
  field_simp
  try ring

/-! ## Half-integral flows and their doubling -/

/-- A rational flow is half-integral when every edge value is half of an
integer, i.e. `2 * f e` is an integer. -/
def IsHalfIntegral (f : QFlow A W) : Prop := ∀ e, ∃ n : ℤ, f e = (n : ℚ) / 2

/-- The doubled (integer) flow of a half-integral flow. -/
noncomputable def halfIntegralDouble (f : QFlow A W) (h : IsHalfIntegral f) : QFlow A W :=
  fun e => ((Classical.choose (h e) : ℤ) : ℚ)

/-- The doubled flow is twice the half-integral flow. -/
theorem halfIntegralDouble_eq (f : QFlow A W) (h : IsHalfIntegral f) (e : BdEdge A W) :
    halfIntegralDouble f h e = 2 * f e := by
  unfold halfIntegralDouble
  have hspec := Classical.choose_spec (h e)
  linarith

/-- The doubled flow has doubled rational throughput. -/
theorem qThroughput_double (rep : W → W) (f : QFlow A W) (h : IsHalfIntegral f)
    (edges : List (BdEdge A W)) (v : W) :
    qThroughput rep (halfIntegralDouble f h) edges v = 2 * qThroughput rep f edges v := by
  have hf : halfIntegralDouble f h = fun e => 2 * f e := by
    funext e; exact halfIntegralDouble_eq f h e
  rw [hf, qThroughput_smul]

/-- The doubled flow has doubled rational balance. -/
theorem qBalance_double (rep : W → W) (f : QFlow A W) (h : IsHalfIntegral f)
    (edges : List (BdEdge A W)) (v : W) :
    qBalance rep (halfIntegralDouble f h) edges v = 2 * qBalance rep f edges v := by
  have hf : halfIntegralDouble f h = fun e => 2 * f e := by
    funext e; exact halfIntegralDouble_eq f h e
  rw [hf, qBalance_smul]

/-- **The doubling theorem (no half-integral gap for the exact likelihood).**
For every half-integral §6.2 feasible flow `f` with throughput `d` and positive
total length `∑ d`, the doubled flow is an *integer* §6.2 feasible flow with
throughput `2d`, and it has exactly the same exact likelihood as `f`.  Hence
every half-integral candidate's exact likelihood is matched by an integer
candidate, so the half-integral relaxation of the §6.2 flow polytope cannot
strictly beat the integer optimum for the exact multinomial objective. -/
theorem half_integral_doubling (rep : W → W) (verts : List W) (edges : List (BdEdge A W))
    (f : QFlow A W) (d : W → ℚ) (h : IsHalfIntegral f)
    (hf : QFeasible62 rep verts edges f d) (x : W → ℕ)
    (hsum : 0 < ∑ u ∈ verts.toFinset, d u) :
    QFeasible62 rep verts edges (halfIntegralDouble f h) (fun v => 2 * d v) ∧
      exactLik (fun v => 2 * d v) x verts = exactLik d x verts := by
  constructor
  · obtain ⟨h1, h2, h3, h4⟩ := hf
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro e he
      rw [halfIntegralDouble_eq]
      have := h1 e he
      linarith
    · intro v hv
      rw [qThroughput_double]
      have := h2 v hv
      linarith
    · intro v hv
      rw [qBalance_double, h3 v hv]
      ring
    · intro v hv
      rw [qThroughput_double, h4 v hv]
      try ring
  · exact exactLik_smul d x verts 2 (by norm_num) hsum

/-! ## Non-vacuity

The doubling is not vacuous: on the minimal `AAATT` §6.2 instance of
`AssemblyP1.Section62NonSpelledFlow` the half-integral flow `h = (5/2,1,1)` and
its integer double `2h = (5,2,2)` have the same normalized throughput.  We
record the abstract arithmetic fact that the `AAA` exact-multinomial factor is
equal at `d` and `2d` after renormalization; the concrete flow-level feasibility
is the cited module's. -/

/-- The exact-likelihood factor at the half-integral point `d = 5/2` of a length
`5` genome equals the factor at the doubled point `d = 5` of a length `10`
genome: `(5/2)/5 = 5/10`.  This is the local form of `exactLik_smul`. -/
theorem half_integral_factor_scale :
    ((5 / 2 : ℚ) / 5) = ((5 : ℚ) / 10) := by
  norm_num

/-- The squared factor comparison that makes the half-integral `AAA` candidate
tie its integer double under the exact objective. -/
theorem half_integral_factor_pow :
    ((5 / 2 : ℚ) / 5) ^ 2 = ((5 : ℚ) / 10) ^ 2 := by
  norm_num

#print axioms qThroughput_smul
#print axioms qBalance_smul
#print axioms qFeasible62_smul
#print axioms exactLik_smul
#print axioms halfIntegralDouble_eq
#print axioms qThroughput_double
#print axioms qBalance_double
#print axioms half_integral_doubling
#print axioms half_integral_factor_scale
#print axioms half_integral_factor_pow

end AssemblyP1.Section62HalfIntegralExactML
