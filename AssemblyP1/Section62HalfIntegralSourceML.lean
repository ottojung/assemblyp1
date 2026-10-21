import Mathlib
import AssemblyP1.Section62BidirectedFlow

/-!
# The half-integral relaxation of the literal §6.2 flow polytope (#261)

Board issue #261 has one free axis "integer flows vs half-integral relaxation".
The already-merged `AssemblyP1.GeneralBidirectedFlowML.half_integral_gap` answers
it **for the §6.1 separable binomial with fixed external `N`**: there the integer
constraint *is* binding (`625/576 > 1`).

This module answers the *other*, well-defined reading of the same axis, stated
against the **literal** §6.2 object of `AssemblyP1.Section62BidirectedFlow`
(`BdEdge`, `throughput`, `balCore`, `Admissible`, `Feasible62`), not against a
proxy:

* **Candidate set.** Rational flows `f : BdEdge A W → ℚ` satisfying the §6.2
  clauses (edge lower bound `0`, vertex lower bound `1`, zero-terminal
  signed-incidence balance `0`, throughput vector `d`) — the *rational
  relaxation* `Feasible62Rat` of the literal `Feasible62`.  Candidates are
  **flows**, not spelled circuits and not circular genomes.  The half-integral
  subclass is `IsHalfIntegral`.
* **Truth.** Admitted (any feasible rational flow).
* **Likelihood.** The exact multinomial likelihood `qExactLik` of the candidate's
  normalized throughput, with the candidate's own length `N = ∑ᵥ dᵥ` (the §6.1
  first display, variable length universe).
* **Length universe.** Variable (`N = ∑ d`).

## Result

The exact likelihood is homogeneous of degree `0` (`qExactLik_smul`), and the
§6.2 clauses are homogeneous (`feasible62Rat_smul`), so doubling a half-integral
feasible flow produces an **integer** feasible flow in the literal `Feasible62`
sense (`halfIntegral_double_feasible62`) with the same exact likelihood
(`no_half_integral_gap_exact`).  Hence the half-integral relaxation cannot
strictly beat the integer optimum for the exact variable-length objective, and
ML maximality of the truth is the same in both classes
(`truth_half_maximal_iff_int_maximal`).

The relaxation is nevertheless a *strict* enlargement of the candidate point set
(`integral_strict_subset_half_integral`), so the equivalence of optima is a real
theorem about a strictly larger feasible set, not a vacuous restatement.

## Scope and non-claims

* This is one concrete, fully specified family: rational §6.2 flows under the
  **exact variable-length multinomial**.  It is **not** a general criterion, and
  it does **not** transfer to the fixed-external-`N` binomial, where the gap is
  real (see `AssemblyP1.GeneralBidirectedFlowML.half_integral_gap`).
* No claim about spelled circuits, circular genomes, the real (non-half-integral)
  LP relaxation, or transitive reduction.
* No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

set_option autoImplicit false

namespace AssemblyP1.Section62HalfIntegralSourceML

open AssemblyP1.Section62Flow
open Finset

variable {A W : Type} [DecidableEq W]

/-! ## The rational relaxation of the literal §6.2 object -/

/-- A rational flow on the §6.2 bidirected overlap graph. -/
abbrev RatFlow (A : Type) (W : Type) [DecidableEq W] : Type := BdEdge A W → ℚ

/-- The rational throughput, mirroring `throughput`'s edge-occurrence `foldr`
exactly (so that duplicates and self-loops are counted identically). -/
def qThroughput (rep : W → W) (f : RatFlow A W) (edges : List (BdEdge A W))
    (v : W) : ℚ :=
  edges.foldr (fun e acc => if rep e.sx = v then f e + acc else acc) 0

/-- The rational signed-incidence balance, mirroring `balCore` exactly. -/
def qBalance (rep : W → W) (f : RatFlow A W) (edges : List (BdEdge A W))
    (v : W) : ℚ :=
  (edges.filter (fun e => rep e.sx = v)).foldr
      (fun e acc => (e.sgnX : ℚ) * f e + acc) 0 +
    (edges.filter (fun e => rep e.sy = v)).foldr
      (fun e acc => (e.sgnY : ℚ) * f e + acc) 0

/-! ## Bridges to the literal integer/`ℤ` source definitions -/

theorem qThroughput_cast (rep : W → W) (g : BdFlow A W) (edges : List (BdEdge A W))
    (v : W) :
    qThroughput rep (fun e => (g e : ℚ)) edges v = (throughput A W rep g edges v : ℚ) := by
  unfold qThroughput throughput
  induction edges with
  | nil => simp
  | cons a t ih =>
      simp only [List.foldr_cons]
      by_cases h : rep a.sx = v <;> simp [h, ih, Nat.cast_add]

theorem foldr_sgn_cast (l : List (BdEdge A W)) (sgn : BdEdge A W → ℤ) (g : BdFlow A W) :
    l.foldr (fun e acc => (sgn e : ℚ) * (g e : ℚ) + acc) 0
      = ((l.foldr (fun e acc => (g e : ℤ) * sgn e + acc) 0 : ℤ) : ℚ) := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.foldr_cons, ih]
      push_cast
      ring

theorem qBalance_cast (rep : W → W) (g : BdFlow A W) (edges : List (BdEdge A W))
    (v : W) :
    qBalance rep (fun e => (g e : ℚ)) edges v = (balCore A W rep g edges v : ℚ) := by
  unfold qBalance balCore
  rw [foldr_sgn_cast, foldr_sgn_cast]
  push_cast
  ring

/-! ## Homogeneity of the §6.2 clauses -/

theorem qThroughput_smul (rep : W → W) (f : RatFlow A W) (edges : List (BdEdge A W))
    (v : W) (k : ℚ) :
    qThroughput rep (fun e => k * f e) edges v = k * qThroughput rep f edges v := by
  unfold qThroughput
  induction edges with
  | nil => simp
  | cons a t ih =>
      simp only [List.foldr_cons, ih]
      split_ifs <;> ring

theorem foldr_sgn_smul (l : List (BdEdge A W)) (sgn : BdEdge A W → ℤ)
    (f : RatFlow A W) (k : ℚ) :
    l.foldr (fun e acc => (sgn e : ℚ) * (k * f e) + acc) 0
      = k * l.foldr (fun e acc => (sgn e : ℚ) * f e + acc) 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.foldr_cons, ih]
      ring

theorem qBalance_smul (rep : W → W) (f : RatFlow A W) (edges : List (BdEdge A W))
    (v : W) (k : ℚ) :
    qBalance rep (fun e => k * f e) edges v = k * qBalance rep f edges v := by
  unfold qBalance
  rw [foldr_sgn_smul, foldr_sgn_smul]
  ring

/-- Rational §6.2 feasibility: the `ℚ`-analogue of the literal `Feasible62`
clauses (zero terminals): edge lower bound `0`, vertex lower bound `1`,
signed-incidence balance `0`, throughput vector `d`. -/
def Feasible62Rat (rep : W → W) (verts : List W) (edges : List (BdEdge A W))
    (f : RatFlow A W) (d : W → ℚ) : Prop :=
  (∀ e ∈ edges, (0 : ℚ) ≤ f e) ∧
    (∀ v ∈ verts, (1 : ℚ) ≤ qThroughput rep f edges v) ∧
    (∀ v ∈ verts, qBalance rep f edges v = 0) ∧
    (∀ v ∈ verts, qThroughput rep f edges v = d v)

theorem feasible62Rat_smul (rep : W → W) (verts : List W) (edges : List (BdEdge A W))
    (f : RatFlow A W) (d : W → ℚ) (k : ℚ) (hk : 1 ≤ k)
    (h : Feasible62Rat rep verts edges f d) :
    Feasible62Rat rep verts edges (fun e => k * f e) (fun v => k * d v) := by
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

/-- An integer flow is a rational feasible flow through the cast, with the cast
throughput.  This is the inclusion `integer ⊆ rational` used below. -/
theorem feasible62Rat_of_feasible62 (rep : W → W) (verts : List W)
    (edges : List (BdEdge A W)) (g : BdFlow A W) (d : W → ℕ)
    (h : Feasible62 A W rep verts edges g (noTerminals W) d) :
    Feasible62Rat rep verts edges (fun e => (g e : ℚ)) (fun v => (d v : ℚ)) := by
  obtain ⟨⟨h1, h2, h3, h4⟩, _⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he
    change (0 : ℚ) ≤ (g e : ℚ)
    exact_mod_cast h1 e he
  · intro v hv
    rw [qThroughput_cast]
    exact_mod_cast h2 v hv
  · intro v hv
    rw [qBalance_cast]
    have hb : balance A W rep g (noTerminals W) edges v
        = balCore A W rep g edges v := by
      simp [balance, noTerminals]
    have h3v := h3 v hv
    rw [hb] at h3v
    exact_mod_cast h3v
  · intro v hv
    rw [qThroughput_cast]
    change (throughput A W rep g edges v : ℚ) = (d v : ℚ)
    exact_mod_cast h4 v hv

/-! ## Half-integral flows and their integer doubling -/

/-- A rational flow is half-integral when every edge value is half of an integer. -/
def IsHalfIntegral (f : RatFlow A W) : Prop := ∀ e, ∃ n : ℤ, f e = (n : ℚ) / 2

/-- The doubled (integer) flow of a half-integral flow. -/
noncomputable def halfDoubleNat (f : RatFlow A W) (h : IsHalfIntegral f) : BdFlow A W :=
  fun e => (Classical.choose (h e)).toNat

theorem halfDoubleNat_cast (f : RatFlow A W) (h : IsHalfIntegral f) (e : BdEdge A W)
    (hfe : 0 ≤ f e) : (halfDoubleNat f h e : ℚ) = 2 * f e := by
  have hspec : f e = ((Classical.choose (h e) : ℤ) : ℚ) / 2 := Classical.choose_spec (h e)
  have hn0 : (0 : ℤ) ≤ Classical.choose (h e) := by
    have h2 : (0 : ℚ) ≤ ((Classical.choose (h e) : ℤ) : ℚ) / 2 := by
      rw [← hspec]; exact hfe
    have h2' : (0 : ℚ) ≤ ((Classical.choose (h e) : ℤ) : ℚ) := by linarith
    exact_mod_cast h2'
  have hcoe : (((Classical.choose (h e)).toNat : ℕ) : ℚ)
      = ((Classical.choose (h e) : ℤ) : ℚ) := by
    exact_mod_cast (Int.toNat_of_nonneg hn0)
  simp only [halfDoubleNat]
  rw [hcoe]
  linarith

theorem qThroughput_double (rep : W → W) (f : RatFlow A W) (h : IsHalfIntegral f)
    (edges : List (BdEdge A W)) (v : W) (hf : ∀ e ∈ edges, 0 ≤ f e) :
    qThroughput rep (fun e => (halfDoubleNat f h e : ℚ)) edges v
      = 2 * qThroughput rep f edges v := by
  unfold qThroughput
  induction edges with
  | nil => simp
  | cons a t ih =>
      have ha : 0 ≤ f a := hf a (by simp)
      have ht : ∀ e ∈ t, 0 ≤ f e := fun e he => hf e (by simp [he])
      simp only [List.foldr_cons]
      rw [halfDoubleNat_cast f h a ha, ih ht]
      split_ifs <;> ring

theorem foldr_sgn_double (l : List (BdEdge A W)) (sgn : BdEdge A W → ℤ)
    (f : RatFlow A W) (h : IsHalfIntegral f) (hf : ∀ e ∈ l, 0 ≤ f e) :
    l.foldr (fun e acc => (sgn e : ℚ) * (halfDoubleNat f h e : ℚ) + acc) 0
      = 2 * l.foldr (fun e acc => (sgn e : ℚ) * f e + acc) 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have ha : 0 ≤ f a := hf a (by simp)
      have ht : ∀ e ∈ t, 0 ≤ f e := fun e he => hf e (by simp [he])
      simp only [List.foldr_cons]
      rw [halfDoubleNat_cast f h a ha, ih ht]
      ring

theorem qBalance_double (rep : W → W) (f : RatFlow A W) (h : IsHalfIntegral f)
    (edges : List (BdEdge A W)) (v : W) (hf : ∀ e ∈ edges, 0 ≤ f e) :
    qBalance rep (fun e => (halfDoubleNat f h e : ℚ)) edges v
      = 2 * qBalance rep f edges v := by
  unfold qBalance
  rw [foldr_sgn_double (edges.filter (fun e => rep e.sx = v)) (fun e => e.sgnX) f h
        (fun e he => hf e (List.mem_of_mem_filter he)),
      foldr_sgn_double (edges.filter (fun e => rep e.sy = v)) (fun e => e.sgnY) f h
        (fun e he => hf e (List.mem_of_mem_filter he))]
  ring

/-- **Doubling a half-integral §6.2 flow gives a literal integer `Feasible62`
flow.**  This is the source-connected form of the relaxation statement: the
doubled flow satisfies the *actual* §6.2 predicate of
`AssemblyP1.Section62BidirectedFlow`, not a proxy. -/
theorem halfIntegral_double_feasible62 (rep : W → W) (verts : List W)
    (edges : List (BdEdge A W)) (f : RatFlow A W) (d : W → ℚ) (h : IsHalfIntegral f)
    (hf : Feasible62Rat rep verts edges f d) :
    Feasible62 A W rep verts edges (halfDoubleNat f h) (noTerminals W)
      (fun v => throughput A W rep (halfDoubleNat f h) edges v) := by
  obtain ⟨h1, h2, h3, h4⟩ := hf
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro e he
    exact Nat.zero_le _
  · intro v hv
    have hcast : (throughput A W rep (halfDoubleNat f h) edges v : ℚ)
        = 2 * qThroughput rep f edges v := by
      rw [← qThroughput_cast rep (halfDoubleNat f h) edges v,
        qThroughput_double rep f h edges v h1]
    have hge : (1 : ℚ) ≤ (throughput A W rep (halfDoubleNat f h) edges v : ℚ) := by
      rw [hcast]
      nlinarith [h2 v hv]
    exact_mod_cast hge
  · intro v hv
    have hb : balance A W rep (halfDoubleNat f h) (noTerminals W) edges v
        = balCore A W rep (halfDoubleNat f h) edges v := by
      simp [balance, noTerminals]
    rw [hb]
    have hcast : (balCore A W rep (halfDoubleNat f h) edges v : ℚ) = 0 := by
      rw [← qBalance_cast rep (halfDoubleNat f h) edges v,
        qBalance_double rep f h edges v h1, h3 v hv]
      ring
    exact_mod_cast hcast
  · intro v hv
    rfl
  · intro v
    exact noTerminals_usage_zero W v

/-! ## The exact multinomial likelihood and its scale invariance -/

/-- The exact multinomial likelihood of a rational throughput `d` over the
observed vertex set `verts` at observed counts `x`, with the candidate's own
length `N = ∑ᵥ dᵥ`: `∏ᵥ (dᵥ / ∑ᵤ dᵤ) ^ (xᵥ)`. -/
noncomputable def qExactLik (d : W → ℚ) (x : W → ℕ) (verts : List W) : ℚ :=
  ∏ v ∈ verts.toFinset, (d v / (∑ u ∈ verts.toFinset, d u)) ^ (x v)

/-- **The exact likelihood is scale-invariant** (homogeneous of degree `0`).  No
positivity of the total is needed: in `ℚ` division by zero is `0`, and the
argument is uniform. -/
theorem qExactLik_smul (d : W → ℚ) (x : W → ℕ) (verts : List W) (k : ℚ) (hk : 0 < k) :
    qExactLik (fun v => k * d v) x verts = qExactLik d x verts := by
  unfold qExactLik
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  rw [← Finset.mul_sum]
  exact mul_div_mul_left (d v) (∑ u ∈ verts.toFinset, d u) (ne_of_gt hk)

theorem qExactLik_congr_on (d d' : W → ℚ) (x : W → ℕ) (verts : List W)
    (h : ∀ v ∈ verts.toFinset, d v = d' v) :
    qExactLik d x verts = qExactLik d' x verts := by
  unfold qExactLik
  apply Finset.prod_congr rfl
  intro v hv
  have hsum : (∑ u ∈ verts.toFinset, d u) = ∑ u ∈ verts.toFinset, d' u :=
    Finset.sum_congr rfl (fun u hu => h u hu)
  rw [h v hv, hsum]

/-! ## No half-integral gap for the exact objective -/

/-- **The half-integral relaxation cannot strictly beat the integer optimum for
the exact variable-length objective.**  Every half-integral feasible rational flow
has an integer `Feasible62` double with the same exact likelihood on every
observed sample. -/
theorem no_half_integral_gap_exact (rep : W → W) (verts : List W)
    (edges : List (BdEdge A W)) (f : RatFlow A W) (d : W → ℚ) (h : IsHalfIntegral f)
    (hf : Feasible62Rat rep verts edges f d) (x : W → ℕ) :
    qExactLik (fun v => (throughput A W rep (halfDoubleNat f h) edges v : ℚ)) x verts
      = qExactLik d x verts := by
  have hagree : ∀ v ∈ verts.toFinset,
      (throughput A W rep (halfDoubleNat f h) edges v : ℚ) = 2 * d v := by
    intro v hv
    rw [← qThroughput_cast rep (halfDoubleNat f h) edges v,
      qThroughput_double rep f h edges v hf.1,
      hf.2.2.2 v (by simpa using hv)]
  calc qExactLik (fun v => (throughput A W rep (halfDoubleNat f h) edges v : ℚ)) x verts
      = qExactLik (fun v => 2 * d v) x verts :=
        qExactLik_congr_on _ _ x verts hagree
    _ = qExactLik d x verts := qExactLik_smul d x verts 2 (by norm_num)

/-! ## ML maximality is the same in both classes -/

/-- The objective value of a rational flow, using its own rational throughput. -/
noncomputable def ratObj (rep : W → W) (edges : List (BdEdge A W)) (f : RatFlow A W)
    (x : W → ℕ) (verts : List W) : ℚ :=
  qExactLik (fun v => qThroughput rep f edges v) x verts

/-- The objective value of an integer flow, using its literal `throughput`. -/
noncomputable def intObj (rep : W → W) (edges : List (BdEdge A W)) (g : BdFlow A W)
    (x : W → ℕ) (verts : List W) : ℚ :=
  qExactLik (fun v => (throughput A W rep g edges v : ℚ)) x verts

theorem ratObj_of_int (rep : W → W) (edges : List (BdEdge A W)) (g : BdFlow A W)
    (x : W → ℕ) (verts : List W) :
    ratObj rep edges (fun e => (g e : ℚ)) x verts = intObj rep edges g x verts := by
  unfold ratObj intObj
  congr 1
  funext v
  exact qThroughput_cast rep g edges v

/-- A half-integral feasible rational flow. -/
def HalfIntegralFeasible (rep : W → W) (verts : List W) (edges : List (BdEdge A W))
    (f : RatFlow A W) : Prop :=
  IsHalfIntegral f ∧ ∃ d : W → ℚ, Feasible62Rat rep verts edges f d

/-- An integer feasible flow (literal `Feasible62`, zero terminals). -/
def IntegerFeasible (rep : W → W) (verts : List W) (edges : List (BdEdge A W))
    (g : BdFlow A W) : Prop :=
  ∃ d : W → ℕ, Feasible62 A W rep verts edges g (noTerminals W) d

/-- **The half-integral relaxation does not change ML maximality of the truth**
for the exact variable-length objective: the truth is maximal against every
half-integral candidate iff it is maximal against every integer candidate.  The
`⇐` direction is the doubling theorem; the `⇒` direction uses that every integer
flow is a half-integral rational flow with the same objective. -/
theorem truth_half_maximal_iff_int_maximal (rep : W → W) (verts : List W)
    (edges : List (BdEdge A W)) (truth : RatFlow A W)
    (_htruth : HalfIntegralFeasible rep verts edges truth) (x : W → ℕ) :
    (∀ f, HalfIntegralFeasible rep verts edges f →
        ratObj rep edges f x verts ≤ ratObj rep edges truth x verts) ↔
      (∀ g, IntegerFeasible rep verts edges g →
        intObj rep edges g x verts ≤ ratObj rep edges truth x verts) := by
  constructor
  · intro h g hg
    obtain ⟨d, hd⟩ := hg
    have hrat : HalfIntegralFeasible rep verts edges (fun e => (g e : ℚ)) := by
      refine ⟨?_, ?_⟩
      · intro e
        exact ⟨2 * (g e : ℤ), by push_cast; ring⟩
      · exact ⟨fun v => (d v : ℚ), feasible62Rat_of_feasible62 rep verts edges g d hd⟩
    have hle := h (fun e => (g e : ℚ)) hrat
    rwa [ratObj_of_int] at hle
  · intro h f hf
    obtain ⟨d, hd⟩ := hf.2
    have hrat : ratObj rep edges f x verts = qExactLik d x verts := by
      unfold ratObj
      exact qExactLik_congr_on (fun v => qThroughput rep f edges v) d x verts
        (fun v hv => hd.2.2.2 v (by simpa using hv))
    have hg : IntegerFeasible rep verts edges (halfDoubleNat f hf.1) :=
      ⟨fun v => throughput A W rep (halfDoubleNat f hf.1) edges v,
        halfIntegral_double_feasible62 rep verts edges f d hf.1 hd⟩
    have hle := h (halfDoubleNat f hf.1) hg
    have hbridge : intObj rep edges (halfDoubleNat f hf.1) x verts
        = qExactLik d x verts := by
      unfold intObj
      exact no_half_integral_gap_exact rep verts edges f d hf.1 hd x
    rw [hbridge] at hle
    rw [hrat]
    exact hle

/-! ## Non-vacuity: the relaxation is a strict enlargement

A four-edge bidirected graph on two molecule classes `{0,1}` with the
half-integral circulation `f = (1/2,1/2,1/2,1/2)` is §6.2-feasible (throughput
`(1,1)`) but has no integral representative, so the half-integral class is a
*strict* superset of the integer class.  Its double is the literal integer
`Feasible62` flow `(1,1,1,1)`. -/

namespace Witness

abbrev A0 : Type := Unit
abbrev W2 : Type := Fin 2

/-- The molecule-class representative map: identity. -/
def rep2 : W2 → W2 := id

def e00 : BdEdge A0 W2 := ⟨0, 0, 1, 1, -1⟩
def e01 : BdEdge A0 W2 := ⟨0, 1, 1, 1, -1⟩
def e10 : BdEdge A0 W2 := ⟨1, 0, 1, 1, -1⟩
def e11 : BdEdge A0 W2 := ⟨1, 1, 1, 1, -1⟩

/-- The four-edge bidirected graph. -/
def edges2 : List (BdEdge A0 W2) := [e00, e01, e10, e11]

/-- The half-integral circulation: `1/2` on each of the four graph edges. -/
def halfFlow : RatFlow A0 W2 :=
  fun e => if e ∈ edges2 then (1 / 2 : ℚ) else 0

theorem halfFlow_isHalfIntegral : IsHalfIntegral halfFlow := by
  intro e
  by_cases h : e ∈ edges2
  · exact ⟨1, by simp [halfFlow, h]⟩
  · exact ⟨0, by simp [halfFlow, h]⟩

/-- The half-integral circulation is §6.2-feasible with throughput `(1,1)`. -/
theorem halfFlow_feasible : Feasible62Rat rep2 [0, 1] edges2 halfFlow (fun _ => 1) := by
  unfold Feasible62Rat
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he
    simp only [edges2, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with h | h | h | h <;> subst h <;>
      norm_num [halfFlow, edges2, e00, e01, e10, e11]
  · intro v hv
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with h | h <;> subst h <;>
      norm_num [qThroughput, halfFlow, edges2, rep2, e00, e01, e10, e11]
  · intro v hv
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with h | h <;> subst h <;>
      norm_num [qBalance, halfFlow, edges2, rep2, e00, e01, e10, e11]
  · intro v hv
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with h | h <;> subst h <;>
      norm_num [qThroughput, halfFlow, edges2, rep2, e00, e01, e10, e11]

/-- The half-integral circulation has no integral representative: the edge `e01`
carries flow `1/2`, which is not a natural number. -/
theorem halfFlow_not_integral :
    ¬ ∃ g : BdFlow A0 W2, (fun e => (g e : ℚ)) = halfFlow := by
  rintro ⟨g, hg⟩
  have h01 : (g e01 : ℚ) = (1 / 2 : ℚ) := by
    have := congrFun hg e01
    simpa [halfFlow, edges2] using this
  have h2 : (2 : ℚ) * (g e01 : ℚ) = 1 := by rw [h01]; norm_num
  have h2n : 2 * g e01 = 1 := by exact_mod_cast h2
  omega

/-- **The half-integral relaxation is a strict enlargement** of the integer
candidate point set on this family. -/
theorem integral_strict_subset_half_integral :
    HalfIntegralFeasible rep2 [0, 1] edges2 halfFlow ∧
      ¬ ∃ g : BdFlow A0 W2, (fun e => (g e : ℚ)) = halfFlow :=
  ⟨⟨halfFlow_isHalfIntegral, ⟨fun _ => 1, halfFlow_feasible⟩⟩, halfFlow_not_integral⟩

/-- The double of the half-integral circulation is a literal integer `Feasible62`
flow. -/
theorem halfFlow_double_feasible :
    Feasible62 A0 W2 rep2 [0, 1] edges2 (halfDoubleNat halfFlow halfFlow_isHalfIntegral)
      (noTerminals W2)
      (fun v => throughput A0 W2 rep2 (halfDoubleNat halfFlow halfFlow_isHalfIntegral)
        edges2 v) :=
  halfIntegral_double_feasible62 rep2 [0, 1] edges2 halfFlow (fun _ => 1)
    halfFlow_isHalfIntegral halfFlow_feasible

/-- On the witness, the half-integral circulation and its integer double have the
same exact likelihood on an arbitrary sample (here `x = (1,2)`). -/
theorem halfFlow_double_same_likelihood :
    qExactLik (fun v => (throughput A0 W2 rep2
          (halfDoubleNat halfFlow halfFlow_isHalfIntegral) edges2 v : ℚ)) (fun v => (v : ℕ) + 1) [0, 1]
      = qExactLik (fun _ => (1 : ℚ)) (fun v => (v : ℕ) + 1) [0, 1] :=
  no_half_integral_gap_exact rep2 [0, 1] edges2 halfFlow (fun _ => 1)
    halfFlow_isHalfIntegral halfFlow_feasible (fun v => (v : ℕ) + 1)

end Witness

end AssemblyP1.Section62HalfIntegralSourceML
