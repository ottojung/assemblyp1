import AssemblyP1.ExactRigidityCriterion

set_option linter.unusedVariables false

/-!
# The length-3 antiparallel bridge: a rigid repetitive support beyond the bridge
(issue #257, §8.1)

This module advances open item **§8.1** of
`docs/source-notes/issue-257-rigid-read-graphs.md` past both the *bouquet* family
of `AssemblyP1/RigidityBouquet.lean` and the *antiparallel bridge* of
`AssemblyP1/RigidityBridge.lean`. It does **not** redefine or re-prove any merged
result: it imports `AssemblyP1.ExactRigidityCriterion`
(`nonrigid_iff_exists_delta`, Theorem 1) and is a new topology with a new
phenomenon.

## The topology

The merged bridge is the complete digraph `K₃*` — two `2`-cycles through a hub
`v`, joined by an antiparallel arc pair between their interior vertices. Its
classification (`RigidityBridge.bridgeA_rigid_iff_trivial`) says the bridge is
rigid **iff** every edge has multiplicity `1`; every repetitive bridge is
non-rigid.

Here we replace each `2`-cycle by a **`3`-cycle**:

```
C1 : v → x → a₂ → v        C2 : v → y → b₂ → v
bridge : x → y , y → x
```

on the five vertices `v, x, a₂, y, b₂`, with eight arcs. This is the
*length-3 antiparallel bridge*. It has the same cycle rank `4` as the merged
bridge but is **not** covered by it, and — the point of this module — it
**refutes** the natural generalisation of the bridge classification: the
length-3 bridge is rigid for multiplicities `(m₁, m₂, f) = (1, 1, 2)`, i.e. a
*repetitive* support (the bridge arcs are traversed twice) that is nevertheless
rigid. Thus "rigid iff all multiplicities `1`" is specific to `2`-cycles.

## Main results

* `length3Bridge_nonrigid_iff`: the exact four-variable criterion. A circulation
  is determined by four integers `(a, c, u, w)` (`a` on `v → x`, `c` on `v → y`,
  `u` on `x → y`, `w` on `y → x`); the six remaining arc values are forced by
  balance, and zero total mass is `3a + 3c + u + w = 0`. The box constraints
  genuinely couple the parameters.
* `length3Bridge_rigid_iff`: the complete classification
  `Rigid ↔ m₁ = 1 ∧ m₂ = 1 ∧ f ≤ 2`.
* `length3Bridge_rigid_repetitive`: the kernel-checked rigid repetitive instance
  `(m₁, m₂, f) = (1, 1, 2)`.
* `length3Bridge_nonrigid_m1`, `length3Bridge_nonrigid_m2`,
  `length3Bridge_nonrigid_f`: explicit non-rigidity witnesses in every other
  case.

## Epistemic status

All theorems are kernel-checked with only `[propext, Classical.choice,
Quot.sound]` (`AssemblyP1.RigidityLength3BridgeAudit`); no `sorry`/`admit`/
`axiom`/`native_decide`. The topology is an *abstract* oriented support graph;
realizability as a de Bruijn read-support is not claimed (as for the merged
bridge). The general residual — a *polynomial* min-cut/max-flow closed form for
arbitrary supports, or a proof that none exists — remains **OPEN** (§8.1/§8.2).
-/

namespace AssemblyP1.RigidityLength3Bridge

open Finset BigOperators

/-- Vertices: `0 = v`, `1 = x`, `2 = a₂`, `3 = y`, `4 = b₂`. -/
abbrev Vtx := Fin 5

/-- Arcs: `0 = v→x`, `1 = x→a₂`, `2 = a₂→v`, `3 = v→y`, `4 = y→b₂`,
`5 = b₂→v`, `6 = x→y`, `7 = y→x`. -/
abbrev Arc := Fin 8

/-- Tail map of the length-3 bridge. -/
def l3tail : Arc → Vtx := ![0, 1, 2, 0, 3, 4, 1, 3]

/-- Head map of the length-3 bridge. -/
def l3head : Arc → Vtx := ![1, 2, 0, 3, 4, 0, 3, 1]

/-- Every vertex is a node. -/
def l3nodes : Finset Vtx := Finset.univ

/-- Every one of the eight arcs is a support edge. -/
def l3edges : Finset Arc := Finset.univ

/-- Out-arcs of `v`. -/
def l3outF (v : Vtx) : Finset Arc := l3edges.filter (fun e => l3tail e = v)

/-- In-arcs of `v`. -/
def l3inF (v : Vtx) : Finset Arc := l3edges.filter (fun e => l3head e = v)

/-- Explicit balance predicate on the eight arcs. -/
def BalancedL3 (B : Arc → ℤ) : Prop :=
  ∀ v ∈ l3nodes, (∑ e ∈ l3outF v, B e) = (∑ e ∈ l3inF v, B e)

/-- `BalancedL3` is exactly the support-domain `BalancedZ` of
`ExactRigidityCriterion`. -/
lemma balancedL3_iff_balancedZ (B : Arc → ℤ) :
    BalancedL3 B ↔
      AssemblyP1.ExactRigidityCriterion.BalancedZ l3tail l3head l3nodes l3edges B :=
  Iff.rfl

/-- The multiplicity vector `A` of the length-3 bridge: `m1` on each `C1` arc,
`m2` on each `C2` arc, `f` on each bridge arc. -/
def l3A (m1 m2 f : ℕ) : Arc → ℤ := fun i => ![m1, m1, m1, m2, m2, m2, f, f] i

/-- Total mass of the length-3 bridge base circulation. -/
def l3G (m1 m2 f : ℕ) : ℕ := 3 * m1 + 3 * m2 + 2 * f

lemma l3A_apply_zero (m1 m2 f : ℕ) : l3A m1 m2 f 0 = m1 := rfl
lemma l3A_apply_one (m1 m2 f : ℕ) : l3A m1 m2 f 1 = m1 := rfl
lemma l3A_apply_two (m1 m2 f : ℕ) : l3A m1 m2 f 2 = m1 := rfl
lemma l3A_apply_three (m1 m2 f : ℕ) : l3A m1 m2 f 3 = m2 := rfl
lemma l3A_apply_four (m1 m2 f : ℕ) : l3A m1 m2 f 4 = m2 := rfl
lemma l3A_apply_five (m1 m2 f : ℕ) : l3A m1 m2 f 5 = m2 := rfl
lemma l3A_apply_six (m1 m2 f : ℕ) : l3A m1 m2 f 6 = f := rfl
lemma l3A_apply_seven (m1 m2 f : ℕ) : l3A m1 m2 f 7 = f := rfl

@[simp] lemma l3outF_zero : l3outF 0 = ({0, 3} : Finset Arc) := by decide
@[simp] lemma l3outF_one : l3outF 1 = ({1, 6} : Finset Arc) := by decide
@[simp] lemma l3outF_two : l3outF 2 = ({2} : Finset Arc) := by decide
@[simp] lemma l3outF_three : l3outF 3 = ({4, 7} : Finset Arc) := by decide
@[simp] lemma l3outF_four : l3outF 4 = ({5} : Finset Arc) := by decide
@[simp] lemma l3inF_zero : l3inF 0 = ({2, 5} : Finset Arc) := by decide
@[simp] lemma l3inF_one : l3inF 1 = ({0, 7} : Finset Arc) := by decide
@[simp] lemma l3inF_two : l3inF 2 = ({1} : Finset Arc) := by decide
@[simp] lemma l3inF_three : l3inF 3 = ({3, 6} : Finset Arc) := by decide
@[simp] lemma l3inF_four : l3inF 4 = ({4} : Finset Arc) := by decide

/-- The length-3 bridge base circulation is balanced. -/
lemma l3A_balancedL3 (m1 m2 f : ℕ) : BalancedL3 (l3A m1 m2 f) := by
  intro v _
  fin_cases v <;>
    simp [l3A]

/-- The length-3 bridge base circulation is balanced. -/
lemma l3A_balanced (m1 m2 f : ℕ) :
    AssemblyP1.ExactRigidityCriterion.BalancedZ l3tail l3head l3nodes l3edges
      (l3A m1 m2 f) :=
  (balancedL3_iff_balancedZ (l3A m1 m2 f)).mp (l3A_balancedL3 m1 m2 f)

/-- The length-3 bridge base circulation has total mass `l3G`. -/
lemma l3A_total (m1 m2 f : ℕ) :
    ∑ e ∈ l3edges, l3A m1 m2 f e = (l3G m1 m2 f : ℤ) := by
  simp only [l3edges, Fin.sum_univ_eight, l3A, l3G]
  push_cast
  ring

/-! ## The four-variable exact criterion -/

/-- The four-parameter form of a length-3 bridge circulation. -/
def phi (a c u w : ℤ) : Arc → ℤ := ![a, a - u + w, a - u + w, c, c - w + u, c - w + u, u, w]

lemma phi_zero : phi 0 0 0 0 = 0 := by
  funext e; fin_cases e <;> rfl

lemma phi_eq_zero_iff (a c u w : ℤ) :
    phi a c u w = 0 ↔ a = 0 ∧ c = 0 ∧ u = 0 ∧ w = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h3 := congrFun h 3
    have h6 := congrFun h 6
    have h7 := congrFun h 7
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simpa [phi] using ‹_›
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact phi_zero

/-- `BalancedL3` is exactly the four independent balance equations (the hub
balance `δ 0 + δ 3 = δ 2 + δ 5` is a consequence). -/
lemma balancedL3_iff_eqs (δ : Arc → ℤ) :
    BalancedL3 δ ↔
      δ 2 = δ 1 ∧ δ 5 = δ 4 ∧ δ 1 + δ 6 = δ 0 + δ 7 ∧ δ 4 + δ 7 = δ 3 + δ 6 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using h 2 (Finset.mem_univ 2)
    · simpa using h 4 (Finset.mem_univ 4)
    · simpa using h 1 (Finset.mem_univ 1)
    · simpa using h 3 (Finset.mem_univ 3)
  · rintro ⟨h21, h54, h16, h47⟩ v _
    fin_cases v <;> simp
    all_goals linarith

lemma phi_balancedL3 (a c u w : ℤ) : BalancedL3 (phi a c u w) := by
  intro v _
  fin_cases v <;> simp [phi]
  all_goals ring

lemma phi_sum (a c u w : ℤ) :
    ∑ e ∈ l3edges, phi a c u w e = 3 * a + 3 * c + u + w := by
  simp only [l3edges, Fin.sum_univ_eight]
  simp [phi]
  ring

lemma phi_of_balanced (δ : Arc → ℤ) (h : BalancedL3 δ) :
    δ = phi (δ 0) (δ 3) (δ 6) (δ 7) := by
  have ⟨h21, h54, h16, h47⟩ := (balancedL3_iff_eqs δ).mp h
  funext e
  fin_cases e <;> simp [phi]
  all_goals omega

/-- **Exact four-variable criterion for the length-3 antiparallel bridge.** The
length-3 bridge base circulation is non-rigid **iff** there are integers
`a, c, u, w`, not all zero, with `3a + 3c + u + w = 0` (zero total mass) and the
six coupled box inequalities `a ≥ 1 - m1`, `a - u + w ≥ 1 - m1`,
`c ≥ 1 - m2`, `c - w + u ≥ 1 - m2`, `u ≥ 1 - f`, `w ≥ 1 - f`. This is the
length-3 analogue of `AssemblyP1.RigidityBridge.bridge_nonrigid_iff`; the box
constraints couple `a` with `w - u` and `c` with `u - w`, and the zero-sum
coefficients are `3, 3, 1, 1` rather than the bridge's `2, 2, 1, 1`. -/
theorem length3Bridge_nonrigid_iff (m1 m2 f : ℕ) (hm1 : 1 ≤ m1) (hm2 : 1 ≤ m2)
    (hf : 1 ≤ f) :
    (¬ AssemblyP1.ExactRigidityCriterion.Rigid l3tail l3head l3nodes l3edges
        (l3A m1 m2 f) (l3G m1 m2 f)) ↔
      ∃ a c u w : ℤ,
        (a ≠ 0 ∨ c ≠ 0 ∨ u ≠ 0 ∨ w ≠ 0) ∧
        3 * a + 3 * c + u + w = 0 ∧
        (1 - (m1 : ℤ) ≤ a) ∧ (1 - (m1 : ℤ) ≤ a - u + w) ∧
        (1 - (m2 : ℤ) ≤ c) ∧ (1 - (m2 : ℤ) ≤ c - w + u) ∧
        (1 - (f : ℤ) ≤ u) ∧ (1 - (f : ℤ) ≤ w) := by
  rw [AssemblyP1.ExactRigidityCriterion.nonrigid_iff_exists_delta l3tail l3head l3nodes l3edges
      (l3A m1 m2 f) (l3G m1 m2 f) (l3A_balanced m1 m2 f) (l3A_total m1 m2 f)]
  constructor
  · rintro ⟨δ, ⟨e0, he0, hne⟩, hδbal, hδsum, hδbox⟩
    have hbal := (balancedL3_iff_eqs δ).mp hδbal
    have hphi := phi_of_balanced δ hδbal
    have hδ1 : δ 1 = δ 0 - δ 6 + δ 7 := by linarith [hbal.2.2.1]
    have hδ4 : δ 4 = δ 3 - δ 7 + δ 6 := by linarith [hbal.2.2.2]
    refine ⟨δ 0, δ 3, δ 6, δ 7, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      obtain ⟨h0, h3, h6, h7⟩ := hcon
      apply hne
      rw [hphi, h0, h3, h6, h7]
      exact congrFun phi_zero e0
    · have hz := hδsum
      rw [AssemblyP1.ExactRigidityCriterion.ZeroSum] at hz
      rw [hphi, phi_sum] at hz
      exact hz
    · have := hδbox 0 (Finset.mem_univ 0); simpa [l3A] using this
    · have := hδbox 1 (Finset.mem_univ 1); rw [hδ1] at this; simpa [l3A] using this
    · have := hδbox 3 (Finset.mem_univ 3); simpa [l3A] using this
    · have := hδbox 4 (Finset.mem_univ 4); rw [hδ4] at this; simpa [l3A] using this
    · have := hδbox 6 (Finset.mem_univ 6); simpa [l3A] using this
    · have := hδbox 7 (Finset.mem_univ 7); simpa [l3A] using this
  · rintro ⟨a, c, u, w, hne, hsum, ha, hb, hc, hd, hu, hw⟩
    have hne' : ∃ e ∈ l3edges, phi a c u w e ≠ 0 := by
      by_contra h
      push Not at h
      have h0 : a = 0 := by simpa [phi] using h 0 (Finset.mem_univ 0)
      have h3 : c = 0 := by simpa [phi] using h 3 (Finset.mem_univ 3)
      have h6 : u = 0 := by simpa [phi] using h 6 (Finset.mem_univ 6)
      have h7 : w = 0 := by simpa [phi] using h 7 (Finset.mem_univ 7)
      rw [h0, h3, h6, h7] at hne
      simp at hne
    refine ⟨phi a c u w, hne',
      (balancedL3_iff_balancedZ (phi a c u w)).mp (phi_balancedL3 a c u w), ?_, ?_⟩
    · rw [AssemblyP1.ExactRigidityCriterion.ZeroSum, phi_sum]; exact hsum
    · intro e _
      fin_cases e <;> simp only [phi, l3A] <;>
        first
          | exact ha | exact hb | exact hc | exact hd | exact hu | exact hw

/-! ## Classification and witnesses -/

/-- Non-rigidity witness when the first cycle has multiplicity `≥ 2`:
`(a, c, u, w) = (-1, 1, 0, 0)`. -/
theorem length3Bridge_nonrigid_m1 (m1 m2 f : ℕ) (hm1 : 2 ≤ m1) (hm2 : 1 ≤ m2)
    (hf : 1 ≤ f) :
    ¬ AssemblyP1.ExactRigidityCriterion.Rigid l3tail l3head l3nodes l3edges
        (l3A m1 m2 f) (l3G m1 m2 f) := by
  rw [length3Bridge_nonrigid_iff m1 m2 f (by omega) hm2 hf]
  refine ⟨-1, 1, 0, 0, Or.inl (by norm_num), by ring, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals omega

/-- Non-rigidity witness when the second cycle has multiplicity `≥ 2`:
`(a, c, u, w) = (1, -1, 0, 0)`. -/
theorem length3Bridge_nonrigid_m2 (m1 m2 f : ℕ) (hm1 : 1 ≤ m1) (hm2 : 2 ≤ m2)
    (hf : 1 ≤ f) :
    ¬ AssemblyP1.ExactRigidityCriterion.Rigid l3tail l3head l3nodes l3edges
        (l3A m1 m2 f) (l3G m1 m2 f) := by
  rw [length3Bridge_nonrigid_iff m1 m2 f hm1 (by omega) hf]
  refine ⟨1, -1, 0, 0, Or.inr (Or.inl (by norm_num)), by ring, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals omega

/-- Non-rigidity witness when `m1 = m2 = 1` and the bridge has multiplicity
`≥ 3`: `(a, c, u, w) = (1, 0, -1, -2)`. -/
theorem length3Bridge_nonrigid_f (m1 m2 f : ℕ) (hm1 : m1 = 1) (hm2 : m2 = 1)
    (hf : 3 ≤ f) :
    ¬ AssemblyP1.ExactRigidityCriterion.Rigid l3tail l3head l3nodes l3edges
        (l3A m1 m2 f) (l3G m1 m2 f) := by
  subst hm1; subst hm2
  rw [length3Bridge_nonrigid_iff 1 1 f (by norm_num) (by norm_num) (by omega)]
  refine ⟨1, 0, -1, -2, Or.inl (by norm_num), by ring, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals omega

/-- The rigid repetitive instance `(m1, m2, f) = (1, 1, 2)`: both bridge arcs are
traversed twice, yet the support is rigid. This is the kernel-checked refutation
of the naive generalisation of `RigidityBridge.bridgeA_rigid_iff_trivial`. -/
theorem length3Bridge_rigid_repetitive :
    AssemblyP1.ExactRigidityCriterion.Rigid l3tail l3head l3nodes l3edges
      (l3A 1 1 2) (l3G 1 1 2) := by
  by_contra hnr
  rw [length3Bridge_nonrigid_iff 1 1 2 (by norm_num) (by norm_num) (by norm_num)] at hnr
  obtain ⟨a, c, u, w, hne, hsum, ha, hb, hc, hd, hu, hw⟩ := hnr
  simp only [Nat.cast_one, Nat.cast_ofNat] at ha hb hc hd hu hw
  have hac : a + c ≤ 0 := by omega
  have ha0 : a = 0 := by omega
  have hc0 : c = 0 := by omega
  have hu0 : u = 0 := by omega
  have hw0 : w = 0 := by omega
  rcases hne with h | h | h | h
  · exact h ha0
  · exact h hc0
  · exact h hu0
  · exact h hw0

/-- **Complete rigidity classification of the length-3 antiparallel bridge.**
For multiplicities `m1, m2, f ≥ 1`, the base circulation is rigid **iff**
`m1 = 1 ∧ m2 = 1 ∧ f ≤ 2`. In particular the length-3 bridge has rigid
*repetitive* members (`f = 2`), so the merged `2`-cycle bridge classification
does **not** generalise. -/
theorem length3Bridge_rigid_iff (m1 m2 f : ℕ) (hm1 : 1 ≤ m1) (hm2 : 1 ≤ m2)
    (hf : 1 ≤ f) :
    AssemblyP1.ExactRigidityCriterion.Rigid l3tail l3head l3nodes l3edges
        (l3A m1 m2 f) (l3G m1 m2 f) ↔
      m1 = 1 ∧ m2 = 1 ∧ f ≤ 2 := by
  constructor
  · intro hr
    refine ⟨?_, ?_, ?_⟩
    · by_contra h
      exact absurd hr (length3Bridge_nonrigid_m1 m1 m2 f (by omega) hm2 hf)
    · by_contra h
      exact absurd hr (length3Bridge_nonrigid_m2 m1 m2 f hm1 (by omega) hf)
    · by_contra h
      have h1 : m1 = 1 := by
        by_contra h'
        exact absurd hr (length3Bridge_nonrigid_m1 m1 m2 f (by omega) hm2 hf)
      have h2 : m2 = 1 := by
        by_contra h'
        exact absurd hr (length3Bridge_nonrigid_m2 m1 m2 f hm1 (by omega) hf)
      exact absurd hr (length3Bridge_nonrigid_f m1 m2 f h1 h2 (by omega))
  · rintro ⟨rfl, rfl, hf2⟩
    interval_cases f
    · -- f = 1: every arc has multiplicity 1
      by_contra hnr
      rw [length3Bridge_nonrigid_iff 1 1 1 (by norm_num) (by norm_num) (by norm_num)] at hnr
      obtain ⟨a, c, u, w, hne, hsum, ha, hb, hc, hd, hu, hw⟩ := hnr
      simp only [Nat.cast_one] at ha hb hc hd hu hw
      have : a = 0 ∧ c = 0 ∧ u = 0 ∧ w = 0 := by omega
      rcases this with ⟨rfl, rfl, rfl, rfl⟩
      simp at hne
    · -- f = 2: the rigid repetitive instance
      exact length3Bridge_rigid_repetitive

end AssemblyP1.RigidityLength3Bridge
