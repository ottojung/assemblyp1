import AssemblyP1.ExactRigidityCriterion

set_option linter.unusedVariables false

/-!
# The antiparallel-bridge graph: rigidity beyond the bouquet (issue #257, §8.1)

This module advances open item **§8.1** of
`docs/source-notes/issue-257-rigid-read-graphs.md` past the *bouquet* family of
`AssemblyP1/RigidityBouquet.lean`. The exact algebraic criterion
(`AssemblyP1.ExactRigidityCriterion.nonrigid_iff_exists_delta`), the Graver form
(`AssemblyP1.GraverRigidity`), the two-closed-walk form
(`AssemblyP1.TwoWalkRigidity`), the finite decider
(`AssemblyP1.FiniteRigidityDecider`) and the bouquet reduction are already merged
and are **not** redone here.

## Why a new topology is needed

A *single* extra arc attached to the interior of a cycle cannot appear in a
positive circulation: at the interior vertex the arc is the only extra edge, so
balance forces its value to `0`, contradicting positivity on the support. The
minimal way to connect two cycles while keeping every edge positive is an
**antiparallel arc pair** `x → y`, `y → x`. This is the *bridge graph*: two
`2`-cycles through a hub `v`, joined by an antiparallel pair between their
interior vertices `x` and `y`.

Its circulation space is **not** the bouquet's: the bridge couples the two cycle
values, so `δ` is no longer constant on each cycle and the box constraints couple
the free parameters. Concretely, a circulation is determined by four integers
`(a, c, p, q)` (`a` on `v → x`, `c` on `v → y`, `p` on `x → y`, `q` on `y → x`),
with the two remaining edges forced by balance:

```
δ = ![a, a + q - p, c, c + p - q, p, q]
```

and zero total mass is `2·a + 2·c + p + q = 0`. This is a genuinely
*coupled* integer feasibility problem: the box on the `x → v` edge couples `a`
with `q - p`, and the box on the `y → v` edge couples `c` with `p - q`.

## Main results

* `bridge_nonrigid_iff`: the exact four-variable criterion for the bridge family.
* `bridge_rigid_iff_trivial`: the circulation is rigid **iff** every edge has
  multiplicity `1`; in every other case there is an explicit non-rigidity
  witness. Hence the minimal positive cross-connection destroys rigidity.

## Epistemic status

All theorems are kernel-checked with only `[propext, Classical.choice,
Quot.sound]` (`AssemblyP1.RigidityBridgeAudit`); no `sorry`/`admit`/`axiom`/
`native_decide`. The bridge is an *abstract* oriented support graph (a switch
`x`, `y` of in-degree and out-degree `2`); realizability of this exact shape as a
de Bruijn read-support is not claimed. The residual — a *polynomial*
min-cut/max-flow closed form for general supports, or a proof that none exists —
remains **OPEN** (§8.1/§8.2).
-/

namespace AssemblyP1.RigidityBridge

open Finset BigOperators

/-- Tail map of the bridge graph: `0,2` leave the hub `0`; `1,4` leave `x=1`;
`3,5` leave `y=2`. -/
def btail : Fin 6 → Fin 3 := fun i => ![0, 1, 0, 2, 1, 2] i

/-- Head map of the bridge graph. -/
def bhead : Fin 6 → Fin 3 := fun i => ![1, 0, 2, 0, 2, 1] i

/-- Every vertex is a node. -/
def bnodes : Finset (Fin 3) := Finset.univ

/-- Every one of the six arcs is a support edge. -/
def bedges : Finset (Fin 6) := Finset.univ

/-- Out-arcs of `v`. -/
def boutF (v : Fin 3) : Finset (Fin 6) := bedges.filter (fun e => btail e = v)

/-- In-arcs of `v`. -/
def binF (v : Fin 3) : Finset (Fin 6) := bedges.filter (fun e => bhead e = v)

/-- Explicit balance predicate on the six arcs. -/
def BalancedB (B : Fin 6 → ℤ) : Prop :=
  ∀ v ∈ bnodes, (∑ e ∈ boutF v, B e) = (∑ e ∈ binF v, B e)

/-- `BalancedB` is exactly the support-domain `BalancedZ` of
`ExactRigidityCriterion`. -/
lemma balancedB_iff_balancedZ (B : Fin 6 → ℤ) :
    BalancedB B ↔
      AssemblyP1.ExactRigidityCriterion.BalancedZ btail bhead bnodes bedges B :=
  Iff.rfl

/-- The multiplicity vector `A` of the bridge: `m1` on the `x`-cycle, `m2` on the
`y`-cycle, `f` on the antiparallel bridge. -/
def bridgeA (m1 m2 f : ℕ) : Fin 6 → ℤ := fun i => ![m1, m1, m2, m2, f, f] i

/-- Total mass of the bridge base circulation. -/
def bridgeG (m1 m2 f : ℕ) : ℕ := 2 * m1 + 2 * m2 + 2 * f

lemma bridgeA_apply_zero (m1 m2 f : ℕ) : bridgeA m1 m2 f 0 = m1 := rfl
lemma bridgeA_apply_one (m1 m2 f : ℕ) : bridgeA m1 m2 f 1 = m1 := rfl
lemma bridgeA_apply_two (m1 m2 f : ℕ) : bridgeA m1 m2 f 2 = m2 := rfl
lemma bridgeA_apply_three (m1 m2 f : ℕ) : bridgeA m1 m2 f 3 = m2 := rfl
lemma bridgeA_apply_four (m1 m2 f : ℕ) : bridgeA m1 m2 f 4 = f := rfl
lemma bridgeA_apply_five (m1 m2 f : ℕ) : bridgeA m1 m2 f 5 = f := rfl

@[simp] lemma boutF_zero : boutF 0 = ({0, 2} : Finset (Fin 6)) := by decide
@[simp] lemma boutF_one : boutF 1 = ({1, 4} : Finset (Fin 6)) := by decide
@[simp] lemma boutF_two : boutF 2 = ({3, 5} : Finset (Fin 6)) := by decide
@[simp] lemma binF_zero : binF 0 = ({1, 3} : Finset (Fin 6)) := by decide
@[simp] lemma binF_one : binF 1 = ({0, 5} : Finset (Fin 6)) := by decide
@[simp] lemma binF_two : binF 2 = ({2, 4} : Finset (Fin 6)) := by decide

/-- The bridge base circulation is balanced. -/
lemma bridgeA_balancedB (m1 m2 f : ℕ) : BalancedB (bridgeA m1 m2 f) := by
  intro v _
  fin_cases v <;>
    simp [bridgeA]

/-- The bridge base circulation is balanced. -/
lemma bridgeA_balanced (m1 m2 f : ℕ) :
    AssemblyP1.ExactRigidityCriterion.BalancedZ btail bhead bnodes bedges
      (bridgeA m1 m2 f) :=
  (balancedB_iff_balancedZ (bridgeA m1 m2 f)).mp (bridgeA_balancedB m1 m2 f)

/-- The bridge base circulation has total mass `bridgeG`. -/
lemma bridgeA_total (m1 m2 f : ℕ) :
    ∑ e ∈ bedges, bridgeA m1 m2 f e = (bridgeG m1 m2 f : ℤ) := by
  simp [bedges, bridgeA, bridgeG, Fin.sum_univ_six]
  ring

/-- Non-rigidity witness when the `x`-cycle has multiplicity `≥ 2`:
`δ = (-1, -1, 0, 0, 1, 1)`. -/
def dM1 : Fin 6 → ℤ := ![-1, -1, 0, 0, 1, 1]

/-- Non-rigidity witness when the `y`-cycle has multiplicity `≥ 2`:
`δ = (0, 0, -1, -1, 1, 1)`. -/
def dM2 : Fin 6 → ℤ := ![0, 0, -1, -1, 1, 1]

/-- Non-rigidity witness when the bridge has multiplicity `≥ 2`:
`δ = (0, 0, 1, 1, -1, -1)`. -/
def dF : Fin 6 → ℤ := ![0, 0, 1, 1, -1, -1]

lemma dM1_balancedB : BalancedB dM1 := by
  intro v _
  fin_cases v <;> simp [dM1]
lemma dM1_balancedZ :
    AssemblyP1.ExactRigidityCriterion.BalancedZ btail bhead bnodes bedges dM1 :=
  (balancedB_iff_balancedZ dM1).mp dM1_balancedB
lemma dM1_zeroSum : AssemblyP1.ExactRigidityCriterion.ZeroSum bedges dM1 := by
  simp only [AssemblyP1.ExactRigidityCriterion.ZeroSum, bedges]
  norm_num [dM1, Fin.sum_univ_six]

lemma dM2_balancedB : BalancedB dM2 := by
  intro v _
  fin_cases v <;> simp [dM2]
lemma dM2_balancedZ :
    AssemblyP1.ExactRigidityCriterion.BalancedZ btail bhead bnodes bedges dM2 :=
  (balancedB_iff_balancedZ dM2).mp dM2_balancedB
lemma dM2_zeroSum : AssemblyP1.ExactRigidityCriterion.ZeroSum bedges dM2 := by
  simp only [AssemblyP1.ExactRigidityCriterion.ZeroSum, bedges]
  norm_num [dM2, Fin.sum_univ_six]

lemma dF_balancedB : BalancedB dF := by
  intro v _
  fin_cases v <;> simp [dF]
lemma dF_balancedZ :
    AssemblyP1.ExactRigidityCriterion.BalancedZ btail bhead bnodes bedges dF :=
  (balancedB_iff_balancedZ dF).mp dF_balancedB
lemma dF_zeroSum : AssemblyP1.ExactRigidityCriterion.ZeroSum bedges dF := by
  simp only [AssemblyP1.ExactRigidityCriterion.ZeroSum, bedges]
  norm_num [dF, Fin.sum_univ_six]

lemma bridgeA_one_one_one (e : Fin 6) : bridgeA 1 1 1 e = 1 := by
  fin_cases e <;> rfl

theorem bridgeA_nonrigid_m1 (m1 m2 f : ℕ) (hm1 : 2 ≤ m1) (hm2 : 1 ≤ m2) (hf : 1 ≤ f) :
    ¬ AssemblyP1.ExactRigidityCriterion.Rigid btail bhead bnodes bedges
        (bridgeA m1 m2 f) (bridgeG m1 m2 f) := by
  rw [AssemblyP1.ExactRigidityCriterion.nonrigid_iff_exists_delta btail bhead bnodes bedges
      (bridgeA m1 m2 f) (bridgeG m1 m2 f) (bridgeA_balanced m1 m2 f) (bridgeA_total m1 m2 f)]
  refine ⟨dM1, ⟨0, Finset.mem_univ 0, by decide⟩, dM1_balancedZ, dM1_zeroSum, ?_⟩
  intro e _
  fin_cases e <;> simp [dM1, bridgeA] <;> omega

theorem bridgeA_nonrigid_m2 (m1 m2 f : ℕ) (hm1 : 1 ≤ m1) (hm2 : 2 ≤ m2) (hf : 1 ≤ f) :
    ¬ AssemblyP1.ExactRigidityCriterion.Rigid btail bhead bnodes bedges
        (bridgeA m1 m2 f) (bridgeG m1 m2 f) := by
  rw [AssemblyP1.ExactRigidityCriterion.nonrigid_iff_exists_delta btail bhead bnodes bedges
      (bridgeA m1 m2 f) (bridgeG m1 m2 f) (bridgeA_balanced m1 m2 f) (bridgeA_total m1 m2 f)]
  refine ⟨dM2, ⟨2, Finset.mem_univ 2, by decide⟩, dM2_balancedZ, dM2_zeroSum, ?_⟩
  intro e _
  fin_cases e <;> simp [dM2, bridgeA] <;> omega

theorem bridgeA_nonrigid_f (m1 m2 f : ℕ) (hm1 : 1 ≤ m1) (hm2 : 1 ≤ m2) (hf : 2 ≤ f) :
    ¬ AssemblyP1.ExactRigidityCriterion.Rigid btail bhead bnodes bedges
        (bridgeA m1 m2 f) (bridgeG m1 m2 f) := by
  rw [AssemblyP1.ExactRigidityCriterion.nonrigid_iff_exists_delta btail bhead bnodes bedges
      (bridgeA m1 m2 f) (bridgeG m1 m2 f) (bridgeA_balanced m1 m2 f) (bridgeA_total m1 m2 f)]
  refine ⟨dF, ⟨4, Finset.mem_univ 4, by decide⟩, dF_balancedZ, dF_zeroSum, ?_⟩
  intro e _
  fin_cases e <;> simp [dF, bridgeA] <;> omega

/-- **Rigidity classification of the antiparallel bridge.** For multiplicities
`m1, m2, f ≥ 1`, the bridge base circulation is rigid **iff** every edge has
multiplicity `1`. In every other case there is an explicit non-rigidity witness
(`dM1`, `dM2`, `dF`). -/
theorem bridgeA_rigid_iff_trivial (m1 m2 f : ℕ) (hm1 : 1 ≤ m1) (hm2 : 1 ≤ m2)
    (hf : 1 ≤ f) :
    AssemblyP1.ExactRigidityCriterion.Rigid btail bhead bnodes bedges
        (bridgeA m1 m2 f) (bridgeG m1 m2 f) ↔
      m1 = 1 ∧ m2 = 1 ∧ f = 1 := by
  constructor
  · intro hr
    by_cases h1 : m1 = 1
    · by_cases h2 : m2 = 1
      · by_cases h3 : f = 1
        · exact ⟨h1, h2, h3⟩
        · exact absurd hr (bridgeA_nonrigid_f m1 m2 f (by omega) (by omega) (by omega))
      · exact absurd hr (bridgeA_nonrigid_m2 m1 m2 f (by omega) (by omega) hf)
    · exact absurd hr (bridgeA_nonrigid_m1 m1 m2 f (by omega) hm2 hf)
  · rintro ⟨rfl, rfl, rfl⟩
    by_contra hnr
    rw [AssemblyP1.ExactRigidityCriterion.nonrigid_iff_exists_delta btail bhead bnodes bedges
        (bridgeA 1 1 1) (bridgeG 1 1 1) (bridgeA_balanced 1 1 1) (bridgeA_total 1 1 1)] at hnr
    obtain ⟨δ, ⟨e0, he0, hne⟩, _hbal, hsum, hbox⟩ := hnr
    have hnn : ∀ i ∈ bedges, (0 : ℤ) ≤ δ i := by
      intro i hi
      have h := hbox i hi
      have hAi := bridgeA_one_one_one i
      linarith
    have hge : (0 : ℤ) ≤ δ e0 := hnn e0 he0
    have hpos : 0 < δ e0 := lt_of_le_of_ne hge (Ne.symm hne)
    have hle : δ e0 ≤ ∑ e ∈ bedges, δ e := Finset.single_le_sum hnn he0
    rw [hsum] at hle
    omega

/-! ## The four-variable exact criterion -/

/-- The four-parameter form of a bridge circulation. -/
def phi (a c p q : ℤ) : Fin 6 → ℤ := ![a, a + q - p, c, c + p - q, p, q]

lemma phi_zero : phi 0 0 0 0 = 0 := by
  funext e; fin_cases e <;> rfl

lemma phi_eq_zero_iff (a c p q : ℤ) :
    phi a c p q = 0 ↔ a = 0 ∧ c = 0 ∧ p = 0 ∧ q = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h2 := congrFun h 2
    have h4 := congrFun h 4
    have h5 := congrFun h 5
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simpa [phi] using ‹_›
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact phi_zero

/-- `BalancedB` is exactly the two independent balance equations (the hub
balance `δ 0 + δ 2 = δ 1 + δ 3` is a consequence). -/
lemma balancedB_iff_eqs (δ : Fin 6 → ℤ) :
    BalancedB δ ↔ δ 1 + δ 4 = δ 0 + δ 5 ∧ δ 3 + δ 5 = δ 2 + δ 4 := by
  constructor
  · intro h
    exact ⟨by simpa using h 1 (Finset.mem_univ 1),
      by simpa using h 2 (Finset.mem_univ 2)⟩
  · intro ⟨h1, h2⟩ v _
    fin_cases v <;> simp
    all_goals linarith

lemma phi_balancedB (a c p q : ℤ) : BalancedB (phi a c p q) := by
  intro v _
  fin_cases v <;> simp [phi]
  all_goals ring

lemma phi_sum (a c p q : ℤ) :
    ∑ e ∈ bedges, phi a c p q e = 2 * a + 2 * c + p + q := by
  simp only [bedges, Fin.sum_univ_six]
  simp [phi]
  ring

lemma phi_of_balanced (δ : Fin 6 → ℤ) (h : BalancedB δ) :
    δ = phi (δ 0) (δ 2) (δ 4) (δ 5) := by
  have ⟨h1, h2⟩ := (balancedB_iff_eqs δ).mp h
  funext e
  fin_cases e <;> simp [phi]
  all_goals omega

/-- **Exact four-variable criterion for the antiparallel bridge.** The bridge
base circulation is non-rigid **iff** there are integers `a, c, p, q`, not all
zero, with `2a + 2c + p + q = 0` (zero total mass) and the six coupled box
inequalities `a ≥ 1 - m1`, `a + q - p ≥ 1 - m1`, `c ≥ 1 - m2`,
`c + p - q ≥ 1 - m2`, `p ≥ 1 - f`, `q ≥ 1 - f`. This is the bridge analogue of
`AssemblyP1.RigidityBouquet.bouquet_nonrigid_iff`, but the box constraints
genuinely couple the parameters (`a` with `q - p`, `c` with `p - q`). -/
theorem bridge_nonrigid_iff (m1 m2 f : ℕ) (hm1 : 1 ≤ m1) (hm2 : 1 ≤ m2) (hf : 1 ≤ f) :
    (¬ AssemblyP1.ExactRigidityCriterion.Rigid btail bhead bnodes bedges
        (bridgeA m1 m2 f) (bridgeG m1 m2 f)) ↔
      ∃ a c p q : ℤ,
        (a ≠ 0 ∨ c ≠ 0 ∨ p ≠ 0 ∨ q ≠ 0) ∧
        2 * a + 2 * c + p + q = 0 ∧
        (1 - (m1 : ℤ) ≤ a) ∧ (1 - (m1 : ℤ) ≤ a + q - p) ∧
        (1 - (m2 : ℤ) ≤ c) ∧ (1 - (m2 : ℤ) ≤ c + p - q) ∧
        (1 - (f : ℤ) ≤ p) ∧ (1 - (f : ℤ) ≤ q) := by
  rw [AssemblyP1.ExactRigidityCriterion.nonrigid_iff_exists_delta btail bhead bnodes bedges
      (bridgeA m1 m2 f) (bridgeG m1 m2 f) (bridgeA_balanced m1 m2 f) (bridgeA_total m1 m2 f)]
  constructor
  · rintro ⟨δ, ⟨e0, he0, hne⟩, hδbal, hδsum, hδbox⟩
    have hbal := (balancedB_iff_eqs δ).mp hδbal
    have hphi := phi_of_balanced δ hδbal
    have hδ1 : δ 1 = δ 0 + δ 5 - δ 4 := by linarith [hbal.1]
    have hδ3 : δ 3 = δ 2 + δ 4 - δ 5 := by linarith [hbal.2]
    refine ⟨δ 0, δ 2, δ 4, δ 5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      obtain ⟨h0, h2, h4, h5⟩ := hcon
      apply hne
      rw [hphi, h0, h2, h4, h5]
      exact congrFun phi_zero e0
    · have hz := hδsum
      rw [AssemblyP1.ExactRigidityCriterion.ZeroSum] at hz
      rw [hphi, phi_sum] at hz
      exact hz
    · have := hδbox 0 (Finset.mem_univ 0); simpa [bridgeA] using this
    · have := hδbox 1 (Finset.mem_univ 1); rw [hδ1] at this; simpa [bridgeA] using this
    · have := hδbox 2 (Finset.mem_univ 2); simpa [bridgeA] using this
    · have := hδbox 3 (Finset.mem_univ 3); rw [hδ3] at this; simpa [bridgeA] using this
    · have := hδbox 4 (Finset.mem_univ 4); simpa [bridgeA] using this
    · have := hδbox 5 (Finset.mem_univ 5); simpa [bridgeA] using this
  · rintro ⟨a, c, p, q, hne, hsum, ha, hb, hc, hd, hp, hq⟩
    have hne' : ∃ e ∈ bedges, phi a c p q e ≠ 0 := by
      by_contra h
      push Not at h
      have h0 : a = 0 := by simpa [phi] using h 0 (Finset.mem_univ 0)
      have h2 : c = 0 := by simpa [phi] using h 2 (Finset.mem_univ 2)
      have h4 : p = 0 := by simpa [phi] using h 4 (Finset.mem_univ 4)
      have h5 : q = 0 := by simpa [phi] using h 5 (Finset.mem_univ 5)
      rw [h0, h2, h4, h5] at hne
      simp at hne
    refine ⟨phi a c p q, hne',
      (balancedB_iff_balancedZ (phi a c p q)).mp (phi_balancedB a c p q), ?_, ?_⟩
    · rw [AssemblyP1.ExactRigidityCriterion.ZeroSum, phi_sum]; exact hsum
    · intro e _
      fin_cases e <;> simp only [phi, bridgeA] <;>
        first
          | exact ha | exact hb | exact hc | exact hd | exact hp | exact hq

end AssemblyP1.RigidityBridge
