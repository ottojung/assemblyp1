import AssemblyP1.ExactRigidityCriterion

set_option linter.unusedVariables false

/-!
# The double-theta graph: coupling begins at cycle rank 3 (issue #257, §8.1)

This module advances open item **§8.1** of
`docs/source-notes/issue-257-rigid-read-graphs.md`. The exact algebraic criterion
(`AssemblyP1.ExactRigidityCriterion.nonrigid_iff_exists_delta`), the Graver form
(`AssemblyP1.GraverRigidity`), the two-closed-walk form
(`AssemblyP1.TwoWalkRigidity`), the finite decider
(`AssemblyP1.FiniteRigidityDecider`), the bouquet reduction
(`AssemblyP1.RigidityBouquet`) and the antiparallel bridge
(`AssemblyP1.RigidityBridge`, `AssemblyP1.RigidityLength3Bridge`,
`AssemblyP1.RigidityGeneralBridge`) are already merged and are **not** redone
here.

## Why a new topology is needed

The merged criteria cover the *bouquet* family (all cycle rank `≥ 2`, but with
edge-disjoint cycles, so the box is diagonal) and the *antiparallel bridge*
family (cycle rank `4`, coupling through the bridge box). Every strongly
connected support of cycle rank `≤ 2` is a *theta graph* (two cycles sharing a
directed path) or a figure-eight; in all of these the shared-path/vertex balance
forces the shared value to be the **sum** of the two cycle values, so the shared
box is implied by the per-cycle boxes and the instance satisfies the **bouquet
criterion** (`bouquet_nonrigid_iff`). Coupling therefore cannot start below rank
`3`.

This module exhibits the **minimal coupled support**: the *double-theta graph*,
of cycle rank `3`, obtained by taking two hubs `u, v` and joining them by two
parallel arcs in each direction, one of length `1` and one of length `2`:

```
u → v                 (P1, one arc)          u → w → v   (P2, two arcs)
v → u                 (Q1, one arc)          v → z → u   (Q2, two arcs)
```

on four vertices `u, v, w, z` and six arcs. Here the two hubs carry two
*independent* balance equations `α₁ + α₂ = β₁ + β₂` (the total flow out of `u`
equals the total flow into `u`), so a circulation is **not** constant on a single
cycle and the box constraints couple through an **extra balance equation**
rather than being diagonal. This is a genuinely different coupling from the
bridge, whose coupling sits in the box.

Concretely a circulation is determined by four integers
`(α₁, α₂, β₁, β₂)` (the constant values on `P1, P2, Q1, Q2`), with
`δ = ![α₁, α₂, α₂, β₁, β₂, β₂]`, subject to `α₁ + α₂ = β₁ + β₂`, and zero total
mass is `α₁ + 2·α₂ + β₁ + 2·β₂ = 0`.

## Main results

* `doubleTheta_nonrigid_iff`: the exact four-variable criterion for the
  double-theta family.
* `doubleTheta_rigid_repetitive`: the instance `(m₁,m₂,n₁,n₂) = (2,1,2,1)` is
  **rigid** although the `P1` and `Q1` arcs are each traversed twice.
* `doubleTheta_nonrigid_witness`: an explicit non-rigidity witness.
* `relaxed_not_sound`: the *relaxed* criterion obtained by dropping the balance
  equation `α₁ + α₂ = β₁ + β₂` (the naive "independent per-path / bouquet-style"
  relaxation) is **not** sound: it reports non-rigidity at the rigid instance
  `(2,1,2,1)`. So the double-theta criterion is genuinely coupled.

## Epistemic status

All theorems are kernel-checked with only `[propext, Classical.choice,
Quot.sound]` (`AssemblyP1/RigidityDoubleThetaAudit.lean`); no
`sorry`/`admit`/`axiom`/`native_decide`. The double-theta is an *abstract*
oriented support graph (two hubs of degree `4`, two of degree `2`); realizability
of this exact shape as a de Bruijn read-support is not claimed (a de Bruijn graph
has at most one arc between any ordered pair of vertices). The residual — a
*polynomial* min-cut/max-flow closed form for general supports, or a proof that
none exists — remains **OPEN** (§8.1/§8.2).
-/

namespace AssemblyP1.RigidityDoubleTheta

open Finset BigOperators

/-- Tail map of the double-theta graph: arcs `0,1` leave hub `u=0`, arc `2`
leaves `w=2`, arcs `3,4` leave hub `v=1`, arc `5` leaves `z=3`. -/
def dtail : Fin 6 → Fin 4 := fun i => ![0, 0, 2, 1, 1, 3] i

/-- Head map of the double-theta graph. -/
def dhead : Fin 6 → Fin 4 := fun i => ![1, 2, 1, 0, 3, 0] i

/-- Every vertex is a node. -/
def dnodes : Finset (Fin 4) := Finset.univ

/-- Every one of the six arcs is a support edge. -/
def dedges : Finset (Fin 6) := Finset.univ

/-- Out-arcs of `v`. -/
def doutF (v : Fin 4) : Finset (Fin 6) := dedges.filter (fun e => dtail e = v)

/-- In-arcs of `v`. -/
def dinF (v : Fin 4) : Finset (Fin 6) := dedges.filter (fun e => dhead e = v)

/-- Explicit balance predicate on the six arcs. -/
def BalancedB (B : Fin 6 → ℤ) : Prop :=
  ∀ v ∈ dnodes, (∑ e ∈ doutF v, B e) = (∑ e ∈ dinF v, B e)

/-- `BalancedB` is exactly the support-domain `BalancedZ` of
`ExactRigidityCriterion`. -/
lemma balancedB_iff_balancedZ (B : Fin 6 → ℤ) :
    BalancedB B ↔
      AssemblyP1.ExactRigidityCriterion.BalancedZ dtail dhead dnodes dedges B :=
  Iff.rfl

/-- The multiplicity vector `A` of the double theta: `m1` on `P1`, `m2` on each
`P2` arc, `n1` on `Q1`, `n2` on each `Q2` arc. -/
def dtA (m1 m2 n1 n2 : ℕ) : Fin 6 → ℤ := fun i => ![m1, m2, m2, n1, n2, n2] i

/-- Total mass of the double-theta base circulation. -/
def dtG (m1 m2 n1 n2 : ℕ) : ℕ := m1 + 2 * m2 + n1 + 2 * n2

lemma dtA_apply_zero (m1 m2 n1 n2 : ℕ) : dtA m1 m2 n1 n2 0 = m1 := rfl
lemma dtA_apply_one (m1 m2 n1 n2 : ℕ) : dtA m1 m2 n1 n2 1 = m2 := rfl
lemma dtA_apply_two (m1 m2 n1 n2 : ℕ) : dtA m1 m2 n1 n2 2 = m2 := rfl
lemma dtA_apply_three (m1 m2 n1 n2 : ℕ) : dtA m1 m2 n1 n2 3 = n1 := rfl
lemma dtA_apply_four (m1 m2 n1 n2 : ℕ) : dtA m1 m2 n1 n2 4 = n2 := rfl
lemma dtA_apply_five (m1 m2 n1 n2 : ℕ) : dtA m1 m2 n1 n2 5 = n2 := rfl

@[simp] lemma doutF_zero : doutF 0 = ({0, 1} : Finset (Fin 6)) := by decide
@[simp] lemma doutF_one : doutF 1 = ({3, 4} : Finset (Fin 6)) := by decide
@[simp] lemma doutF_two : doutF 2 = ({2} : Finset (Fin 6)) := by decide
@[simp] lemma doutF_three : doutF 3 = ({5} : Finset (Fin 6)) := by decide
@[simp] lemma dinF_zero : dinF 0 = ({3, 5} : Finset (Fin 6)) := by decide
@[simp] lemma dinF_one : dinF 1 = ({0, 2} : Finset (Fin 6)) := by decide
@[simp] lemma dinF_two : dinF 2 = ({1} : Finset (Fin 6)) := by decide
@[simp] lemma dinF_three : dinF 3 = ({4} : Finset (Fin 6)) := by decide

/-- `BalancedB` is exactly the three independent balance equations: the two
degree-`2` vertices force `δ 1 = δ 2` and `δ 4 = δ 5`, and the hub balance
`δ 0 + δ 1 = δ 3 + δ 5` becomes `δ 0 + δ 1 = δ 3 + δ 4`. -/
lemma balancedB_iff_eqs (δ : Fin 6 → ℤ) :
    BalancedB δ ↔ δ 1 = δ 2 ∧ δ 4 = δ 5 ∧ δ 0 + δ 1 = δ 3 + δ 4 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa using (h 2 (Finset.mem_univ 2)).symm
    · simpa using (h 3 (Finset.mem_univ 3)).symm
    · have h0 : δ 0 + δ 1 = δ 3 + δ 5 := by simpa using h 0 (Finset.mem_univ 0)
      have h5 : δ 5 = δ 4 := by simpa using h 3 (Finset.mem_univ 3)
      linarith
  · rintro ⟨h1, h2, h3⟩ v _
    fin_cases v <;> simp_all

/-- The double-theta base circulation is balanced provided `m1 + m2 = n1 + n2`
(the two hubs have equal total through-flow). -/
lemma dtA_balancedB (m1 m2 n1 n2 : ℕ) (hm : m1 + m2 = n1 + n2) :
    BalancedB (dtA m1 m2 n1 n2) := by
  rw [balancedB_iff_eqs]
  refine ⟨rfl, rfl, ?_⟩
  simp [dtA]
  omega

/-- The double-theta base circulation is balanced. -/
lemma dtA_balanced (m1 m2 n1 n2 : ℕ) (hm : m1 + m2 = n1 + n2) :
    AssemblyP1.ExactRigidityCriterion.BalancedZ dtail dhead dnodes dedges
      (dtA m1 m2 n1 n2) :=
  (balancedB_iff_balancedZ (dtA m1 m2 n1 n2)).mp (dtA_balancedB m1 m2 n1 n2 hm)

/-- The double-theta base circulation has total mass `dtG`. -/
lemma dtA_total (m1 m2 n1 n2 : ℕ) :
    ∑ e ∈ dedges, dtA m1 m2 n1 n2 e = (dtG m1 m2 n1 n2 : ℤ) := by
  simp [dedges, dtA, dtG, Fin.sum_univ_six]
  ring

/-! ## The four-variable exact criterion -/

/-- The four-parameter form of a double-theta circulation:
`δ = ![α₁, α₂, α₂, β₁, β₂, β₂]`. It is balanced exactly when
`α₁ + α₂ = β₁ + β₂`. -/
def phi (a b c d : ℤ) : Fin 6 → ℤ := ![a, b, b, c, d, d]

lemma phi_zero : phi 0 0 0 0 = 0 := by
  funext e; fin_cases e <;> rfl

lemma phi_eq_zero_iff (a b c d : ℤ) :
    phi a b c d = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h3 := congrFun h 3
    have h4 := congrFun h 4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simpa [phi] using ‹_›
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact phi_zero

lemma phi_balancedB (a b c d : ℤ) (h : a + b = c + d) : BalancedB (phi a b c d) := by
  rw [balancedB_iff_eqs]
  refine ⟨rfl, rfl, ?_⟩
  simp [phi]
  linarith

lemma phi_sum (a b c d : ℤ) :
    ∑ e ∈ dedges, phi a b c d e = a + 2 * b + c + 2 * d := by
  simp only [dedges, Fin.sum_univ_six]
  simp [phi]
  ring

lemma phi_of_balanced (δ : Fin 6 → ℤ) (h : BalancedB δ) :
    δ = phi (δ 0) (δ 1) (δ 3) (δ 4) := by
  have ⟨h1, h2, h3⟩ := (balancedB_iff_eqs δ).mp h
  funext e
  fin_cases e <;> simp [phi] <;> linarith

/-- **Exact four-variable criterion for the double theta.** For multiplicities
`m1, m2, n1, n2 ≥ 1` with `m1 + m2 = n1 + n2`, the base circulation is non-rigid
**iff** there are integers `α₁, α₂, β₁, β₂`, not all zero, with

```
α₁ + α₂ = β₁ + β₂                       (hub balance, the coupling)
α₁ + 2·α₂ + β₁ + 2·β₂ = 0               (zero total mass)
α₁ ≥ 1 - m1,  α₂ ≥ 1 - m2,              (P1, P2 boxes)
β₁ ≥ 1 - n1,  β₂ ≥ 1 - n2.              (Q1, Q2 boxes)
```

The hub-balance equation couples the four parameters; it is *not* implied by
the box constraints (see `relaxed_not_sound`). -/
theorem doubleTheta_nonrigid_iff (m1 m2 n1 n2 : ℕ) (hm1 : 1 ≤ m1) (hm2 : 1 ≤ m2)
    (hn1 : 1 ≤ n1) (hn2 : 1 ≤ n2) (hm : m1 + m2 = n1 + n2) :
    (¬ AssemblyP1.ExactRigidityCriterion.Rigid dtail dhead dnodes dedges
        (dtA m1 m2 n1 n2) (dtG m1 m2 n1 n2)) ↔
      ∃ a b c d : ℤ,
        (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) ∧
        a + b = c + d ∧
        a + 2 * b + c + 2 * d = 0 ∧
        (1 - (m1 : ℤ) ≤ a) ∧ (1 - (m2 : ℤ) ≤ b) ∧
        (1 - (n1 : ℤ) ≤ c) ∧ (1 - (n2 : ℤ) ≤ d) := by
  rw [AssemblyP1.ExactRigidityCriterion.nonrigid_iff_exists_delta dtail dhead dnodes dedges
      (dtA m1 m2 n1 n2) (dtG m1 m2 n1 n2) (dtA_balanced m1 m2 n1 n2 hm)
      (dtA_total m1 m2 n1 n2)]
  constructor
  · rintro ⟨δ, ⟨e0, he0, hne⟩, hδbal, hδsum, hδbox⟩
    have hphi := phi_of_balanced δ hδbal
    have ⟨h1, h2, h3⟩ := (balancedB_iff_eqs δ).mp hδbal
    refine ⟨δ 0, δ 1, δ 3, δ 4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      obtain ⟨h0, h1', h3', h4'⟩ := hcon
      apply hne
      rw [hphi, h0, h1', h3', h4']
      exact congrFun phi_zero e0
    · -- hub balance
      linarith
    · -- zero total mass
      have hz := hδsum
      rw [AssemblyP1.ExactRigidityCriterion.ZeroSum] at hz
      rw [hphi, phi_sum] at hz
      exact hz
    · have := hδbox 0 (Finset.mem_univ 0); simpa [dtA] using this
    · have := hδbox 1 (Finset.mem_univ 1); simpa [dtA] using this
    · have := hδbox 3 (Finset.mem_univ 3); simpa [dtA] using this
    · have := hδbox 4 (Finset.mem_univ 4); simpa [dtA] using this
  · rintro ⟨a, b, c, d, hne, hbal, hsum, ha, hb, hc, hd⟩
    have hne' : ∃ e ∈ dedges, phi a b c d e ≠ 0 := by
      by_contra h
      push Not at h
      have h0 : a = 0 := by simpa [phi] using h 0 (Finset.mem_univ 0)
      have h1 : b = 0 := by simpa [phi] using h 1 (Finset.mem_univ 1)
      have h3 : c = 0 := by simpa [phi] using h 3 (Finset.mem_univ 3)
      have h4 : d = 0 := by simpa [phi] using h 4 (Finset.mem_univ 4)
      rw [h0, h1, h3, h4] at hne
      simp at hne
    refine ⟨phi a b c d, hne',
      (balancedB_iff_balancedZ (phi a b c d)).mp (phi_balancedB a b c d hbal), ?_, ?_⟩
    · rw [AssemblyP1.ExactRigidityCriterion.ZeroSum, phi_sum]; exact hsum
    · intro e _
      fin_cases e <;> simp only [phi, dtA] <;>
        first
          | exact ha | exact hb | exact hc | exact hd

/-! ## Worked instances and the coupling refutation -/

/-- **Non-rigidity witness.** At multiplicities `(m₁,m₂,n₁,n₂) = (1,2,1,2)` the
parameters `(α₁,α₂,β₁,β₂) = (2,-1,2,-1)` give a nonzero coupled circulation with
zero total mass inside the box, so the instance is not rigid. -/
theorem doubleTheta_nonrigid_witness :
    ¬ AssemblyP1.ExactRigidityCriterion.Rigid dtail dhead dnodes dedges
        (dtA 1 2 1 2) (dtG 1 2 1 2) := by
  rw [doubleTheta_nonrigid_iff 1 2 1 2 (by decide) (by decide) (by decide) (by decide)
    (by decide)]
  exact ⟨2, -1, 2, -1, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Rigid repetitive instance.** At multiplicities `(m₁,m₂,n₁,n₂) = (2,1,2,1)`
the arcs of `P1` and `Q1` are each traversed **twice**, yet the instance is
rigid. The hub-balance coupling forces the only admissible perturbation to be
zero. -/
theorem doubleTheta_rigid_repetitive :
    AssemblyP1.ExactRigidityCriterion.Rigid dtail dhead dnodes dedges
        (dtA 2 1 2 1) (dtG 2 1 2 1) := by
  by_contra hnr
  rw [doubleTheta_nonrigid_iff 2 1 2 1 (by decide) (by decide) (by decide) (by decide)
    (by decide)] at hnr
  obtain ⟨a, b, c, d, hne, hbal, hsum, ha, hb, hc, hd⟩ := hnr
  have h0 : a = 0 := by omega
  have h1 : b = 0 := by omega
  have h2 : c = 0 := by omega
  have h3 : d = 0 := by omega
  rcases hne with h | h | h | h <;> omega

/-- The **relaxed** double-theta predicate: the exact criterion with the
hub-balance equation `α₁ + α₂ = β₁ + β₂` dropped, i.e. the naive
"independent per-path / bouquet-style" relaxation that treats the four path
values as free. -/
def RelaxedDT (m1 m2 n1 n2 : ℕ) : Prop :=
  ∃ a b c d : ℤ,
    (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) ∧
    a + 2 * b + c + 2 * d = 0 ∧
    (1 - (m1 : ℤ) ≤ a) ∧ (1 - (m2 : ℤ) ≤ b) ∧
    (1 - (n1 : ℤ) ≤ c) ∧ (1 - (n2 : ℤ) ≤ d)

/-- **The coupling equation is essential (failed simpler hypothesis).** At
`(m₁,m₂,n₁,n₂) = (2,1,2,1)` the relaxed predicate `RelaxedDT` is **satisfied**
(witness `(α₁,α₂,β₁,β₂) = (-1,1,-1,0)`) while the instance is **rigid**. Hence
the hub-balance coupling cannot be dropped: no criterion of the naive
independent-path (bouquet-style) form decides the double theta. -/
theorem relaxed_not_sound :
    RelaxedDT 2 1 2 1 ∧
      AssemblyP1.ExactRigidityCriterion.Rigid dtail dhead dnodes dedges
        (dtA 2 1 2 1) (dtG 2 1 2 1) := by
  refine ⟨?_, doubleTheta_rigid_repetitive⟩
  exact ⟨-1, 1, -1, 0, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩

end AssemblyP1.RigidityDoubleTheta
