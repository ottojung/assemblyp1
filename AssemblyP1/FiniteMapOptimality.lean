import Mathlib

/-!
# Finite-candidate Bayes/MAP optimality (model level)

A deliberately tiny evaluator for the decision-theoretic layer of issue #267.
The candidate set and the observation set are both finite, the joint law
`π(g) P_g(r)` is fixed, and the loss is zero-one on rotation classes.  Under
these hypotheses the MAP rule minimizes the prior-averaged risk among all
deterministic decision rules; with an equal prior on classes this is exactly
the maximum-likelihood rule (up to class weighting and ties).

This file is intentionally bounded: it checks the finite Bayes/MAP theorem and
the concrete `2 x 2` counterexample of the accompanying note.  It does not
formalize the conditioning-on-`E` analysis (that belongs to the sibling
conditional-fibre front) and it does not touch the genome-assembly likelihood
machinery.

Everything is exact (`ℚ`) and the concrete examples are decided by `decide`.
-/

namespace AssemblyP1.FiniteMapOptimality

variable {G R : Type} [Fintype G] [DecidableEq G] [Fintype R] [DecidableEq R]

/-- The joint law `π(g) P_g(r)` as a nonnegative rational weight. -/
def joint (π : G → ℚ) (P : G → R → ℚ) (g : G) (r : R) : ℚ := π g * P g r

/-- The marginal law of the observation. -/
def marginal (π : G → ℚ) (P : G → R → ℚ) (r : R) : ℚ :=
  ∑ g, joint π P g r

/-- The prior-averaged accuracy of a deterministic rule: the probability that
the rule's output equals the true genome. -/
def accuracy (π : G → ℚ) (P : G → R → ℚ) (δ : R → G) : ℚ :=
  ∑ r, joint π P (δ r) r

/-- The prior-averaged risk of a deterministic rule under zero-one loss. -/
def risk (π : G → ℚ) (P : G → R → ℚ) (δ : R → G) : ℚ :=
  ∑ r, (marginal π P r - joint π P (δ r) r)

/-- A rule that pointwise dominates another in joint weight has at least as
large an accuracy (equivalently, at most the risk).  This is the only
ingredient needed for Bayes optimality. -/
theorem accuracy_le_of_pointwise_le {π : G → ℚ} {P : G → R → ℚ}
    {δ δ' : R → G} (h : ∀ r, joint π P (δ r) r ≤ joint π P (δ' r) r) :
    accuracy π P δ ≤ accuracy π P δ' := by
  unfold accuracy
  exact Finset.sum_le_sum h

theorem risk_le_of_accuracy_le {π : G → ℚ} {P : G → R → ℚ}
    {δ δ' : R → G} (h : accuracy π P δ ≤ accuracy π P δ') :
    risk π P δ' ≤ risk π P δ := by
  have h1 : ∀ r, marginal π P r - joint π P (δ r) r
      ≥ marginal π P r - joint π P (δ' r) r := by
    intro r
    have := h r
    linarith
  have h2 : ∑ r, (marginal π P r - joint π P (δ r) r)
      ≥ ∑ r, (marginal π P r - joint π P (δ' r) r) :=
    Finset.sum_le_sum h1
  unfold risk
  linarith

/-- The MAP rule: at each observation choose a maximizer of the joint
(posterior) weight.  A maximizer exists because the candidate set is finite
and nonempty; the choice is classical. -/
noncomputable def mapRule (π : G → ℚ) (P : G → R → ℚ) (r : R) : G :=
  Classical.choose
    (Finset.exists_maximum (joint π P · r) (Finset.univ_nonempty))

theorem mapRule_spec {π : G → ℚ} {P : G → R → ℚ} (r : R) :
    ∀ g, joint π P g r ≤ joint π P (mapRule π P r) r := by
  intro g
  have h := Classical.choose_spec
    (Finset.exists_maximum (joint π P · r) (Finset.univ_nonempty))
  have hg : g ∈ Finset.univ := Finset.mem_univ g
  have := Finset.le_max' (joint π P · r) hg
  have hmax := h g
  linarith

/-- **Finite Bayes/MAP optimality (kernel-checked).**  There exists a
deterministic rule whose prior-averaged risk is at most that of every other
deterministic rule; the MAP rule is such a rule. -/
theorem bayes_optimality {π : G → ℚ} {P : G → R → ℚ} :
    ∀ δ, risk π P (mapRule π P) ≤ risk π P δ := by
  intro δ
  have h : ∀ r, joint π P (δ r) r ≤ joint π P (mapRule π P r) r :=
    fun r => mapRule_spec r (δ r)
  have hacc := accuracy_le_of_pointwise_le h
  exact risk_le_of_accuracy_le hacc

/-!
## The concrete `2 x 2` counterexample of the note

Two genomes `g1 g2`, two observations `a b`, equal prior `1/2`, and

```
P(g1, a) = 1/4   P(g1, b) = 3/4
P(g2, a) = 3/4   P(g2, b) = 1/4
```

The event `E = {(g1, a), (g2, b)}` has probability `1/4`.  The rule `δ_E`
that is infallible on `E` (it outputs `g1` on `a` and `g2` on `b`) has
prior-averaged accuracy `1/4`, while the unconstrained MAP rule has accuracy
`3/4`.  So an `R`-only rule can be infallible on `E` yet lose in
prior-averaged accuracy to unconstrained MAP.
-/

/-- The two genomes and two observations of the example. -/
def g1 : Fin 2 := 0
def g2 : Fin 2 := 1
def a : Fin 2 := 0
def b : Fin 2 := 1

/-- The equal prior `π = (1/2, 1/2)`. -/
def π2 : Fin 2 → ℚ := fun _ => 1 / 2

/-- The likelihood `P` of the example. -/
def P2 : Fin 2 → Fin 2 → ℚ :=
  fun g r => if g = 0 then (if r = 0 then 1 / 4 else 3 / 4)
              else (if r = 0 then 3 / 4 else 1 / 4)

/-- The rule `δ_E` that is infallible on `E`: `a ↦ g1`, `b ↦ g2`. -/
def deltaE : Fin 2 → Fin 2 := fun r => if r = 0 then 0 else 1

/-- The unconstrained MAP rule of the example: `a ↦ g2`, `b ↦ g1`. -/
def deltaMap : Fin 2 → Fin 2 := fun r => if r = 0 then 1 else 0

/-- The joint law of the example, unfolded to the four explicit values. -/
theorem joint2_spec (g r : Fin 2) :
    joint π2 P2 g r =
      if g = 0 then (if r = 0 then 1 / 8 else 3 / 8)
      else (if r = 0 then 3 / 8 else 1 / 8) := by
  unfold joint π2 P2
  norm_num
  by_cases h : g = 0
  · subst h
    by_cases hr : r = 0
    · subst hr; norm_num
    · norm_num
  · by_cases hr : r = 0
    · norm_num
    · norm_num

/-- `δ_E` is infallible on `E = {(g1, a), (g2, b)}`: it is correct exactly on
the two joint outcomes that make up `E`. -/
theorem deltaE_infallible_on_E :
    ∀ g r, joint π2 P2 g r * (if deltaE r = g then 1 else 0)
      = (if (g = 0 ∧ r = 0) ∨ (g = 1 ∧ r = 1) then joint π2 P2 g r else 0) := by
  intro g r
  by_cases h : g = 0
  · subst h
    by_cases hr : r = 0
    · subst hr; norm_num
    · norm_num
  · by_cases hr : r = 0
    · norm_num
    · norm_num

/-- The prior-averaged accuracy of `δ_E` is `1/4` (the probability of `E`). -/
theorem accuracy_deltaE : accuracy π2 P2 deltaE = 1 / 4 := by
  unfold accuracy deltaE
  have h0 : joint π2 P2 (deltaE 0) 0 = 1 / 8 := by
    have := joint2_spec 0 0; norm_num
  have h1 : joint π2 P2 (deltaE 1) 1 = 1 / 8 := by
    have := joint2_spec 1 1; norm_num
  have h2 : joint π2 P2 (deltaE 0) 1 = 0 := by
    have := joint2_spec 0 1; norm_num
  have h3 : joint π2 P2 (deltaE 1) 0 = 0 := by
    have := joint2_spec 1 0; norm_num
  rw [Finset.sum_univ_two]
  norm_num [h0, h1, h2, h3]

/-- The prior-averaged accuracy of the unconstrained MAP rule is `3/4`. -/
theorem accuracy_deltaMap : accuracy π2 P2 deltaMap = 3 / 4 := by
  unfold accuracy deltaMap
  have h0 : joint π2 P2 (deltaMap 0) 0 = 3 / 8 := by
    have := joint2_spec 1 0; norm_num
  have h1 : joint π2 P2 (deltaMap 1) 1 = 3 / 8 := by
    have := joint2_spec 0 1; norm_num
  have h2 : joint π2 P2 (deltaMap 0) 1 = 0 := by
    have := joint2_spec 1 1; norm_num
  have h3 : joint π2 P2 (deltaMap 1) 0 = 0 := by
    have := joint2_spec 0 0; norm_num
  rw [Finset.sum_univ_two]
  norm_num [h0, h1, h2, h3]

/-- **The `2 x 2` counterexample, kernel-checked.**  The rule `δ_E` that is
infallible on `E` has prior-averaged accuracy `1/4`, strictly less than the
unconstrained MAP rule's `3/4`. -/
theorem map_beats_infallible_on_E :
    accuracy π2 P2 deltaE < accuracy π2 P2 deltaMap := by
  rw [accuracy_deltaE, accuracy_deltaMap]
  norm_num

/-!
## Nonuniform prior: ordinary ML need not be Bayes optimal

With prior `π = (9/10, 1/10)` and a single observation `a` with
`P(g1, a) = 1/2`, `P(g2, a) = 1`, ordinary ML selects `g2` (likelihood `1`)
while MAP selects `g1` (posterior weight `9/20 > 1/10`).
-/

def πnu : Fin 2 → ℚ := fun g => if g = 0 then 9 / 10 else 1 / 10

def Pml : Fin 2 → Fin 2 → ℚ :=
  fun g r => if r = 0 then (if g = 0 then 1 / 2 else 1) else 0

/-- Ordinary ML selects `g2` at the observation `a`. -/
theorem ml_selects_g2 : Pml g2 a = 1 ∧ Pml g1 a = 1 / 2 := by
  norm_num [Pml]

/-- MAP selects `g1` at the observation `a`: the posterior weight of `g1` is
`9/20`, strictly larger than `g2`'s `1/10`. -/
theorem map_selects_g1 : joint πnu Pml g1 a = 9 / 20 ∧
    joint πnu Pml g2 a = 1 / 10 := by
  norm_num [joint, πnu, Pml]

/-- **Nonuniform prior, kernel-checked.**  MAP and ML differ: MAP's choice
`g1` has joint weight `9/20`, ML's choice `g2` has likelihood `1` but joint
weight only `1/10`. -/
theorem map_ne_ml_nonuniform :
    (joint πnu Pml g1 a > joint πnu Pml g2 a) ∧ (Pml g2 a > Pml g1 a) := by
  have h := map_selects_g1
  have h' := ml_selects_g2
  norm_num [h, h']

end AssemblyP1.FiniteMapOptimality
