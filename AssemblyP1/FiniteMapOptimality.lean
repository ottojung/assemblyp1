import Mathlib

/-!
# Finite-candidate Bayes/MAP optimality (model level)

A deliberately tiny, self-contained evaluator for the decision-theoretic layer
of issue #267. The candidate set `G` and the observation set `R` are finite,
the joint law `π g * P g r` is fixed, and the loss is zero-one. Under these
hypotheses a pointwise maximum-a-posteriori rule minimizes prior-averaged risk
among all deterministic rules; with an equal prior on classes this is the
maximum-likelihood rule (up to class weighting and ties).

The file also kernel-checks the concrete `2 × 2` counterexample of the
accompanying note. A rule that is infallible on a truth-dependent event `E`
can have strictly smaller prior-averaged accuracy than the unconstrained MAP
rule, so an `R`-only rule that is perfect on `E` need not be Bayes optimal.

Everything is exact over `ℚ`, and the concrete computations are decided by
`decide`/`norm_num`; no `native_decide`, `sorry`, `axiom`, or `admit` is used.
The MAP maximizer is obtained from the explicit finite `Finset` maximum
`Finset.exists_max_image` rather than any heavy automation.

This is the finite Bayesian decision theorem, not the MB09 product-binomial
surrogate, nor an assembly-flow realization theorem. It is intentionally
standalone: it imports only Mathlib and does not touch the genome-assembly
likelihood machinery.
-/

namespace AssemblyP1.FiniteMapOptimality

variable {G R : Type} [Fintype G] [DecidableEq G] [Fintype R] [DecidableEq R]

/-- The joint law `π(g) P_g(r)` as a rational weight. -/
def joint (π : G → ℚ) (P : G → R → ℚ) (g : G) (r : R) : ℚ := π g * P g r

/-- The marginal law of the observation. -/
def marginal (π : G → ℚ) (P : G → R → ℚ) (r : R) : ℚ := ∑ g, joint π P g r

/-- Prior-averaged accuracy of a deterministic rule: the probability that the
rule's output equals the true genome. -/
def accuracy (π : G → ℚ) (P : G → R → ℚ) (δ : R → G) : ℚ :=
  ∑ r, joint π P (δ r) r

/-- Prior-averaged zero-one risk of a deterministic rule. -/
def risk (π : G → ℚ) (P : G → R → ℚ) (δ : R → G) : ℚ :=
  ∑ r, (marginal π P r - joint π P (δ r) r)

omit [Fintype G] [DecidableEq G] [DecidableEq R] in
/-- Pointwise domination in joint weight gives at least as large an accuracy.
This is the only ingredient needed for Bayes optimality. -/
theorem accuracy_le_of_pointwise_le {π : G → ℚ} {P : G → R → ℚ}
    {δ δ' : R → G} (h : ∀ r, joint π P (δ r) r ≤ joint π P (δ' r) r) :
    accuracy π P δ ≤ accuracy π P δ' := by
  unfold accuracy
  exact Finset.sum_le_sum (fun r _ => h r)

omit [DecidableEq G] [DecidableEq R] in
/-- Higher prior-averaged accuracy is lower prior-averaged zero-one risk. -/
theorem risk_le_of_accuracy_le {π : G → ℚ} {P : G → R → ℚ}
    {δ δ' : R → G} (h : accuracy π P δ ≤ accuracy π P δ') :
    risk π P δ' ≤ risk π P δ := by
  have hA : (∑ r, joint π P (δ r) r) ≤ ∑ r, joint π P (δ' r) r := by
    simpa [accuracy] using h
  simp only [risk, Finset.sum_sub_distrib]
  linarith

/-- The MAP rule: at each observation choose a maximizer of the joint
(posterior) weight. Existence is the explicit finite `Finset` maximum
`Finset.exists_max_image`; the choice is classical. -/
noncomputable def mapRule [Nonempty G] (π : G → ℚ) (P : G → R → ℚ) (r : R) : G :=
  Classical.choose
    (Finset.exists_max_image (Finset.univ : Finset G) (fun g => joint π P g r)
      (Finset.univ_nonempty))

omit [DecidableEq G] [Fintype R] [DecidableEq R] in
/-- The MAP rule is a genuine pointwise maximizer of the joint weight. -/
theorem mapRule_spec [Nonempty G] {π : G → ℚ} {P : G → R → ℚ} (r : R) :
    ∀ g, joint π P g r ≤ joint π P (mapRule π P r) r := by
  intro g
  have h := Classical.choose_spec
    (Finset.exists_max_image (Finset.univ : Finset G) (fun g => joint π P g r)
      (Finset.univ_nonempty))
  exact h.2 g (Finset.mem_univ g)

omit [DecidableEq G] [DecidableEq R] in
/-- **Finite Bayes/MAP optimality (kernel-checked).** For a finite nonempty
candidate set, the MAP rule has prior-averaged zero-one risk at most that of
every deterministic rule. -/
theorem bayes_optimality [Nonempty G] {π : G → ℚ} {P : G → R → ℚ} :
    ∀ δ, risk π P (mapRule π P) ≤ risk π P δ := by
  intro δ
  have h : ∀ r, joint π P (δ r) r ≤ joint π P (mapRule π P r) r :=
    fun r => mapRule_spec r (δ r)
  exact risk_le_of_accuracy_le (accuracy_le_of_pointwise_le h)

/-!
## The concrete `2 × 2` counterexample of the note

Two genomes `g1 g2`, two observations `a b`, equal prior `1/2`, and

```
P(g1, a) = 1/4   P(g1, b) = 3/4
P(g2, a) = 3/4   P(g2, b) = 1/4
```

The event `E = {(g1, a), (g2, b)}` has probability `1/4`. The rule `δ_E`
that is infallible on `E` (it outputs `g1` on `a` and `g2` on `b`) has
prior-averaged accuracy `1/4`, while the unconstrained MAP rule has accuracy
`3/4`. So an `R`-only rule can be infallible on `E` yet lose in
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
  fin_cases g <;> fin_cases r <;> norm_num [joint, π2, P2]

/-- The prior-averaged accuracy of `δ_E` is `1/4` (the probability of `E`). -/
theorem accuracy_deltaE : accuracy π2 P2 deltaE = 1 / 4 := by
  unfold accuracy
  rw [Fin.sum_univ_two]
  norm_num [joint, π2, P2, deltaE]

/-- The prior-averaged accuracy of the unconstrained MAP rule is `3/4`. -/
theorem accuracy_deltaMap : accuracy π2 P2 deltaMap = 3 / 4 := by
  unfold accuracy
  rw [Fin.sum_univ_two]
  norm_num [joint, π2, P2, deltaMap]

/-- **The `2 × 2` counterexample, kernel-checked.** The rule `δ_E` that is
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

/-- The nonuniform prior `π = (9/10, 1/10)`. -/
def πnu : Fin 2 → ℚ := fun g => if g = 0 then 9 / 10 else 1 / 10

/-- The likelihood `P` of the nonuniform example. -/
def Pml : Fin 2 → Fin 2 → ℚ :=
  fun g r => if r = 0 then (if g = 0 then 1 / 2 else 1) else 0

/-- Ordinary ML selects `g2` at the observation `a`. -/
theorem ml_selects_g2 : Pml g2 a = 1 ∧ Pml g1 a = 1 / 2 := by
  constructor <;> norm_num [Pml, g1, g2, a]

/-- MAP selects `g1` at the observation `a`: the posterior weight of `g1` is
`9/20`, strictly larger than `g2`'s `1/10`. -/
theorem map_selects_g1 : joint πnu Pml g1 a = 9 / 20 ∧
    joint πnu Pml g2 a = 1 / 10 := by
  constructor <;> norm_num [joint, πnu, Pml, g1, g2, a]

/-- **Nonuniform prior, kernel-checked.** MAP and ML differ: MAP's choice
`g1` has joint weight `9/20`, ML's choice `g2` has likelihood `1` but joint
weight only `1/10`. -/
theorem map_ne_ml_nonuniform :
    (joint πnu Pml g1 a > joint πnu Pml g2 a) ∧ (Pml g2 a > Pml g1 a) := by
  constructor <;> norm_num [joint, πnu, Pml, g1, g2, a]

#print axioms bayes_optimality
#print axioms map_beats_infallible_on_E
#print axioms map_ne_ml_nonuniform

end AssemblyP1.FiniteMapOptimality
