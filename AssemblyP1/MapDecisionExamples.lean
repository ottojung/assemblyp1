import Mathlib.Data.Fin.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.NormNum

/-!
# Concrete finite decision examples for issue #267

This file supplies the concrete, kernel-checked examples used by
`docs/bayes-optimality-conditional-feasibility-267.md`.  The general
finite-candidate Bayes/MAP optimality theorem is **not** re-proved here: it is
`AssemblyP1.FiniteBayesDecision.pointwise_MAP_optimal` together with the
constructed-rule corollary `chooseMAP_optimal`, merged on `main` via the
sibling Bayes issue #269 / PR #174.  Issue #267 only needs finite sanity
checks of the arithmetic of the reconciliation:

* `map_ne_ml_nonuniform` — with a nonuniform prior, the ordinary
  maximum-likelihood choice need not be the Bayes-optimal (MAP) choice;
* `map_beats_infallible_on_E` — an `R`-only rule that is infallible on the
  truth-dependent event `E` can lose in prior-averaged accuracy to the
  unconstrained MAP rule;
* the `toy` block — a two-hypothesis joint law in which the ordinary
  uniform-prior ML choice is a candidate that is *not* information-feasible,
  while conditioning on `E` makes the posterior supported on the feasible
  candidate alone (posterior mass `1`).

To keep this file's dependencies light (it is deliberately not an `import
Mathlib` file), the prior-averaged accuracy is the two-observation
specialization `acc2`, the shape of `FiniteBayesDecision.success` at `Fin 2`.
The likelihoods are pattern-matching tables, so the concrete values reduce
definitionally and `norm_num` finishes the arithmetic.  No `axiom`, `sorry`,
or `admit` is introduced.
-/

namespace AssemblyP1.MapDecisionExamples

/-- The joint weight `π(g) P_g(r)`. -/
def joint {G R : Type} (π : G → ℚ) (P : G → R → ℚ) (g : G) (r : R) : ℚ :=
  π g * P g r

/-- Prior-averaged accuracy of a deterministic rule `δ` on a two-point
observation space: the probability that the rule's output equals the truth.
This is the `Fin 2` specialization of `FiniteBayesDecision.success`. -/
def acc2 (J : Fin 2 → Fin 2 → ℚ) (δ : Fin 2 → Fin 2) : ℚ :=
  J (δ 0) 0 + J (δ 1) 1

/-! ## Nonuniform prior: ordinary ML need not be Bayes optimal

Prior `π = (9/10, 1/10)`, one relevant observation `a` with
`P(g₁, a) = 1/2` and `P(g₂, a) = 1`.  Ordinary ML selects `g₂` (likelihood `1`)
while MAP selects `g₁` (joint weight `9/20 > 1/10`). -/

/-- Prior `π = (9/10, 1/10)`. -/
def πnu : Fin 2 → ℚ
  | 0 => 9 / 10
  | 1 => 1 / 10

/-- Likelihood concentrated on the observation `a = 0`. -/
def Pml : Fin 2 → Fin 2 → ℚ
  | 0, 0 => 1 / 2
  | 1, 0 => 1
  | _, _ => 0

/-- Joint weight `π(g) P(g, r)` of the nonuniform-prior example. -/
def Jnu : Fin 2 → Fin 2 → ℚ := fun g r => joint πnu Pml g r

/-- Ordinary ML selects `g₂` at the observation `a`. -/
theorem ml_selects_g2 : Pml 1 0 > Pml 0 0 := by norm_num [Pml]

/-- MAP selects `g₁` at the observation `a`: its joint weight `9/20` exceeds
`g₂`'s `1/10`. -/
theorem map_selects_g1 : Jnu 0 0 > Jnu 1 0 := by
  norm_num [Jnu, joint, πnu, Pml]

/-- **Nonuniform prior, kernel-checked.**  MAP and ML differ: MAP's choice `g₁`
has larger joint weight than ML's choice `g₂`, even though `g₂` has the larger
likelihood. -/
theorem map_ne_ml_nonuniform : Jnu 0 0 > Jnu 1 0 ∧ Pml 1 0 > Pml 0 0 :=
  ⟨map_selects_g1, ml_selects_g2⟩

/-! ## The `2 × 2` example: infallible on `E` yet losing to MAP

Two genomes `g₁ g₂`, two observations `a b`, equal prior `1/2`, and

```
P(g₁, a) = 1/4   P(g₁, b) = 3/4
P(g₂, a) = 3/4   P(g₂, b) = 1/4
```

The event `E = {(g₁, a), (g₂, b)}` has probability `1/4`.  The rule `δ_E` that
is infallible on `E` (outputs `g₁` on `a` and `g₂` on `b`) has prior-averaged
accuracy `1/4`, while the unconstrained MAP rule `δ_MAP` (outputs `g₂` on `a`
and `g₁` on `b`) has accuracy `3/4`. -/

/-- Equal prior `π = (1/2, 1/2)`. -/
def π2 : Fin 2 → ℚ := fun _ => 1 / 2

/-- The likelihood `P` of the `2 × 2` example. -/
def P2 : Fin 2 → Fin 2 → ℚ
  | 0, 0 => 1 / 4
  | 0, 1 => 3 / 4
  | 1, 0 => 3 / 4
  | 1, 1 => 1 / 4

/-- Joint weight `π(g) P(g, r)` of the `2 × 2` example. -/
def J2 : Fin 2 → Fin 2 → ℚ := fun g r => joint π2 P2 g r

/-- The rule `δ_E` infallible on `E`: `a ↦ g₁`, `b ↦ g₂`. -/
def deltaE : Fin 2 → Fin 2
  | 0 => 0
  | 1 => 1

/-- The unconstrained MAP rule of the example: `a ↦ g₂`, `b ↦ g₁`. -/
def deltaMap : Fin 2 → Fin 2
  | 0 => 1
  | 1 => 0

/-- The prior-averaged accuracy of `δ_E` is `1/4` (the probability of `E`). -/
theorem accuracy_deltaE : acc2 J2 deltaE = 1 / 4 := by
  norm_num [acc2, J2, joint, π2, P2, deltaE]

/-- The prior-averaged accuracy of the unconstrained MAP rule is `3/4`. -/
theorem accuracy_deltaMap : acc2 J2 deltaMap = 3 / 4 := by
  norm_num [acc2, J2, joint, π2, P2, deltaMap]

/-- **The `2 × 2` counterexample, kernel-checked.**  The rule `δ_E` that is
infallible on `E` has prior-averaged accuracy `1/4`, strictly less than the
unconstrained MAP rule's `3/4`. -/
theorem map_beats_infallible_on_E : acc2 J2 deltaE < acc2 J2 deltaMap := by
  rw [accuracy_deltaE, accuracy_deltaMap]
  norm_num

/-! ## The two-hypothesis toy: ML picks a nonfeasible candidate, `E`-posterior
is certain on the feasible one

Hypotheses `g` (`= 0`) and `h` (`= 1`), observations `x` (`= 0`) and `y`
(`= 1`), equal prior `1/2`:

```
P_g(x) = 1/10   P_g(y) = 9/10
P_h(x) = 1/5    P_h(y) = 4/5
```

The feasibility predicate is `F(g, r) = (g = g₀ ∧ r = x)`: the true genome `g`
is information-feasible on `x`, and `h` is not.  The ordinary uniform-prior ML
rule picks `h` on `x` (`1/5 > 1/10`).  Conditioning on `E = F(G, R)` restricts
the joint law to `F = 1`; at `x` the only feasible candidate is `g`, so the
conditional posterior is supported on `g` alone — mass `1` on `g` — and the
conditional MAP returns `g` with certainty.  This is the precise sense in which
conditioning on `E` is a *different experiment*. -/

/-- The likelihood of the toy. -/
def toyP : Fin 2 → Fin 2 → ℚ
  | 0, 0 => 1 / 10
  | 0, 1 => 9 / 10
  | 1, 0 => 1 / 5
  | 1, 1 => 4 / 5

/-- Equal prior `π = (1/2, 1/2)`. -/
def toyπ : Fin 2 → ℚ := fun _ => 1 / 2

/-- Joint weight of the toy. -/
def toyJ : Fin 2 → Fin 2 → ℚ := fun g r => joint toyπ toyP g r

/-- Feasibility predicate: only `(g, x)` is information-feasible.  (`abbrev`,
not `def`, so that instance search sees the underlying decidable conjunction
when `toyCondJ` forms an `if`.) -/
abbrev toyF (g r : Fin 2) : Prop := g = 0 ∧ r = 0

/-- The conditional joint weight `π(g) P(g, r) 1_F(g, r)`. -/
def toyCondJ (g r : Fin 2) : ℚ := if toyF g r then toyJ g r else 0

/-- Ordinary uniform-prior ML picks `h` on `x`. -/
theorem toy_ml_picks_h : toyP 1 0 > toyP 0 0 := by norm_num [toyP]

/-- The unconstrained MAP rule also picks `h` on `x` (the prior is uniform). -/
theorem toy_map_picks_h : toyJ 1 0 > toyJ 0 0 := by
  norm_num [toyJ, joint, toyπ, toyP]

/-- Conditioning on `E` kills `h` on `x`: the conditional joint weight of `h`
is `0`, while that of `g` is `1/20`. -/
theorem toy_cond_support : toyCondJ 0 0 = 1 / 20 ∧ toyCondJ 1 0 = 0 := by
  constructor <;> norm_num [toyCondJ, toyF, toyJ, joint, toyπ, toyP]

/-- The conditional MAP strictly prefers `g` over `h` on `x`. -/
theorem toy_cond_g_beats_h : toyCondJ 1 0 < toyCondJ 0 0 := by
  rw [toy_cond_support.1, toy_cond_support.2]
  norm_num

/-- **Conditional posterior mass `1` on `g`.**  Normalizing the conditional
joint weight at `x` gives `1` on `g` and `0` on `h`. -/
theorem toy_cond_normalized :
    toyCondJ 0 0 / (toyCondJ 0 0 + toyCondJ 1 0) = 1 := by
  rw [toy_cond_support.1, toy_cond_support.2]
  norm_num

end AssemblyP1.MapDecisionExamples
