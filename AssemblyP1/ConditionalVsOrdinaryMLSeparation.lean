import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Conditional Bayes vs ordinary finite ML: an exact same-model separation (issue #271)

**Status: abstract finite pmf witness, Lean kernel-checked. This is NOT a
source-faithful genome witness.** It makes no claim about the AssemblyP1 read
model, genome universe, or MB09 likelihood. It exhibits, inside one and the
same generative model, the exact boundary between the two finite-recovery
guarantees compared in #271:

* (A) posterior certainty under an externally supplied side observation `E`,
  versus
* (B) unconditional ordinary maximum likelihood from `R` alone.

The model is the concrete witness of the #271 research note: two candidate
hypotheses `Θ = {A, B}`, observation alphabet `W = {0, 1}`, equal positive
prior `π_A = π_B = 1/2`, and likelihoods

`P_A(0) = 1/4`, `P_A(1) = 3/4`, `P_B(0) = 3/4`, `P_B(1) = 1/4`.

All probabilities are exact rationals; every statement below is checked by the
Lean kernel. `#print axioms` is clean: the only axioms are the Mathlib
foundations `propext`, `Classical.choice`, `Quot.sound` (see
`AssemblyP1/AxiomAudit271.lean`).

## Unconditional event probability vs posterior conditioning

`joint h r` is the UNCONDITIONAL probability of the pair `(h, r)`;
`evidence r` is the unconditional event probability `P(R = r)`; `posterior`
is ordinary conditioning on the observation; `jointE`/`evidenceE`/
`condPosterior` condition additionally on the side observation `E`, i.e. the
conditional posterior is proportional to `π(h) · p_h(r) · 1_{E(h, r)}` — the
formula the conditional-Bayes question of #271 asks about, with the indicator
made explicit.

## Two samples separate the guarantees

* at `r = 0` with truth `A`: R-only ordinary ML strictly prefers the wrong
  hypothesis `B` (`3/4 > 1/4`), so `A` is not even a maximizer, and the
  ordinary posterior `P(A | r) = 1/4` is not certainty; yet the truth-dependent
  side observation `E` (supplied externally, NOT computable from `R`) excludes
  `B` and yields `P(A | r, E) = 1`;
* at `r = 1` with truth `A`: ordinary ML uniquely selects the truth `A`, but
  the ordinary posterior `P(A | r) = 3/4` is still not certainty — so even the
  unique-maximizer form of (B) does not imply (A) without side information.

## The exact decision boundary

At a fixed observation `r`, conditional recovery is certain for some candidate
exactly when the posterior support fibre
`{g : π g > 0 ∧ p_g(r) > 0 ∧ E g r}` is a singleton — `condRecoveryCertain_iff`
below (orbits are singletons in this two-candidate toy; the general
orbit-class statement is `AssemblyP1.FiniteBayesianSideInformation.posteriorMass_eq_one_iff`,
#272). Ordinary ML truth-maximality holds exactly when the truth's likelihood
dominates every candidate's (`isMLMaximizer`), with the unique-maximizer form
additionally requiring strict inequality off the truth; neither the prior nor
`E` enters (B). The two boundaries are logically incomparable, witnessed by
`separation_A_not_B` and `separation_B_not_A`.

## Data-only vs hypothesis-dependent side observations

A side observation that is DATA-ONLY (a function of `R` alone) cannot change
the per-sample posterior: the indicator is constant across hypotheses at fixed
`r` and cancels (`condPosterior_dataOnly`). The toy's `E` is genuinely
HYPOTHESIS-DEPENDENT (`sideInfo_not_dataOnly`), so it must be supplied
externally. Contrast: "knowing the truth satisfies `F`" as side information is
not the same as running ordinary ML over `F`-qualified candidates, and not the
same as a theorem for unrestricted likelihood.
-/

namespace AssemblyP1.ConditionalVsOrdinaryMLSeparation

/-- The two candidate hypotheses `Θ = {A, B}`. -/
inductive Hypothesis : Type
  | A
  | B
  deriving DecidableEq

/-- The observation alphabet `W = {0, 1}`. -/
inductive Obs : Type
  | r0
  | r1
  deriving DecidableEq

open Hypothesis Obs

/-- Exact likelihood of observation `r` under hypothesis `h`: a bona fide pmf
(`lik_pmf`). -/
def lik (h : Hypothesis) (r : Obs) : ℚ :=
  match h, r with
  | A, r0 => 1 / 4
  | A, r1 => 3 / 4
  | B, r0 => 3 / 4
  | B, r1 => 1 / 4

/-- Equal positive prior on the two hypotheses (the uniform-orbit prior). -/
def prior (_ : Hypothesis) : ℚ := 1 / 2

/-- UNCONDITIONAL probability of the pair `(h, r)`: `π(h) · p_h(r)`. -/
def joint (h : Hypothesis) (r : Obs) : ℚ := prior h * lik h r

/-- UNCONDITIONAL event probability `P(R = r)` under the prior. -/
def evidence (r : Obs) : ℚ := joint A r + joint B r

/-- Ordinary posterior `P(θ = h | R = r)`, conditioning on the observation
alone: `π(h) · p_h(r) / P(R = r)`. -/
def posterior (h : Hypothesis) (r : Obs) : ℚ := joint h r / evidence r

/-- The truth-dependent side observation `E(θ, r)`, supplied externally:
`E` holds at `(θ, r)` iff `(r = 0 ∧ θ = A) ∨ (r = 1 ∧ θ = B)`. Declared as an
`abbrev` so that instance search sees the underlying decidable disjunction when
`jointE` forms an `if`. -/
abbrev sideInfo (h : Hypothesis) (r : Obs) : Prop :=
  (h = A ∧ r = r0) ∨ (h = B ∧ r = r1)

/-- Joint probability of `(h, r)` together with the side observation `E`: the
conditional posterior is proportional to `π(h) · p_h(r) · 1_{E(h, r)}`, with
the indicator made explicit. -/
def jointE (E : Hypothesis → Obs → Prop) [DecidableRel E] (h : Hypothesis) (r : Obs) : ℚ :=
  if E h r then joint h r else 0

/-- Probability of the observation `r` together with the side observation `E`. -/
def evidenceE (E : Hypothesis → Obs → Prop) [DecidableRel E] (r : Obs) : ℚ :=
  jointE E A r + jointE E B r

/-- Posterior under the externally supplied side observation `E`:
`P(θ = h | R = r, E)`. -/
def condPosterior (E : Hypothesis → Obs → Prop) [DecidableRel E]
    (h : Hypothesis) (r : Obs) : ℚ :=
  jointE E h r / evidenceE E r

/-! ## Basic model facts

Each hypothesis is a genuine pmf on `W` with positive prior mass, and each
joint weight is positive. -/

theorem lik_nonneg (h : Hypothesis) (r : Obs) : 0 ≤ lik h r := by
  cases h <;> cases r <;> norm_num [lik]

theorem lik_pmf (h : Hypothesis) : lik h r0 + lik h r1 = 1 := by
  cases h <;> norm_num [lik]

theorem prior_pos (h : Hypothesis) : 0 < prior h := by
  cases h <;> norm_num [prior]

theorem joint_pos (h : Hypothesis) (r : Obs) : 0 < joint h r := by
  cases h <;> cases r <;> norm_num [joint, prior, lik]

theorem joint_nonneg (h : Hypothesis) (r : Obs) : 0 ≤ joint h r :=
  le_of_lt (joint_pos h r)

theorem evidence_pos (r : Obs) : 0 < evidence r := by
  cases r <;> norm_num [evidence, joint, prior, lik]

theorem jointE_nonneg {E : Hypothesis → Obs → Prop} [DecidableRel E]
    (h : Hypothesis) (r : Obs) : 0 ≤ jointE E h r := by
  unfold jointE
  split
  · exact joint_nonneg h r
  · exact le_refl 0

/-! ## Unconditional event probabilities and ordinary posteriors -/

theorem joint_A_r0 : joint A r0 = 1 / 8 := by norm_num [joint, prior, lik]

theorem joint_B_r0 : joint B r0 = 3 / 8 := by norm_num [joint, prior, lik]

theorem joint_A_r1 : joint A r1 = 3 / 8 := by norm_num [joint, prior, lik]

theorem joint_B_r1 : joint B r1 = 1 / 8 := by norm_num [joint, prior, lik]

/-- Each observation has unconditional probability exactly `1/2`. -/
theorem evidence_r0 : evidence r0 = 1 / 2 := by
  norm_num [evidence, joint, prior, lik]

theorem evidence_r1 : evidence r1 = 1 / 2 := by
  norm_num [evidence, joint, prior, lik]

theorem posterior_A_r0 : posterior A r0 = 1 / 4 := by
  norm_num [posterior, evidence, joint, prior, lik]

theorem posterior_B_r0 : posterior B r0 = 3 / 4 := by
  norm_num [posterior, evidence, joint, prior, lik]

theorem posterior_A_r1 : posterior A r1 = 3 / 4 := by
  norm_num [posterior, evidence, joint, prior, lik]

theorem posterior_B_r1 : posterior B r1 = 1 / 4 := by
  norm_num [posterior, evidence, joint, prior, lik]

/-- At `r = 0` the ordinary posterior on the truth `A` is `1/4`: NOT certainty. -/
theorem posterior_A_r0_not_certain : posterior A r0 ≠ 1 := by
  rw [posterior_A_r0]; norm_num

/-- At `r = 1` the ordinary posterior on the truth `A` is `3/4`: NOT certainty,
even though ordinary ML selects the truth there. -/
theorem posterior_A_r1_not_certain : posterior A r1 ≠ 1 := by
  rw [posterior_A_r1]; norm_num

/-! ## Ordinary R-only ML

The ML maximizer predicate at observation `r`: `h` is a maximizer when no other
hypothesis has strictly larger likelihood. -/

/-- Ordinary ML truth-maximality: `h` maximizes the likelihood at `r` (ties
allowed). The prior and the side observation do not enter. -/
def isMLMaximizer (h : Hypothesis) (r : Obs) : Prop :=
  ∀ h', lik h' r ≤ lik h r

/-- At `r = 0` ordinary ML strictly prefers the wrong hypothesis `B`
(`3/4 > 1/4`), and `B` is the UNIQUE maximizer. -/
theorem ml_unique_maximizer_r0 :
    isMLMaximizer B r0 ∧ ∀ h, isMLMaximizer h r0 → h = B := by
  constructor
  · intro h'
    cases h' <;> norm_num [lik]
  · intro h hmax
    cases h with
    | A => exact absurd (hmax B) (by norm_num [lik])
    | B => rfl

/-- At `r = 0` the truth `A` is not even a maximizer of the likelihood. -/
theorem truth_not_ml_maximizer_r0 : ¬ isMLMaximizer A r0 := by
  intro h
  exact absurd (h B) (by norm_num [lik])

/-- At `r = 1` ordinary ML strictly prefers `A` (`3/4 > 1/4`) and `A` is the
UNIQUE maximizer: the truth is selected. -/
theorem ml_unique_maximizer_r1 :
    isMLMaximizer A r1 ∧ ∀ h, isMLMaximizer h r1 → h = A := by
  constructor
  · intro h'
    cases h' <;> norm_num [lik]
  · intro h hmax
    cases h with
    | A => rfl
    | B => exact absurd (hmax A) (by norm_num [lik])

/-- Ordinary ML ignores the prior entirely: the strict likelihood ordering is a
statement about `p_h(r)` alone. -/
theorem ml_ignores_prior_r0 : lik A r0 < lik B r0 := by norm_num [lik]

/-! ## Data-only vs hypothesis-dependent side observations -/

/-- A side observation is DATA-ONLY when it is a function of the observation
alone (no dependence on the latent hypothesis). -/
def dataOnly (E : Hypothesis → Obs → Prop) : Prop :=
  ∃ f : Obs → Prop, ∀ h r, E h r ↔ f r

/-- Conditioning on a DATA-ONLY side observation cannot change the per-sample
posterior: at fixed `r` the indicator `1_{E(h, r)} = f r` is constant across
hypotheses and cancels against the denominator. -/
theorem condPosterior_dataOnly {E : Hypothesis → Obs → Prop} [DecidableRel E]
    {f : Obs → Prop} (hfe : ∀ h r, E h r ↔ f r) {r : Obs} (hf : f r)
    (h : Hypothesis) : condPosterior E h r = posterior h r := by
  have hE : E h r := (hfe h r).mpr hf
  have hjE : jointE E h r = joint h r := by
    unfold jointE
    rw [ite_eq_left hE]
  have hsum : ∀ g, jointE E g r = joint g r := fun g => by
    unfold jointE
    rw [ite_eq_left ((hfe g r).mpr hf)]
  have hev : evidenceE E r = evidence r := by
    unfold evidenceE evidence
    rw [hsum A, hsum B]
  unfold condPosterior
  rw [hjE, hev]
  rfl

/-- `E` is genuinely truth-dependent: at the SAME observation `r = 0`, `E`
holds under `A` and fails under `B`. -/
theorem sideInfo_truth_dependent_r0 :
    sideInfo A r0 ∧ ¬ sideInfo B r0 := by
  constructor <;> simp [sideInfo]

/-- Consequently `E` is not a function of `R` alone: no predicate `f r` on the
observation can equal `sideInfo h r` for every `h`. `E` must be externally
supplied; it cannot be inferred from `R`. -/
theorem sideInfo_not_dataOnly : ¬ dataOnly sideInfo := by
  rintro ⟨f, hf⟩
  have h0 : sideInfo A r0 := by simp [sideInfo]
  have h1 : ¬ sideInfo B r0 := by simp [sideInfo]
  rw [hf A r0] at h0
  rw [hf B r0] at h1
  exact h1 h0

/-! ## Conditional recovery with the truth-dependent side observation `E`

`E` must actually be PROVIDED as side information: it is deliberately an
abstract truth-revealing counterexample, not a Not-So-Greedy information-
feasibility condition and not an observable function of `R`. -/

/-- The toy's `E`-fibre at `r = 0` is exactly `{A}`. -/
theorem sideInfo_fibre_r0 (h : Hypothesis) (hs : sideInfo h r0) : h = A := by
  cases h with
  | A => rfl
  | B => simp [sideInfo] at hs

/-- The toy's `E`-fibre at `r = 1` is exactly `{B}`. -/
theorem sideInfo_fibre_r1 (h : Hypothesis) (hs : sideInfo h r1) : h = B := by
  cases h with
  | A => simp [sideInfo] at hs
  | B => rfl

/-- When the `E`-fibre at `r` is the singleton `{h}` with positive joint mass,
the conditional posterior is certain on `h` — regardless of what unconditional
ML selects. -/
theorem condPosterior_singleton_fibre {E : Hypothesis → Obs → Prop} [DecidableRel E]
    {h : Hypothesis} {r : Obs} (hE : E h r) (hne : ∀ h', h' ≠ h → ¬ E h' r)
    (hpos : 0 < joint h r) : condPosterior E h r = 1 := by
  have hcj : jointE E h r = joint h r := by
    unfold jointE
    rw [ite_eq_left hE]
  have hev : evidenceE E r = joint h r := by
    unfold evidenceE
    cases h with
    | A =>
      have hB0 : jointE E B r = 0 := by
        unfold jointE
        rw [ite_eq_right (hne B (by decide))]
      rw [hcj, hB0, add_zero]
    | B =>
      have hA0 : jointE E A r = 0 := by
        unfold jointE
        rw [ite_eq_right (hne A (by decide))]
      rw [hA0, hcj, zero_add]
  unfold condPosterior
  rw [hcj, hev, div_self (ne_of_gt hpos)]

/-- Off the singleton `E`-fibre the conditional posterior is exactly zero. -/
theorem condPosterior_fibre_zero {E : Hypothesis → Obs → Prop} [DecidableRel E]
    {h h' : Hypothesis} {r : Obs} (hne : ∀ t, t ≠ h → ¬ E t r)
    (h'ne : h' ≠ h) : condPosterior E h' r = 0 := by
  have hj0 : jointE E h' r = 0 := by
    unfold jointE
    rw [ite_eq_right (hne h' h'ne)]
  unfold condPosterior
  rw [hj0]
  exact zero_div _

/-- Given `E` at `r = 0`, the posterior on the truth `A` is exactly `1`:
conditional recovery is CERTAIN. -/
theorem condPosterior_A_r0 : condPosterior sideInfo A r0 = 1 := by
  apply condPosterior_singleton_fibre
  · simp [sideInfo]
  · intro h' hh'
    cases h' with
    | A => exact absurd rfl hh'
    | B => simp [sideInfo]
  · exact joint_pos A r0

/-- Given `E` at `r = 0`, the posterior on the wrong hypothesis `B` is exactly
`0`: `B` is excluded by `E`. -/
theorem condPosterior_B_r0 : condPosterior sideInfo B r0 = 0 :=
  condPosterior_fibre_zero (E := sideInfo) (h := A) (r := r0)
    (hne := fun t ht => by
      cases t with
      | A => exact absurd rfl ht
      | B => simp [sideInfo])
    (h'ne := by decide)

/-- At `r = 1` the side observation `E` certifies `B` instead: the same
truth-dependent mechanism works on the other branch. -/
theorem condPosterior_B_r1 : condPosterior sideInfo B r1 = 1 := by
  apply condPosterior_singleton_fibre
  · simp [sideInfo]
  · intro h' hh'
    cases h' with
    | A => simp [sideInfo]
    | B => exact absurd rfl hh'
  · exact joint_pos B r1

theorem condPosterior_A_r1 : condPosterior sideInfo A r1 = 0 :=
  condPosterior_fibre_zero (E := sideInfo) (h := B) (r := r1)
    (hne := fun t ht => by
      cases t with
      | A => simp [sideInfo]
      | B => exact absurd rfl ht)
    (h'ne := by decide)

/-! ## The (A)-boundary: conditional recovery iff singleton support fibre -/

/-- Conditional recovery at `r` under side observation `E`: some candidate's
conditional posterior is exactly `1`. -/
def CondCertain (E : Hypothesis → Obs → Prop) [DecidableRel E] (r : Obs) : Prop :=
  ∃ g, condPosterior E g r = 1

/-- If some candidate's conditional posterior is `1`, then that candidate has
positive joint mass, satisfies `E`, and every other candidate's conditional
joint weight vanishes. -/
theorem condPosterior_one_imp {E : Hypothesis → Obs → Prop} [DecidableRel E]
    {g : Hypothesis} {r : Obs} (h1 : condPosterior E g r = 1) :
    0 < joint g r ∧ E g r ∧ ∀ h, h ≠ g → jointE E h r = 0 := by
  have hden_ne : evidenceE E r ≠ 0 := by
    intro h0
    have hz : condPosterior E g r = 0 := by
      unfold condPosterior
      rw [h0, div_zero]
    rw [hz] at h1
    exact zero_ne_one h1
  have hden_nonneg : 0 ≤ evidenceE E r := by
    unfold evidenceE
    linarith [jointE_nonneg (E := E) A r, jointE_nonneg (E := E) B r]
  have hden_pos : 0 < evidenceE E r :=
    lt_of_le_of_ne hden_nonneg (Ne.symm hden_ne)
  have hcj_eq : jointE E g r = evidenceE E r := by
    have h := (div_eq_iff hden_ne).mp (by
      show jointE E g r / evidenceE E r = 1
      exact h1)
    rwa [one_mul] at h
  have hcj_pos : 0 < jointE E g r := by rw [hcj_eq]; exact hden_pos
  have hE : E g r := by
    by_contra hne
    unfold jointE at hcj_pos
    rw [ite_eq_right hne] at hcj_pos
    norm_num at hcj_pos
  have hjpos : 0 < joint g r := by
    have hje : jointE E g r = joint g r := by
      unfold jointE
      rw [ite_eq_left hE]
    rw [hje] at hcj_pos
    exact hcj_pos
  refine ⟨hjpos, hE, ?_⟩
  intro h hh
  have hsum : jointE E g r + jointE E h r = evidenceE E r := by
    unfold evidenceE
    cases g <;> cases h <;> simp_all [add_comm]
  rw [← hcj_eq] at hsum
  have := jointE_nonneg (E := E) h r
  linarith

/-- If some candidate has positive joint mass, satisfies `E`, and every other
candidate's conditional joint weight vanishes, then its conditional posterior
is exactly `1`. -/
theorem condPosterior_of_fibre {E : Hypothesis → Obs → Prop} [DecidableRel E]
    {g : Hypothesis} {r : Obs} (hE : E g r) (hjpos : 0 < joint g r)
    (hoff : ∀ h, h ≠ g → jointE E h r = 0) : condPosterior E g r = 1 := by
  have hcj : jointE E g r = joint g r := by
    unfold jointE
    rw [ite_eq_left hE]
  have hden : evidenceE E r = joint g r := by
    unfold evidenceE
    cases g with
    | A =>
      rw [hcj, hoff B (by decide)]
      exact add_zero _
    | B =>
      rw [hoff A (by decide), hcj]
      exact zero_add _
  unfold condPosterior
  rw [hden, hcj, div_self (ne_of_gt hjpos)]

/-- **The (A)-boundary, toy level.** Conditional recovery at `r` under `E`
holds iff the posterior support fibre `{g : π g > 0 ∧ p_g(r) > 0 ∧ E g r}` is a
singleton — the "posterior support has one genome orbit" boundary of #271, with
orbits singletons in this two-candidate toy. -/
theorem condRecoveryCertain_iff {E : Hypothesis → Obs → Prop} [DecidableRel E]
    {r : Obs} :
    CondCertain E r ↔
      ∃ g, 0 < joint g r ∧ E g r ∧ ∀ h, h ≠ g → jointE E h r = 0 := by
  constructor
  · rintro ⟨g, h1⟩
    exact ⟨g, condPosterior_one_imp h1⟩
  · rintro ⟨g, hjpos, hE, hoff⟩
    exact ⟨g, condPosterior_of_fibre hE hjpos hoff⟩

/-! ## The two separations -/

/-- **Separation (A ∧ ¬B).** At `r = 0` with truth `A`, conditional recovery is
certain under the truth-dependent side observation `E` (`P(A | r, E) = 1`),
while ordinary R-only ML strictly prefers the wrong hypothesis `B`
(`3/4 > 1/4`), so the truth `A` is not even a maximizer and the ordinary
posterior on the truth is `1/4`, not certainty. -/
theorem separation_A_not_B :
    CondCertain sideInfo r0 ∧ isMLMaximizer B r0 ∧ ¬ isMLMaximizer A r0 ∧
      posterior A r0 = 1 / 4 ∧ posterior A r0 ≠ 1 :=
  ⟨⟨A, condPosterior_A_r0⟩, ml_unique_maximizer_r0.1, truth_not_ml_maximizer_r0,
    posterior_A_r0, posterior_A_r0_not_certain⟩

/-- **Separation (B ∧ ¬A).** At `r = 1` with truth `A`, ordinary ML uniquely
selects the truth (`3/4 > 1/4`), yet the ordinary posterior on the truth is
`3/4`, not certainty: unique-maximizer ML recovery does not give posterior
certainty without side information. -/
theorem separation_B_not_A :
    isMLMaximizer A r1 ∧ (∀ h, isMLMaximizer h r1 → h = A) ∧
      posterior A r1 = 3 / 4 ∧ posterior A r1 ≠ 1 :=
  ⟨ml_unique_maximizer_r1.1, ml_unique_maximizer_r1.2, posterior_A_r1,
    posterior_A_r1_not_certain⟩

/-- Certainty is a property of the support-collapse mechanism, not of
correctness: under `E`, conditioning at `r = 1` certifies the WRONG candidate
`B` (for truth `A`), because `E`'s fibre at `r = 1` is `{B}`. -/
theorem condPosterior_E_certifies_wrong_r1 :
    condPosterior sideInfo B r1 = 1 ∧ condPosterior sideInfo A r1 = 0 :=
  ⟨condPosterior_B_r1, condPosterior_A_r1⟩

/-! ## Prior support: uniform sequences vs uniform rotation/RC orbits

A uniform prior over SEQUENCES induces orbit mass proportional to orbit size; a
uniform prior over ORBITS gives each orbit equal mass. When orbit sizes differ
the two priors differ, and the posterior differs with them. -/

/-- Orbit sizes in the toy: `A` is a periodic (rotation/RC-orbit-size-1)
candidate, `B` has orbit size 2. -/
def orbitSize (h : Hypothesis) : ℕ := if h = A then 1 else 2

/-- Uniform prior over orbits. -/
def priorOrbit (_ : Hypothesis) : ℚ := 1 / 2

/-- Uniform prior over sequences: orbit `h` gets mass proportional to its orbit
size. -/
def priorSeq (h : Hypothesis) : ℚ :=
  (orbitSize h : ℚ) / ((orbitSize A : ℚ) + (orbitSize B : ℚ))

def jointSeq (h : Hypothesis) (r : Obs) : ℚ := priorSeq h * lik h r

def posteriorSeq (h : Hypothesis) (r : Obs) : ℚ :=
  jointSeq h r / (jointSeq A r + jointSeq B r)

theorem orbitSize_A : orbitSize A = 1 := rfl

theorem orbitSize_B : orbitSize B = 2 := rfl

theorem priorSeq_A : priorSeq A = 1 / 3 := by
  norm_num [priorSeq, orbitSize]

theorem priorSeq_B : priorSeq B = 2 / 3 := by
  norm_num [priorSeq, orbitSize]

/-- The two priors genuinely differ because the orbit sizes differ. -/
theorem priorOrbit_ne_priorSeq_A : priorOrbit A ≠ priorSeq A := by
  rw [priorSeq_A]
  norm_num [priorOrbit]

theorem posteriorSeq_A_r0 : posteriorSeq A r0 = 1 / 7 := by
  norm_num [posteriorSeq, jointSeq, priorSeq, lik, orbitSize]

/-- Switching from the uniform-orbit prior to the uniform-sequence prior
changes the posterior on `A` at `r = 0` from `1/4` to `1/7`, while ordinary ML
is unchanged. -/
theorem posteriorSeq_A_r0_ne_posterior_A_r0 :
    posteriorSeq A r0 ≠ posterior A r0 := by
  rw [posteriorSeq_A_r0, posterior_A_r0]
  norm_num

end AssemblyP1.ConditionalVsOrdinaryMLSeparation
