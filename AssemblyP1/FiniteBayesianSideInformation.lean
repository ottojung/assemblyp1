import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Finite Bayesian side information for certain orbit-class recovery (#272)

This file extends the support-only abstraction of
`AssemblyP1.FiniteSideInformationColoring` (#164) with the probabilities,
priors, and posterior that #272 asks for.  The central object is the
*truth-dependent promise event* `E g r`, which is conditioned on jointly with
the read `r`, not inferred from `r`.

Setup.  `Genome` is a finite candidate set, `Obs` a finite read sample space,
and `orbit : Genome → Θ` maps each candidate to its circular-rotation orbit
class in the finite class type `Θ`.  A normalized prior `π` and a generative
likelihood `p` are combined with the promise `E` into the unnormalized joint
mass

`jointMass π p E g r = π g · p_g(r) · 1_E(g,r)`.

Conditioning on the observed pair `(R = r, E)` means dividing by the
predictive mass `predictiveMass π p E r = ∑_g jointMass π p E g r`; this is the
"condition the prior AND the likelihood on `E`" requirement of #272, made
explicit rather than silently dropping the indicator.

Main result (`posteriorMass_eq_one_iff`).  For an observed `r` with positive
predictive mass, the conditional posterior on the orbit class `θ` equals one
exactly when every genome with positive prior, positive read likelihood, and
positive promise indicator lies in `θ`.  Equivalently
(`posteriorMass_eq_one_iff_excluded`) the posterior on the true orbit class is
one exactly when the promise excludes every other orbit that the read alone
would leave possible.  The side-channel version `posteriorMassZ_eq_one_iff`
replaces the promise by an observed auxiliary variable and reads: the
supported fibre of `(R, Z)` is a single orbit class.

Nothing here asserts the external Shomorony et al. Not-So-Greedy theorem.
`fibreUnique_of_decoder` and `conditional_certain_of_fibreUnique` are the
honest, kernel-checked bridge: *if* a read-only decoder is correct on the
support of a promise predicate, *then* that predicate's fibre is a single
orbit and conditioning on it gives posterior one.  Supplying the actual
information-feasibility predicate is a separate, attributed premise.
-/

set_option linter.unusedSectionVars false

namespace AssemblyP1.FiniteBayesianSideInformation

open Finset

variable {Genome Obs Aux Θ : Type*}

/-- If `f` is nonnegative then the orbit-restricted sum equals the full sum
exactly when every positive entry already lies in the orbit `θ`.  This is the
combinatorial core shared by the promise and side-channel posterior theorems. -/
lemma sum_ite_eq_total_iff {ι : Type*} [Fintype ι] {Θ' : Type*} [DecidableEq Θ']
    (orbit : ι → Θ') (θ : Θ') {f : ι → ℝ} (hfnn : ∀ i, 0 ≤ f i) :
    (∑ i, (if orbit i = θ then f i else 0)) = (∑ i, f i) ↔
      ∀ i, 0 < f i → orbit i = θ := by
  have hle : ∀ i, (if orbit i = θ then f i else 0) ≤ f i := by
    intro i
    by_cases hh : orbit i = θ
    · rw [ite_eq_left hh]
    · rw [ite_eq_right hh]
      exact hfnn i
  have hiff : (∑ i, (if orbit i = θ then f i else 0)) = (∑ i, f i) ↔
      ∀ i, (if orbit i = θ then f i else 0) = f i := by
    simpa using (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (f := fun i => if orbit i = θ then f i else 0) (g := f)
      (fun i _ => hle i))
  rw [hiff]
  constructor
  · intro H i hpos
    by_contra hne
    have h0 : (if orbit i = θ then f i else 0) = 0 := ite_eq_right hne
    have := H i
    rw [h0] at this
    exact (ne_of_gt hpos) this.symm
  · intro H i
    by_cases hh : orbit i = θ
    · exact ite_eq_left hh
    · have hz : f i = 0 := by
        have : ¬ 0 < f i := fun hpos => hh (H i hpos)
        exact le_antisymm (not_lt.mp this) (hfnn i)
      exact (ite_eq_right hh).trans hz.symm

section Core

variable [Fintype Genome] [Fintype Obs] [Fintype Θ] [DecidableEq Θ]

/-- Unnormalized joint mass of `(genome, read)` under prior `π`, likelihood
`p`, and the truth-dependent promise event `E`: `π g · p_g(r) · 1_E(g,r)`. -/
noncomputable def jointMass (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (E : Genome → Obs → Prop) [DecidableRel E] (g : Genome) (r : Obs) : ℝ :=
  π g * p g r * if E g r then (1 : ℝ) else 0

/-- Predictive mass of the joint observation `(R = r, E)`:
`∑_g π g · p_g(r) · 1_E(g,r)`. -/
noncomputable def predictiveMass (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (E : Genome → Obs → Prop) [DecidableRel E] (r : Obs) : ℝ :=
  ∑ g : Genome, jointMass π p E g r

/-- Conditional posterior mass of the orbit class `θ` given `(R = r, E)`. -/
noncomputable def posteriorMass (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (E : Genome → Obs → Prop) [DecidableRel E] (orbit : Genome → Θ)
    (r : Obs) (θ : Θ) : ℝ :=
  (∑ g : Genome, if orbit g = θ then jointMass π p E g r else 0) /
    predictiveMass π p E r

theorem jointMass_nonneg (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (E : Genome → Obs → Prop) [DecidableRel E]
    (hπ : ∀ g, 0 ≤ π g) (hp : ∀ g r, 0 ≤ p g r) (g : Genome) (r : Obs) :
    0 ≤ jointMass π p E g r := by
  unfold jointMass
  by_cases h : E g r
  · rw [ite_eq_left h, mul_one]
    exact mul_nonneg (hπ g) (hp g r)
  · rw [ite_eq_right h, mul_zero]

theorem jointMass_pos_iff (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (E : Genome → Obs → Prop) [DecidableRel E]
    (hπ : ∀ g, 0 ≤ π g) (hp : ∀ g r, 0 ≤ p g r) (g : Genome) (r : Obs) :
    0 < jointMass π p E g r ↔ 0 < π g ∧ 0 < p g r ∧ E g r := by
  unfold jointMass
  by_cases h : E g r
  · rw [ite_eq_left h, mul_one]
    exact ⟨fun hpos =>
        ⟨pos_of_mul_pos_left hpos (hp g r), pos_of_mul_pos_right hpos (hπ g), h⟩,
      fun ⟨h1, h2, _⟩ => mul_pos h1 h2⟩
  · rw [ite_eq_right h, mul_zero]
    exact ⟨fun hpos => absurd hpos (lt_irrefl 0), fun ⟨_, _, hE⟩ => absurd hE h⟩

/-- The supported fibre of `(R = r, E)` (candidates of positive joint mass) is
contained in a single orbit class. -/
def SupportInOrbit (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (E : Genome → Obs → Prop) [DecidableRel E] (orbit : Genome → Θ)
    (r : Obs) (θ : Θ) : Prop :=
  ∀ h, 0 < jointMass π p E h r → orbit h = θ

theorem supportInOrbit_iff (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (E : Genome → Obs → Prop) [DecidableRel E] (orbit : Genome → Θ)
    (hπ : ∀ g, 0 ≤ π g) (hp : ∀ g r, 0 ≤ p g r) (r : Obs) (θ : Θ) :
    SupportInOrbit π p E orbit r θ ↔
      ∀ h, 0 < π h → 0 < p h r → E h r → orbit h = θ := by
  unfold SupportInOrbit
  constructor
  · intro H h hπ' hp' hE
    exact H h ((jointMass_pos_iff π p E hπ hp h r).mpr ⟨hπ', hp', hE⟩)
  · intro H h hpos
    obtain ⟨hπ', hp', hE⟩ := (jointMass_pos_iff π p E hπ hp h r).mp hpos
    exact H h hπ' hp' hE

/-- **Exact necessary-and-sufficient theorem.**  For an observed read `r` with
positive predictive mass, the conditional posterior on the orbit class `θ` is
one iff the supported truth-fibre of `(R = r, E)` lies inside `θ`. -/
theorem posteriorMass_eq_one_iff (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (E : Genome → Obs → Prop) [DecidableRel E] (orbit : Genome → Θ)
    (hπ : ∀ g, 0 ≤ π g) (hp : ∀ g r, 0 ≤ p g r)
    (r : Obs) (θ : Θ) (hZ : 0 < predictiveMass π p E r) :
    posteriorMass π p E orbit r θ = 1 ↔
      ∀ h, 0 < π h → 0 < p h r → E h r → orbit h = θ := by
  have hfnn : ∀ h, 0 ≤ jointMass π p E h r :=
    fun h => jointMass_nonneg π p E hπ hp h r
  unfold posteriorMass predictiveMass
  rw [div_eq_one_iff_eq
    (show (∑ h : Genome, jointMass π p E h r) ≠ 0 from ne_of_gt hZ)]
  rw [sum_ite_eq_total_iff orbit θ (f := fun h => jointMass π p E h r) hfnn]
  exact supportInOrbit_iff π p E orbit hπ hp r θ

/-- **Excluded-competitor form.**  The posterior on the true orbit class is one
iff every genome of positive prior and positive read likelihood outside that
orbit is excluded by the promise `E`. -/
theorem posteriorMass_eq_one_iff_excluded (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (E : Genome → Obs → Prop) [DecidableRel E] (orbit : Genome → Θ)
    (hπ : ∀ g, 0 ≤ π g) (hp : ∀ g r, 0 ≤ p g r)
    (r : Obs) (g : Genome) (hZ : 0 < predictiveMass π p E r) :
    posteriorMass π p E orbit r (orbit g) = 1 ↔
      ∀ h, 0 < π h → 0 < p h r → orbit h ≠ orbit g → ¬ E h r := by
  rw [posteriorMass_eq_one_iff π p E orbit hπ hp r (orbit g) hZ]
  constructor
  · intro H h hπ' hp' hne hE
    exact hne (H h hπ' hp' hE)
  · intro H h hπ' hp' hE
    by_contra hne
    exact H h hπ' hp' hne hE

/-- A zero-prior candidate carries zero joint mass and is never in the support;
this is the zero-prior corner case that the "positive prior" hypothesis of the
exact theorem is designed to exclude. -/
theorem jointMass_eq_zero_of_prior_zero (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (E : Genome → Obs → Prop) [DecidableRel E]
    (g : Genome) (r : Obs) (h0 : π g = 0) : jointMass π p E g r = 0 := by
  simp [jointMass, h0]

theorem predictiveMass_nonneg (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (E : Genome → Obs → Prop) [DecidableRel E]
    (hπ : ∀ g, 0 ≤ π g) (hp : ∀ g r, 0 ≤ p g r) (r : Obs) :
    0 ≤ predictiveMass π p E r := by
  unfold predictiveMass
  exact Finset.sum_nonneg (fun g _ => jointMass_nonneg π p E hπ hp g r)

/-- Read-only form: without any promise, the posterior on an orbit class is one
iff every genome of positive prior and positive read likelihood already lies in
that orbit.  This is `posteriorMass_eq_one_iff` with `E ≡ True`. -/
theorem readOnly_posterior_eq_one_iff (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) (hπ : ∀ g, 0 ≤ π g) (hp : ∀ g r, 0 ≤ p g r)
    (r : Obs) (θ : Θ) (hZ : 0 < predictiveMass π p (fun _ _ => True) r) :
    posteriorMass π p (fun _ _ => True) orbit r θ = 1 ↔
      ∀ h, 0 < π h → 0 < p h r → orbit h = θ := by
  rw [posteriorMass_eq_one_iff π p (fun _ _ => True) orbit hπ hp r θ hZ]
  simp

/-- **a.s. versus pointwise.**  The aggregate conditional mass of a decoder's
orbit class equals the total predictive mass (i.e. conditional success is
certain almost surely) exactly when the pointwise posterior is one at every
observation of positive predictive mass. -/
theorem ae_certain_iff_pointwise (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (E : Genome → Obs → Prop) [DecidableRel E] (orbit : Genome → Θ)
    (d : Obs → Genome) (hπ : ∀ g, 0 ≤ π g) (hp : ∀ g r, 0 ≤ p g r) :
    (∑ r : Obs, (∑ g : Genome,
          if orbit g = orbit (d r) then jointMass π p E g r else 0))
        = (∑ r : Obs, predictiveMass π p E r)
      ↔ ∀ r, 0 < predictiveMass π p E r →
          posteriorMass π p E orbit r (orbit (d r)) = 1 := by
  have hle : ∀ r : Obs, (∑ g : Genome,
        if orbit g = orbit (d r) then jointMass π p E g r else 0)
      ≤ predictiveMass π p E r := by
    intro r
    unfold predictiveMass
    apply Finset.sum_le_sum
    intro g _
    by_cases hh : orbit g = orbit (d r)
    · rw [ite_eq_left hh]
    · rw [ite_eq_right hh]
      exact jointMass_nonneg π p E hπ hp g r
  have hnn : ∀ r : Obs, 0 ≤ (∑ g : Genome,
        if orbit g = orbit (d r) then jointMass π p E g r else 0) := by
    intro r
    exact Finset.sum_nonneg (fun g _ => by
      by_cases hh : orbit g = orbit (d r)
      · rw [ite_eq_left hh]; exact jointMass_nonneg π p E hπ hp g r
      · rw [ite_eq_right hh])
  have hiff : (∑ r : Obs, (∑ g : Genome,
          if orbit g = orbit (d r) then jointMass π p E g r else 0))
        = (∑ r : Obs, predictiveMass π p E r) ↔
      ∀ r : Obs, (∑ g : Genome,
          if orbit g = orbit (d r) then jointMass π p E g r else 0)
        = predictiveMass π p E r := by
    simpa using (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (f := fun r : Obs => ∑ g : Genome,
        if orbit g = orbit (d r) then jointMass π p E g r else 0)
      (g := fun r : Obs => predictiveMass π p E r)
      (fun r _ => hle r))
  rw [hiff]
  constructor
  · intro H r hZr
    have hcr := H r
    unfold posteriorMass
    rw [hcr, div_self (ne_of_gt hZr)]
  · intro H r
    by_cases hZr : 0 < predictiveMass π p E r
    · have := H r hZr
      unfold posteriorMass at this
      rw [div_eq_one_iff_eq (ne_of_gt hZr)] at this
      exact this
    · have hZ0 : predictiveMass π p E r = 0 :=
        le_antisymm (not_lt.mp hZr) (predictiveMass_nonneg π p E hπ hp r)
      have hc0 : (∑ g : Genome,
            if orbit g = orbit (d r) then jointMass π p E g r else 0) = 0 :=
        le_antisymm (hZ0 ▸ hle r) (hnn r)
      exact hc0.trans hZ0.symm

end Core

section SideChannel

variable [Fintype Genome] [Fintype Obs] [Fintype Aux] [Fintype Θ] [DecidableEq Θ]

/-- Unnormalized joint mass of `(genome, read, auxiliary observation)` under the
side channel `q`: `π g · p_g(r) · q_g(z | r)`. -/
noncomputable def jointMassZ (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (q : Genome → Obs → Aux → ℝ) (g : Genome) (r : Obs) (z : Aux) : ℝ :=
  π g * p g r * q g r z

noncomputable def predictiveMassZ (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (q : Genome → Obs → Aux → ℝ) (r : Obs) (z : Aux) : ℝ :=
  ∑ g : Genome, jointMassZ π p q g r z

noncomputable def posteriorMassZ (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (q : Genome → Obs → Aux → ℝ) (orbit : Genome → Θ)
    (r : Obs) (z : Aux) (θ : Θ) : ℝ :=
  (∑ g : Genome, if orbit g = θ then jointMassZ π p q g r z else 0) /
    predictiveMassZ π p q r z

theorem jointMassZ_nonneg (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (q : Genome → Obs → Aux → ℝ)
    (hπ : ∀ g, 0 ≤ π g) (hp : ∀ g r, 0 ≤ p g r) (hq : ∀ g r z, 0 ≤ q g r z)
    (g : Genome) (r : Obs) (z : Aux) : 0 ≤ jointMassZ π p q g r z := by
  unfold jointMassZ
  exact mul_nonneg (mul_nonneg (hπ g) (hp g r)) (hq g r z)

theorem jointMassZ_pos_iff (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (q : Genome → Obs → Aux → ℝ)
    (hπ : ∀ g, 0 ≤ π g) (hp : ∀ g r, 0 ≤ p g r) (hq : ∀ g r z, 0 ≤ q g r z)
    (g : Genome) (r : Obs) (z : Aux) :
    0 < jointMassZ π p q g r z ↔ 0 < π g ∧ 0 < p g r ∧ 0 < q g r z := by
  unfold jointMassZ
  constructor
  · intro hpos
    have hπp : 0 < π g * p g r := pos_of_mul_pos_left hpos (hq g r z)
    exact ⟨pos_of_mul_pos_left hπp (hp g r),
      pos_of_mul_pos_right hπp (hπ g),
      pos_of_mul_pos_right hpos (mul_nonneg (hπ g) (hp g r))⟩
  · intro ⟨h1, h2, h3⟩
    exact mul_pos (mul_pos h1 h2) h3

/-- **Side-channel form.**  For an observed `(r, z)` with positive predictive
mass, the posterior on the orbit class `θ` is one iff the supported fibre of
`(R, Z)` lies inside `θ`, i.e. the side channel leaves at most one orbit. -/
theorem posteriorMassZ_eq_one_iff (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (q : Genome → Obs → Aux → ℝ) (orbit : Genome → Θ)
    (hπ : ∀ g, 0 ≤ π g) (hp : ∀ g r, 0 ≤ p g r) (hq : ∀ g r z, 0 ≤ q g r z)
    (r : Obs) (z : Aux) (θ : Θ) (hZ : 0 < predictiveMassZ π p q r z) :
    posteriorMassZ π p q orbit r z θ = 1 ↔
      ∀ h, 0 < π h → 0 < p h r → 0 < q h r z → orbit h = θ := by
  have hfnn : ∀ h, 0 ≤ jointMassZ π p q h r z :=
    fun h => jointMassZ_nonneg π p q hπ hp hq h r z
  unfold posteriorMassZ predictiveMassZ
  rw [div_eq_one_iff_eq
    (show (∑ h : Genome, jointMassZ π p q h r z) ≠ 0 from ne_of_gt hZ)]
  rw [sum_ite_eq_total_iff orbit θ (f := fun h => jointMassZ π p q h r z) hfnn]
  constructor
  · intro H h hπ' hp' hq'
    exact H h ((jointMassZ_pos_iff π p q hπ hp hq h r z).mpr ⟨hπ', hp', hq'⟩)
  · intro H h hpos
    obtain ⟨hπ', hp', hq'⟩ := (jointMassZ_pos_iff π p q hπ hp hq h r z).mp hpos
    exact H h hπ' hp' hq'

end SideChannel

section Bridge

variable [Fintype Genome] [Fintype Obs] [Fintype Θ] [DecidableEq Θ]

/-- If a read-only decoder `A` is correct on the support of a promise predicate
`F` (i.e. `F g r → orbit (A r) = orbit g`), then the `F`-fibre of any fixed read
`r` is contained in a single orbit class.  The correctness hypothesis is exactly
the external Not-So-Greedy guarantee and is *not* proved here. -/
theorem fibreUnique_of_decoder (F : Genome → Obs → Prop) (A : Obs → Genome)
    (orbit : Genome → Θ) (hA : ∀ g r, F g r → orbit (A r) = orbit g) :
    ∀ g h r, F g r → F h r → orbit g = orbit h := by
  intro g h r hg hh
  rw [← hA g r hg, ← hA h r hh]

/-- Fibre uniqueness of a promise predicate forces conditional posterior one for
every positive-probability observation of a positive-probability truth. -/
theorem conditional_certain_of_fibreUnique (F : Genome → Obs → Prop)
    [DecidableRel F] (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) (hπ : ∀ g, 0 ≤ π g) (hp : ∀ g r, 0 ≤ p g r)
    (hF : ∀ g h r, F g r → F h r → orbit g = orbit h)
    (g : Genome) (r : Obs) (hπg : 0 < π g) (hpg : 0 < p g r) (hFg : F g r) :
    posteriorMass π p F orbit r (orbit g) = 1 := by
  have hZ : 0 < predictiveMass π p F r := by
    have hg : 0 < jointMass π p F g r :=
      (jointMass_pos_iff π p F hπ hp g r).mpr ⟨hπg, hpg, hFg⟩
    unfold predictiveMass
    exact lt_of_lt_of_le hg
      (Finset.single_le_sum (fun h _ => jointMass_nonneg π p F hπ hp h r)
        (Finset.mem_univ g))
  rw [posteriorMass_eq_one_iff π p F orbit hπ hp r (orbit g) hZ]
  intro h _ _ hFh
  exact (hF g h r hFg hFh).symm

end Bridge

section Weakest

variable [Fintype Genome] [Fintype Obs] [Fintype Θ] [DecidableEq Θ]

/-- `E₁` is at least as strong (informative) as `E₂` when it implies it. -/
def Stronger (E₁ E₂ : Genome → Obs → Prop) : Prop := ∀ g r, E₁ g r → E₂ g r

/-- Structural sufficiency of a promise: after conditioning, the supported
fibre at each read is a single orbit class.  This is decidable-free and implies
the posterior-one condition (`sufficient_implies_conditional_certain`). -/
def Sufficient (π : Genome → ℝ) (p : Genome → Obs → ℝ) (orbit : Genome → Θ)
    (E : Genome → Obs → Prop) : Prop :=
  ∀ g r, 0 < π g → 0 < p g r → E g r →
    ∀ h, 0 < π h → 0 < p h r → E h r → orbit h = orbit g

/-- Support-restricted sufficiency, used for finite `decide`-checked
counterexamples: only candidates in the read-support `S` can be confused. -/
def SufficientOn (S : Genome → Obs → Prop) (orbit : Genome → Θ)
    (E : Genome → Obs → Prop) : Prop :=
  ∀ g r, S g r → E g r → ∀ h, S h r → E h r → orbit h = orbit g

theorem sufficientOn_mono {S : Genome → Obs → Prop} {orbit : Genome → Θ}
    {E E' : Genome → Obs → Prop} (hsub : ∀ g r, E' g r → E g r)
    (hE : SufficientOn S orbit E) : SufficientOn S orbit E' := by
  intro g r hSg hE'g h hSh hE'h
  exact hE g r hSg (hsub g r hE'g) h hSh (hsub h r hE'h)

/-- A promise is sufficient (structurally) exactly when conditioning on it gives
posterior one for every positive-probability truth. -/
theorem sufficient_implies_conditional_certain (π : Genome → ℝ)
    (p : Genome → Obs → ℝ) (orbit : Genome → Θ) (E : Genome → Obs → Prop)
    [DecidableRel E] (hπ : ∀ g, 0 ≤ π g) (hp : ∀ g r, 0 ≤ p g r)
    (hS : Sufficient π p orbit E) :
    ∀ g r, 0 < π g → 0 < p g r → E g r →
      posteriorMass π p E orbit r (orbit g) = 1 := by
  intro g r hπg hpg hEg
  have hZ : 0 < predictiveMass π p E r := by
    have hg : 0 < jointMass π p E g r :=
      (jointMass_pos_iff π p E hπ hp g r).mpr ⟨hπg, hpg, hEg⟩
    unfold predictiveMass
    exact lt_of_lt_of_le hg
      (Finset.single_le_sum (fun h _ => jointMass_nonneg π p E hπ hp h r)
        (Finset.mem_univ g))
  rw [posteriorMass_eq_one_iff π p E orbit hπ hp r (orbit g) hZ]
  intro h hπh hph hEh
  exact hS g r hπg hpg hEg h hπh hph hEh

/-- The read-support lies in a single orbit class.  This is the weakest
read-only promise that can certify a read. -/
def Unambiguous (π : Genome → ℝ) (p : Genome → Obs → ℝ) (orbit : Genome → Θ)
    (r : Obs) : Prop :=
  ∀ g h, 0 < π g → 0 < p g r → 0 < π h → 0 < p h r → orbit h = orbit g

theorem unambiguous_sufficient (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) :
    Sufficient π p orbit (fun _ r => Unambiguous π p orbit r) := by
  intro g r hπg hpg hEg h hπh hph _
  exact hEg g h hπg hpg hπh hph

/-- Every sufficient read-only promise implies `Unambiguous`; combined with
`unambiguous_sufficient`, the weakest read-only sufficient promise exists and is
unique up to equivalence.  In contrast, arbitrary truth-dependent promises have
no weakest member (`NoWeakest.no_weakest_sufficient`). -/
theorem unambiguous_weakest_readonly (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) (φ : Obs → Prop)
    (hφ : Sufficient π p orbit (fun _ r => φ r)) :
    ∀ r, φ r → Unambiguous π p orbit r := by
  intro r hφr g h hπg hpg hπh hph
  exact hφ g r hπg hpg hφr h hπh hph hφr

theorem unambiguous_unique_weakest_readonly (π : Genome → ℝ)
    (p : Genome → Obs → ℝ) (orbit : Genome → Θ) (φ : Obs → Prop)
    (hφ : Sufficient π p orbit (fun _ r => φ r)) :
    (∀ r, φ r → Unambiguous π p orbit r) ∧
      Sufficient π p orbit (fun _ r => Unambiguous π p orbit r) :=
  ⟨unambiguous_weakest_readonly π p orbit φ hφ,
    unambiguous_sufficient π p orbit⟩

/-- Support-restricted `Unambiguous`. -/
def UnambiguousOn (S : Genome → Obs → Prop) (orbit : Genome → Θ)
    (r : Obs) : Prop :=
  ∀ g h, S g r → S h r → orbit h = orbit g

theorem unambiguousOn_sufficient (S : Genome → Obs → Prop) (orbit : Genome → Θ) :
    SufficientOn S orbit (fun _ r => UnambiguousOn S orbit r) := by
  intro g r hSg hEg h hSh _
  exact hEg g h hSg hSh

theorem unambiguousOn_weakest (S : Genome → Obs → Prop) (orbit : Genome → Θ)
    (φ : Obs → Prop) (hφ : SufficientOn S orbit (fun _ r => φ r)) :
    ∀ r, φ r → UnambiguousOn S orbit r := by
  intro r hφr g h hSg hSh
  exact hφ g r hSg hφr h hSh hφr

/- Four candidates in two read-confusability pairs (`{0,1}` at read `0`,
`{2,3}` at read `1`) with distinct orbit classes.  Two sufficient promises that
each select one member of each pair are incomparable, and no promise containing
both is sufficient: there is no weakest sufficient truth-dependent promise. -/
namespace NoWeakest

def S : Fin 4 → Fin 2 → Prop :=
  fun g r => (r = 0 ∧ (g = 0 ∨ g = 1)) ∨ (r = 1 ∧ (g = 2 ∨ g = 3))

def orbit : Fin 4 → Fin 4 := id

def E1 : Fin 4 → Fin 2 → Prop := fun g r => (r = 0 ∧ g = 0) ∨ (r = 1 ∧ g = 2)

def E2 : Fin 4 → Fin 2 → Prop := fun g r => (r = 0 ∧ g = 1) ∨ (r = 1 ∧ g = 3)

theorem e1_sufficient : SufficientOn S orbit E1 := by
  intro g r _ hE1g h _ hE1h
  rcases hE1g with ⟨hr, hg⟩ | ⟨hr, hg⟩ <;>
    rcases hE1h with ⟨hr', hh⟩ | ⟨hr', hh⟩
  · simp [orbit, hg, hh]
  · exact absurd (hr.symm.trans hr') (by decide)
  · exact absurd (hr.symm.trans hr') (by decide)
  · simp [orbit, hg, hh]

theorem e2_sufficient : SufficientOn S orbit E2 := by
  intro g r _ hE2g h _ hE2h
  rcases hE2g with ⟨hr, hg⟩ | ⟨hr, hg⟩ <;>
    rcases hE2h with ⟨hr', hh⟩ | ⟨hr', hh⟩
  · simp [orbit, hg, hh]
  · exact absurd (hr.symm.trans hr') (by decide)
  · exact absurd (hr.symm.trans hr') (by decide)
  · simp [orbit, hg, hh]

theorem union_not_sufficient :
    ¬ SufficientOn S orbit (fun g r => E1 g r ∨ E2 g r) := by
  intro h
  have h01 := h 0 0 (by unfold S; decide) (by unfold E1 E2; decide)
    1 (by unfold S; decide) (by unfold E1 E2; decide)
  simp only [orbit, id_eq] at h01
  exact (by decide : (1 : Fin 4) ≠ 0) h01

/-- No sufficient promise contains every sufficient promise, so there is no
weakest (least informative) sufficient truth-dependent promise. -/
theorem no_weakest_sufficient :
    ¬ ∃ E : Fin 4 → Fin 2 → Prop, SufficientOn S orbit E ∧
      ∀ E' : Fin 4 → Fin 2 → Prop, SufficientOn S orbit E' → ∀ g r, E' g r → E g r := by
  rintro ⟨E, hE, hmax⟩
  have h1 : ∀ g r, E1 g r → E g r := hmax E1 e1_sufficient
  have h2 : ∀ g r, E2 g r → E g r := hmax E2 e2_sufficient
  have hunion : SufficientOn S orbit (fun g r => E1 g r ∨ E2 g r) :=
    sufficientOn_mono (fun g r h => h.elim (h1 g r) (h2 g r)) hE
  exact union_not_sufficient hunion

end NoWeakest

end Weakest

section Example

/- Two equally likely candidates, one read; the read alone leaves the posterior
at `1/2`, but the truth-dependent promise `E = (g = 0)` — supplied, not
inferred — makes the posterior one.  This is the smallest instance of "the side
information must actually be supplied". -/
namespace TwoCandidate

def orbit : Fin 2 → Fin 2 := id
noncomputable def π : Fin 2 → ℝ := fun _ => 1 / 2
def p : Fin 2 → Fin 1 → ℝ := fun _ _ => 1
def E : Fin 2 → Fin 1 → Prop := fun g _ => g = 0

instance : DecidableRel E := fun g r => by unfold E; infer_instance

theorem pi_normalized : ∑ g : Fin 2, π g = 1 := by
  rw [Fin.sum_univ_two]
  norm_num [π]

theorem pi_nonneg : ∀ g : Fin 2, 0 ≤ π g := fun g => by norm_num [π]
theorem p_nonneg : ∀ g : Fin 2, ∀ r : Fin 1, 0 ≤ p g r := fun g r => by norm_num [p]

theorem readOnly_not_certain :
    posteriorMass π p (fun _ _ => True) orbit (0 : Fin 1) (orbit 0) ≠ 1 := by
  intro h
  have hZ : 0 < predictiveMass π p (fun _ _ => True) (0 : Fin 1) := by
    have hg : 0 < jointMass π p (fun _ _ => True) 0 0 := by
      rw [jointMass_pos_iff π p (fun _ _ => True) pi_nonneg p_nonneg]
      exact ⟨by norm_num [π], by norm_num [p], trivial⟩
    unfold predictiveMass
    exact lt_of_lt_of_le hg
      (Finset.single_le_sum
        (fun h _ => jointMass_nonneg π p (fun _ _ => True) pi_nonneg p_nonneg h 0)
        (Finset.mem_univ 0))
  have h1 := (readOnly_posterior_eq_one_iff π p orbit pi_nonneg p_nonneg
    (0 : Fin 1) (orbit 0) hZ).mp h (1 : Fin 2) (by norm_num [π]) (by norm_num [p])
  simp only [orbit, id_eq] at h1
  exact (by decide : (1 : Fin 2) ≠ 0) h1

theorem truth_satisfies_promise : E 0 0 := rfl

theorem promise_certain : posteriorMass π p E orbit (0 : Fin 1) (orbit 0) = 1 := by
  have hZ : 0 < predictiveMass π p E (0 : Fin 1) := by
    have hg : 0 < jointMass π p E 0 0 := by
      rw [jointMass_pos_iff π p E pi_nonneg p_nonneg]
      exact ⟨by norm_num [π], by norm_num [p], rfl⟩
    unfold predictiveMass
    exact lt_of_lt_of_le hg
      (Finset.single_le_sum
        (fun h _ => jointMass_nonneg π p E pi_nonneg p_nonneg h 0)
        (Finset.mem_univ 0))
  rw [posteriorMass_eq_one_iff π p E orbit pi_nonneg p_nonneg (0 : Fin 1) (orbit 0) hZ]
  intro h _ _ hEh
  exact congrArg orbit hEh

/-- The read-only posterior is not one, the truth satisfies the promise, and the
promise-conditioned posterior is one. -/
theorem side_information_needed :
    posteriorMass π p (fun _ _ => True) orbit (0 : Fin 1) (orbit 0) ≠ 1 ∧
      posteriorMass π p E orbit (0 : Fin 1) (orbit 0) = 1 ∧ E 0 0 :=
  ⟨readOnly_not_certain, promise_certain, truth_satisfies_promise⟩

end TwoCandidate

/- Two candidates and two reads, fully normalized.  Candidate `0` produces
reads `0` and `1` with probability `1/2` each; candidate `1` produces read `0`
with probability `1` and read `1` with probability `0`.  The truth-dependent
promise `E g r := (g = 0 ∧ r = 0)` and the read-only promise `Unambiguous` are
both sufficient and genuinely incomparable, with witnesses on the *positive*
support:

* `E` holds at the positive pair `(0,0)`, where `Unambiguous(0)` fails because
  read `0` supports both candidates; so `E` does not imply `Unambiguous`.
* `Unambiguous` holds at read `1` (only candidate `0` has positive likelihood),
  while `E 0 1` fails; so `Unambiguous` does not imply `E`.

Sufficiency alone therefore imposes no ordering between promises, and in
particular does not order them against the source `I_s` predicate. -/
namespace Incomparable

def orbit : Fin 2 → Fin 2 := id
noncomputable def π : Fin 2 → ℝ := fun _ => 1 / 2
noncomputable def p : Fin 2 → Fin 2 → ℝ :=
  fun g r => if g = 0 then (1 / 2 : ℝ) else if r = 0 then 1 else 0
def E : Fin 2 → Fin 2 → Prop := fun g r => g = 0 ∧ r = 0

instance : DecidableRel E := fun g r => by unfold E; infer_instance

theorem pi_normalized : ∑ g : Fin 2, π g = 1 := by
  rw [Fin.sum_univ_two]; norm_num [π]

theorem p_normalized : ∀ g : Fin 2, ∑ r : Fin 2, p g r = 1 := by
  intro g
  fin_cases g <;> norm_num [p, Fin.sum_univ_two]

theorem pi_pos : ∀ g : Fin 2, 0 < π g := fun g => by norm_num [π]

theorem p_nonneg : ∀ g : Fin 2, ∀ r : Fin 2, 0 ≤ p g r := by
  intro g r
  unfold p
  by_cases hg : g = 0
  · simp [hg]
  · by_cases hr : r = 0 <;> simp [hg, hr]

theorem sufficient_E : Sufficient π p orbit E := by
  intro g r _ _ hEg h _ _ hEh
  have hg : g = 0 := hEg.1
  have hh : h = 0 := hEh.1
  exact congrArg orbit (hh.trans hg.symm)

theorem sufficient_unambiguous :
    Sufficient π p orbit (fun _ r => Unambiguous π p orbit r) :=
  unambiguous_sufficient π p orbit

/-- `E` holds at the positive pair `(0,0)` while `Unambiguous(0)` fails, so `E`
does not imply `Unambiguous`. -/
theorem E_not_imp_unambiguous :
    ¬ (∀ g r, E g r → Unambiguous π p orbit r) := by
  intro h
  have hu : Unambiguous π p orbit 0 := h 0 0 ⟨rfl, rfl⟩
  have h10 := hu 0 1 (by norm_num [π]) (by norm_num [p]) (by norm_num [π]) (by norm_num [p])
  simp only [orbit, id_eq] at h10
  exact (by decide : (1 : Fin 2) ≠ 0) h10

/-- `Unambiguous` holds at read `1` while `E 0 1` fails at the positive pair
`(0,1)`, so `Unambiguous` does not imply `E`. -/
theorem unambiguous_not_imp_E :
    ¬ (∀ g r, Unambiguous π p orbit r → E g r) := by
  intro h
  have hu1 : Unambiguous π p orbit 1 := by
    intro g h' hπg hpg hπh hph
    have hg0 : g = 0 := by
      by_contra hg
      have hpz : ¬ 0 < p g 1 := by simp [p, hg]
      exact hpz hpg
    have hh0 : h' = 0 := by
      by_contra hh
      have hpz : ¬ 0 < p h' 1 := by simp [p, hh]
      exact hpz hph
    exact congrArg orbit (hh0.trans hg0.symm)
  have hE : E 0 1 := h 0 1 hu1
  exact (by decide : (1 : Fin 2) ≠ 0) hE.2

/-- Two normalized, positive-support sufficient promises that are incomparable:
sufficiency does not order promises, so no claim that `I_s`, `Unambiguous`, or an
arbitrary sufficient `F` is weaker or stronger than another follows from
sufficiency alone. -/
theorem sufficient_promises_incomparable :
    (∑ g : Fin 2, π g = 1) ∧
      (∀ g : Fin 2, ∑ r : Fin 2, p g r = 1) ∧
      Sufficient π p orbit E ∧
      Sufficient π p orbit (fun _ r => Unambiguous π p orbit r) ∧
      ¬ (∀ g r, E g r → Unambiguous π p orbit r) ∧
      ¬ (∀ g r, Unambiguous π p orbit r → E g r) :=
  ⟨pi_normalized, p_normalized, sufficient_E, sufficient_unambiguous,
    E_not_imp_unambiguous, unambiguous_not_imp_E⟩

end Incomparable

end Example

end AssemblyP1.FiniteBayesianSideInformation
