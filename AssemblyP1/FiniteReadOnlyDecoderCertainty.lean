import Mathlib
import AssemblyP1.FiniteBayesianSideInformation
import AssemblyP1.FiniteSideInformationOrder
import AssemblyP1.FiniteSideInformationOrdering

/-!
# Read-only decoder certainty for finite Bayesian orbit recovery (#272, target 3)

This module answers **target 3** of issue #272:

> Characterize certainty achievable by any read-only decoder without extra
> information, versus certainty given a known external truth-dependent promise
> `E`.  Explicitly formalize "the side information must actually be supplied";
> never infer `E` merely because it happens to hold.

It reuses the exact posterior semantics `π(g)·p_g(r)·1_E(g,r)` of
`AssemblyP1.FiniteBayesianSideInformation` and the promise-order machinery of
`AssemblyP1.FiniteSideInformationOrder` / `AssemblyP1.FiniteSideInformationOrdering`
unchanged; it does **not** re-derive the posterior-iff theorem and does **not**
assert the external Shomorony--Kim--Courtade--Tse Not-So-Greedy theorem.

## 1. Certainty achievable by a read-only decoder

A **read-only decoder** is a function `A : Obs → Genome` that guesses the truth
from the observed read alone.  Fixing the trivial promise `E ≡ True`, its
conditional success on the orbit class of its guess at read `r` is
`posteriorMass π p (fun _ _ => True) orbit r (orbit (A r))`.

* `readOnly_decoder_certain_implies_unambiguous` — the "only when" half: if some
  read-only decoder reaches posterior one at `r`, then the supported truth-fibre
  of `r` already lies in a single orbit class (`Unambiguous`).
* `exists_readOnly_decoder_certain_iff_support_singleton` — the exact
  characterization: **some** read-only decoder reaches posterior one at `r`
  **iff** the supported truth-fibre of `r` is nonempty and lies in a single
  orbit class.  In other words, a read-only decoder can be certain exactly at the
  reads where no side information is needed, and nowhere else.
* `readOnly_certain_set_eq_weakest` — the same statement together with the merged
  order result `unambiguous_isWeakest_readonly`: the set of reads at which *any*
  read-only decoder can be certain is exactly the weakest admissible sufficient
  read-only promise `Unambiguous`.

## 2. "The side information must actually be supplied"

* `admReadOnly_iff_factorable` — a promise can be inferred from the observed read
  alone **iff** it factors through `r` (`∃ φ, E g r ↔ φ r`), i.e. iff it is
  read-only.  This makes "inferable from `R`" a theorem rather than an
  assumption.
* `truthDependent_not_factorable` — consequently a truth-dependent promise
  (`¬ AdmReadOnly E`) is not a function of the observation and must be supplied
  as an extra input.  Nothing here infers `E` from `R`.
* `TwoCandidateDecoder` instantiates this on the merged two-candidate model: no
  read-only decoder is certain at the ambiguous read, while the supplied
  truth-dependent promise `E = (g = 0)` yields posterior one.

## 3. Minimum versus weakest sufficient promise (target 4, bounded)

* `IsMinimumSufficient` / `empty_isMinimumSufficient` / `minimum_exists_unique` —
  the *minimum* (strongest, most informative) sufficient promise always exists
  and is unique up to logical equivalence; it is the empty promise, which carries
  no information.
* `weakest_isMaximal` — a *weakest* (maximum) sufficient promise, when it exists,
  is maximal.
* `minimum_without_weakest` — on the merged `NoWeakestProb` model a minimum
  exists but no weakest does, so the trivial minimum must not be confused with a
  genuine weakest (least informative) promise.

No `axiom`, `sorry`, or `admit` is introduced; the axiom audit is
`AssemblyP1/FiniteReadOnlyDecoderCertaintyAudit.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AssemblyP1.FiniteReadOnlyDecoderCertainty

open AssemblyP1.FiniteBayesianSideInformation
open AssemblyP1.FiniteSideInformationOrder

universe u v w

variable {Genome : Type u} {Obs : Type v} {Θ : Type w}
variable [Fintype Genome] [Fintype Obs] [Fintype Θ] [DecidableEq Θ]

/-! ## 1. Certainty achievable by a read-only decoder -/

/-- The read-only predictive mass at read `r`: the merged `predictiveMass` with
the trivial promise `E ≡ True`.  It is positive exactly when `r` has a
positive-prior, positive-likelihood candidate. -/
theorem readOnly_predictive_pos_iff (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (hπ : ∀ g, 0 ≤ π g) (hp : ∀ g r, 0 ≤ p g r) (r : Obs) :
    0 < predictiveMass π p (fun _ _ => True) r ↔
      ∃ g, 0 < π g ∧ 0 < p g r := by
  unfold predictiveMass
  rw [Finset.sum_pos_iff_of_nonneg
    (fun g _ => jointMass_nonneg π p (fun _ _ => True) hπ hp g r)]
  constructor
  · rintro ⟨g, _, hg⟩
    obtain ⟨hπg, hpg, _⟩ := (jointMass_pos_iff π p (fun _ _ => True) hπ hp g r).mp hg
    exact ⟨g, hπg, hpg⟩
  · rintro ⟨g, hπg, hpg⟩
    exact ⟨g, Finset.mem_univ g,
      (jointMass_pos_iff π p (fun _ _ => True) hπ hp g r).mpr ⟨hπg, hpg, trivial⟩⟩

/-- **The "only when" half of the read-only decoder characterization.**  If a
read-only decoder `A` reaches posterior one on its guessed orbit class at read
`r`, then the supported truth-fibre of `r` already lies in a single orbit class:
the read support is `Unambiguous`.  No read-only decoder can manufacture
certainty that the read alone does not already provide. -/
theorem readOnly_decoder_certain_implies_unambiguous (π : Genome → ℝ)
    (p : Genome → Obs → ℝ) (orbit : Genome → Θ) (hπ : ∀ g, 0 ≤ π g)
    (hp : ∀ g r, 0 ≤ p g r) (A : Obs → Genome) (r : Obs)
    (h : posteriorMass π p (fun _ _ => True) orbit r (orbit (A r)) = 1) :
    Unambiguous π p orbit r := by
  have hpred : predictiveMass π p (fun _ _ => True) r ≠ 0 := by
    intro hz0
    unfold posteriorMass at h
    rw [hz0, div_zero] at h
    exact one_ne_zero h.symm
  have hZ : 0 < predictiveMass π p (fun _ _ => True) r :=
    lt_of_le_of_ne (predictiveMass_nonneg π p (fun _ _ => True) hπ hp r) (Ne.symm hpred)
  have hall :=
    (readOnly_posterior_eq_one_iff π p orbit hπ hp r (orbit (A r)) hZ).mp h
  intro g h' hπg hpg hπh hph
  exact (hall h' hπh hph).trans (hall g hπg hpg).symm

/-- **Exact read-only decoder certainty characterization (target 3).**  Some
read-only decoder reaches posterior one at read `r` **iff** the supported
truth-fibre of `r` is nonempty and lies in a single orbit class.  The nonempty
conjunct is exactly the positive-predictive-mass hypothesis; together with
`Unambiguous` it says the supported truth-fibre is one orbit class. -/
theorem exists_readOnly_decoder_certain_iff_support_singleton (π : Genome → ℝ)
    (p : Genome → Obs → ℝ) (orbit : Genome → Θ) (hπ : ∀ g, 0 ≤ π g)
    (hp : ∀ g r, 0 ≤ p g r) (r : Obs) :
    (∃ A : Obs → Genome,
        posteriorMass π p (fun _ _ => True) orbit r (orbit (A r)) = 1) ↔
      Unambiguous π p orbit r ∧ ∃ g, 0 < π g ∧ 0 < p g r := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨readOnly_decoder_certain_implies_unambiguous π p orbit hπ hp A r hA, ?_⟩
    have hpred : predictiveMass π p (fun _ _ => True) r ≠ 0 := by
      intro hz0
      unfold posteriorMass at hA
      rw [hz0, div_zero] at hA
      exact one_ne_zero hA.symm
    have hZ : 0 < predictiveMass π p (fun _ _ => True) r :=
      lt_of_le_of_ne (predictiveMass_nonneg π p (fun _ _ => True) hπ hp r) (Ne.symm hpred)
    exact (readOnly_predictive_pos_iff π p hπ hp r).mp hZ
  · rintro ⟨hu, g₀, hπg₀, hpg₀⟩
    refine ⟨fun _ => g₀, ?_⟩
    have hZ : 0 < predictiveMass π p (fun _ _ => True) r :=
      (readOnly_predictive_pos_iff π p hπ hp r).mpr ⟨g₀, hπg₀, hpg₀⟩
    rw [readOnly_posterior_eq_one_iff π p orbit hπ hp r (orbit g₀) hZ]
    intro h' hπh' hph'
    exact hu g₀ h' hπg₀ hpg₀ hπh' hph'

/-- **The read-only certainty boundary is the weakest read-only promise.**  The
set of reads at which *some* read-only decoder can be certain is exactly
`Unambiguous`, which the merged order result `unambiguous_isWeakest_readonly`
identifies as the unique weakest admissible sufficient read-only promise.  So the
maximum certainty a read-only decoder can achieve is precisely the weakest
read-only sufficient side information; nothing weaker suffices and nothing
stronger is needed. -/
theorem readOnly_certain_set_eq_weakest (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) (hπ : ∀ g, 0 ≤ π g) (hp : ∀ g r, 0 ≤ p g r) :
    (∀ r, (∃ A : Obs → Genome,
          posteriorMass π p (fun _ _ => True) orbit r (orbit (A r)) = 1) ↔
        (Unambiguous π p orbit r ∧ ∃ g, 0 < π g ∧ 0 < p g r)) ∧
      IsWeakestAdmissible AdmReadOnly π p orbit (fun _ r => Unambiguous π p orbit r) :=
  ⟨fun r => exists_readOnly_decoder_certain_iff_support_singleton π p orbit hπ hp r,
    unambiguous_isWeakest_readonly π p orbit⟩

/-! ## 2. The side information must actually be supplied -/

/-- A promise **factors through the observation** when it can be evaluated from
the observed read alone. -/
def ReadOnlyFactorable (E : Genome → Obs → Prop) : Prop :=
  ∃ φ : Obs → Prop, ∀ g r, E g r ↔ φ r

/-- **Inferable from the read iff read-only.**  A promise is a function of the
observed read `r` alone exactly when it is read-only (`AdmReadOnly`).  This turns
"`E` can be inferred from `R`" into a theorem about factorization. -/
theorem admReadOnly_iff_factorable (E : Genome → Obs → Prop) :
    AdmReadOnly E ↔ ReadOnlyFactorable E := by
  constructor
  · intro hE
    exact ⟨fun r => ∃ g, E g r,
      fun g r => ⟨fun h => ⟨g, h⟩, fun ⟨g', hg'⟩ => (hE g g' r).mpr hg'⟩⟩
  · rintro ⟨φ, hφ⟩ g g' r
    rw [hφ g r, hφ g' r]

/-- **A truth-dependent promise must be supplied.**  If `E` is not read-only then
it does not factor through the observation, so no decoder that sees only `R = r`
can evaluate it; `E` is genuine extra information rather than something inferred
from the reads. -/
theorem truthDependent_not_factorable (E : Genome → Obs → Prop)
    (h : ¬ AdmReadOnly E) : ¬ ReadOnlyFactorable E :=
  fun hf => h ((admReadOnly_iff_factorable E).mpr hf)

/-- On the merged two-candidate model the supplied promise `E = (g = 0)` is
truth-dependent: it is not read-only. -/
theorem twoCandidate_E_not_admReadOnly :
    ¬ AdmReadOnly TwoCandidate.E := by
  intro h
  have h10 : TwoCandidate.E 1 0 := (h 0 1 0).mp rfl
  exact (by decide : (1 : Fin 2) ≠ 0) h10

/-! ## 3. Concrete instance: no read-only decoder is certain, the supplied
promise is -/

namespace TwoCandidateDecoder

open AssemblyP1.FiniteBayesianSideInformation.TwoCandidate

/-- In the merged `TwoCandidate` model the read at `0` is genuinely ambiguous, so
**no** read-only decoder is certain there: the read support contains both
candidate `0` and candidate `1`, which lie in different orbit classes. -/
theorem no_readOnly_decoder_certain :
    ¬ ∃ A : Fin 1 → Fin 2,
        posteriorMass π p (fun _ _ => True) orbit (0 : Fin 1) (orbit (A 0)) = 1 := by
  rintro ⟨A, hA⟩
  have hu := readOnly_decoder_certain_implies_unambiguous π p orbit
    pi_nonneg p_nonneg A (0 : Fin 1) hA
  have h10 := hu 0 1 (by norm_num [π]) (by norm_num [p])
    (by norm_num [π]) (by norm_num [p])
  simp only [orbit, id_eq] at h10
  exact (by decide : (1 : Fin 2) ≠ 0) h10

/-- **The side information must actually be supplied (concrete).**  On the merged
`TwoCandidate` model no read-only decoder is certain at the ambiguous read, yet
the *supplied* truth-dependent promise `E = (g = 0)` — which is not read-only
(`twoCandidate_E_not_admReadOnly`) — makes the posterior one. -/
theorem side_information_must_be_supplied :
    (¬ ∃ A : Fin 1 → Fin 2,
        posteriorMass π p (fun _ _ => True) orbit (0 : Fin 1) (orbit (A 0)) = 1) ∧
      posteriorMass π p E orbit (0 : Fin 1) (orbit 0) = 1 ∧ E 0 0 :=
  ⟨no_readOnly_decoder_certain, promise_certain, truth_satisfies_promise⟩

end TwoCandidateDecoder

/-! ## 4. Minimum versus weakest sufficient promise (target 4, bounded) -/

/-- A **minimum** sufficient promise: sufficient and stronger (more informative)
than every sufficient promise.  This is the least informative in the "weaker"
direction; the empty promise is the canonical one. -/
def IsMinimumSufficient (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) (W : Genome → Obs → Prop) : Prop :=
  Sufficient π p orbit W ∧ ∀ E, Sufficient π p orbit E → Stronger W E

/-- A **maximal** sufficient promise: sufficient, and no sufficient promise is
strictly weaker (a strictly larger event). -/
def IsMaximalSufficient (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) (W : Genome → Obs → Prop) : Prop :=
  Sufficient π p orbit W ∧
    ∀ E, Sufficient π p orbit E → Stronger W E → Stronger E W

/-- The empty promise is a minimum sufficient promise: it is sufficient
vacuously and implies everything. -/
theorem empty_isMinimumSufficient (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) : IsMinimumSufficient π p orbit (fun _ _ => False) :=
  ⟨sufficient_false π p orbit, fun _ _ _ _ h => h.elim⟩

/-- The minimum sufficient promise is unique up to logical equivalence. -/
theorem minimum_unique (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) {W₁ W₂ : Genome → Obs → Prop}
    (h₁ : IsMinimumSufficient π p orbit W₁) (h₂ : IsMinimumSufficient π p orbit W₂) :
    ∀ g r, W₁ g r ↔ W₂ g r :=
  stronger_antisymm (h₁.2 W₂ h₂.1) (h₂.2 W₁ h₁.1)

/-- A minimum sufficient promise exists for every model, and is unique up to
logical equivalence. -/
theorem minimum_exists_unique (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) :
    (∃ W, IsMinimumSufficient π p orbit W) ∧
      ∀ W₁ W₂, IsMinimumSufficient π p orbit W₁ →
        IsMinimumSufficient π p orbit W₂ → ∀ g r, W₁ g r ↔ W₂ g r :=
  ⟨⟨_, empty_isMinimumSufficient π p orbit⟩,
    fun _ _ h₁ h₂ => minimum_unique π p orbit h₁ h₂⟩

/-- A weakest (maximum) sufficient promise, when it exists, is maximal. -/
theorem weakest_isMaximal (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) {W : Genome → Obs → Prop}
    (hW : IsWeakestSufficient π p orbit W) : IsMaximalSufficient π p orbit W :=
  ⟨hW.1, fun E hE _ => hW.2 E hE⟩

/-- **Minimum without weakest.**  On the merged `NoWeakestProb` model a minimum
sufficient promise exists (the trivial empty promise) but **no** weakest
(least informative) sufficient promise does.  The trivial minimum must therefore
not be confused with a genuine weakest sufficient promise. -/
theorem minimum_without_weakest :
    (∃ W : Fin 4 → Fin 2 → Prop,
        IsMinimumSufficient NoWeakestProb.π NoWeakestProb.p NoWeakestProb.orbit W) ∧
      ¬ ∃ W : Fin 4 → Fin 2 → Prop,
          IsWeakestSufficient NoWeakestProb.π NoWeakestProb.p NoWeakestProb.orbit W :=
  ⟨⟨_, empty_isMinimumSufficient NoWeakestProb.π NoWeakestProb.p NoWeakestProb.orbit⟩,
    NoWeakestProb.no_weakest_sufficient⟩

end AssemblyP1.FiniteReadOnlyDecoderCertainty
