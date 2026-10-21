import Mathlib
import AssemblyP1.FiniteSideInformationOrder
import AssemblyP1.FiniteSideInformationSourcePromise
import AssemblyP1.FiniteSourceDefinedWeakest
import AssemblyP1.FiniteReadOnlyDecoderCertainty

/-!
# Minimum and minimal sufficient promises in the source-defined family (#272, target 4)

This module discharges the *minimum / minimal* half of the "weakest conditioning"
question of issue #272, complementing the weakest-member results already proved
for the source-defined family in `AssemblyP1.FiniteSourceDefinedWeakest`.

The issue asks to *distinguish a minimal sufficient promise from a minimum* and to
avoid claiming an intrinsic least event without establishing it.  The precise
answer proved here, under the fixed structural family `AdmSourceDefined`
(promises built only from the observed read or only from the truth), is:

| notion | status in the source-defined family | certificate |
|---|---|---|
| minimum sufficient promise | **always exists**, is the **vacuous empty promise** | `fun _ _ => False` |
| weakest sufficient promise | exists **iff** `∀ r, Unambiguous` (merged, PR #371) | `True` when it exists |
| non-vacuous sufficient promise | exactly the **candidate designations** `g = g₀` | truth-only singletons |

The key correction the issue warns about: the empty promise is *always*
sufficient (vacuously, `sufficient_false`), so the "minimum additional
information" is trivially *nothing*.  That corner case is genuine and is recorded
explicitly (`minimum_vacuous`).  The meaningful certificates are the
*non-vacuous* sufficient promises, and within the source-defined family those are
exactly the candidate designations.  On an ambiguous model there are two or more
incomparable designations, so no single weakest (least informative) certificate
exists — you must be *told a candidate*, and there is no canonical choice.

## Results

* `minimum_vacuous` — the minimum sufficient promise is always the vacuous empty
  promise; the "minimum additional information" is genuinely vacuous.
* `sufficient_iff_not_both` — on the ambiguous `TwoCandidate` model a promise is
  sufficient iff it does not admit both candidates.
* `nonvacuous_sufficient_is_designation` — every non-vacuous sufficient promise
  is a candidate designation.
* `designation_nonvacuous_sufficient` — every candidate designation is
  non-vacuous and sufficient.
* `designations_incomparable` — the two designations are incomparable, so the
  source-defined family has no weakest member.
* `three_way_distinction` — the packaged bundle: a minimum exists, the
  non-vacuous sufficient certificates are the designations, and no weakest
  exists.

Nothing here asserts the external Shomorony et al. Not-So-Greedy theorem, and
nothing here decides subclaims (a) and (c).  No `axiom`, `sorry`, or `admit` is
introduced.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AssemblyP1.FiniteSourceDefinedMinimal

open AssemblyP1.FiniteBayesianSideInformation
open AssemblyP1.FiniteSideInformationOrder
open AssemblyP1.FiniteSideInformationSourcePromise
open AssemblyP1.FiniteSourceDefinedWeakest
open AssemblyP1.FiniteReadOnlyDecoderCertainty

universe u v w

variable {Genome : Type u} {Obs : Type v} {Θ : Type w}
variable [Fintype Genome] [Fintype Obs] [Fintype Θ] [DecidableEq Θ]

/-- A promise is **non-vacuous** when it holds of at least one (candidate, read)
pair.  The empty promise is the unique vacuous sufficient promise. -/
def Nonvacuous (E : Genome → Obs → Prop) : Prop := ∃ g r, E g r

/-- **The minimum additional information is vacuous.**  The minimum sufficient
promise is always the empty promise (it is sufficient vacuously), and the empty
promise is not non-vacuous.  Hence "the least additional information that
certifies recovery" is genuinely *nothing* — a corner case that must not be
confused with a meaningful certificate. -/
theorem minimum_vacuous (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) :
    IsMinimumSufficient π p orbit (fun (_ : Genome) (_ : Obs) => False) ∧
      ¬ Nonvacuous (fun (_ : Genome) (_ : Obs) => False) :=
  ⟨empty_isMinimumSufficient π p orbit, fun ⟨_, _, h⟩ => h.elim⟩

/-! ## The ambiguous two-candidate model: designations are the only certificates

On the merged `TwoCandidate` model (two candidates, one read, both realizable,
distinct orbits) a promise is sufficient iff it does not admit both candidates.
Consequently the non-vacuous sufficient promises are exactly the two candidate
designations, which are incomparable: there is no single weakest certificate. -/

namespace TwoCandidate

open AssemblyP1.FiniteBayesianSideInformation.TwoCandidate

/-- A promise is sufficient iff it does not admit both candidates at the read. -/
theorem sufficient_iff_not_both (E : Fin 2 → Fin 1 → Prop) :
    Sufficient π p orbit E ↔ ¬(E 0 0 ∧ E 1 0) := by
  constructor
  · intro hS hBoth
    have h0 := hS 0 0 (by norm_num [π]) (by norm_num [p]) hBoth.1 1
      (by norm_num [π]) (by norm_num [p]) hBoth.2
    simp only [orbit, id_eq] at h0
    exact (by decide : (1 : Fin 2) ≠ 0) h0
  · intro hNotBoth g r _ _ hg h _ _ hh
    fin_cases r
    fin_cases g
    · fin_cases h
      · rfl
      · exfalso
        exact hNotBoth ⟨hg, hh⟩
    · fin_cases h
      · exfalso
        exact hNotBoth ⟨hh, hg⟩
      · rfl

/-- **Every non-vacuous sufficient promise is a candidate designation.** -/
theorem nonvacuous_sufficient_is_designation (E : Fin 2 → Fin 1 → Prop)
    (hS : Sufficient π p orbit E) (hnv : Nonvacuous E) :
    ((∀ g r, E g r ↔ g = 0) ∨ (∀ g r, E g r ↔ g = 1)) := by
  obtain ⟨g, r, hgr⟩ := hnv
  fin_cases g
  · fin_cases r
    left
    intro g' r'
    fin_cases g'
    · fin_cases r'
      constructor
      · intro _
        exact rfl
      · intro _
        exact hgr
    · fin_cases r'
      constructor
      · intro hg'
        exfalso
        have hh := hS 0 0 (by norm_num [π]) (by norm_num [p]) hgr 1
          (by norm_num [π]) (by norm_num [p]) hg'
        simp only [orbit, id_eq] at hh
        exact (by decide : (1 : Fin 2) ≠ 0) hh
      · intro h
        exact absurd h (by decide : (1 : Fin 2) ≠ 0)
  · fin_cases r
    right
    intro g' r'
    fin_cases g'
    · fin_cases r'
      constructor
      · intro hg'
        exfalso
        have hh := hS 1 0 (by norm_num [π]) (by norm_num [p]) hgr 0
          (by norm_num [π]) (by norm_num [p]) hg'
        simp only [orbit, id_eq] at hh
        exact (by decide : (0 : Fin 2) ≠ 1) hh
      · intro h
        exact absurd h (by decide : (0 : Fin 2) ≠ 1)
    · fin_cases r'
      constructor
      · intro _
        exact rfl
      · intro _
        exact hgr

/-- **Every candidate designation is non-vacuous and sufficient.** -/
theorem designation_nonvacuous_sufficient (g₀ : Fin 2) :
    Sufficient π p orbit (fun (g : Fin 2) (_ : Fin 1) => g = g₀) ∧
      Nonvacuous (fun (g : Fin 2) (_ : Fin 1) => g = g₀) :=
  ⟨singleton_sufficient π p orbit g₀, ⟨g₀, (0 : Fin 1), rfl⟩⟩

/-- The two candidate designations are **incomparable**: neither implies the
other.  Hence there is no weakest (least informative) sufficient certificate —
you must be told a candidate, and there is no canonical choice. -/
theorem designations_incomparable :
    ¬ Stronger (fun (g : Fin 2) (_ : Fin 1) => g = 0)
                (fun (g : Fin 2) (_ : Fin 1) => g = 1) ∧
      ¬ Stronger (fun (g : Fin 2) (_ : Fin 1) => g = 1)
                (fun (g : Fin 2) (_ : Fin 1) => g = 0) := by
  refine ⟨?_, ?_⟩
  · intro h
    exact (by decide : (0 : Fin 2) ≠ 1) (h 0 0 rfl)
  · intro h
    exact (by decide : (1 : Fin 2) ≠ 0) (h 1 1 rfl)

/-- **Three-way distinction** on the ambiguous model.  A minimum sufficient
promise exists (the vacuous empty promise); every non-vacuous sufficient promise
is a candidate designation; and the source-defined family has no weakest member.
This distinguishes a minimum from a minimal (irreducible) certificate and from
a weakest. -/
theorem three_way_distinction :
    (∃ W, IsMinimumSufficient π p orbit W) ∧
      (∀ (E : Fin 2 → Fin 1 → Prop), Sufficient π p orbit E → Nonvacuous E →
        ((∀ g r, E g r ↔ g = 0) ∨ (∀ g r, E g r ↔ g = 1))) ∧
      ¬ ∃ W, IsWeakestAdmissible AdmSourceDefined π p orbit W :=
  ⟨⟨_, empty_isMinimumSufficient π p orbit⟩,
    fun E hS hnv => nonvacuous_sufficient_is_designation E hS hnv,
    AssemblyP1.FiniteSourceDefinedWeakest.AmbiguousRead.no_weakest⟩

end TwoCandidate

end AssemblyP1.FiniteSourceDefinedMinimal
