import Mathlib
import AssemblyP1.FiniteSideInformationOrder
import AssemblyP1.FiniteSamplingCounterexample

/-!
# The ordering of the source predicate `I_s` against `Unambiguous` (#272)

This module answers the ordering question left OPEN by the merged modules
`AssemblyP1.FiniteBayesianSideInformation` (PR #195, `b0a6e9f`) and
`AssemblyP1.FiniteSideInformationOrder` (PR #204, `c312cbbc`):

> Is the source-faithful information-feasibility predicate `I_s` of
> Shomorony--Kim--Courtade--Tse (2016) ordered against the read-only promise
> `Unambiguous`: does `I_s ⇒ Unambiguous`, does `Unambiguous ⇒ I_s`, or
> neither?

The answer proved here is: **neither**, and the reason is structural rather than
a matter of a missing lemma.  `Unambiguous` is a *read-only* promise: it depends
only on the observed read, not on the unknown truth.  `InformationFeasible`
(`I_s`) is a *truth-dependent* promise: its coverage and bridging clauses are
predicates of the candidate genome.  The two therefore live in different
promise families, and the read-only boundary theorem
(`sufficient_readonly_iff_imp_unambiguous`, proved here) does not apply to `I_s`.

Concretely, this module proves:

1. **Read-only boundary (new, general).**  A read-only promise `φ` is sufficient
   **iff** it implies `Unambiguous`:
   `Sufficient (fun _ r => φ r) ↔ ∀ r, φ r → Unambiguous r`.  Equivalently, any
   promise whatsoever that implies `Unambiguous` is sufficient
   (`sufficient_of_imp_unambiguous`).  So `Unambiguous` is the exact sufficient
   *lower boundary* of the read-only family.
2. **Truth-dependence defeats the boundary (new, general).**  The singleton
   truth-dependent promise `fun g _ => g = g₀` is always sufficient
   (`singleton_promise_sufficient`), but in any model with a genuinely ambiguous
   read it does not imply `Unambiguous`
   (`singleton_promise_not_imp_unambiguous`), and in any model with a
   non-`g₀` positive candidate at some unambiguous read it is not implied by
   `Unambiguous` (`unambiguous_not_imp_singleton`).  The combined
   `truthdependent_sufficient_incomparable` states both failures at once, and
   `ThreeCandidate.neither_implication` instantiates it on a concrete finite
   model distinct from the merged `Incomparable`/`NoWeakest` witnesses.
3. **The source predicate is truth-dependent (new, concrete).**  The literal
   `SourceFaithfulIs.InformationFeasible` is **not** a read-only promise:
   `informationFeasible_not_readOnly` exhibits two length-`5` spellings
   (`AABBC`, which is `I_s`-feasible at `L = 3`, `R = {0,3}`, and `AAAAB`, which
   is not) with the *same* read-start set, so `I_s` genuinely depends on the
   candidate.  Hence `I_s` is outside the read-only family to which the boundary
   theorem and the merged read-only weakest-promise theorem apply.

Nothing here asserts the external Shomorony et al. Not-So-Greedy theorem; the
external decoder guarantee remains an attributed premise (see
`AssemblyP1.FiniteBayesianSideInformation.fibreUnique_of_decoder` and
`AssemblyP1.ConditionalIdentifiability`).  No `axiom`, `sorry`, or `admit` is
introduced.  The literal source-faithful *read-string* adapter that would make
the ordering a well-typed question about a single observation type is still
OPEN and is recorded in `docs/issue272-is-vs-unambiguous-ordering.md`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AssemblyP1.FiniteSideInformationOrdering

open AssemblyP1.FiniteBayesianSideInformation

universe u v w

variable {Genome : Type u} {Obs : Type v} {Θ : Type w}

section General

variable [Fintype Genome] [Fintype Obs] [Fintype Θ] [DecidableEq Θ]

/-- **The read-only lower boundary is sufficient.**  Any promise at all that
implies the read-only `Unambiguous` is sufficient: conditioning on a promise
stronger than `Unambiguous` can only shrink the supported fibre further.  This is
`sufficient_of_stronger` applied to the merged `unambiguous_sufficient`. -/
theorem sufficient_of_imp_unambiguous (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) {E : Genome → Obs → Prop}
    (himp : ∀ g r, E g r → Unambiguous π p orbit r) :
    Sufficient π p orbit E := by
  intro g r hπg hpg hEg h hπh hph hEh
  exact himp g r hEg g h hπg hpg hπh hph

/-- **Exact characterization for read-only promises.**  A promise that depends
only on the observed read is sufficient **iff** it implies `Unambiguous`.  This
is the precise sense in which `Unambiguous` is the boundary of read-only
sufficiency: no read-only promise can be sufficient while failing to imply it,
and every read-only promise that implies it is sufficient. -/
theorem sufficient_readonly_iff_imp_unambiguous (π : Genome → ℝ)
    (p : Genome → Obs → ℝ) (orbit : Genome → Θ) (φ : Obs → Prop) :
    Sufficient π p orbit (fun _ r => φ r) ↔
      ∀ r, φ r → Unambiguous π p orbit r := by
  constructor
  · intro hS r hφ g h hπg hpg hπh hph
    exact hS g r hπg hpg hφ h hπh hph hφ
  · intro h
    exact sufficient_of_imp_unambiguous π p orbit (fun _ r hφ => h r hφ)

/-- The read-only promise `Unambiguous` itself is read-only. -/
theorem unambiguous_promise_readOnly (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) :
    AssemblyP1.FiniteSideInformationOrder.AdmReadOnly
      (fun (_ : Genome) r => Unambiguous π p orbit r) :=
  fun _ _ _ => Iff.rfl

/-- **The singleton truth-dependent promise is sufficient.**  `fun g _ => g = g₀`
has a fibre of at most one candidate at every read, hence its positive joint-mass
fibre always lies in a single orbit. -/
theorem singleton_promise_sufficient (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) (g₀ : Genome) :
    Sufficient π p orbit (fun g _ => g = g₀) := by
  intro g r _ _ hg h _ _ hh
  exact (congrArg orbit (hg.trans hh.symm)).symm

/-- **Sufficiency does not force a truth-dependent promise to imply
`Unambiguous`.**  If some read `r` is genuinely ambiguous and `g₀` is possible at
`r`, then the sufficient singleton promise `g = g₀` is *not* below
`Unambiguous`: `Unambiguous r` fails even though `g₀ = g₀` holds. -/
theorem singleton_promise_not_imp_unambiguous (π : Genome → ℝ)
    (p : Genome → Obs → ℝ) (orbit : Genome → Θ) (g₀ : Genome) (r : Obs)
    (hπ₀ : 0 < π g₀) (hp₀ : 0 < p g₀ r)
    (hbad : ∃ h, 0 < π h ∧ 0 < p h r ∧ orbit h ≠ orbit g₀) :
    ¬ (∀ g r, (g = g₀) → Unambiguous π p orbit r) := by
  rintro H
  obtain ⟨h, hπh, hph, hne⟩ := hbad
  exact hne (H g₀ r rfl g₀ h hπ₀ hp₀ hπh hph)

/-- **`Unambiguous` does not force a truth-dependent promise either.**  If
`Unambiguous r` holds and some candidate `g₁ ≠ g₀` is possible at `r`, then the
read-only `Unambiguous` is *not* below the truth-dependent singleton promise
`g = g₀`: `Unambiguous r` holds while `g₁ = g₀` fails. -/
theorem unambiguous_not_imp_singleton (π : Genome → ℝ)
    (p : Genome → Obs → ℝ) (orbit : Genome → Θ) (g₀ g₁ : Genome) (r : Obs)
    (hun : Unambiguous π p orbit r) (hne : g₁ ≠ g₀) :
    ¬ (∀ g r, Unambiguous π p orbit r → g = g₀) := by
  rintro H
  exact hne (H g₁ r hun)

/-- **Neither implication holds for a truth-dependent promise.**  A single
concrete finite model and truth-dependent promise `g = g₀` that is sufficient,
does not imply `Unambiguous`, and is not implied by `Unambiguous`.  The two
failures may occur at different reads: `r₀` is ambiguous with `g₀` possible,
while `r₁` is unambiguous with a non-`g₀` candidate possible. -/
theorem truthdependent_sufficient_incomparable (π : Genome → ℝ)
    (p : Genome → Obs → ℝ) (orbit : Genome → Θ) (g₀ : Genome)
    (r₀ r₁ : Obs) (g₁ : Genome)
    (hπ₀ : 0 < π g₀) (hp₀ : 0 < p g₀ r₀)
    (hbad : ∃ h, 0 < π h ∧ 0 < p h r₀ ∧ orbit h ≠ orbit g₀)
    (hun₁ : Unambiguous π p orbit r₁) (hne₁ : g₁ ≠ g₀) :
    Sufficient π p orbit (fun g _ => g = g₀) ∧
      ¬ (∀ g r, (g = g₀) → Unambiguous π p orbit r) ∧
      ¬ (∀ g r, Unambiguous π p orbit r → g = g₀) :=
  ⟨singleton_promise_sufficient π p orbit g₀,
   singleton_promise_not_imp_unambiguous π p orbit g₀ r₀ hπ₀ hp₀ hbad,
   unambiguous_not_imp_singleton π p orbit g₀ g₁ r₁ hun₁ hne₁⟩

end General

/-! ## A concrete non-vacuous model: three candidates, two reads

This is deliberately a different model from the merged `Incomparable`
(two candidates) and `NoWeakest` (four candidates) witnesses.  Read `0` is
ambiguous between candidates `0` and `1`; read `1` is unambiguous and only
candidate `2` is possible there. -/

namespace ThreeCandidate

/-- Distinct orbits (identity). -/
def orbit : Fin 3 → Fin 3 := id

/-- Equal prior on the three candidates. -/
noncomputable def π : Fin 3 → ℝ := fun _ => 1 / 3

/-- Read `0`: candidates `0` and `1` with mass `1/2`, candidate `2` with mass `0`.
Read `1`: only candidate `2` with mass `1`. -/
noncomputable def p : Fin 3 → Fin 2 → ℝ :=
  fun g r => if r = 0 then (if g = 2 then 0 else 1 / 2) else (if g = 2 then 1 else 0)

theorem p_at_read1 (g : Fin 3) : 0 < p g 1 → g = 2 := by
  fin_cases g <;> simp [p]

/-- Read `1` is unambiguous: only candidate `2` is possible. -/
theorem unambiguous_one : Unambiguous π p orbit (1 : Fin 2) := by
  intro g h _ hpg _ hph
  rw [p_at_read1 g hpg, p_at_read1 h hph]

/-- **The ordering verdict on the concrete model.**  The sufficient
truth-dependent promise `g = 0` neither implies nor is implied by the read-only
`Unambiguous`. -/
theorem neither_implication :
    Sufficient π p orbit (fun g _ => g = (0 : Fin 3)) ∧
      ¬ (∀ g r, (g = (0 : Fin 3)) → Unambiguous π p orbit r) ∧
      ¬ (∀ g r, Unambiguous π p orbit r → g = (0 : Fin 3)) :=
  truthdependent_sufficient_incomparable π p orbit (0 : Fin 3) (0 : Fin 2) (1 : Fin 2)
    (2 : Fin 3)
    (by norm_num [π]) (by norm_num [p])
    ⟨1, by norm_num [π], by norm_num [p], by decide⟩
    unambiguous_one (by decide)

end ThreeCandidate

/-! ## The source predicate `I_s` is truth-dependent

Fix the genome length `G = 5` and read length `L = 3`.  A candidate is a spelling
`Fin 5 → Base`; the source predicate is `InformationFeasible` at the read-start
set `R = {0,3}`.  Two spellings with the same `(L, R)` disagree on `I_s`, which is
exactly the failure of read-only-ness: `I_s` cannot be a function of `R` alone. -/

namespace IsTruthDependence

open AssemblyP1.SourceFaithfulIs
open AssemblyP1.FiniteSamplingCounterexample

/-- A length-`5` circular genome over the four-symbol DNA alphabet `Base`. -/
abbrev Spelling : Type := Fin 5 → Base

/-- The circular genome carried by a spelling. -/
def ofSpelling (w : Spelling) : AssemblyP1.SourceFaithfulIs.Genome Base where
  len := 5
  len_pos := by norm_num
  sym := w

/-- The truth spelling `AABBC` of the merged finite-sampling witness. -/
def truthSpelling : Spelling := ![Base.A, Base.A, Base.B, Base.B, Base.C]

/-- The spelling `AAAAB`, which carries a long triple repeat that clause 2 of
`I_s` forbids. -/
def aaaabSpelling : Spelling := ![Base.A, Base.A, Base.A, Base.A, Base.B]

/-- The read-start set `{0,3}` used by both spellings. -/
def starts : Finset (Fin 5) := {0, 3}

/-- The source-faithful `I_s` predicate, read as a promise of `(candidate,
read-start set)`. -/
def isPromise (w : Spelling) (R : Finset (Fin 5)) : Prop :=
  InformationFeasible (ofSpelling w) 3 R

/-- `AABBC` is `I_s`-feasible at `L = 3`, `R = {0,3}` (the same certificate as
the merged finite-sampling witness, re-decided on this spelling). -/
theorem truthSpelling_feasible : isPromise truthSpelling starts := by
  unfold isPromise ofSpelling truthSpelling starts InformationFeasible
  decide

/-- `AAAAB` is **not** `I_s`-feasible at `L = 3`, `R = {0,3}`: its only maximal
triple repeat (length `2` at starts `0,1,2`) cannot be bridged by length-`3`
reads. -/
theorem aaaabSpelling_not_feasible : ¬ isPromise aaaabSpelling starts := by
  unfold isPromise ofSpelling aaaabSpelling starts InformationFeasible
  decide

/-- **The source predicate `I_s` is not a read-only promise.**  If it depended
only on the read-start set `R`, then `AABBC` and `AAAAB` — which share
`L = 3` and `R = {0,3}` — would have the same `I_s` status; they do not.  Hence
`I_s` lies outside `AdmReadOnly`, the family for which the merged read-only
weakest-promise theorem and the read-only boundary theorem
(`sufficient_readonly_iff_imp_unambiguous`) are stated. -/
theorem informationFeasible_not_readOnly :
    ¬ AssemblyP1.FiniteSideInformationOrder.AdmReadOnly isPromise := by
  intro h
  have hiff := h truthSpelling aaaabSpelling starts
  exact aaaabSpelling_not_feasible (hiff.mp truthSpelling_feasible)

/-- **The ordering verdict for the source predicate.**  `I_s` is truth-dependent
(`informationFeasible_not_readOnly`), while `Unambiguous` is read-only
(`unambiguous_promise_readOnly`, proved for every model); and a sufficient
truth-dependent promise need not imply `Unambiguous`
(`truthdependent_sufficient_incomparable`).  Therefore no implication
`I_s ⇒ Unambiguous` or `Unambiguous ⇒ I_s` follows from the merged semantics, and
the literal read-string ordering remains OPEN pending the historical adapter. -/
theorem ordering_verdict :
    ¬ AssemblyP1.FiniteSideInformationOrder.AdmReadOnly isPromise :=
  informationFeasible_not_readOnly

end IsTruthDependence

end AssemblyP1.FiniteSideInformationOrdering
