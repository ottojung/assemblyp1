import Mathlib
import AssemblyP1.FiniteBayesianSideInformation
import AssemblyP1.FiniteSideInformationOrder
import AssemblyP1.FiniteSideInformationSourcePromise

/-!
# The weakest source-defined sufficient promise (#272, subclaim (b))

This module discharges subclaim (b) of issue #272: the exact characterization
of the weakest source-defined bridging promise certifying posterior-1 recovery.

The **source-defined** family `AdmSourceDefined` consists of promises that are
built only from the observed read (read-only) or only from the truth
(truth-only): the side channel reports a property of the read or of the
candidate, but not a joint property of both.  This is the union of the two
structural families resolved by the merged modules
(`AssemblyP1.FiniteSideInformationOrder` for read-only,
`AssemblyP1.FiniteSideInformationSourcePromise` for truth-only), and it is the
abstract form of a "minimal bridging set built only from observed read
strings".

## Result

| promise family | weakest sufficient promise | existence |
|---|---|---|
| read-only `AdmReadOnly` (merged) | `Unambiguous`, unique | always |
| truth-only `AdmTruthOnly` (merged) | `True`, unique | iff `∀ r, Unambiguous` |
| **source-defined `AdmSourceDefined` (this module)** | **`True`, unique** | **iff `∀ r, Unambiguous π p orbit r`** |
| arbitrary truth-dependent (merged `NoWeakest`) | none generically | fails on any ambiguous model |

The engine is the order-theoretic observation that the truth-only singletons
are source-defined and sufficient, so the union of all source-defined
sufficient promises is always the vacuous promise `True`:

* `unionSourceDefined_eq_true` — every candidate is named by its truth-only
  singleton, which is source-defined and sufficient.
* `weakest_sourceDefined_iff_sufficient_true` — by the merged
  `weakest_admissible_iff_union`, a weakest source-defined sufficient promise
  exists **iff** the vacuous promise is sufficient.
* `weakest_sourceDefined_iff_unambiguous` — specialized via the merged
  `sufficient_true_iff_unambiguous`, this is **iff** the read-only posterior is
  already certain at every positive-probability read.
* `true_isWeakest_sourceDefined`, `weakest_sourceDefined_unique` — when it
  exists, the weakest source-defined sufficient promise is `True`, unique up to
  equivalence.
* `AmbiguousRead.no_weakest_sourceDefined` — on the merged `TwoCandidate`
  model (two candidates, one ambiguous read, distinct orbits), the source-defined
  family has **no** weakest sufficient promise: a genuine counterexample to
  existence.

The source-defined criterion coincides with the truth-only criterion because
the truth-only singletons already saturate the union at `True`; adding the
read-only promises does not change the weakest member.  This is the precise
answer to subclaim (b): the source-defined family has a weakest sufficient
promise **iff no side information is needed at all**, i.e. iff the read-only
posterior is already certain.

Nothing here asserts the external Shomorony et al. Not-So-Greedy theorem, and
nothing here decides subclaims (a) and (c).  No `axiom`, `sorry`, or `admit`
is introduced.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AssemblyP1.FiniteSourceDefinedWeakest

open AssemblyP1.FiniteBayesianSideInformation
open AssemblyP1.FiniteSideInformationOrder
open AssemblyP1.FiniteSideInformationSourcePromise

universe u v w

/-- The **source-defined** family: promises built only from the observed read
(read-only) or only from the truth (truth-only).  The side channel reports a
property of the read or of the candidate, but not a joint property of both.
This is the union of the two structural families resolved by the merged
modules, and the abstract form of a "minimal bridging set built only from
observed read strings".

Both clauses are written inline to avoid propagating the explicit type
parameters of the merged `AdmReadOnly` and `AdmTruthOnly` definitions; they
are definitionally the merged families. -/
def AdmSourceDefined {Genome : Type u} {Obs : Type v} :
    (Genome → Obs → Prop) → Prop :=
  fun E => (∀ g g' r, E g r ↔ E g' r) ∨ (∀ g r r', E g r ↔ E g r')

/-- The source-defined family is closed under pointwise logical equivalence. -/
theorem admSourceDefined_congr {Genome : Type u} {Obs : Type v}
    {E E' : Genome → Obs → Prop}
    (heq : ∀ g r, E g r ↔ E' g r) (hE : AdmSourceDefined E) : AdmSourceDefined E' :=
  hE.elim
    (fun h => Or.inl fun g g' r => (heq g r).symm.trans ((h g g' r).trans (heq g' r)))
    (fun h => Or.inr fun g r r' => (heq g r).symm.trans ((h g r r').trans (heq g r')))

/-- Every singleton truth-promise is source-defined (it is truth-only). -/
theorem admSourceDefined_singleton {Genome : Type u} {Obs : Type v} (g₀ : Genome) :
    AdmSourceDefined (fun (g : Genome) (_ : Obs) => g = g₀) :=
  Or.inr (fun _ _ _ => Iff.rfl)

/-- The vacuous promise is source-defined (it is read-only). -/
theorem admSourceDefined_true {Genome : Type u} {Obs : Type v} :
    AdmSourceDefined (fun (_ : Genome) (_ : Obs) => True) :=
  Or.inl (fun _ _ _ => Iff.rfl)

/-- **Union of the source-defined family is vacuous.**  The union of all
source-defined sufficient promises is always the constant-`True` promise:
every candidate is named by its own sufficient truth-only singleton, which is
source-defined. -/
theorem unionSourceDefined_eq_true {Genome : Type u} {Obs : Type v} {Θ : Type w}
    [Fintype Genome] [Fintype Obs] [Fintype Θ] [DecidableEq Θ]
    (π : Genome → ℝ) (p : Genome → Obs → ℝ) (orbit : Genome → Θ) :
    ∀ g r, unionAdmissible AdmSourceDefined π p orbit g r ↔ True := by
  intro g r
  constructor
  · intro _; trivial
  · intro _
    exact ⟨fun g' _ => g' = g, admSourceDefined_singleton g,
      singleton_sufficient π p orbit g, rfl⟩

/-- **Existence criterion for the source-defined family.**  A weakest
source-defined sufficient promise exists **iff** the vacuous promise is itself
sufficient.  This is the merged `weakest_admissible_iff_union` combined with
the vacuous union of `unionSourceDefined_eq_true`. -/
theorem weakest_sourceDefined_iff_sufficient_true {Genome : Type u} {Obs : Type v}
    {Θ : Type w} [Fintype Genome] [Fintype Obs] [Fintype Θ] [DecidableEq Θ]
    (π : Genome → ℝ) (p : Genome → Obs → ℝ) (orbit : Genome → Θ) :
    (∃ W, IsWeakestAdmissible AdmSourceDefined π p orbit W) ↔
      Sufficient π p orbit (fun _ _ => True) := by
  have hcrit := weakest_admissible_iff_union AdmSourceDefined admSourceDefined_congr π p orbit
  have heq : ∀ g r,
      unionAdmissible AdmSourceDefined π p orbit g r ↔ True :=
    fun g r => unionSourceDefined_eq_true π p orbit g r
  have hsu : Sufficient π p orbit (unionAdmissible AdmSourceDefined π p orbit) ↔
      Sufficient π p orbit (fun _ _ => True) :=
    sufficient_congr π p orbit heq
  have hadm : AdmSourceDefined (unionAdmissible AdmSourceDefined π p orbit) ↔
      AdmSourceDefined (fun _ _ => True) :=
    ⟨fun h => admSourceDefined_congr heq h,
      fun h => admSourceDefined_congr (fun g r => (heq g r).symm) h⟩
  constructor
  · rintro hW
    exact hsu.mp (hcrit.mpr hW).2
  · intro hS
    exact hcrit.mp ⟨hadm.mpr admSourceDefined_true, hsu.mpr hS⟩

/-- **Manuscript-ready criterion.**  A weakest source-defined sufficient promise
exists **iff** the read-only posterior is already certain at every
positive-probability read (`∀ r, Unambiguous π p orbit r`).  In particular, any
genuinely ambiguous read destroys existence. -/
theorem weakest_sourceDefined_iff_unambiguous {Genome : Type u} {Obs : Type v}
    {Θ : Type w} [Fintype Genome] [Fintype Obs] [Fintype Θ] [DecidableEq Θ]
    (π : Genome → ℝ) (p : Genome → Obs → ℝ) (orbit : Genome → Θ) :
    (∃ W, IsWeakestAdmissible AdmSourceDefined π p orbit W) ↔
      ∀ r, Unambiguous π p orbit r :=
  (weakest_sourceDefined_iff_sufficient_true π p orbit).trans
    (sufficient_true_iff_unambiguous π p orbit)

/-- The positive direction of the criterion: when every read is unambiguous, a
weakest source-defined sufficient promise exists. -/
theorem weakest_sourceDefined_exists_of_readonly_certain {Genome : Type u}
    {Obs : Type v} {Θ : Type w} [Fintype Genome] [Fintype Obs] [Fintype Θ]
    [DecidableEq Θ] (π : Genome → ℝ) (p : Genome → Obs → ℝ) (orbit : Genome → Θ)
    (h : ∀ r, Unambiguous π p orbit r) :
    ∃ W, IsWeakestAdmissible AdmSourceDefined π p orbit W :=
  (weakest_sourceDefined_iff_unambiguous π p orbit).mpr h

/-- When the vacuous promise is sufficient, it is the weakest source-defined
sufficient promise: it is source-defined, sufficient, and implied by every
source-defined promise. -/
theorem true_isWeakest_sourceDefined {Genome : Type u} {Obs : Type v}
    {Θ : Type w} [Fintype Genome] [Fintype Obs] [Fintype Θ] [DecidableEq Θ]
    (π : Genome → ℝ) (p : Genome → Obs → ℝ) (orbit : Genome → Θ)
    (hS : Sufficient π p orbit (fun _ _ => True)) :
    IsWeakestAdmissible AdmSourceDefined π p orbit (fun _ _ => True) :=
  ⟨admSourceDefined_true, hS, fun _ _ _ _ _ _ => trivial⟩

/-- **Uniqueness.**  Any weakest source-defined sufficient promise is logically
equivalent to the vacuous promise `True`. -/
theorem weakest_sourceDefined_unique {Genome : Type u} {Obs : Type v}
    {Θ : Type w} [Fintype Genome] [Fintype Obs] [Fintype Θ] [DecidableEq Θ]
    (π : Genome → ℝ) (p : Genome → Obs → ℝ) (orbit : Genome → Θ)
    (hS : Sufficient π p orbit (fun _ _ => True))
    {W : Genome → Obs → Prop} (hW : IsWeakestAdmissible AdmSourceDefined π p orbit W) :
    ∀ g r, W g r ↔ True :=
  weakest_admissible_unique AdmSourceDefined π p orbit hW
    (true_isWeakest_sourceDefined π p orbit hS)

/-! ## Explicit counterexample: no weakest source-defined promise

On the merged two-candidate, one-read model (`TwoCandidate` in
`AssemblyP1.FiniteBayesianSideInformation`), read `0` supports both candidates
in different orbits, so the vacuous promise is not sufficient.  By
`weakest_sourceDefined_iff`, the source-defined family therefore has **no**
weakest sufficient promise. -/

namespace AmbiguousRead

open AssemblyP1.FiniteBayesianSideInformation.TwoCandidate

/-- The vacuous promise is not sufficient: the single read is ambiguous. -/
theorem not_sufficient_true :
    ¬ Sufficient π p orbit (fun _ _ => True) := by
  intro hS
  have h := hS (0 : Fin 2) (0 : Fin 1) (by norm_num [π]) (by norm_num [p]) trivial
    (1 : Fin 2) (by norm_num [π]) (by norm_num [p]) trivial
  have h10 : (1 : Fin 2) = 0 := h
  exact (by decide : (1 : Fin 2) ≠ 0) h10

/-- The union of all sufficient source-defined promises is the vacuous promise
`True`. -/
theorem union_eq_true :
    ∀ g r, unionAdmissible AdmSourceDefined π p orbit g r ↔ True :=
  unionSourceDefined_eq_true π p orbit

/-- That union is **not** sufficient: it fails at the ambiguous read. -/
theorem union_not_sufficient :
    ¬ Sufficient π p orbit (unionAdmissible AdmSourceDefined π p orbit) := by
  intro h
  exact not_sufficient_true
    ((sufficient_congr π p orbit (fun g r => union_eq_true g r)).mp h)

/-- **No weakest sufficient source-defined promise exists.** -/
theorem no_weakest :
    ¬ ∃ W, IsWeakestAdmissible AdmSourceDefined π p orbit W := by
  intro h
  exact not_sufficient_true ((weakest_sourceDefined_iff_sufficient_true π p orbit).mp h)

/-- The combined counterexample bundle: the source-defined union is `True`, that
union is insufficient, and no weakest sufficient source-defined promise
exists. -/
theorem counterexample :
    (∀ g r, unionAdmissible AdmSourceDefined π p orbit g r ↔ True) ∧
      ¬ Sufficient π p orbit (unionAdmissible AdmSourceDefined π p orbit) ∧
      ¬ ∃ W, IsWeakestAdmissible AdmSourceDefined π p orbit W :=
  ⟨union_eq_true, union_not_sufficient, no_weakest⟩

end AmbiguousRead

/-! ## Positive example: a weakest source-defined promise does exist

A two-candidate, two-read model in which each read is produced by exactly one
candidate, so every read is unambiguous.  By
`weakest_sourceDefined_exists_of_readonly_certain` the source-defined family
does have a weakest sufficient promise, namely the vacuous promise `True`. -/

namespace UnambiguousExample

/-- Distinct orbits (identity). -/
def orbit : Fin 2 → Fin 2 := id

/-- Equal prior on the two candidates. -/
noncomputable def π : Fin 2 → ℝ := fun _ => 1 / 2

/-- Read `r` is produced with probability `1` by candidate `r` and `0` by the
other candidate. -/
def p : Fin 2 → Fin 2 → ℝ := fun g r => if g = r then 1 else 0

/-- Candidate `g` has positive likelihood at read `r` exactly when `g = r`. -/
theorem p_pos_iff (g r : Fin 2) : 0 < p g r ↔ g = r := by
  by_cases h : g = r <;> simp [p, h]

/-- Every read is unambiguous: read `r` supports only candidate `r`. -/
theorem unambiguous : ∀ r, Unambiguous π p orbit r := by
  intro r g h _ hpg _ hph
  have hg : g = r := (p_pos_iff g r).mp hpg
  have hh : h = r := (p_pos_iff h r).mp hph
  rw [hg, hh]

/-- A weakest sufficient source-defined promise exists. -/
theorem weakest_exists :
    ∃ W, IsWeakestAdmissible AdmSourceDefined π p orbit W :=
  weakest_sourceDefined_exists_of_readonly_certain π p orbit unambiguous

/-- The weakest sufficient source-defined promise is the vacuous promise. -/
theorem true_is_weakest :
    IsWeakestAdmissible AdmSourceDefined π p orbit (fun _ _ => True) :=
  true_isWeakest_sourceDefined π p orbit
    ((sufficient_true_iff_unambiguous π p orbit).mpr unambiguous)

/-- Existence and identification together. -/
theorem weakest_exists_and_is_true :
    (∃ W, IsWeakestAdmissible AdmSourceDefined π p orbit W) ∧
      IsWeakestAdmissible AdmSourceDefined π p orbit (fun _ _ => True) :=
  ⟨weakest_exists, true_is_weakest⟩

end UnambiguousExample

end AssemblyP1.FiniteSourceDefinedWeakest
