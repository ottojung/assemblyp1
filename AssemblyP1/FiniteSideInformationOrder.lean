import Mathlib
import AssemblyP1.FiniteBayesianSideInformation

/-!
# The order of sufficient side-information promises (#272)

This file answers the *weakest conditioning* question of issue #272 for the
exact posterior semantics already fixed by
`AssemblyP1.FiniteBayesianSideInformation`:

> when does a **weakest** (least informative, largest-event) sufficient promise
> exist, and is it unique?

The merged module proves the exact posterior-iff criterion, a no-weakest
counterexample for arbitrary truth-dependent promises (`NoWeakest`), and that
the read-only family has a unique weakest member (`Unambiguous`).  What was left
open was a *general* characterization: under a clearly fixed admissible family,
when does a weakest sufficient promise exist?  The answer proved here is purely
order-theoretic and is stated for an arbitrary family `Adm` of promises:

* `sufficient_of_stronger` — sufficiency is **downward closed**: strengthening a
  sufficient promise keeps it sufficient.
* `sufficient_and` / `sufficient_iInter` — the pointwise **conjunction** of
  sufficient promises is sufficient.  Sufficiency is a meet-semilattice.
* `unionAllSufficient` and `weakest_iff_union` — the **union** (disjunction) of
  all sufficient promises is the canonical candidate for a weakest sufficient
  promise, and it is sufficient **iff** a weakest sufficient promise exists.
* `weakest_unique` — if a weakest sufficient promise exists it is unique up to
  logical equivalence.
* `weakest_admissible_iff_union` — the same criterion inside an arbitrary
  structural family `Adm` that is closed under logical equivalence, with
  `weakest_admissible_unique` for uniqueness.
* `unambiguous_isWeakest_readonly` — the read-only family satisfies the
  criterion: its unique weakest sufficient member is `Unambiguous`.
* `NoWeakestProb.no_weakest_sufficient` / `NoWeakestProb.unionAllSufficient_not_sufficient`
  — the full truth-dependent family does **not** satisfy the criterion: on a
  finite normalized-support model the union of all sufficient promises is
  itself insufficient, so no weakest sufficient promise exists.  This reuses the
  merged `NoWeakest` counterexample rather than reproving it.
* `NoWeakestProb.union_e1_e2_not_sufficient` — sufficiency is **not** closed
  under binary union, at the `Sufficient` level.

Nothing here asserts the external Shomorony et al. Not-So-Greedy theorem, and
nothing here decides whether the source predicate `I_s` is ordered against
`Unambiguous`; that ordering question remains OPEN and is discussed in
`docs/issue272-side-information-order.md`.  No `axiom`, `sorry`, or `admit` is
introduced.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AssemblyP1.FiniteSideInformationOrder

open AssemblyP1.FiniteBayesianSideInformation

universe u v w

variable {Genome : Type u} {Obs : Type v} {Θ : Type w}

/-! ## 1. The implication order on promises

`Stronger E₁ E₂` (already defined in the merged module) says `E₁` implies `E₂`,
i.e. `E₁` is the stronger, more informative promise.  It is a preorder.

`Stronger`, `Sufficient` and `SufficientOn` were declared inside a `section`
with `[Fintype Genome] [Fintype Obs] [Fintype Θ] [DecidableEq Θ]` in the merged
module, so those instances are implicit arguments of the definitions; they are
made available below for the whole file. -/

section Order

variable [Fintype Genome] [Fintype Obs] [Fintype Θ] [DecidableEq Θ]

theorem Stronger.refl (E : Genome → Obs → Prop) : Stronger E E :=
  fun _ _ h => h

theorem Stronger.trans {E₁ E₂ E₃ : Genome → Obs → Prop}
    (h₁ : Stronger E₁ E₂) (h₂ : Stronger E₂ E₃) : Stronger E₁ E₃ :=
  fun g r h => h₂ g r (h₁ g r h)

/-- Two promises that imply each other are logically equivalent pointwise. -/
theorem stronger_antisymm {E₁ E₂ : Genome → Obs → Prop}
    (h₁ : Stronger E₁ E₂) (h₂ : Stronger E₂ E₁) : ∀ g r, E₁ g r ↔ E₂ g r :=
  fun g r => ⟨h₁ g r, h₂ g r⟩

/-! ## 2. Sufficiency is downward closed and closed under conjunction -/

/-- Sufficiency is invariant under logical equivalence of promises. -/
theorem sufficient_congr (π : Genome → ℝ) (p : Genome → Obs → ℝ) (orbit : Genome → Θ)
    {E E' : Genome → Obs → Prop} (heq : ∀ g r, E g r ↔ E' g r) :
    Sufficient π p orbit E ↔ Sufficient π p orbit E' := by
  constructor
  · intro hS g r hπg hpg hE'g h hπh hph hE'h
    exact hS g r hπg hpg ((heq g r).mpr hE'g) h hπh hph ((heq h r).mpr hE'h)
  · intro hS g r hπg hpg hEg h hπh hph hEh
    exact hS g r hπg hpg ((heq g r).mp hEg) h hπh hph ((heq h r).mp hEh)

/-- **Downward closure.**  If `E'` is sufficient and `E` is stronger than `E'`
(`E ⇒ E'`), then `E` is sufficient: shrinking a sufficient promise keeps it
sufficient.  Consequently the *weakest* sufficient promise, if it exists, is the
*largest* sufficient event. -/
theorem sufficient_of_stronger (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) {E E' : Genome → Obs → Prop}
    (hS : Sufficient π p orbit E') (hstr : Stronger E E') :
    Sufficient π p orbit E :=
  fun g r hπg hpg hEg h hπh hph hEh =>
    hS g r hπg hpg (hstr g r hEg) h hπh hph (hstr h r hEh)

/-- The empty promise is sufficient (vacuously) and is the strongest promise.
It is the intrinsic *least* sufficient event, but it carries no information. -/
theorem sufficient_false (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) :
    Sufficient π p orbit (fun _ _ => False) :=
  fun _ _ _ _ h => h.elim

theorem false_strongest {E : Genome → Obs → Prop} :
    Stronger (fun _ _ => False) E :=
  fun _ _ h => h.elim

/-- **Meet.**  The conjunction of two sufficient promises is sufficient. -/
theorem sufficient_and (π : Genome → ℝ) (p : Genome → Obs → ℝ) (orbit : Genome → Θ)
    {E₁ E₂ : Genome → Obs → Prop}
    (h₁ : Sufficient π p orbit E₁) (_h₂ : Sufficient π p orbit E₂) :
    Sufficient π p orbit (fun g r => E₁ g r ∧ E₂ g r) :=
  fun g r hπg hpg hg h hπh hph hh =>
    h₁ g r hπg hpg hg.1 h hπh hph hh.1

/-- **Arbitrary meet.**  The pointwise conjunction of a nonempty family of
sufficient promises is sufficient. -/
theorem sufficient_iInter (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) {ι : Type*} [Nonempty ι]
    (Efam : ι → Genome → Obs → Prop)
    (hsu : ∀ i, Sufficient π p orbit (Efam i)) :
    Sufficient π p orbit (fun g r => ∀ i, Efam i g r) := by
  intro g r hπg hpg hg h hπh hph hh
  exact hsu (Classical.arbitrary ι) g r hπg hpg (hg _) h hπh hph (hh _)

/-! ## 3. The weakest sufficient promise exists iff its union is sufficient -/

/-- The pointwise **union** (disjunction) of every sufficient promise: the
canonical candidate for the weakest (least informative) sufficient promise.  It
is the largest event that any sufficient promise implies, so it is the weakest
promise that could possibly be sufficient. -/
def unionAllSufficient (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) : Genome → Obs → Prop :=
  fun g r => ∃ E : Genome → Obs → Prop, Sufficient π p orbit E ∧ E g r

/-- `W` is a weakest sufficient promise: sufficient, and implied by every
sufficient promise (hence weaker than all of them). -/
def IsWeakestSufficient (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) (W : Genome → Obs → Prop) : Prop :=
  Sufficient π p orbit W ∧ ∀ E, Sufficient π p orbit E → Stronger E W

/-- **Existence criterion.**  A weakest sufficient promise exists **iff** the
union of all sufficient promises is itself sufficient.  The forward direction is
the union itself; the reverse identifies any weakest sufficient promise with the
union up to logical equivalence. -/
theorem weakest_iff_union (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) :
    Sufficient π p orbit (unionAllSufficient π p orbit) ↔
      ∃ W, IsWeakestSufficient π p orbit W := by
  constructor
  · intro hU
    exact ⟨_, hU, fun E hE g r h => ⟨E, hE, h⟩⟩
  · rintro ⟨W, hW, hmax⟩
    refine (sufficient_congr π p orbit
      (E := unionAllSufficient π p orbit) (E' := W) ?_).mpr hW
    intro g r
    exact ⟨fun ⟨E, hE, hgr⟩ => hmax E hE g r hgr,
      fun hWgr => ⟨W, hW, hWgr⟩⟩

/-- **Uniqueness.**  Any two weakest sufficient promises are logically
equivalent.  There is at most one weakest sufficient promise up to
equivalence. -/
theorem weakest_unique (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) {W₁ W₂ : Genome → Obs → Prop}
    (h₁ : IsWeakestSufficient π p orbit W₁) (h₂ : IsWeakestSufficient π p orbit W₂) :
    ∀ g r, W₁ g r ↔ W₂ g r :=
  stronger_antisymm (h₂.2 W₁ h₁.1) (h₁.2 W₂ h₂.1)

/-! ## 4. The criterion inside an arbitrary structural family

For a family `Adm` of "allowed" promises (e.g. source-shaped predicates), a
weakest *admissible* sufficient promise exists iff the union of all admissible
sufficient promises is itself admissible and sufficient.  The family must be
closed under logical equivalence, which every structural predicate family
defined by shape (rather than by a particular syntax tree) satisfies. -/

/-- Union of all sufficient promises that lie in the admissible family `Adm`. -/
def unionAdmissible (Adm : (Genome → Obs → Prop) → Prop)
    (π : Genome → ℝ) (p : Genome → Obs → ℝ) (orbit : Genome → Θ) :
    Genome → Obs → Prop :=
  fun g r => ∃ E : Genome → Obs → Prop, Adm E ∧ Sufficient π p orbit E ∧ E g r

/-- `W` is the weakest sufficient promise **within** `Adm`. -/
def IsWeakestAdmissible (Adm : (Genome → Obs → Prop) → Prop)
    (π : Genome → ℝ) (p : Genome → Obs → ℝ) (orbit : Genome → Θ)
    (W : Genome → Obs → Prop) : Prop :=
  Adm W ∧ Sufficient π p orbit W ∧
    ∀ E, Adm E → Sufficient π p orbit E → Stronger E W

/-- **Family-relative existence criterion.**  Inside an equivalence-closed
family `Adm`, a weakest admissible sufficient promise exists iff the union of
all admissible sufficient promises is admissible and sufficient. -/
theorem weakest_admissible_iff_union
    (Adm : (Genome → Obs → Prop) → Prop)
    (hAdm_congr : ∀ {E E' : Genome → Obs → Prop},
      (∀ g r, E g r ↔ E' g r) → Adm E → Adm E')
    (π : Genome → ℝ) (p : Genome → Obs → ℝ) (orbit : Genome → Θ) :
    (Adm (unionAdmissible Adm π p orbit) ∧
        Sufficient π p orbit (unionAdmissible Adm π p orbit)) ↔
      ∃ W, IsWeakestAdmissible Adm π p orbit W := by
  constructor
  · rintro ⟨hAdm, hS⟩
    exact ⟨_, hAdm, hS, fun E hE hSE g r h => ⟨E, hE, hSE, h⟩⟩
  · rintro ⟨W, hAdmW, hSW, hmax⟩
    have heq : ∀ g r, unionAdmissible Adm π p orbit g r ↔ W g r := by
      intro g r
      exact ⟨fun ⟨E, hE, hSE, hgr⟩ => hmax E hE hSE g r hgr,
        fun hW => ⟨W, hAdmW, hSW, hW⟩⟩
    exact ⟨hAdm_congr (fun g r => (heq g r).symm) hAdmW,
      (sufficient_congr π p orbit heq).mpr hSW⟩

/-- **Family-relative uniqueness.** -/
theorem weakest_admissible_unique (Adm : (Genome → Obs → Prop) → Prop)
    (π : Genome → ℝ) (p : Genome → Obs → ℝ) (orbit : Genome → Θ)
    {W₁ W₂ : Genome → Obs → Prop}
    (h₁ : IsWeakestAdmissible Adm π p orbit W₁)
    (h₂ : IsWeakestAdmissible Adm π p orbit W₂) :
    ∀ g r, W₁ g r ↔ W₂ g r :=
  stronger_antisymm (h₂.2.2 W₁ h₁.1 h₁.2.1) (h₁.2.2 W₂ h₂.1 h₂.2.1)

/-! ## 5. Read-only family: the criterion holds, weakest is `Unambiguous` -/

/-- The **read-only** family: promises that do not depend on the unknown truth
`g`, only on the observed read `r`.  This is the abstract form of a structural
predicate supplied by a read-only side channel. -/
def AdmReadOnly : (Genome → Obs → Prop) → Prop :=
  fun E => ∀ g g' r, E g r ↔ E g' r

theorem admReadOnly_congr {E E' : Genome → Obs → Prop}
    (heq : ∀ g r, E g r ↔ E' g r) (hE : AdmReadOnly E) : AdmReadOnly E' :=
  fun g g' r => (heq g r).symm.trans ((hE g g' r).trans (heq g' r))

/-- The union of all sufficient read-only promises is exactly `Unambiguous`:
any sufficient read-only promise that fires at `r` forces the read support at
`r` into one orbit, and `Unambiguous` is itself a sufficient read-only promise. -/
theorem unionReadOnly_eq_unambiguous (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) :
    ∀ g r, unionAdmissible AdmReadOnly π p orbit g r ↔ Unambiguous π p orbit r := by
  intro g r
  constructor
  · rintro ⟨E, hEro, hSE, hgr⟩ g' h' hπg' hpg' hπh' hph'
    exact hSE g' r hπg' hpg' ((hEro g' g r).mpr hgr) h' hπh' hph'
      ((hEro h' g r).mpr hgr)
  · intro hu
    exact ⟨fun _ r' => Unambiguous π p orbit r', fun _ _ _ => Iff.rfl,
      unambiguous_sufficient π p orbit, hu⟩

/-- **The read-only family has a weakest sufficient promise, namely
`Unambiguous`.**  It is sufficient, read-only, and every read-only sufficient
promise implies it. -/
theorem unambiguous_isWeakest_readonly (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) :
    IsWeakestAdmissible AdmReadOnly π p orbit (fun _ r => Unambiguous π p orbit r) := by
  refine ⟨fun _ _ _ => Iff.rfl, unambiguous_sufficient π p orbit, ?_⟩
  intro E hEro hSE g r hgr g' h' hπg' hpg' hπh' hph'
  exact hSE g' r hπg' hpg' ((hEro g' g r).mpr hgr) h' hπh' hph'
    ((hEro h' g r).mpr hgr)

/-- Existence of the weakest read-only sufficient promise, derived through the
general union criterion of `weakest_admissible_iff_union`. -/
theorem weakest_readonly_exists (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) :
    ∃ W, IsWeakestAdmissible AdmReadOnly π p orbit W :=
  ⟨_, unambiguous_isWeakest_readonly π p orbit⟩

/-- Uniqueness of the weakest read-only sufficient promise. -/
theorem weakest_readonly_unique (π : Genome → ℝ) (p : Genome → Obs → ℝ)
    (orbit : Genome → Θ) {W : Genome → Obs → Prop}
    (hW : IsWeakestAdmissible AdmReadOnly π p orbit W) :
    ∀ g r, W g r ↔ Unambiguous π p orbit r :=
  weakest_admissible_unique AdmReadOnly π p orbit hW
    (unambiguous_isWeakest_readonly π p orbit)

/-! ## 6. Full truth-dependent family: the criterion fails

On the merged `NoWeakest` finite model (four candidates, two reads, confusability
pairs `{0,1}` and `{2,3}`), the read support is realized by the unnormalized
weights `π ≡ 1` and `p g r = 1_{S(g,r)}`.  On that model `Sufficient` coincides
with the merged support-restricted `SufficientOn`, so the merged no-weakest
counterexample transfers verbatim. -/

namespace NoWeakestProb

instance : DecidableRel NoWeakest.S := fun g r => by unfold NoWeakest.S; infer_instance

/-- Prior, equal on all four candidates. -/
noncomputable def π : Fin 4 → ℝ := fun _ => 1

/-- Likelihood supported exactly on the merged confusability support `S`. -/
def p : Fin 4 → Fin 2 → ℝ := fun g r => if NoWeakest.S g r then 1 else 0

/-- Distinct orbits (identity). -/
def orbit : Fin 4 → Fin 4 := id

theorem pi_pos : ∀ g : Fin 4, 0 < π g := fun _ => by norm_num [π]

theorem p_pos_iff (g : Fin 4) (r : Fin 2) : 0 < p g r ↔ NoWeakest.S g r := by
  unfold p
  by_cases h : NoWeakest.S g r <;> simp [h]

/-- On this model the probabilistic `Sufficient` is exactly the merged
support-restricted `SufficientOn`. -/
theorem sufficient_iff_sufficientOn (E : Fin 4 → Fin 2 → Prop) :
    Sufficient π p orbit E ↔ SufficientOn NoWeakest.S orbit E := by
  constructor
  · intro hS g r hSg hEg h hSh hEh
    exact hS g r (pi_pos g) ((p_pos_iff g r).mpr hSg) hEg h (pi_pos h)
      ((p_pos_iff h r).mpr hSh) hEh
  · intro hS g r _ hpg hEg h _ hph hEh
    exact hS g r ((p_pos_iff g r).mp hpg) hEg h ((p_pos_iff h r).mp hph) hEh

/-- **No weakest sufficient promise** in the full truth-dependent family,
transferred from the merged counterexample. -/
theorem no_weakest_sufficient :
    ¬ ∃ W, IsWeakestSufficient π p orbit W := by
  rintro ⟨W, hW, hmax⟩
  apply NoWeakest.no_weakest_sufficient
  exact ⟨W, (sufficient_iff_sufficientOn W).mp hW,
    fun E' hE' => hmax E' ((sufficient_iff_sufficientOn E').mpr hE')⟩

/-- Consequently the union of all sufficient promises is **not** sufficient:
the existence criterion of `weakest_iff_union` fails. -/
theorem unionAllSufficient_not_sufficient :
    ¬ Sufficient π p orbit (unionAllSufficient π p orbit) :=
  fun hU => no_weakest_sufficient ((weakest_iff_union π p orbit).mp hU)

/-- The merged sufficient promises `E1`, `E2`, now at the `Sufficient` level. -/
def E1 : Fin 4 → Fin 2 → Prop := NoWeakest.E1

def E2 : Fin 4 → Fin 2 → Prop := NoWeakest.E2

theorem e1_sufficient : Sufficient π p orbit E1 :=
  (sufficient_iff_sufficientOn E1).mpr NoWeakest.e1_sufficient

theorem e2_sufficient : Sufficient π p orbit E2 :=
  (sufficient_iff_sufficientOn E2).mpr NoWeakest.e2_sufficient

/-- **Sufficiency is not closed under binary union.**  Two sufficient promises
whose disjunction is insufficient. -/
theorem union_e1_e2_not_sufficient :
    ¬ Sufficient π p orbit (fun g r => E1 g r ∨ E2 g r) :=
  fun h => NoWeakest.union_not_sufficient
    ((sufficient_iff_sufficientOn (fun g r => E1 g r ∨ E2 g r)).mp h)

/-- The concrete failure bundle: `E1` and `E2` are sufficient, their union is
not, and no weakest sufficient promise exists. -/
theorem order_failure_bundle :
    Sufficient π p orbit E1 ∧ Sufficient π p orbit E2 ∧
      ¬ Sufficient π p orbit (fun g r => E1 g r ∨ E2 g r) ∧
      ¬ ∃ W, IsWeakestSufficient π p orbit W :=
  ⟨e1_sufficient, e2_sufficient, union_e1_e2_not_sufficient, no_weakest_sufficient⟩

end NoWeakestProb

end Order

end AssemblyP1.FiniteSideInformationOrder
