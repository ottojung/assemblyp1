import AssemblyP1.ConditionalVsMLGenomeAdapter271
import AssemblyP1.ConditionalIdentifiability
import Mathlib.Tactic

/-!
# Full-read-set weighted placement mass for the #271 separation witness

This module connects the single-read `(A ∧ ¬B)` separation witness of
`AssemblyP1/ConditionalVsMLGenomeAdapter271.lean` to the **source-faithful
weighted placement mass over the full observed read set** formalized abstractly
in `AssemblyP1.ConditionalIdentifiability.PlacementModel`, with the literal
historical event `AssemblyP1.HistoricalCovers.HistoricalInformationFeasibleLiteral`
as the feasibility predicate.  It closes (with a precise boundary) open item 2 of
`docs/conditional-vs-ml-genome-adapter-271.md`.

## What is built

The same finite model as the adapter (binary alphabet, circular genomes of
length `4`, oriented read length `2`, the three rotation-orbit representatives
`0001`, `0011`, `0101`) is re-read at the **placement level**:

* the observation `Y : Finset Read` is the *deduplicated observed read-string
  set* (the source's `observedTypes_ofFinset`);
* `fullFeasible g T` is the literal historical `I_s`
  `HistoricalInformationFeasibleLiteral (genOf g) 2 T`;
* `fullConsistent g T Y` says the placement `T` on candidate `g` induces exactly
  the observed read set `Y`;
* `fullWeight g T = (1/4)^{|T|}` is the source-faithful placement mass (each of
  the `|T|` sampled starts is one of the four positions).

The resulting `PlacementModel` is a **concrete** instance: its external
Not-So-Greedy field `decode_correct` is proved here, not hypothesized, because on
this four-symbol length-`2` model the literal event forces the observed read set
to be one of two values (`coverage_iff`) and candidate `0` is never literally
feasible (`fullFeasible_zero`).  The merged #266 theorem
`placement_posterior_certain` is then applied by name.

## The two kernel-checked findings

1. **Positive connection at the full read set.**  Candidate `1` (`0011`) is
   literally feasible at the *saturated* placement `{0,1,2,3}`, whose induced
   read set is the full read set `Y1 = {00,01,10,11}`.  At `Y1` the weighted
   placement mass is strictly positive on the truth orbit `1` and identically
   zero on `0` and `2` (`fullReadSet_support`), so the full-read-set
   placement-level conditional recovery is certain
   (`fullReadSet_posterior_eq_one`).

2. **Precise boundary: the single-read witness does not lift.**  The witness's
   `(A)`-side event uses the *placement-based* `SourceFaithfulIs.InformationFeasible`
   at the two-start placement `{0,2}` (`feasible_genOf_one`), which is **not**
   the literal historical event (`witness_placement_not_literal`): at read length
   `2` the literal §6.4 coverage clause forces every position to be a match
   start, and `{0,2}` leaves positions `1` and `3` uncovered.  Consequently the
   literal weighted placement mass **vanishes at every single-read observation**
   (`fullJoint_singleton_eq_zero`).  So the single-read `(A ∧ ¬B)` separation is
   not reproduced by the literal full-read-set mass at the same observation; the
   literal mass instead gives `(A ∧ B)` coincidence at the full read set.  This
   is a representation/saturation boundary, not a contradiction, and it is
   recorded honestly.

No `sorry`/`admit`/`axiom`/`native_decide`; the axiom audit is in
`AxiomAudit271.lean`.
-/

set_option linter.dupNamespace false
set_option maxHeartbeats 1000000

namespace AssemblyP1.ConditionalVsMLFullReadSet271

open AssemblyP1.ConditionalVsMLGenomeAdapter271
open AssemblyP1.ConditionalIdentifiability
open AssemblyP1.HistoricalCovers
open AssemblyP1.SourceFaithfulIs
open Finset BigOperators

/-- The observed deduplicated read-string set (the source's read set). -/
abbrev Obs : Type := Finset Read

/-- The full observed read set of the truth candidate `0011`: all four oriented
length-`2` read strings. -/
def Y1 : Obs := {r2 0 0, r2 0 1, r2 1 0, r2 1 1}

/-- The observed read set of the converse candidate `0101`. -/
def Y2 : Obs := {r2 0 1, r2 1 0}

/-- The window-type image of candidate `0001`. -/
def Z0 : Obs := {r2 0 0, r2 0 1, r2 1 0}

/-- The saturated placement: reads sampled at every position. -/
def Tfull : Finset (Fin 4) := {0, 1, 2, 3}

/-- The literal historical event at the placement level. -/
abbrev fullFeasible (g : Fin 3) (T : Finset (Fin 4)) : Prop :=
  HistoricalInformationFeasibleLiteral (genOf g) 2 T

/-- Placement `T` on candidate `g` induces exactly the observed read set `Y`. -/
abbrev fullConsistent (g : Fin 3) (T : Finset (Fin 4)) (Y : Obs) : Prop :=
  observedTypes_ofFinset (genOf g) 2 T = Y

/-- Source-faithful placement weight: each of the `|T|` sampled starts is chosen
uniformly among the four positions, so the placement carries mass `(1/4)^{|T|}`. -/
noncomputable def fullWeight (_ : Fin 3) (T : Finset (Fin 4)) : ℝ := (1 / 4) ^ T.card

/-- The window-type image of a candidate: the set of oriented read strings that
occur anywhere on its circle. -/
def winImg (g : Fin 3) : Obs := (Finset.univ : Finset (Fin 4)).image ((genOf g).window 2)

/-! ## Literal feasibility forces the read set (coverage at read length two) -/

/-- **Coverage at read length two forces every position to be a match start.**
`HistoricalCovers S 2 obs` is `∀ t, ∃ d : Fin 1, …`; `Fin 1` has one element, so
it says every position's length-`2` window lies in `obs`, i.e. the window-type
image of `S` is contained in `obs`. -/
theorem coverage_window_mem (g : Fin 3) :
    ∀ T : Finset (Fin 4),
      HistoricalCovers (genOf g) 2 (observedTypes_ofFinset (genOf g) 2 T) →
        winImg g ⊆ observedTypes_ofFinset (genOf g) 2 T := by
  fin_cases g <;> decide

/-- The window-type image has at least two strings for every candidate. -/
theorem winImg_card_ge : ∀ g : Fin 3, 2 ≤ (winImg g).card := by decide

/-- **The literal event pins the observed read set.**  On this model
`HistoricalCovers (genOf g) 2 obs` holds exactly when `obs` is the window-type
image of `g`: `Y1` for `g = 1`, `Y2` for `g = 2`, `Z0` for `g = 0`. -/
theorem coverage_iff (g : Fin 3) :
    ∀ T : Finset (Fin 4),
      HistoricalCovers (genOf g) 2 (observedTypes_ofFinset (genOf g) 2 T) ↔
        (g = 1 ∧ observedTypes_ofFinset (genOf g) 2 T = Y1) ∨
          (g = 2 ∧ observedTypes_ofFinset (genOf g) 2 T = Y2) ∨
            (g = 0 ∧ observedTypes_ofFinset (genOf g) 2 T = Z0) := by
  fin_cases g <;> decide

/-- Candidate `0` (`0001`) is literally infeasible at every placement: it has the
length-`1` triple repeat `A` at starts `{0,1,2}`, and read length `2` cannot
bridge any copy of length `≥ 1` (`bridgesCopy_length` forces `e + 2 ≤ 2`). -/
theorem fullFeasible_zero (T : Finset (Fin 4)) : ¬ fullFeasible 0 T := by
  intro h
  have ht : IsTripleOccurrence (genOf 0) 1 0 1 2 := by decide
  have hb := (h.2.1 (⟨1, by norm_num⟩ : Fin (genOf 0).len) 0 1 2 ht).1
  have := bridgesCopy_length hb
  omega

/-! ## The concrete placement model and its proved Not-So-Greedy field -/

/-- The read-only decoder on the two attainable full read sets. -/
def fullDecode (Y : Obs) : Fin 3 :=
  if Y = Y1 then 1 else if Y = Y2 then 2 else 0

/-- **The external Not-So-Greedy field, proved.**  A consistent, literally
feasible placement forces the read set to be `Y1` (candidate `1`) or `Y2`
(candidate `2`); candidate `0` is never feasible. -/
theorem fullDecode_correct (g : Fin 3) (T : Finset (Fin 4)) (Y : Obs)
    (hc : fullConsistent g T Y) (hf : fullFeasible g T) : fullDecode Y = g := by
  have hcov : HistoricalCovers (genOf g) 2 (observedTypes_ofFinset (genOf g) 2 T) := hf.1
  rcases (coverage_iff g T).mp hcov with ⟨rfl, hY⟩ | ⟨rfl, hY⟩ | ⟨rfl, hY⟩
  · have hY' : Y = Y1 := by rw [← hc, hY]
    rw [hY']; simp [fullDecode]
  · have hY' : Y = Y2 := by rw [← hc, hY]
    have hne : Y2 ≠ Y1 := by decide
    rw [hY']; simp [fullDecode, hne]
  · exact absurd hf (fullFeasible_zero T)

/-- **The full-read-set placement model.**  A concrete `PlacementModel` on the
witness candidate universe: orbit is candidate-index equality, the feasibility
predicate is the literal historical `I_s`, consistency is exact agreement of the
induced read set, and the decoder is `fullDecode`. -/
def fullModel : PlacementModel (Fin 3) (fun _ => Finset (Fin 4)) Obs where
  orbit := fun a b => a = b
  orbit_equiv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩
  decode := fullDecode
  feasible := fullFeasible
  consistent := fullConsistent
  decode_correct := fullDecode_correct

/-! ## The weighted placement mass -/

/-- If no placement is both consistent with `Y` and literally feasible, the
weighted mass of `g` at `Y` is zero. -/
theorem fullJoint_eq_zero_of (Y : Obs) (g : Fin 3)
    (h : ∀ T : Finset (Fin 4), ¬ (fullConsistent g T Y ∧ fullFeasible g T)) :
    placementJoint fullModel fullWeight Y g = 0 := by
  unfold placementJoint fullModel
  apply Finset.sum_eq_zero
  intro T _
  rw [if_neg (h T)]

/-- Candidate `0` never induces the full read set `Y1` (its window types omit
`11`), so its literal placement mass at `Y1` is zero. -/
theorem obs_zero_ne_Y1 : ∀ T : Finset (Fin 4),
    observedTypes_ofFinset (genOf 0) 2 T ≠ Y1 := by decide

/-- Candidate `2` never induces the full read set `Y1` (its window types are only
`01`, `10`). -/
theorem obs_two_ne_Y1 : ∀ T : Finset (Fin 4),
    observedTypes_ofFinset (genOf 2) 2 T ≠ Y1 := by decide

/-- The only placement on candidate `1` inducing the full read set `Y1` is the
saturated placement. -/
theorem obs_one_eq_Y1_iff : ∀ T : Finset (Fin 4),
    observedTypes_ofFinset (genOf 1) 2 T = Y1 ↔ T = Tfull := by decide

/-- Candidate `0` has zero literal placement mass at `Y1`. -/
theorem fullJoint_Y1_zero_zero : placementJoint fullModel fullWeight Y1 0 = 0 := by
  apply fullJoint_eq_zero_of
  intro T hc
  exact obs_zero_ne_Y1 T hc.1

/-- Candidate `2` has zero literal placement mass at `Y1`. -/
theorem fullJoint_Y1_zero_two : placementJoint fullModel fullWeight Y1 2 = 0 := by
  apply fullJoint_eq_zero_of
  intro T hc
  exact obs_two_ne_Y1 T hc.1

/-- The saturated placement on the truth candidate is literally feasible. -/
theorem fullFeasible_one_saturated : fullFeasible 1 Tfull := by decide

/-- The truth candidate `1` has strictly positive literal placement mass at its
full read set `Y1` (the saturated placement contributes `(1/4)^4`). -/
theorem fullJoint_Y1_pos_one : 0 < placementJoint fullModel fullWeight Y1 1 := by
  unfold placementJoint fullModel
  have hcond : fullConsistent 1 Tfull Y1 ∧ fullFeasible 1 Tfull := ⟨by decide, by decide⟩
  have hsum :
      (∑ T : Finset (Fin 4),
          (if fullConsistent 1 T Y1 ∧ fullFeasible 1 T then fullWeight 1 T else 0))
        = (if fullConsistent 1 Tfull Y1 ∧ fullFeasible 1 Tfull
            then fullWeight 1 Tfull else 0) := by
    apply Finset.sum_eq_single Tfull
    · intro T _ hne
      rw [if_neg]
      intro hc
      exact hne ((obs_one_eq_Y1_iff T).mp hc.1)
    · intro h
      exact absurd (Finset.mem_univ Tfull) h
  rw [hsum, if_pos hcond]
  unfold fullWeight; positivity

/-- **The full-read-set placement mass is supported on the truth orbit.** -/
theorem fullReadSet_support :
    placementJoint fullModel fullWeight Y1 0 = 0 ∧
      placementJoint fullModel fullWeight Y1 2 = 0 ∧
      0 < placementJoint fullModel fullWeight Y1 1 :=
  ⟨fullJoint_Y1_zero_zero, fullJoint_Y1_zero_two, fullJoint_Y1_pos_one⟩

/-- The full read set `Y1` is exactly the read set induced by the saturated
placement on the truth candidate. -/
theorem Y1_eq_observedTypes :
    observedTypes_ofFinset (genOf 1) 2 Tfull = Y1 := by decide

/-- `Y1` is the *full* observed read set: every oriented length-`2` string. -/
theorem Y1_eq_univ : Y1 = (Finset.univ : Obs) := by decide

/-! ## Conditional posterior certainty at the full read set (merged #266 theorem) -/

/-- The placement-level conditional mass of the decoder's orbit equals the total
placement mass at `Y1` — the merged `ConditionalIdentifiability` theorem
`placement_posterior_certain`, applied by name. -/
theorem fullReadSet_orbit_mass_eq_total :
    (∑ g : Fin 3, if fullModel.orbit g (fullModel.decode Y1)
        then placementJoint fullModel fullWeight Y1 g else 0)
      = ∑ g : Fin 3, placementJoint fullModel fullWeight Y1 g :=
  placement_posterior_certain fullModel fullWeight Y1

/-- **Full-read-set conditional recovery is certain.**  The conditional posterior
on the truth orbit `1` under the literal weighted placement mass is exactly `1`
at the full read set `Y1`. -/
theorem fullReadSet_posterior_eq_one :
    placementJoint fullModel fullWeight Y1 1 /
        (∑ g : Fin 3, placementJoint fullModel fullWeight Y1 g) = 1 := by
  have htotal : (∑ g : Fin 3, placementJoint fullModel fullWeight Y1 g)
      = placementJoint fullModel fullWeight Y1 1 := by
    rw [Fin.sum_univ_three, fullJoint_Y1_zero_zero, fullJoint_Y1_zero_two]
    ring
  rw [htotal]
  exact div_self (ne_of_gt fullJoint_Y1_pos_one)

/-! ## The precise boundary: the single-read witness does not lift

The adapter's `(A)`-side event is built from the placement-based
`InformationFeasible` at the two-start placement `{0,2}`, which is *not* the
literal historical predicate, and no singleton observed read set carries literal
placement mass.  This locates exactly where the single-read separation and the
literal full-read-set mass separate. -/

/-- **The witness's placement is `InformationFeasible` but not literal.** -/
theorem witness_placement_not_literal :
    InformationFeasible (genOf 1) 2 ({0, 2} : Finset (Fin 4)) ∧
      ¬ HistoricalInformationFeasibleLiteral (genOf 1) 2 ({0, 2} : Finset (Fin 4)) :=
  ⟨feasible_genOf_one, by decide⟩

/-- **The literal weighted placement mass vanishes at every single-read
observation.**  Literal feasibility forces coverage, which forces the window-type
image (of cardinality `≥ 2`) into the observed read set; a singleton cannot
contain it.  Hence the single-read `(A ∧ ¬B)` separation cannot be reproduced by
the literal full-read-set mass at the same observation. -/
theorem fullJoint_singleton_eq_zero (w : Read) (g : Fin 3) :
    placementJoint fullModel fullWeight ({w} : Obs) g = 0 := by
  apply fullJoint_eq_zero_of
  intro T hc
  have hcov : HistoricalCovers (genOf g) 2 (observedTypes_ofFinset (genOf g) 2 T) := hc.2.1
  have hsub : winImg g ⊆ observedTypes_ofFinset (genOf g) 2 T := coverage_window_mem g T hcov
  have hcard : 2 ≤ (observedTypes_ofFinset (genOf g) 2 T).card :=
    le_trans (winImg_card_ge g) (Finset.card_le_card hsub)
  rw [hc.1] at hcard
  simp only [Finset.card_singleton] at hcard
  omega

/-- **Packaged boundary.**  At the truth's full read set the literal mass is
certain on orbit `1`; at any single-read observation the literal mass is
identically zero; and the witness's own feasible placement is not literal. -/
theorem fullReadSet_boundary :
    placementJoint fullModel fullWeight Y1 1 /
        (∑ g : Fin 3, placementJoint fullModel fullWeight Y1 g) = 1 ∧
      (∀ (w : Read) (g : Fin 3), placementJoint fullModel fullWeight ({w} : Obs) g = 0) ∧
      InformationFeasible (genOf 1) 2 ({0, 2} : Finset (Fin 4)) ∧
      ¬ HistoricalInformationFeasibleLiteral (genOf 1) 2 ({0, 2} : Finset (Fin 4)) :=
  ⟨fullReadSet_posterior_eq_one, fullJoint_singleton_eq_zero,
    witness_placement_not_literal.1, witness_placement_not_literal.2⟩

/-! ## Kernel-checking boundary -/

#print axioms fullFeasible_zero
#print axioms fullDecode_correct
#print axioms fullModel
#print axioms fullJoint_eq_zero_of
#print axioms fullJoint_Y1_zero_zero
#print axioms fullJoint_Y1_zero_two
#print axioms fullJoint_Y1_pos_one
#print axioms fullReadSet_support
#print axioms fullReadSet_orbit_mass_eq_total
#print axioms fullReadSet_posterior_eq_one
#print axioms witness_placement_not_literal
#print axioms fullJoint_singleton_eq_zero
#print axioms fullReadSet_boundary

end AssemblyP1.ConditionalVsMLFullReadSet271
