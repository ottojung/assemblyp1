import Mathlib
import AssemblyP1.SourceFaithfulIs
import AssemblyP1.ShortFiniteMLCounterexamples

/-!
# Short finite-read ML counterexample: true length 5 (`G = 5` cell)

This module kernel-checks one further cell of the general family
truth `A^{G-1}T` vs competitor `A^G T` at `L = G - 1` (board issue #300),
under the same **source-faithful oriented single-strand** reading as
`AssemblyP1/ShortFiniteMLCounterexamples.lean` (whose `G = 2, 3, 4` cells
it extends, and whose layer definitions it reuses):

* truth `S = AAAAT` (`|S| = 5`, reusing `genAAAAT`);
* competitor `D = AAAAAT` (`|D| = 6`);
* observation: one read from every true starting position, plus one extra
  read from start `0`, i.e. `AAAA, AAAT, AATA, ATAA, TAAA, AAAA`;
* exact ordered-read likelihoods `P(R|S) = (1/5)^6 = 1/15625` and
  `P(R|D) = (2/6)^2 (1/6)^4 = 1/11664`, ratio `15625/11664 > 1`.

The truth carries three maximal triple repeats (two of length `1` and one
of length `2`); all are bridged by the length-`4` reads, and there is no
interleaved pair of maximal repeats.  No minimality is claimed.
-/

namespace AssemblyP1.ShortFiniteMLCounterexamplesG5

open AssemblyP1.SourceFaithfulIs
open AssemblyP1.ShortFiniteMLCounterexamples

/-! ## The `G = 5` genomes -/

/-- The `G = 5` competitor `AAAAAT` (`A^5 T`, length `6`). -/
abbrev genAAAAAT : Genome Base where
  len := 6
  len_pos := by norm_num
  sym := ![.A, .A, .A, .A, .A, .T]

/-- Candidate-intrinsic lengths are explicit (`genAAAAT` is the length-`5`
truth, reused from the base module). -/
theorem len_AAAAT_5 : genAAAAT.len = 5 := rfl
theorem len_AAAAAT : genAAAAAT.len = 6 := rfl

/-! ## Read types, observation, and spectra (`L = 4`) -/

/-- Length-`4` read types. -/
abbrev wAAAA : Read 4 := ![.A, .A, .A, .A]
abbrev wAAAT : Read 4 := ![.A, .A, .A, .T]
abbrev wAATA : Read 4 := ![.A, .A, .T, .A]
abbrev wATAA : Read 4 := ![.A, .T, .A, .A]
abbrev wTAAA : Read 4 := ![.T, .A, .A, .A]

/-- Realized start set (the support of the sample). -/
def rs5 : Finset (Fin 5) := {0, 1, 2, 3, 4}

/-- The realized placements: one read from every true start, plus one extra
from start `0`. -/
def reads5 : List (Fin 5) := [0, 1, 2, 3, 4, 0]

/-- Observed read types for `G = 5`. -/
def ws5 : List (Read 4) := [wAAAA, wAAAT, wAATA, wATAA, wTAAA, wAAAA]

/-- The observation really is the windows of the realized placements. -/
theorem observed_reads5 : observed genAAAAT 4 reads5 = ws5 := by decide

/-! ### Spectra -/

theorem spec_AAAAT_4_AAAA : spec genAAAAT 4 wAAAA = 1 := by simp only [spec]; decide
theorem spec_AAAAT_4_AAAT : spec genAAAAT 4 wAAAT = 1 := by simp only [spec]; decide
theorem spec_AAAAT_4_AATA : spec genAAAAT 4 wAATA = 1 := by simp only [spec]; decide
theorem spec_AAAAT_4_ATAA : spec genAAAAT 4 wATAA = 1 := by simp only [spec]; decide
theorem spec_AAAAT_4_TAAA : spec genAAAAT 4 wTAAA = 1 := by simp only [spec]; decide
theorem spec_AAAAAT_4_AAAA : spec genAAAAAT 4 wAAAA = 2 := by simp only [spec]; decide
theorem spec_AAAAAT_4_AAAT : spec genAAAAAT 4 wAAAT = 1 := by simp only [spec]; decide
theorem spec_AAAAAT_4_AATA : spec genAAAAAT 4 wAATA = 1 := by simp only [spec]; decide
theorem spec_AAAAAT_4_ATAA : spec genAAAAAT 4 wATAA = 1 := by simp only [spec]; decide
theorem spec_AAAAAT_4_TAAA : spec genAAAAAT 4 wTAAA = 1 := by simp only [spec]; decide

/-! ## The full source-faithful information-feasibility predicate `I_s` -/

theorem truth_information_feasible_5 :
    InformationFeasible genAAAAT 4 rs5 := by decide

/-! ### The maximal triple repeats and their bridging

The length-`5` truth carries three maximal triple repeats: two of length
`1` and one of length `2`.  All copies are bridged by the length-`4`
reads (the bound `e + 2 ≤ L` holds for both `e = 1` and `e = 2`). -/

theorem triple_repeat_5a : genAAAAT.IsTripleRepeat 1 0 1 3 := by decide
theorem triple_repeat_5b : genAAAAT.IsTripleRepeat 1 0 2 3 := by decide
theorem triple_repeat_5c : genAAAAT.IsTripleRepeat 2 0 1 2 := by decide

theorem triple_repeat_all_bridged_5a :
    IsTripleRepeatAllBridged genAAAAT 4 rs5 1 0 1 3 := by decide
theorem triple_repeat_all_bridged_5b :
    IsTripleRepeatAllBridged genAAAAT 4 rs5 1 0 2 3 := by decide
theorem triple_repeat_all_bridged_5c :
    IsTripleRepeatAllBridged genAAAAT 4 rs5 2 0 1 2 := by decide

/-- The `G = 5` truth has no interleaved pair of maximal repeats. -/
theorem no_interleaved_5 :
    ∀ (e₁ e₂ : Fin genAAAAT.len) (a b c d : Fin genAAAAT.len),
      ¬ (genAAAAT.IsRepeat e₁.val a b ∧ genAAAAT.IsRepeat e₂.val c d ∧
          Interleaved genAAAAT a b c d) := by
  decide

/-! ## Section 6.2 feasibility -/

/-- Truth walk for `G = 5`: spells `AAAAT`. -/
def walkS5 : List (Read 4) := [wAAAA, wAAAT, wAATA, wATAA, wTAAA]
/-- Competitor walk for `G = 5`: spells `AAAAAT`. -/
def walkD5 : List (Read 4) := [wAAAA, wAAAA, wAAAT, wAATA, wATAA, wTAAA]

theorem circuit_S5 : IsCircuit 4 walkS5 := by decide
theorem circuit_D5 : IsCircuit 4 walkD5 := by decide

/-- The truth walk's type counts are the truth spectrum (`G = 5`). -/
theorem counts_S5 : ∀ c : Read 4, listCount walkS5 c = spec genAAAAT 4 c := by decide
/-- The competitor walk's type counts are the competitor spectrum (`G = 5`). -/
theorem counts_D5 : ∀ c : Read 4, listCount walkD5 c = spec genAAAAAT 4 c := by decide

theorem truth_perVertex_5 : PerVertexFeasible (spec genAAAAT 4) (obsCount genAAAAT 4 reads5) := by
  unfold PerVertexFeasible; decide
theorem competitor_perVertex_5 : PerVertexFeasible (spec genAAAAAT 4) (obsCount genAAAAT 4 reads5) := by
  unfold PerVertexFeasible; decide
theorem truth_spelled_5 : SpelledFeasible62 (spec genAAAAT 4) (obsCount genAAAAT 4 reads5) := by
  unfold SpelledFeasible62 PerVertexFeasible; decide
theorem competitor_spelled_5 : SpelledFeasible62 (spec genAAAAAT 4) (obsCount genAAAAT 4 reads5) := by
  unfold SpelledFeasible62 PerVertexFeasible; decide
theorem truth_section62_5 : Section62Feasible 4 walkS5 (spec genAAAAT 4) (obsCount genAAAAT 4 reads5) :=
  ⟨circuit_S5, counts_S5, by decide⟩
theorem competitor_section62_5 : Section62Feasible 4 walkD5 (spec genAAAAAT 4) (obsCount genAAAAT 4 reads5) :=
  ⟨circuit_D5, counts_D5, by decide⟩

/-! ## Exact ordered-read likelihoods and strict ratio -/

/-- `G = 5`: truth likelihood `(1/5)^6 = 1/15625`. -/
theorem lik_truth_5 : orderedLik genAAAAT 4 ws5 = 1 / 15625 := by
  simp only [orderedLik, ws5, spec_AAAAT_4_AAAA, spec_AAAAT_4_AAAT,
    spec_AAAAT_4_AATA, spec_AAAAT_4_ATAA, spec_AAAAT_4_TAAA,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  norm_num

/-- `G = 5`: competitor likelihood `(2/6)^2 (1/6)^4 = 1/11664`. -/
theorem lik_competitor_5 : orderedLik genAAAAAT 4 ws5 = 1 / 11664 := by
  simp only [orderedLik, ws5, spec_AAAAAT_4_AAAA, spec_AAAAAT_4_AAAT,
    spec_AAAAAT_4_AATA, spec_AAAAAT_4_ATAA, spec_AAAAAT_4_TAAA,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  norm_num

/-- `G = 5` exact ratio `15625/11664 > 1`. -/
theorem ratio_5 : orderedLik genAAAAAT 4 ws5 / orderedLik genAAAAT 4 ws5 = 15625 / 11664 := by
  rw [lik_competitor_5, lik_truth_5]; norm_num

theorem candidate_strictly_better_5 : orderedLik genAAAAT 4 ws5 < orderedLik genAAAAAT 4 ws5 := by
  rw [lik_truth_5, lik_competitor_5]; norm_num

theorem multinom_ratio_5 :
    multinomLik genAAAAAT 4 ws5 / multinomLik genAAAAT 4 ws5 = 15625 / 11664 := by
  rw [multinomLik_ratio, ratio_5]

/-! ## The endpoint -/

/-- **`G = 5`, `L = 4` witness.** The truth `AAAAT` is information-feasible
(at full strength, with three bridged maximal triple repeats and no
interleaved pair); both `AAAAT` and the competitor `AAAAAT` are genuinely
§6.2-feasible (per-vertex, spelled, and closed-walk circuit); the competitor
has strictly greater exact ordered-read likelihood, ratio `15625/11664`. -/
theorem short_finite_ml_counterexample_5 :
    InformationFeasible genAAAAT 4 rs5 ∧
      Section62Feasible 4 walkS5 (spec genAAAAT 4) (obsCount genAAAAT 4 reads5) ∧
      Section62Feasible 4 walkD5 (spec genAAAAAT 4) (obsCount genAAAAT 4 reads5) ∧
      SpelledFeasible62 (spec genAAAAT 4) (obsCount genAAAAT 4 reads5) ∧
      SpelledFeasible62 (spec genAAAAAT 4) (obsCount genAAAAT 4 reads5) ∧
      genAAAAT.len = 5 ∧ genAAAAAT.len = 6 ∧
      orderedLik genAAAAT 4 ws5 < orderedLik genAAAAAT 4 ws5 ∧
      orderedLik genAAAAAT 4 ws5 / orderedLik genAAAAT 4 ws5 = 15625 / 11664 :=
  ⟨truth_information_feasible_5, truth_section62_5, competitor_section62_5,
    truth_spelled_5, competitor_spelled_5, len_AAAAT_5, len_AAAAAT,
    candidate_strictly_better_5, ratio_5⟩

end AssemblyP1.ShortFiniteMLCounterexamplesG5
