import Mathlib
import AssemblyP1.SourceFaithfulIs
import AssemblyP1.SameLengthSection62Counterexample
import AssemblyP1.PerOccurrenceSameLengthCounterexample

/-!
# Historical read-string coverage for the two same-length §6.2 witnesses

This file is the lane-**247c** deliverable of Antonina issue #247: it adds
**historical read-string coverage** certificates to the two genuine same-length
Section 6.2 molecule-flow witnesses, reusing their existing Lean flow
certificates unchanged.

The two witnesses, both already kernel-checked for genuine MB09 §6.2
bidirected-flow feasibility and for strict molecule-class likelihood advantages:

| witness | truth `S` | competitor `D` | `G` | `L` | sampled starts | exact ratio | binomial ratio |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `W1` | `AAATAT` | `AAAAAT` | `6` | `3` | `[0,0,1,3,5]` | `3` | `5` |
| `W2` (per-occurrence) | `ATATACAC` | `ATACACAC` | `8` | `3` | `[1,3,4,5,6,7]` | `3/2` | `9/5` |

## What is new here, and what is reused

* **New:** the historical coverage predicate `HistoricalCovers` (stated exactly
  as issue #247 PART 2 specifies), the sufficient certificate
  `DenseSampledStarts`, the adapter `denseSampledStarts_historicalCovers`, the
  incomparability regressions against the old `Covers`, and the per-witness
  historical coverage proofs and endpoint theorems.
* **Reused unchanged:** every §6.2 flow certificate
  (`SpelledFeasible62`, the written-out circuits, the throughput/spectrum
  identities) and every objective (the literal §6.1 binomial `lik` and the
  exact multinomial `exactLik`) are the existing theorems of
  `AssemblyP1.SameLengthSection62Counterexample` and
  `AssemblyP1.PerOccurrenceSameLengthCounterexample`, referenced, not
  re-proved.  The exact, binomial and flow predicates stay separate, as in
  those files.

## The historical coverage predicate, and the bridge note

Issue #247 PART 2 asks for

> `HistoricalCovers S L observedTypes`: for `2 ≤ L ≤ G`, `∀ t : Fin G`,
> `∃` observed word `w` and `δ < L − 1`, `w = circularWindow S L ((t+δ)%G)`.

This is the Shomorony et al. (2016) supplement §6.4 Definition 1 reading: every
circular interval of `L − 1` starts contains a match of an **observed read
string**, not merely a base covered by a read placed at a sampled start.  The
source's 1-based interval `[t, t+L−2]` is translated here to the 0-based
`Fin G` index `t` with offset `δ : Fin (L−1)`, i.e. `δ ∈ [0, L−2]`, and the
window is read cyclically at `(t+δ) % G`.

The foundational historical-coverage module is owned by another worker (lane
247a) and is deliberately **not** edited here.  Until that module appears, the
predicate is stated locally in this file, in the exact form above, so that the
bridge to the shared module is a one-line `Iff`: replace the local
`HistoricalCovers` by the shared one and every theorem in this file stands.
When the shared module appears, (1) import it, (2) prove
`HistoricalCovers S L observed ↔ Shared.HistoricalCovers S L observed` (or
whatever its signature is), and (3) delete the local definition.  No theorem
statement or proof in this file needs to change.

The observed word set is derived from the **sampled read multiset** by
`observedWords`: the distinct strands `S.window L r` over the sampled starts
`r`.  Sampled multiplicities are deliberately not part of coverage (they are
recorded by the read-type counts `obs`, which the likelihood consumes); this is
the "do not conflate observed read types, sampled starts, or matching
occurrences" discipline of PART 2.

## Scope

Finite instances only.  This file does not settle which Medvedev–Brudno object
the Shomorony et al. sentence intends, nor the per-occurrence strengthening as
a source rule (it is a project-level strengthening, refuted by `W2`), nor the
single-strand reading, nor the variable-length case.
-/

set_option maxHeartbeats 4000000

namespace AssemblyP1.HistoricalCoverageSameLength

open SourceFaithfulIs

/-! ## The historical coverage predicate (local; see the bridge note above) -/

/-- Historical read-string coverage (Shomorony et al. 2016, supplement §6.4
Definition 1), stated exactly as issue #247 PART 2 specifies.

For `2 ≤ L ≤ G`, every circular position `t` has some observed read word `w`
and some offset `δ < L − 1` such that `w` equals the length-`L` circular window
of `S` at `(t+δ) % G`.  The observed words are the distinct strands sampled at
the realized starts; repeats may match at unsampled positions, which is what
distinguishes this from the old `Covers`. -/
def HistoricalCovers {α : Type*} [DecidableEq α] (S : SourceFaithfulIs.Genome α)
    (L : ℕ) (observed : Finset (Fin L → α)) : Prop :=
  2 ≤ L → L ≤ S.len → ∀ t : Fin S.len,
    ∃ w ∈ observed, ∃ δ : Fin (L - 1),
      w = S.window L ⟨(t.val + δ.val) % S.len, Nat.mod_lt _ S.len_pos⟩

/-- The observed read words derived from a sampling realization: the distinct
length-`L` strands at the sampled starts.  Multiplicities collapse here by
design; they live in the read-type counts. -/
def observedWords {α : Type*} [DecidableEq α] (S : SourceFaithfulIs.Genome α)
    (L : ℕ) (R : Finset (Fin S.len)) : Finset (Fin L → α) :=
  R.image (fun r => S.window L r)

/-- The **matching start set** `MatchStarts`: every circular position at which
some observed read string occurs.  This is the set of *all* positions matching
an observed word, as opposed to the sampled starts; repeats make the two
differ in general.  Historical bridging is quantified over this set. -/
def MatchStarts {α : Type*} [DecidableEq α] (S : SourceFaithfulIs.Genome α)
    (L : ℕ) (observed : Finset (Fin L → α)) : Finset (Fin S.len) :=
  Finset.univ.filter (fun t => S.window L t ∈ observed)

/-- **The full historical information-feasible predicate** `HistoricalInformationFeasible`:
historical read-string coverage (§6.4 Definition 1) **and** historical
bridging (every maximal triple repeat all-bridged and every interleaved pair of
repeats bridged, with the bridging reads placed at the *matching* positions
`MatchStarts` rather than only at the sampled starts).

The source requires BOTH conjuncts.  The bridging conjunct reuses the existing
`SourceFaithfulIs.InformationFeasible` predicate, applied to `MatchStarts`; no
bridging definition is duplicated.  When the matching start set is *saturated*
(equal to the sampled starts, as for both witnesses here), this conjunct is
discharged by the existing full `InformationFeasible` certificate over the
sampled starts.

This is a local definition, stated to be coordinated with the true historical
`I_s` predicates being repaired on PR135 (agent 247f20261009) so that no
duplicate definition is introduced; when that shared module appears, bridge
`HistoricalInformationFeasible` to it and delete the local one. -/
def HistoricalInformationFeasible {α : Type*} [DecidableEq α]
    (S : SourceFaithfulIs.Genome α) (L : ℕ) (observed : Finset (Fin L → α)) : Prop :=
  HistoricalCovers S L observed ∧
    SourceFaithfulIs.InformationFeasible S L (MatchStarts S L observed)

instance {α : Type*} [DecidableEq α] (S : SourceFaithfulIs.Genome α) (L : ℕ)
    (observed : Finset (Fin L → α)) :
    Decidable (HistoricalCovers S L observed) := by
  unfold HistoricalCovers; infer_instance

/-! ## The sufficient certificate `DenseSampledStarts` -/

/-- A useful **sufficient** certificate for historical coverage (PART 2, PART 3):
the distinct sampled starts are dense on the circle, i.e. every position `t`
is within `L − 1` steps of a sampled start.  This is not an equivalent
definition — with repeats, historical coverage can hold without start density
(the reverse implication fails). -/
def DenseSampledStarts (G L : ℕ) (R : Finset (Fin G)) : Prop :=
  2 ≤ L → L ≤ G → ∀ t : Fin G,
    ∃ r ∈ R, ∃ δ : Fin (L - 1), r.val = (t.val + δ.val) % G

instance (G L : ℕ) (R : Finset (Fin G)) :
    Decidable (DenseSampledStarts G L R) := by
  unfold DenseSampledStarts; infer_instance

/-- Windows at two starts with equal values are equal (the window reads the
circle modulo `S.len`). -/
theorem window_eq_of_val_eq {α : Type*} [DecidableEq α]
    (S : SourceFaithfulIs.Genome α) (L : ℕ) (r r' : Fin S.len)
    (h : r.val = r'.val) : S.window L r = S.window L r' := by
  funext d
  simp [SourceFaithfulIs.Genome.window, SourceFaithfulIs.Genome.cycl, h]

/-- **The adapter (PART 3).**  `DenseSampledStarts` implies `HistoricalCovers`
for the observed words derived from the same sampling realization.  Only this
direction is valid in general; the reverse fails with repeats. -/
theorem denseSampledStarts_historicalCovers {α : Type*} [DecidableEq α]
    (S : SourceFaithfulIs.Genome α) (L : ℕ) (R : Finset (Fin S.len))
    (h : DenseSampledStarts S.len L R) :
    HistoricalCovers S L (observedWords S L R) := by
  intro h2 hL t
  obtain ⟨r, hr, δ, hδ⟩ := h h2 hL t
  refine ⟨S.window L r, ?_, δ, ?_⟩
  · apply Finset.mem_image.mpr
    exact ⟨r, hr, rfl⟩
  · apply window_eq_of_val_eq
    exact hδ

/-! ## Regressions: historical coverage and old `Covers` are incomparable

The two tiny test cases of the #247 source audit, kernel-checked here so the
distinction between the historical and the old base-coverage models is
computable, not just asserted.  Both use the four-symbol DNA alphabet of the
per-occurrence witness. -/

/-- Regression A: `S = AAAA`, `G = 4`, `L = 3`, only `AAA` sampled at start `0`.
Historical coverage holds (every window is `AAA`, which is observed), but the
old `Covers` fails because base `3` is never covered at the sampled placement. -/
abbrev regA : SourceFaithfulIs.Genome PerOccurrenceSameLengthCounterexample.Base where
  len := 4
  len_pos := by norm_num
  sym := ![.A, .A, .A, .A]

def regA_observed : Finset (Fin 3 → PerOccurrenceSameLengthCounterexample.Base) :=
  {![.A, .A, .A]}

theorem regA_historicalCovers : HistoricalCovers regA 3 regA_observed := by
  unfold HistoricalCovers regA regA_observed
  decide

theorem regA_not_covers : ¬ SourceFaithfulIs.Covers regA 3 ({0} : Finset (Fin 4)) := by
  unfold SourceFaithfulIs.Covers regA
  decide

/-- Regression B: `S = ACGT`, `G = 4`, `L = 2`, sampled starts `{0, 2}`
(`AC`, `GT`).  Old `Covers` holds, but historical coverage fails: the length-`1`
start intervals at `1` and `3` contain no observed word match (`CG` and `TA`
were never sampled). -/
abbrev regB : SourceFaithfulIs.Genome PerOccurrenceSameLengthCounterexample.Base where
  len := 4
  len_pos := by norm_num
  sym := ![.A, .C, .G, .T]

def regB_observed : Finset (Fin 2 → PerOccurrenceSameLengthCounterexample.Base) :=
  {![.A, .C], ![.G, .T]}

theorem regB_covers : SourceFaithfulIs.Covers regB 2 ({0, 2} : Finset (Fin 4)) := by
  unfold SourceFaithfulIs.Covers regB
  decide

theorem regB_not_historicalCovers : ¬ HistoricalCovers regB 2 regB_observed := by
  unfold HistoricalCovers regB regB_observed
  decide

/-! ## Witness `W1`: `AAATAT → AAAAAT` (per-vertex §6.2 reading) -/

namespace W1

open AssemblyP1.SameLengthSection62Counterexample
open AssemblyP1.Section62Flow

/-- The distinct sampled starts of `W1`: `{0, 1, 3, 5}`. -/
def starts : Finset (Fin 6) := {0, 1, 3, 5}

/-- The realized distinct-start set is exactly the distinct entries of the
sampling realization `[0,0,1,3,5]`. -/
theorem starts_eq_readStarts : starts = readStarts.toFinset := by
  decide

/-- `W1` is start-dense: every position is within `L − 1 = 2` of a sampled
start (cyclic gaps of `{0,1,3,5}` are `1,2,2,1`). -/
theorem dense : DenseSampledStarts 6 3 readStarts.toFinset := by
  decide

/-- **Historical coverage holds for `W1`.**  Via the adapter, from start
density; the observed words are the strands `AAA, AAT, TAT, TAA` sampled at
`[0,0,1,3,5]`. -/
theorem historicalCovers :
    HistoricalCovers truthGenome 3 (observedWords truthGenome 3 readStarts.toFinset) :=
  denseSampledStarts_historicalCovers truthGenome 3 readStarts.toFinset dense

/-- **The matching start set of `W1` is saturated**: every position matching an
observed word is a sampled start, `MatchStarts = {0,1,3,5}`.  (The windows are
`AAA,AAT,ATA,TAT,ATA,TAA`; only `ATA` at positions `2` and `4` fails to be
observed.) -/
theorem matchStarts_eq :
    MatchStarts truthGenome 3 (observedWords truthGenome 3 readStarts.toFinset) = {0, 1, 3, 5} := by
  decide

/-- **The full historical `I_s` holds for `W1`.**  Historical coverage (above)
and historical bridging: because the matching start set is saturated, the
bridging over `MatchStarts` is exactly the bridging over the sampled starts,
which the existing `information_feasible` certificate proves at full strength. -/
theorem w1_historical_information_feasible :
    HistoricalInformationFeasible truthGenome 3 (observedWords truthGenome 3 readStarts.toFinset) :=
  ⟨historicalCovers, by
    rw [matchStarts_eq]
    exact truth_information_feasible⟩

/-- The historical same-length maximality sentence: **full historical `I_s`**
(historical coverage *and* historical bridging) + same candidate length +
genuine §6.2 spelled feasibility of both candidates ⇒ the truth's likelihood is
at least the competitor's. -/
def HistoricalSameLengthMaximality : Prop :=
  (HistoricalInformationFeasible truthGenome 3 (observedWords truthGenome 3 readStarts.toFinset) ∧
      genomeLength truth = genomeLength competitor ∧
      SpelledFeasible62 Base Strand3 toList3 rep3 rc3 readLen oMin readVerts
        spellTruth truthCircuitFlow noTerm dS' ∧
      SpelledFeasible62 Base Strand3 toList3 rep3 rc3 readLen oMin readVerts
        spellCompetitor competitorCircuitFlow noTerm dD') →
    lik obs dD ≤ lik obs dS

/-- **Coverage-only endpoint (weaker; subsumed by the full-`I_s` endpoint
below).**  Historical read-string coverage alone (the §6.4 Definition 1
reading) holds; the competing candidate is a single spelled molecule of exactly
the same length as the truth; both are genuine §6.2 spelled candidates
(certificates reused unchanged from
`AssemblyP1.SameLengthSection62Counterexample`); and the competitor strictly
beats the truth under both the literal §6.1 binomial objective (ratio `5`) and
the exact same-length multinomial objective (ratio `3`). -/
theorem w1_historical_se62_flow_counterexample :
    HistoricalCovers truthGenome 3 (observedWords truthGenome 3 readStarts.toFinset) ∧
      (genomeLength truth = genomeLength competitor) ∧
      (SpelledFeasible62 Base Strand3 toList3 rep3 rc3 readLen oMin readVerts
          spellTruth truthCircuitFlow noTerm dS' ∧
        (SpelledFeasible62 Base Strand3 toList3 rep3 rc3 readLen oMin readVerts
            spellCompetitor competitorCircuitFlow noTerm dD' ∧
          (lik obs dS < lik obs dD ∧ exactLik dD obs / exactLik dS obs = 3))) :=
  ⟨historicalCovers, ⟨same_candidate_length,
    ⟨truth_spelled_feasible62, ⟨competitor_spelled_feasible62,
      ⟨competitor_strictly_better, exactLik_over_truth⟩⟩⟩⟩⟩

/-- **Kernel-checked historical finite counterexample for `W1` with the FULL
historical `I_s`.**  Historical coverage *and* historical bridging hold
(`w1_historical_information_feasible`); the competing candidate is a single
spelled molecule of exactly the same length as the truth; both are genuine §6.2
spelled candidates (certificates reused unchanged); and the competitor strictly
beats the truth under both the literal §6.1 binomial objective (ratio `5`) and
the exact same-length multinomial objective (ratio `3`). -/
theorem w1_historical_full_se62_flow_counterexample :
    HistoricalInformationFeasible truthGenome 3 (observedWords truthGenome 3 readStarts.toFinset) ∧
      (genomeLength truth = genomeLength competitor) ∧
      (SpelledFeasible62 Base Strand3 toList3 rep3 rc3 readLen oMin readVerts
          spellTruth truthCircuitFlow noTerm dS' ∧
        (SpelledFeasible62 Base Strand3 toList3 rep3 rc3 readLen oMin readVerts
            spellCompetitor competitorCircuitFlow noTerm dD' ∧
          (lik obs dS < lik obs dD ∧ exactLik dD obs / exactLik dS obs = 3))) :=
  ⟨w1_historical_information_feasible, ⟨same_candidate_length,
    ⟨truth_spelled_feasible62, ⟨competitor_spelled_feasible62,
      ⟨competitor_strictly_better, exactLik_over_truth⟩⟩⟩⟩⟩

/-- The full historical `I_s` same-length maximality sentence is false. -/
theorem w1_historical_maximality_refuted : ¬ HistoricalSameLengthMaximality := by
  intro h
  have h' := h ⟨w1_historical_information_feasible, same_candidate_length,
    truth_spelled_feasible62, competitor_spelled_feasible62⟩
  have := competitor_strictly_better
  linarith

end W1

/-! ## Witness `W2`: `ATATACAC → ATACACAC` (per-occurrence strengthening) -/

namespace W2

open AssemblyP1.PerOccurrenceSameLengthCounterexample
open AssemblyP1.Section62Flow

/-- The distinct sampled starts of `W2`: `{1, 3, 4, 5, 6, 7}`. -/
def starts : Finset (Fin 8) := {1, 3, 4, 5, 6, 7}

/-- The realized distinct-start set is exactly the distinct entries of the
sampling realization `[1,3,4,5,6,7]`. -/
theorem starts_eq_readStarts : starts = readStarts.toFinset := by
  decide

/-- `W2` is start-dense: every position is within `L − 1 = 2` of a sampled
start (cyclic gaps of `{1,3,4,5,6,7}` are `2,1,1,1,1,2`). -/
theorem dense : DenseSampledStarts 8 3 readStarts.toFinset := by
  decide

/-- **Historical coverage holds for `W2`.**  Via the adapter, from start
density; the observed words are the strands `TAT, TAC, ACA, CAC, CAT` sampled at
`[1,3,4,5,6,7]`. -/
theorem historicalCovers :
    HistoricalCovers truthGenome 3 (observedWords truthGenome 3 readStarts.toFinset) :=
  denseSampledStarts_historicalCovers truthGenome 3 readStarts.toFinset dense

/-- **The matching start set of `W2` is saturated**: `MatchStarts = {1,3,4,5,6,7}`,
the sampled starts.  (The windows are `ATA,TAT,ATA,TAC,ACA,CAC,ACA,CAT`; only
`ATA` at positions `0` and `2` fails to be observed.) -/
theorem matchStarts_eq :
    MatchStarts truthGenome 3 (observedWords truthGenome 3 readStarts.toFinset) = {1, 3, 4, 5, 6, 7} := by
  decide

/-- **The full historical `I_s` holds for `W2`.**  Historical coverage (above)
and historical bridging, the latter discharged by the existing full
`information_feasible` certificate because the matching start set is saturated. -/
theorem w2_historical_information_feasible :
    HistoricalInformationFeasible truthGenome 3 (observedWords truthGenome 3 readStarts.toFinset) :=
  ⟨historicalCovers, by
    rw [matchStarts_eq]
    exact truth_information_feasible⟩

/-- The per-occurrence same-length maximality sentence under the **full
historical `I_s`**. -/
def HistoricalPerOccurrenceSameLengthMaximality : Prop :=
  (HistoricalInformationFeasible truthGenome 3 (observedWords truthGenome 3 readStarts.toFinset) ∧
      genomeLength truth = genomeLength competitor ∧
      PerOccurrenceFeasible dS obs ∧
      SpelledFeasible62 Base W3 toList3 rep3 rc3 readLen oMin readVerts
        spellTruth truthCircuitFlow noTerm dS' ∧
      PerOccurrenceFeasible dD obs ∧
      SpelledFeasible62 Base W3 toList3 rep3 rc3 readLen oMin readVerts
        spellCompetitor competitorCircuitFlow noTerm dD') →
    lik obs dD ≤ lik obs dS

/-- **Coverage-only endpoint (weaker; subsumed by the full-`I_s` endpoint
below).** -/
theorem w2_historical_se62_flow_counterexample :
    HistoricalCovers truthGenome 3 (observedWords truthGenome 3 readStarts.toFinset) ∧
      (genomeLength truth = genomeLength competitor) ∧
      (PerOccurrenceFeasible dS obs ∧ PerOccurrenceFeasible dD obs) ∧
      SpelledFeasible62 Base W3 toList3 rep3 rc3 readLen oMin readVerts
        spellTruth truthCircuitFlow noTerm dS' ∧
      (SpelledFeasible62 Base W3 toList3 rep3 rc3 readLen oMin readVerts
          spellCompetitor competitorCircuitFlow noTerm dD' ∧
        (lik obs dS < lik obs dD ∧ exactLik dD obs / exactLik dS obs = 3 / 2)) :=
  ⟨historicalCovers, ⟨same_candidate_length,
    ⟨truth_peroccurrence, competitor_peroccurrence⟩, truth_spelled_feasible62,
    ⟨competitor_spelled_feasible62, ⟨competitor_strictly_better,
      exactLik_over_truth⟩⟩⟩⟩

/-- **Kernel-checked historical finite counterexample for `W2` with the FULL
historical `I_s`.**  Historical coverage *and* historical bridging hold
(`w2_historical_information_feasible`); the competing candidate is a single
spelled molecule of exactly the same length as the truth; both are genuine §6.2
spelled candidates and both satisfy the per-occurrence strengthening `d_w ≥ x_w`
(certificates reused unchanged); and the competitor strictly beats the truth
under both the literal §6.1 binomial objective (ratio `9/5`) and the exact
same-length multinomial objective (ratio `3/2`). -/
theorem w2_historical_full_se62_flow_counterexample :
    HistoricalInformationFeasible truthGenome 3 (observedWords truthGenome 3 readStarts.toFinset) ∧
      (genomeLength truth = genomeLength competitor) ∧
      (PerOccurrenceFeasible dS obs ∧ PerOccurrenceFeasible dD obs) ∧
      SpelledFeasible62 Base W3 toList3 rep3 rc3 readLen oMin readVerts
        spellTruth truthCircuitFlow noTerm dS' ∧
      (SpelledFeasible62 Base W3 toList3 rep3 rc3 readLen oMin readVerts
          spellCompetitor competitorCircuitFlow noTerm dD' ∧
        (lik obs dS < lik obs dD ∧ exactLik dD obs / exactLik dS obs = 3 / 2)) :=
  ⟨w2_historical_information_feasible, ⟨same_candidate_length,
    ⟨truth_peroccurrence, competitor_peroccurrence⟩, truth_spelled_feasible62,
    ⟨competitor_spelled_feasible62, ⟨competitor_strictly_better,
      exactLik_over_truth⟩⟩⟩⟩

/-- The full historical `I_s` per-occurrence same-length maximality sentence is
false. -/
theorem w2_historical_maximality_refuted :
    ¬ HistoricalPerOccurrenceSameLengthMaximality := by
  intro h
  have h' := h ⟨w2_historical_information_feasible, same_candidate_length,
    truth_peroccurrence, truth_spelled_feasible62, competitor_peroccurrence,
    competitor_spelled_feasible62⟩
  have := competitor_strictly_better
  linarith

end W2

end AssemblyP1.HistoricalCoverageSameLength
