import Mathlib
import AssemblyP1.SourceFaithfulIs

/-!
# Short finite-read ML counterexamples: true lengths 2, 3, 4

This module kernel-checks the three concrete finite-read counterexamples recorded
in board issue #300, under the same **source-faithful oriented single-strand**
reading used by `AssemblyP1/OrientedVariableLengthSe62.lean`:

* read *types* are the oriented length-`L` circular windows of the truth (no
  reverse-complement collapse);
* the truth `S` is the circular word `A^{G-1}T`, the competitor `D` is
  `A^{G}T`, so `|D| = G + 1 ≠ G` (candidate-intrinsic length is a free
  parameter);
* the observation is **one read from every true starting position, plus one
  extra read from start `0`**;
* the likelihood is the ordinary exact i.i.d. ordered-read likelihood
  `P(R | X) = ∏_{w ∈ R} (spec_L(X)(w) / |X|)`, i.e. the probability that the
  observed ordered list of read strings is produced by sampling each read's
  start uniformly from the candidate's `|X|` positions.

| `G` | `L` | truth `S` | competitor `D` | reads | `P(R|D)/P(R|S)` |
|---|---|---|---|---|---|
| 2 | 1 | `AT` | `AAT` | `A,A,T` | `32/27` |
| 3 | 2 | `AAT` | `AAAT` | `AA,AA,AT,TA` | `81/64` |
| 4 | 3 | `AAAT` | `AAAAT` | `AAA,AAA,AAT,ATA,TAA` | `4096/3125` |

For each instance the module proves, by finite `decide` on the *shared*
`SourceFaithfulIs.InformationFeasible` predicate at full strength (coverage,
every maximal triple repeat all-bridged, every interleaved pair of repeats
bridged, quantified over all repeat lengths and all selected starts):

* the truth is information-feasible (`truth_information_feasible_*`);
* both the truth and the competitor are genuinely §6.2-feasible, under the
  literal per-vertex lower bound `1` (`PerVertexFeasible`), the stronger spelled
  support-equality form (`SpelledFeasible62`), **and** the flow/circuit reading
  (`Section62Feasible`, an explicit closed walk of the oriented read-overlap
  graph whose per-type counts are the candidate's spectrum);
* the exact ordered-read likelihoods and their strict ratio
  (`lik_*`, `ratio_*`, `candidate_strictly_better_*`).

## The `L = 1` and `L = 2` edge cases, stated precisely

The issue requires that the two shortest instances not be mislabelled as
refuting a theorem that assumes a larger `L`.

* `SourceFaithfulIs.BridgesCopy` bridges a length-`e` copy only when a single
  read contains a base strictly before and strictly after the copy, so
  `SourceFaithfulIs.bridgesCopy_length` forces `e + 2 ≤ L` for any bridged copy.
  Hence for `L = 1` and `L = 2` **no** copy of length `e ≥ 1` can be bridged,
  and a truth carrying a maximal triple repeat could not be
  information-feasible. The `G = 2` truth `AT` and the `G = 3` truth `AAT`
  carry no maximal triple repeat at all, so their triple-repeat and
  interleaved-repeat clauses are **vacuous**; `InformationFeasible` then reduces
  to coverage. This module proves that vacuity explicitly
  (`no_triple_repeat_*`, `no_interleaved_*`) in addition to discharging the full
  predicate.
* The repository's same-length rigidity theorem
  (`AssemblyP1.OrientedSameLengthML`, `2 ≤ L ≤ G`) does **not** apply to the
  `G = 2, L = 1` instance (`L < 2`), and in any case that theorem is about
  *same-length* candidates whereas these witnesses are variable-length
  (`|D| = G + 1`). Nothing here is claimed to refute a same-length or
  `L ≥ 2` statement; the witnesses settle the **variable-candidate-length**
  question in the oriented, per-vertex-§6.2, source-faithful model.

No minimality is claimed: this module only exhibits the three witnesses and
computes their exact likelihood ratios.
-/

namespace AssemblyP1.ShortFiniteMLCounterexamples

open AssemblyP1.SourceFaithfulIs

/-! ## The alphabet and the read/window/spectrum layer -/

/-- Two-symbol alphabet. -/
inductive Base where
  | A
  | T
  deriving DecidableEq, Inhabited, Repr

instance : Fintype Base where
  elems := {Base.A, Base.T}
  complete := by intro x; cases x <;> simp

/-- A length-`L` oriented read type: the string of `L` symbols a read returns. -/
abbrev Read (L : ℕ) := Fin L → Base

/-- The number of starts of the circular genome `S` whose length-`L` window is
the read type `w`, i.e. the candidate-intrinsic spectrum coordinate `d_w`. -/
def spec (S : Genome Base) (L : ℕ) (w : Read L) : Nat :=
  (Finset.univ.filter (fun r : Fin S.len => S.window L r = w)).card

/-- The observed read types, in sampling order, of a list of realized start
positions in the truth `S`. -/
def observed (S : Genome Base) (L : ℕ) (reads : List (Fin S.len)) : List (Read L) :=
  reads.map (fun r => S.window L r)

/-- The number of observed reads of type `w`. -/
def obsCount (S : Genome Base) (L : ℕ) (reads : List (Fin S.len)) (w : Read L) : Nat :=
  (reads.filter (fun r => S.window L r = w)).length

/-- The count of `c` in the list `l`, via `DecidableEq` only (no `BEq`). -/
def listCount {α : Type} [DecidableEq α] (l : List α) (c : α) : Nat :=
  (l.filter (· = c)).length

/-- The ordinary exact ordered-read likelihood of a list of observed read types
under the candidate `S`: the product over the reads of the probability that a
start chosen uniformly from the candidate's `S.len` positions spells that read. -/
def orderedLik (S : Genome Base) (L : ℕ) (ws : List (Read L)) : ℚ :=
  (ws.map (fun w => (spec S L w : ℚ) / (S.len : ℚ))).prod

/-- The multinomial-count objective's combinatorial coefficient
`n! / ∏_w x_w!` for the observation `ws`.  It depends only on `ws`, so it
cancels in the truth/competitor ratio. -/
def multinomCoeff (L : ℕ) (ws : List (Read L)) : ℚ :=
  (Nat.factorial ws.length : ℚ) /
    (∏ w : Read L, (Nat.factorial (listCount ws w) : ℚ))

/-- The multinomial-count objective: the coefficient times the ordered-read
likelihood.  This is the MB09 §6.1 exact global read-count objective at
candidate-intrinsic length. -/
def multinomLik (S : Genome Base) (L : ℕ) (ws : List (Read L)) : ℚ :=
  multinomCoeff L ws * orderedLik S L ws

/-! ## The three genomes -/

/-- The `G = 2` truth `AT`. -/
abbrev genAT : Genome Base where
  len := 2
  len_pos := by norm_num
  sym := ![.A, .T]

/-- The `G = 3` truth `AAT`; also the `G = 2` competitor `AAT`. -/
abbrev genAAT : Genome Base where
  len := 3
  len_pos := by norm_num
  sym := ![.A, .A, .T]

/-- The `G = 4` truth `AAAT`; also the `G = 3` competitor `AAAT`. -/
abbrev genAAAT : Genome Base where
  len := 4
  len_pos := by norm_num
  sym := ![.A, .A, .A, .T]

/-- The `G = 4` competitor `AAAAT`. -/
abbrev genAAAAT : Genome Base where
  len := 5
  len_pos := by norm_num
  sym := ![.A, .A, .A, .A, .T]

/-- Candidate-intrinsic lengths are explicit. -/
theorem len_AT : genAT.len = 2 := rfl
theorem len_AAT : genAAT.len = 3 := rfl
theorem len_AAAT : genAAAT.len = 4 := rfl
theorem len_AAAAT : genAAAAT.len = 5 := rfl

/-! ## Read types, observations, and spectra -/

/-- Length-`1` read types. -/
abbrev rA : Read 1 := ![.A]
abbrev rT : Read 1 := ![.T]

/-- Length-`2` read types. -/
abbrev wAA : Read 2 := ![.A, .A]
abbrev wAT : Read 2 := ![.A, .T]
abbrev wTA : Read 2 := ![.T, .A]

/-- Length-`3` read types. -/
abbrev wAAA : Read 3 := ![.A, .A, .A]
abbrev wAAT : Read 3 := ![.A, .A, .T]
abbrev wATA : Read 3 := ![.A, .T, .A]
abbrev wTAA : Read 3 := ![.T, .A, .A]

/-- Realized start sets (the support of the sample). -/
def rs2 : Finset (Fin 2) := {0, 1}
def rs3 : Finset (Fin 3) := {0, 1, 2}
def rs4 : Finset (Fin 4) := {0, 1, 2, 3}

/-- The realized placements: one read from every true start, plus one extra
from start `0`. -/
def reads2 : List (Fin 2) := [0, 1, 0]
def reads3 : List (Fin 3) := [0, 1, 2, 0]
def reads4 : List (Fin 4) := [0, 1, 2, 3, 0]

/-- Observed read types for `G = 2` (`A, T, A`). -/
def ws2 : List (Read 1) := [rA, rT, rA]

/-- Observed read types for `G = 3` (`AA, AT, TA, AA`). -/
def ws3 : List (Read 2) := [wAA, wAT, wTA, wAA]

/-- Observed read types for `G = 4` (`AAA, AAT, ATA, TAA, AAA`). -/
def ws4 : List (Read 3) := [wAAA, wAAT, wATA, wTAA, wAAA]

/-- The observation really is the windows of the realized placements. -/
theorem observed_reads2 : observed genAT 1 reads2 = ws2 := by decide
theorem observed_reads3 : observed genAAT 2 reads3 = ws3 := by decide
theorem observed_reads4 : observed genAAAT 3 reads4 = ws4 := by decide

/-! ### Spectra -/

theorem spec_AT_1_A : spec genAT 1 rA = 1 := by simp only [spec]; decide
theorem spec_AT_1_T : spec genAT 1 rT = 1 := by simp only [spec]; decide
theorem spec_AAT_1_A : spec genAAT 1 rA = 2 := by simp only [spec]; decide
theorem spec_AAT_1_T : spec genAAT 1 rT = 1 := by simp only [spec]; decide

theorem spec_AAT_2_AA : spec genAAT 2 wAA = 1 := by simp only [spec]; decide
theorem spec_AAT_2_AT : spec genAAT 2 wAT = 1 := by simp only [spec]; decide
theorem spec_AAT_2_TA : spec genAAT 2 wTA = 1 := by simp only [spec]; decide
theorem spec_AAAT_2_AA : spec genAAAT 2 wAA = 2 := by simp only [spec]; decide
theorem spec_AAAT_2_AT : spec genAAAT 2 wAT = 1 := by simp only [spec]; decide
theorem spec_AAAT_2_TA : spec genAAAT 2 wTA = 1 := by simp only [spec]; decide

theorem spec_AAAT_3_AAA : spec genAAAT 3 wAAA = 1 := by simp only [spec]; decide
theorem spec_AAAT_3_AAT : spec genAAAT 3 wAAT = 1 := by simp only [spec]; decide
theorem spec_AAAT_3_ATA : spec genAAAT 3 wATA = 1 := by simp only [spec]; decide
theorem spec_AAAT_3_TAA : spec genAAAT 3 wTAA = 1 := by simp only [spec]; decide
theorem spec_AAAAT_3_AAA : spec genAAAAT 3 wAAA = 2 := by simp only [spec]; decide
theorem spec_AAAAT_3_AAT : spec genAAAAT 3 wAAT = 1 := by simp only [spec]; decide
theorem spec_AAAAT_3_ATA : spec genAAAAT 3 wATA = 1 := by simp only [spec]; decide
theorem spec_AAAAT_3_TAA : spec genAAAAT 3 wTAA = 1 := by simp only [spec]; decide

/-! ## The full source-faithful information-feasibility predicate `I_s`

All three are discharged by `decide` on the shared
`SourceFaithfulIs.InformationFeasible` at full strength. -/

theorem truth_information_feasible_2 :
    InformationFeasible genAT 1 rs2 := by decide

theorem truth_information_feasible_3 :
    InformationFeasible genAAT 2 rs3 := by decide

theorem truth_information_feasible_4 :
    InformationFeasible genAAAT 3 rs4 := by decide

/-! ### Explicit vacuity / bridging of the repeat clauses

These record *why* the repeat clauses hold, rather than only that the whole
predicate is true. -/

/-- The `G = 2` truth `AT` has no maximal triple repeat (only two starts, and
the two length-`1` windows differ). -/
theorem no_triple_repeat_2 :
    ∀ (e : Fin genAT.len) (a b c : Fin genAT.len),
      ¬ genAT.IsTripleRepeat e.val a b c := by
  decide

/-- The `G = 2` truth has no interleaved pair of maximal repeats. -/
theorem no_interleaved_2 :
    ∀ (e₁ e₂ : Fin genAT.len) (a b c d : Fin genAT.len),
      ¬ (genAT.IsRepeat e₁.val a b ∧ genAT.IsRepeat e₂.val c d ∧
          Interleaved genAT a b c d) := by
  decide

/-- The `G = 3` truth `AAT` has no maximal triple repeat. -/
theorem no_triple_repeat_3 :
    ∀ (e : Fin genAAT.len) (a b c : Fin genAAT.len),
      ¬ genAAT.IsTripleRepeat e.val a b c := by
  decide

/-- The `G = 3` truth has no interleaved pair of maximal repeats (three starts
cannot carry four distinct selected occurrences). -/
theorem no_interleaved_3 :
    ∀ (e₁ e₂ : Fin genAAT.len) (a b c d : Fin genAAT.len),
      ¬ (genAAT.IsRepeat e₁.val a b ∧ genAAT.IsRepeat e₂.val c d ∧
          Interleaved genAAT a b c d) := by
  decide

/-- The `G = 4` truth `AAAT` has exactly one maximal triple repeat: the
length-`1` triple of `A`s at starts `0, 1, 2`. -/
theorem triple_repeat_4 : genAAAT.IsTripleRepeat 1 0 1 2 := by decide

/-- Its three copies are all bridged by the reads of length `3` (the bound
`e + 2 = L` is tight here). -/
theorem triple_repeat_all_bridged_4 :
    IsTripleRepeatAllBridged genAAAT 3 rs4 1 0 1 2 := by decide

/-- The `G = 4` truth has no interleaved pair of maximal repeats. -/
theorem no_interleaved_4 :
    ∀ (e₁ e₂ : Fin genAAAT.len) (a b c d : Fin genAAAT.len),
      ¬ (genAAAT.IsRepeat e₁.val a b ∧ genAAAT.IsRepeat e₂.val c d ∧
          Interleaved genAAAT a b c d) := by
  decide

/-! ## Section 6.2 feasibility

Three readings, in increasing strength: the literal per-vertex lower bound `1`,
the spelled support-equality form, and the flow/circuit reading realized by an
explicit closed walk of the oriented read-overlap graph. -/

/-- **Literal Medvedev–Brudno §6.2 feasibility**: every observed read type
occurs in the candidate at least once. -/
def PerVertexFeasible {L : ℕ} (d x : Read L → Nat) : Prop :=
  ∀ c : Read L, 0 < x c → 1 ≤ d c

/-- The spelled support-equality strengthening: the candidate's window support
is exactly the observed support. -/
def SpelledFeasible62 {L : ℕ} (d x : Read L → Nat) : Prop :=
  (∀ c : Read L, 0 < d c ↔ 0 < x c) ∧ PerVertexFeasible d x

/-- The oriented read-overlap relation: read `c` may be followed by read `e`
when the length-`(L-1)` suffix of `c` equals the length-`(L-1)` prefix of `e`.
For `L = 1` the overlap length is `0`, so the relation is vacuously total. -/
def overlaps (L : ℕ) (c e : Read L) : Bool :=
  decide (∀ i : Fin (L - 1), c ⟨i.val + 1, by omega⟩ = e ⟨i.val, by omega⟩)

/-- Consecutive list elements are related by `R` (vacuously for length `≤ 1`). -/
def consec (L : ℕ) (R : Read L → Read L → Bool) : List (Read L) → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => R a b && consec L R (b :: t)

/-- A closed walk of the read-overlap graph: consecutive reads overlap and the
last read overlaps the first, so the walk spells a circular word. -/
def isCircuit (L : ℕ) (w : List (Read L)) : Bool :=
  decide (w ≠ []) && consec L (fun c e => overlaps L c e) (w ++ w.take 1)

/-- The `Prop` form of `isCircuit`. -/
def IsCircuit (L : ℕ) (w : List (Read L)) : Prop := isCircuit L w = true

instance (L : ℕ) (w : List (Read L)) : Decidable (IsCircuit L w) :=
  inferInstanceAs (Decidable (isCircuit L w = true))

/-- A candidate is genuinely §6.2-feasible when a closed walk of the oriented
read-overlap graph realizes its spectrum and uses every observed read type at
least once. -/
def Section62Feasible (L : ℕ) (w : List (Read L)) (d x : Read L → Nat) : Prop :=
  IsCircuit L w ∧ (∀ c : Read L, listCount w c = d c) ∧ (∀ c ∈ w, 0 < x c)

/-! ### The walks and their certificates -/

/-- Truth walk for `G = 2`: spells `AT`. -/
def walkS2 : List (Read 1) := [rA, rT]
/-- Competitor walk for `G = 2`: spells `AAT`. -/
def walkD2 : List (Read 1) := [rA, rA, rT]

/-- Truth walk for `G = 3`: spells `AAT`. -/
def walkS3 : List (Read 2) := [wAA, wAT, wTA]
/-- Competitor walk for `G = 3`: spells `AAAT`. -/
def walkD3 : List (Read 2) := [wAA, wAA, wAT, wTA]

/-- Truth walk for `G = 4`: spells `AAAT`. -/
def walkS4 : List (Read 3) := [wAAA, wAAT, wATA, wTAA]
/-- Competitor walk for `G = 4`: spells `AAAAT`. -/
def walkD4 : List (Read 3) := [wAAA, wAAA, wAAT, wATA, wTAA]

theorem circuit_S2 : IsCircuit 1 walkS2 := by decide
theorem circuit_D2 : IsCircuit 1 walkD2 := by decide
theorem circuit_S3 : IsCircuit 2 walkS3 := by decide
theorem circuit_D3 : IsCircuit 2 walkD3 := by decide
theorem circuit_S4 : IsCircuit 3 walkS4 := by decide
theorem circuit_D4 : IsCircuit 3 walkD4 := by decide

/-- The truth walk's type counts are the truth spectrum (`G = 2`). -/
theorem counts_S2 : ∀ c : Read 1, listCount walkS2 c = spec genAT 1 c := by decide
/-- The competitor walk's type counts are the competitor spectrum (`G = 2`). -/
theorem counts_D2 : ∀ c : Read 1, listCount walkD2 c = spec genAAT 1 c := by decide
theorem counts_S3 : ∀ c : Read 2, listCount walkS3 c = spec genAAT 2 c := by decide
theorem counts_D3 : ∀ c : Read 2, listCount walkD3 c = spec genAAAT 2 c := by decide
theorem counts_S4 : ∀ c : Read 3, listCount walkS4 c = spec genAAAT 3 c := by decide
theorem counts_D4 : ∀ c : Read 3, listCount walkD4 c = spec genAAAAT 3 c := by decide

/-! ### Section 6.2 certificates for all six (truth, competitor) pairs -/

theorem truth_perVertex_2 : PerVertexFeasible (spec genAT 1) (obsCount genAT 1 reads2) := by
  unfold PerVertexFeasible; decide
theorem competitor_perVertex_2 : PerVertexFeasible (spec genAAT 1) (obsCount genAT 1 reads2) := by
  unfold PerVertexFeasible; decide
theorem truth_spelled_2 : SpelledFeasible62 (spec genAT 1) (obsCount genAT 1 reads2) := by
  unfold SpelledFeasible62 PerVertexFeasible; decide
theorem competitor_spelled_2 : SpelledFeasible62 (spec genAAT 1) (obsCount genAT 1 reads2) := by
  unfold SpelledFeasible62 PerVertexFeasible; decide
theorem truth_section62_2 : Section62Feasible 1 walkS2 (spec genAT 1) (obsCount genAT 1 reads2) :=
  ⟨circuit_S2, counts_S2, by decide⟩
theorem competitor_section62_2 : Section62Feasible 1 walkD2 (spec genAAT 1) (obsCount genAT 1 reads2) :=
  ⟨circuit_D2, counts_D2, by decide⟩

theorem truth_perVertex_3 : PerVertexFeasible (spec genAAT 2) (obsCount genAAT 2 reads3) := by
  unfold PerVertexFeasible; decide
theorem competitor_perVertex_3 : PerVertexFeasible (spec genAAAT 2) (obsCount genAAT 2 reads3) := by
  unfold PerVertexFeasible; decide
theorem truth_spelled_3 : SpelledFeasible62 (spec genAAT 2) (obsCount genAAT 2 reads3) := by
  unfold SpelledFeasible62 PerVertexFeasible; decide
theorem competitor_spelled_3 : SpelledFeasible62 (spec genAAAT 2) (obsCount genAAT 2 reads3) := by
  unfold SpelledFeasible62 PerVertexFeasible; decide
theorem truth_section62_3 : Section62Feasible 2 walkS3 (spec genAAT 2) (obsCount genAAT 2 reads3) :=
  ⟨circuit_S3, counts_S3, by decide⟩
theorem competitor_section62_3 : Section62Feasible 2 walkD3 (spec genAAAT 2) (obsCount genAAT 2 reads3) :=
  ⟨circuit_D3, counts_D3, by decide⟩

theorem truth_perVertex_4 : PerVertexFeasible (spec genAAAT 3) (obsCount genAAAT 3 reads4) := by
  unfold PerVertexFeasible; decide
theorem competitor_perVertex_4 : PerVertexFeasible (spec genAAAAT 3) (obsCount genAAAT 3 reads4) := by
  unfold PerVertexFeasible; decide
theorem truth_spelled_4 : SpelledFeasible62 (spec genAAAT 3) (obsCount genAAAT 3 reads4) := by
  unfold SpelledFeasible62 PerVertexFeasible; decide
theorem competitor_spelled_4 : SpelledFeasible62 (spec genAAAAT 3) (obsCount genAAAT 3 reads4) := by
  unfold SpelledFeasible62 PerVertexFeasible; decide
theorem truth_section62_4 : Section62Feasible 3 walkS4 (spec genAAAT 3) (obsCount genAAAT 3 reads4) :=
  ⟨circuit_S4, counts_S4, by decide⟩
theorem competitor_section62_4 : Section62Feasible 3 walkD4 (spec genAAAAT 3) (obsCount genAAAT 3 reads4) :=
  ⟨circuit_D4, counts_D4, by decide⟩

/-! ## Exact ordered-read likelihoods and strict ratios -/

/-- `G = 2`: truth likelihood `(1/2)^3 = 1/8`. -/
theorem lik_truth_2 : orderedLik genAT 1 ws2 = 1 / 8 := by
  simp only [orderedLik, ws2, spec_AT_1_A, spec_AT_1_T, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil]
  norm_num

/-- `G = 2`: competitor likelihood `(2/3)^2 (1/3) = 4/27`. -/
theorem lik_competitor_2 : orderedLik genAAT 1 ws2 = 4 / 27 := by
  simp only [orderedLik, ws2, spec_AAT_1_A, spec_AAT_1_T, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil]
  norm_num

/-- `G = 3`: truth likelihood `(1/3)^4 = 1/81`. -/
theorem lik_truth_3 : orderedLik genAAT 2 ws3 = 1 / 81 := by
  simp only [orderedLik, ws3, spec_AAT_2_AA, spec_AAT_2_AT, spec_AAT_2_TA,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  norm_num

/-- `G = 3`: competitor likelihood `(2/4)^2 (1/4)^2 = 1/64`. -/
theorem lik_competitor_3 : orderedLik genAAAT 2 ws3 = 1 / 64 := by
  simp only [orderedLik, ws3, spec_AAAT_2_AA, spec_AAAT_2_AT, spec_AAAT_2_TA,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  norm_num

/-- `G = 4`: truth likelihood `(1/4)^5 = 1/1024`. -/
theorem lik_truth_4 : orderedLik genAAAT 3 ws4 = 1 / 1024 := by
  simp only [orderedLik, ws4, spec_AAAT_3_AAA, spec_AAAT_3_AAT, spec_AAAT_3_ATA,
    spec_AAAT_3_TAA, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  norm_num

/-- `G = 4`: competitor likelihood `(2/5)^2 (1/5)^3 = 4/3125`. -/
theorem lik_competitor_4 : orderedLik genAAAAT 3 ws4 = 4 / 3125 := by
  simp only [orderedLik, ws4, spec_AAAAT_3_AAA, spec_AAAAT_3_AAT, spec_AAAAT_3_ATA,
    spec_AAAAT_3_TAA, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  norm_num

/-- `G = 2` exact ratio `32/27 > 1`. -/
theorem ratio_2 : orderedLik genAAT 1 ws2 / orderedLik genAT 1 ws2 = 32 / 27 := by
  rw [lik_competitor_2, lik_truth_2]; norm_num

/-- `G = 3` exact ratio `81/64 > 1`. -/
theorem ratio_3 : orderedLik genAAAT 2 ws3 / orderedLik genAAT 2 ws3 = 81 / 64 := by
  rw [lik_competitor_3, lik_truth_3]; norm_num

/-- `G = 4` exact ratio `4096/3125 > 1`. -/
theorem ratio_4 : orderedLik genAAAAT 3 ws4 / orderedLik genAAAT 3 ws4 = 4096 / 3125 := by
  rw [lik_competitor_4, lik_truth_4]; norm_num

theorem candidate_strictly_better_2 : orderedLik genAT 1 ws2 < orderedLik genAAT 1 ws2 := by
  rw [lik_truth_2, lik_competitor_2]; norm_num

theorem candidate_strictly_better_3 : orderedLik genAAT 2 ws3 < orderedLik genAAAT 2 ws3 := by
  rw [lik_truth_3, lik_competitor_3]; norm_num

theorem candidate_strictly_better_4 : orderedLik genAAAT 3 ws4 < orderedLik genAAAAT 3 ws4 := by
  rw [lik_truth_4, lik_competitor_4]; norm_num

/-! ## The multinomial-count objective has the same ratio

For a fixed observation the multinomial coefficient `n! / ∏_w x_w!` is common to
both candidates, so it cancels; hence the multinomial-count objective shares the
strict ratio of the ordered-read likelihood. -/

theorem multinomCoeff_ne_zero (L : ℕ) (ws : List (Read L)) : multinomCoeff L ws ≠ 0 := by
  unfold multinomCoeff
  have hnum : (0 : ℚ) < (Nat.factorial ws.length : ℚ) := by
    exact_mod_cast Nat.factorial_pos ws.length
  have hden : (0 : ℚ) < ∏ w : Read L, (Nat.factorial (listCount ws w) : ℚ) := by
    apply Finset.prod_pos
    intro w _
    exact_mod_cast Nat.factorial_pos (listCount ws w)
  exact ne_of_gt (div_pos hnum hden)

/-- The multinomial-count objective has the same truth/competitor ratio as the
ordered-read likelihood. -/
theorem multinomLik_ratio (S D : Genome Base) (L : ℕ) (ws : List (Read L)) :
    multinomLik D L ws / multinomLik S L ws =
      orderedLik D L ws / orderedLik S L ws := by
  unfold multinomLik
  rw [mul_div_mul_left _ _ (multinomCoeff_ne_zero L ws)]

theorem multinom_ratio_2 :
    multinomLik genAAT 1 ws2 / multinomLik genAT 1 ws2 = 32 / 27 := by
  rw [multinomLik_ratio, ratio_2]

theorem multinom_ratio_3 :
    multinomLik genAAAT 2 ws3 / multinomLik genAAT 2 ws3 = 81 / 64 := by
  rw [multinomLik_ratio, ratio_3]

theorem multinom_ratio_4 :
    multinomLik genAAAAT 3 ws4 / multinomLik genAAAT 3 ws4 = 4096 / 3125 := by
  rw [multinomLik_ratio, ratio_4]

/-! ## The three endpoints -/

/-- **`G = 2`, `L = 1` witness.** The truth `AT` is information-feasible; both
`AT` and the competitor `AAT` are genuinely §6.2-feasible (per-vertex, spelled,
and closed-walk circuit); the competitor has strictly greater exact
ordered-read likelihood, ratio `32/27`. -/
theorem short_finite_ml_counterexample_2 :
    InformationFeasible genAT 1 rs2 ∧
      Section62Feasible 1 walkS2 (spec genAT 1) (obsCount genAT 1 reads2) ∧
      Section62Feasible 1 walkD2 (spec genAAT 1) (obsCount genAT 1 reads2) ∧
      SpelledFeasible62 (spec genAT 1) (obsCount genAT 1 reads2) ∧
      SpelledFeasible62 (spec genAAT 1) (obsCount genAT 1 reads2) ∧
      genAT.len = 2 ∧ genAAT.len = 3 ∧
      orderedLik genAT 1 ws2 < orderedLik genAAT 1 ws2 ∧
      orderedLik genAAT 1 ws2 / orderedLik genAT 1 ws2 = 32 / 27 :=
  ⟨truth_information_feasible_2, truth_section62_2, competitor_section62_2,
    truth_spelled_2, competitor_spelled_2, len_AT, len_AAT,
    candidate_strictly_better_2, ratio_2⟩

/-- **`G = 3`, `L = 2` witness.** Truth `AAT`, competitor `AAAT`, ratio
`81/64`. -/
theorem short_finite_ml_counterexample_3 :
    InformationFeasible genAAT 2 rs3 ∧
      Section62Feasible 2 walkS3 (spec genAAT 2) (obsCount genAAT 2 reads3) ∧
      Section62Feasible 2 walkD3 (spec genAAAT 2) (obsCount genAAT 2 reads3) ∧
      SpelledFeasible62 (spec genAAT 2) (obsCount genAAT 2 reads3) ∧
      SpelledFeasible62 (spec genAAAT 2) (obsCount genAAT 2 reads3) ∧
      genAAT.len = 3 ∧ genAAAT.len = 4 ∧
      orderedLik genAAT 2 ws3 < orderedLik genAAAT 2 ws3 ∧
      orderedLik genAAAT 2 ws3 / orderedLik genAAT 2 ws3 = 81 / 64 :=
  ⟨truth_information_feasible_3, truth_section62_3, competitor_section62_3,
    truth_spelled_3, competitor_spelled_3, len_AAT, len_AAAT,
    candidate_strictly_better_3, ratio_3⟩

/-- **`G = 4`, `L = 3` witness.** Truth `AAAT`, competitor `AAAAT`, ratio
`4096/3125`. -/
theorem short_finite_ml_counterexample_4 :
    InformationFeasible genAAAT 3 rs4 ∧
      Section62Feasible 3 walkS4 (spec genAAAT 3) (obsCount genAAAT 3 reads4) ∧
      Section62Feasible 3 walkD4 (spec genAAAAT 3) (obsCount genAAAT 3 reads4) ∧
      SpelledFeasible62 (spec genAAAT 3) (obsCount genAAAT 3 reads4) ∧
      SpelledFeasible62 (spec genAAAAT 3) (obsCount genAAAT 3 reads4) ∧
      genAAAT.len = 4 ∧ genAAAAT.len = 5 ∧
      orderedLik genAAAT 3 ws4 < orderedLik genAAAAT 3 ws4 ∧
      orderedLik genAAAAT 3 ws4 / orderedLik genAAAT 3 ws4 = 4096 / 3125 :=
  ⟨truth_information_feasible_4, truth_section62_4, competitor_section62_4,
    truth_spelled_4, competitor_spelled_4, len_AAAT, len_AAAAT,
    candidate_strictly_better_4, ratio_4⟩

end AssemblyP1.ShortFiniteMLCounterexamples
