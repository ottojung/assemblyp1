import Mathlib
import AssemblyP1.SourceFaithfulIs
import AssemblyP1.Section62BidirectedFlow

/-!
# A finite Section 6.2 bridging counterexample (literal bidirected flow)

This file kernel-checks the finite witness recorded in
`docs/bridging-se62-flow-ml-counterexample.md`.  Under the Medvedev–Brudno §6.2
reading in which the vertices of the bidirected read-overlap graph are read
*DNA molecules* (so a word and its reverse complement are one vertex), the
truth-induced flow need not be a maximum-likelihood maximizer, even when the
source-faithful bridging hypothesis `I_s` holds and the truth is an admissible
§6.2 candidate.

Instance:

* alphabet `{A, T}` with the DNA reverse-complement involution `A ↔ T`;
* true circular genome `truth = AAATT` (length `5`);
* read length `L = 3`, realized starts `(0, 1, 4)` (`n = 3` reads);
* external known genome size `N = 5` (Medvedev–Brudno §6.1);
* observed read-molecule classes `x = { AAA:1, AAT:1, TAA:1 }`;
* truth spectrum `d_S = { AAA:1, AAT:2, TAA:2 }`;
* competitor `D = AAAATT` (length `6`), `d_D = { AAA:2, AAT:2, TAA:2 }`.

What is kernel-checked here.  This file proves the **literal Medvedev–Brudno
§6.2 feasibility** of both candidates, via `AssemblyP1.Section62Flow`:

* the explicit bidirected read-overlap graph on the observed read molecules, its
  edges written out and proved equal to the generated `overlapEdges`;
* the transitive edge reduction, vacuous on this graph under both the literal
  "spelled by two shorter overlaps" and the alternative longer-overlap readings;
* the §6.2 vertex lower bound `1` and edge lower bounds `0`, the §3.4
  signed-incidence balance `0` at every read vertex, and **no
  supersource/supersink usage**;
* the vertex throughputs, which by Observation 7 are the candidates' molecule
  spectra `d_S` and `d_D` as already used by the §6.1 objective;
* the **shared, authoritative** `SourceFaithfulIs.InformationFeasible` predicate
  `I_s` at full strength — coverage, *every* triple repeat all-bridged, and
  *every* interleaved pair of repeats bridged, quantified over all repeat lengths
  and all selected starts — proved by finite `decide` on the `Genome` object
  `truthGenome` with read length `3` and the realized placements `{0, 1, 4}`.
  The module-local hand-listed `SourceCertificate` is retained as supporting
  evidence only;

The endpoint theorem is `se62_bridging_bidirected_flow_counterexample`, whose
feasibility clauses are `SpelledFeasible62`, not a proxy.

`SeqSupportLB` (support equality together with the per-occurrence lower bound
`x ≤ d_·`) is **not** the §6.2 definition; it is a stronger finite sufficient
certificate. It is retained here as `se62_bridging_flow_counterexample` only as
supporting evidence, and the independent Python verifier
`scripts/verify_se62_mb09_bidirected_graph.py` remains as a second,
implementation-independent check of the same graph and circuits.

Scope.  This file is about the finite instance only.  It does not settle which
Medvedev–Brudno object the Shomorony et al. (2016) sentence intends, nor the
single-strand or fixed-candidate-length sub-cases.
-/

namespace AssemblyP1.Section62BridgingCounterexample

/-- Two-symbol alphabet for the witness; the reverse-complement involution is
`A ↔ T`. -/
inductive Base where
  | A
  | T
  deriving DecidableEq, Inhabited, Repr

instance : Fintype Base where
  elems := {Base.A, Base.T}
  complete := by intro x; cases x <;> simp

/-- DNA reverse complement on the two-symbol alphabet. -/
def comp : Base → Base
  | .A => .T
  | .T => .A

/-- A length-`3` read type / window. -/
abbrev W3 := Fin 3 → Base

/-- Bit encoding of a symbol (`A ↦ 0`, `T ↦ 1`). -/
def bitA : Base → Nat
  | .A => 0
  | .T => 1

/-- Binary code of a length-`3` word, in `[0, 8)`. -/
def code (w : W3) : Nat := bitA (w 0) * 4 + bitA (w 1) * 2 + bitA (w 2)

/-- Reverse complement of a length-`3` word. -/
def rc (w : W3) : W3 := ![comp (w 2), comp (w 1), comp (w 0)]

lemma code_lt (w : W3) : code w < 8 := by
  have h0 : bitA (w 0) ≤ 1 := by cases w 0 <;> decide
  have h1 : bitA (w 1) ≤ 1 := by cases w 1 <;> decide
  have h2 : bitA (w 2) ≤ 1 := by cases w 2 <;> decide
  unfold code
  omega

/-- Molecule class of a word: the smaller of its own code and the code of its
reverse complement.  This is the `Fin 8` label of the reverse-complement pair. -/
def cls (w : W3) : Fin 8 :=
  ⟨min (code w) (code (rc w)), Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (code_lt w)⟩

/-- The true circular genome `AAATT` of length `5`. -/
def truth : Fin 5 → Base := ![.A, .A, .A, .T, .T]

/-- The competitor `AAAATT` of length `6`. -/
def competitor : Fin 6 → Base := ![.A, .A, .A, .A, .T, .T]

/-- Circular symbol access for a length-`5` genome. -/
def cyc5 (g : Fin 5 → Base) (i : Nat) : Base :=
  g ⟨i % 5, Nat.mod_lt _ (by norm_num)⟩

/-- Circular symbol access for a length-`6` genome. -/
def cyc6 (g : Fin 6 → Base) (i : Nat) : Base :=
  g ⟨i % 6, Nat.mod_lt _ (by norm_num)⟩

/-- Length-`3` circular window at start `r` of a length-`5` genome. -/
def window5 (g : Fin 5 → Base) (r : Fin 5) : W3 :=
  ![cyc5 g r.val, cyc5 g (r.val + 1), cyc5 g (r.val + 2)]

/-- Length-`3` circular window at start `r` of a length-`6` genome. -/
def window6 (g : Fin 6 → Base) (r : Fin 6) : W3 :=
  ![cyc6 g r.val, cyc6 g (r.val + 1), cyc6 g (r.val + 2)]

/-- Number of starts of a length-`5` genome whose window has molecule class `c`. -/
def spec5 (g : Fin 5 → Base) (c : Fin 8) : Nat :=
  (Finset.univ.filter (fun r : Fin 5 => cls (window5 g r) = c)).card

/-- Number of starts of a length-`6` genome whose window has molecule class `c`. -/
def spec6 (g : Fin 6 → Base) (c : Fin 8) : Nat :=
  (Finset.univ.filter (fun r : Fin 6 => cls (window6 g r) = c)).card

/-- The realized read starts `0, 1, 4`. -/
def readStarts : Finset (Fin 5) := {0, 1, 4}

/-- Observed read-molecule class counts `x`. -/
def obs (c : Fin 8) : Nat :=
  (readStarts.filter (fun r => cls (window5 truth r) = c)).card

/-- Truth-induced spectrum `d_S`. -/
def dS (c : Fin 8) : Nat := spec5 truth c

/-- Competitor spectrum `d_D`. -/
def dD (c : Fin 8) : Nat := spec6 competitor c

/-! ## Sequence-level support/lower-bound certificate -/

/-- Sequence-level support/lower-bound certificate for a molecule spectrum `d`
against observed counts `x`: support equality together with the per-occurrence
lower bound `x ≤ d`.  This is a finite *sufficient* condition that holds for
this witness; it is not the Medvedev–Brudno §6.2 flow feasibility definition
(see the module docstring and `docs/section62-mb09-bidirected-graph-audit.md`). -/
def SeqSupportLB (d x : Fin 8 → Nat) : Prop :=
  (∀ c, 0 < d c ↔ 0 < x c) ∧ ∀ c, x c ≤ d c

theorem truth_feasible : SeqSupportLB dS obs := by
  unfold SeqSupportLB dS obs spec5 window5 cyc5 cls code rc bitA comp truth readStarts
  decide

theorem competitor_feasible : SeqSupportLB dD obs := by
  unfold SeqSupportLB dD obs spec6 window6 window5 cyc6 cyc5 cls code rc bitA comp
    truth competitor readStarts
  decide

/-! ## Source-faithful `I_s` certificate -/

/-- Coverage: the realized reads at starts `0, 1, 4` cover all five circular
positions of the truth. -/
def Covers : Prop :=
  ∀ p : Fin 5, ∃ r ∈ readStarts, ∃ d : Fin 3, p.val = (r.val + d.val) % 5

theorem truth_covered : Covers := by
  unfold Covers readStarts
  decide

/-- The maximal triple-repeat obligation for this instance: the length-`1`
windows at starts `0, 1, 2` are equal (`A`), the three-copy maximality
condition holds, and each copy is bridged by a realized read (start `4` bridges
copy `0`, start `0` bridges copy `1`, start `1` bridges copy `2`). -/
def TripleAllBridged : Prop :=
  truth 0 = truth 1 ∧ truth 1 = truth 2 ∧
  ¬(truth 4 = truth 0 ∧ truth 0 = truth 1) ∧
  ¬(truth 1 = truth 2 ∧ truth 2 = truth 3) ∧
  (∀ t : Fin 5, (t.val = 0 ∨ t.val = 1 ∨ t.val = 2) →
    ∃ r ∈ readStarts, (r.val + 1) % 5 = t.val)

theorem truth_triple_all_bridged : TripleAllBridged := by
  unfold TripleAllBridged readStarts truth
  decide

/-! ### Interleaving conjunct, decided by explicit finite enumeration

The source interleaving condition is decided over the finite index range by a
computable `Bool`, exactly as in `scripts/verify_se62_bridging_flow_counterexample.py`.
This avoids relying on typeclass synthesis of `Decidable` for deeply nested
quantifiers over `Fin 5`. -/

/-- Boolean test for a maximal repeat pair of length `e` at starts `t1`, `t2`:
positive length `< 5`, distinct starts, agreement, and differing flanks. -/
def pairB (e t1 t2 : Nat) : Bool :=
  decide (1 ≤ e) && decide (e < 5) && decide (t1 % 5 ≠ t2 % 5) &&
  (List.range 5).all (fun j => !decide (j < e) ||
    decide (cyc5 truth (t1 + j) = cyc5 truth (t2 + j))) &&
  decide (cyc5 truth (t1 + 4) ≠ cyc5 truth (t2 + 4)) &&
  decide (cyc5 truth (t1 + e) ≠ cyc5 truth (t2 + e))

/-- Boolean test for `b` preceding `c` clockwise from `a`. -/
def beforeB (a b c : Nat) : Bool :=
  decide ((b + 5 - a) % 5 < (c + 5 - a) % 5)

/-- Boolean test for the existence of two interleaved maximal repeat pairs. -/
def hasInterleavingB : Bool :=
  (List.range 5).any fun e1 =>
  (List.range 5).any fun t1 =>
  (List.range 5).any fun t2 =>
  (List.range 5).any fun e2 =>
  (List.range 5).any fun t3 =>
  (List.range 5).any fun t4 =>
    pairB e1 t1 t2 && pairB e2 t3 t4 &&
    decide (t1 % 5 ≠ t3 % 5) && decide (t1 % 5 ≠ t4 % 5) &&
    decide (t2 % 5 ≠ t3 % 5) && decide (t2 % 5 ≠ t4 % 5) &&
    beforeB t1 t3 t2 && beforeB t2 t4 t1

/-- The source interleaving condition: two maximal repeat pairs whose four
starts are distinct and cyclically alternate. -/
def HasInterleaving : Prop := hasInterleavingB = true

theorem hasInterleavingB_false : hasInterleavingB = false := by decide

theorem no_interleaving : ¬ HasInterleaving := by
  unfold HasInterleaving
  rw [hasInterleavingB_false]
  decide

/-- The kernel-checked part of the source-faithful `I_s` hypothesis:
coverage, all-bridged maximal triple repeats, and vacuous interleaving. -/
def SourceCertificate : Prop := Covers ∧ TripleAllBridged ∧ ¬ HasInterleaving

theorem truth_source_certificate : SourceCertificate :=
  ⟨truth_covered, truth_triple_all_bridged, no_interleaving⟩

/-! ### The same instance against the shared, authoritative `I_s`

`SourceCertificate` above is the module-local, hand-listed certificate that was
inherited from the earlier proxy-based version of this file.  The hypothesis side
of the endpoint theorem is stated with the *shared* predicate
`SourceFaithfulIs.InformationFeasible` — the same object the same-length module
and every other AssemblyP1 counterexample module use — so that the certificate
being discharged is literally the source `I_s` and not a stand-in for it. -/

open SourceFaithfulIs

/-- The true circular genome `AAATT` in the shared source-faithful
representation, as a reducible abbreviation so that instance search finds the
`Fin`-indexed numerals and the `Decidable` instances of the shared layer. -/
abbrev truthGenome : SourceFaithfulIs.Genome Base where
  len := 5
  len_pos := by norm_num
  sym := truth

/-- The competing candidate `AAAATT` in the shared source-faithful
representation, so candidate-intrinsic length is intrinsic to the object. -/
abbrev competitorGenome : SourceFaithfulIs.Genome Base where
  len := 6
  len_pos := by norm_num
  sym := competitor

/-- The realized length-`3` read placements, the distinct entries of
`readStarts`.  Coverage and bridging are properties of the latent placements, and
`SourceFaithfulIs.Covers`/`BridgesCopy` quantify over a `Finset` of start
positions; `readStarts` is already such a set, so the realized start set of this
instance is literally `readStarts`. -/
def realizedStarts : Finset (Fin 5) := readStarts

/-- The realized start set is exactly the set of realized read starts. -/
theorem realizedStarts_eq : realizedStarts = {0, 1, 4} := rfl

/-- The shared `Genome` length of the truth is the length used everywhere else in
this file. -/
theorem truthGenome_len : truthGenome.len = 5 := rfl

/-- **The actual `I_s` hypothesis for this realization.**  This is
`SourceFaithfulIs.InformationFeasible` at full strength — coverage, *every*
triple repeat all-bridged, and *every* interleaved pair of repeats bridged,
quantified over all repeat lengths and all selected starts — discharged by finite
`decide` on the `Genome` object `truthGenome` with read length `3` and the
realized placements `{0, 1, 4}`.  No repeat is enumerated by hand and no clause is
assumed; in particular the clause "every interleaved pair of repeats is bridged"
is discharged by exhibiting the fact that this truth has no interleaved pair of
maximal repeats at all, not by assuming it away. -/
theorem truth_information_feasible :
    SourceFaithfulIs.InformationFeasible truthGenome 3 realizedStarts := by
  decide

/-! ## Literal §6.1 product-of-binomial-marginals objective -/

/-- One §6.1 binomial marginal for molecule class `c`, with fixed external
`N = 5`, total reads `n = 3`, observed count `x c`, and candidate count `d c`. -/
def marginal (x d : Fin 8 → Nat) (c : Fin 8) : ℚ :=
  (Nat.choose 3 (x c) : ℚ) * ((d c : ℚ) / 5) ^ (x c) *
    (1 - (d c : ℚ) / 5) ^ (3 - x c)

/-- The literal §6.1 product of binomial marginals over the molecule-class
space (zero-count factors retained). -/
def lik (x d : Fin 8 → Nat) : ℚ :=
  ∏ c : Fin 8, marginal x d c

/-- The three molecule classes with positive observed count: `AAA` (code `0`),
`AAT` (code `1`) and `TAA` (code `4`). -/
def relevant : Finset (Fin 8) := {0, 1, 4}

/-- A class with zero observed count and zero candidate multiplicity contributes
the factor `1` to the literal product. -/
lemma marginal_eq_one_of_zero (x d : Fin 8 → Nat) (c : Fin 8)
    (hx : x c = 0) (hd : d c = 0) : marginal x d c = 1 := by
  simp [marginal, hx, hd]

/-- Outside `relevant`, both the observed count and each candidate's
multiplicity vanish; hence the full product reduces to the product over
`relevant`. -/
lemma lik_eq_relevant_prod (x d : Fin 8 → Nat)
    (h : ∀ c : Fin 8, c ∉ relevant → x c = 0 ∧ d c = 0) :
    lik x d = ∏ c ∈ relevant, marginal x d c := by
  unfold lik
  exact (Finset.prod_subset (s₁ := relevant) (s₂ := Finset.univ)
    (by intro c _; exact Finset.mem_univ c)
    (by intro c _ hc; exact marginal_eq_one_of_zero x d c (h c hc).1 (h c hc).2)).symm

theorem truth_zero_off :
    ∀ c : Fin 8, c ∉ relevant → obs c = 0 ∧ dS c = 0 := by
  unfold relevant obs dS spec5 window5 cyc5 cls code rc bitA comp truth readStarts
  decide

theorem competitor_zero_off :
    ∀ c : Fin 8, c ∉ relevant → obs c = 0 ∧ dD c = 0 := by
  unfold relevant obs dD spec6 window6 window5 cyc6 cyc5 cls code rc bitA comp
    truth competitor readStarts
  decide

/-- Expansion of a product over the three-element `relevant` set. -/
lemma relevant_prod_eq (f : Fin 8 → ℚ) :
    ∏ c ∈ relevant, f c = f 0 * (f 1 * f 4) := by
  unfold relevant
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]

theorem obs_0 : obs 0 = 1 := by
  unfold obs window5 cyc5 cls code rc bitA comp truth readStarts; decide

theorem obs_1 : obs 1 = 1 := by
  unfold obs window5 cyc5 cls code rc bitA comp truth readStarts; decide

theorem obs_4 : obs 4 = 1 := by
  unfold obs window5 cyc5 cls code rc bitA comp truth readStarts; decide

theorem dS_0 : dS 0 = 1 := by
  unfold dS spec5 window5 cyc5 cls code rc bitA comp truth; decide

theorem dS_1 : dS 1 = 2 := by
  unfold dS spec5 window5 cyc5 cls code rc bitA comp truth; decide

theorem dS_4 : dS 4 = 2 := by
  unfold dS spec5 window5 cyc5 cls code rc bitA comp truth; decide

theorem dD_0 : dD 0 = 2 := by
  unfold dD spec6 window6 cyc6 cls code rc bitA comp competitor; decide

theorem dD_1 : dD 1 = 2 := by
  unfold dD spec6 window6 cyc6 cls code rc bitA comp competitor; decide

theorem dD_4 : dD 4 = 2 := by
  unfold dD spec6 window6 cyc6 cls code rc bitA comp competitor; decide

/-- Exact value of the truth's literal §6.1 objective, `(48/125)·(54/125)^2`. -/
theorem lik_truth : lik obs dS = (48 / 125) * (54 / 125) ^ 2 := by
  rw [lik_eq_relevant_prod obs dS truth_zero_off, relevant_prod_eq]
  simp only [marginal, obs_0, obs_1, obs_4, dS_0, dS_1, dS_4]
  norm_num

/-- Exact value of the competitor's literal §6.1 objective, `(54/125)^3`. -/
theorem lik_competitor : lik obs dD = (54 / 125) ^ 3 := by
  rw [lik_eq_relevant_prod obs dD competitor_zero_off, relevant_prod_eq]
  simp only [marginal, obs_0, obs_1, obs_4, dD_0, dD_1, dD_4]
  norm_num

theorem lik_truth_pos : 0 < lik obs dS := by
  rw [lik_truth]; norm_num

/-- The competitor strictly beats the truth under the literal §6.1 objective:
ratio `9/8`. -/
theorem lik_competitor_over_truth : lik obs dD / lik obs dS = 9 / 8 := by
  rw [lik_truth, lik_competitor]; norm_num

theorem competitor_strictly_better : lik obs dS < lik obs dD := by
  have h := lik_competitor_over_truth
  have hpos := lik_truth_pos
  rw [div_eq_iff (ne_of_gt hpos)] at h
  rw [h]
  nlinarith [hpos]


/-! ## Literal §6.2 bidirected-flow feasibility (MB09 §6.2)

Everything below replaces the `SeqSupportLB` proxy by the actual §6.2 object: the
explicit bidirected read-overlap graph on the observed read *molecules*, its
transitive edge reduction, the vertex and edge lower bounds, the §3.4
signed-incidence balance, and the supersource/supersink circulation conversion.

The strand and candidate semantics are unchanged from the rest of this file.
Vertices are molecule classes (MB09 §3.1, §4.1) and the candidates are still the
circular sequences `truth` and `competitor`; only the feasibility predicate is
replaced. -/

open AssemblyP1.Section62Flow

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- A *strand*: one single-stranded DNA sequence, written as the list of its
symbols.  MB09 §3.1 models a DNA molecule as an unordered reverse-complement
strand pair, so a strand is its own linearization.  Writing strands as symbol
lists (rather than as functions) keeps strand equality kernel-reducible, which is
what lets the finite certificates below be discharged by `decide`. -/
abbrev Strand3 := List Base

/-- A length-`3` read molecule, as a strand. -/
def m3 (a b c : Base) : Strand3 := [a, b, c]

/-- The linearization of a strand. -/
def toList3 (w : Strand3) : List Base := w

/-- The DNA reverse complement of a strand (MB09 §3.1). -/
def rc3 (w : Strand3) : Strand3 := w.reverse.map comp

/-- The binary code of a strand, least significant symbol last. -/
def code3 (w : Strand3) : Nat := (w.map bitA).foldl (fun a b => a * 2 + b) 0

/-- The molecule-class representative of a strand: the strand itself when its
binary code is the smaller of the two strand codes, and its reverse complement
otherwise.  MB09 §4.1 represents each k-molecule only once, so this is the vertex
label of the §6.2 graph. -/
def rep3 (w : Strand3) : Strand3 := if code3 w ≤ code3 (rc3 w) then w else rc3 w

/-- The bidirected overlap edge of length `L − 1 = 2` between two strands. -/
def e2 (x y : Strand3) : BdEdge Base Strand3 := bdEdge rep3 x y 2

/-- The molecule-class code of a strand, i.e. the `Fin 8` label of its
reverse-complement pair.  This is the indexing used by the already
kernel-checked spectra `dS`, `dD` and by the §6.1 objective. -/
def repCode (w : Strand3) : Fin 8 :=
  if h : min (code3 w) (code3 (rc3 w)) < 8 then
    ⟨min (code3 w) (code3 (rc3 w)), h⟩
  else 0

/-- The three observed read DNA molecules, the vertices of the §6.2 graph. -/
def readVerts : List Strand3 := [m3 .A .A .A, m3 .A .A .T, m3 .T .A .A]

/-- The read length `L = 3`. -/
def readLen : Nat := 3

/-- The §6.2 overlap threshold for this instance, `o_min = L − 1 = 2`. -/
def oMin : Nat := 2

/-- The explicit bidirected overlap graph of MB09 §6.2 on the observed read
molecules: all proper overlaps of length at least `oMin` between strands of
observed molecules, each carrying the signed incidence at both endpoint molecule
classes. -/
def graph : List (BdEdge Base Strand3) :=
  overlapEdges Base Strand3 toList3 rep3 rc3 readLen oMin readVerts

/-- The ten §6.2 overlap edges, written out.  This is the graph of
`docs/section62-mb09-bidirected-graph-audit.md` §2, listed in the order
`overlapEdges` generates them.  The feasibility checks below use this explicit
list so that they stay shallow enough for the kernel to evaluate; `graph_eq`
identifies it with the generated graph, so nothing is lost. -/
def graphList : List (BdEdge Base Strand3) :=
  [ e2 (m3 .A .A .A) (m3 .A .A .A), e2 (m3 .A .A .A) (m3 .A .A .T),
    e2 (m3 .A .A .T) (m3 .A .T .T), e2 (m3 .T .A .A) (m3 .A .A .A),
    e2 (m3 .T .A .A) (m3 .A .A .T), e2 (m3 .T .T .T) (m3 .T .T .T),
    e2 (m3 .T .T .T) (m3 .T .T .A), e2 (m3 .A .T .T) (m3 .T .T .T),
    e2 (m3 .A .T .T) (m3 .T .T .A), e2 (m3 .T .T .A) (m3 .T .A .A) ]

/-- The written-out edge list is exactly the generated §6.2 overlap graph. -/
theorem graph_eq : graph = graphList := by decide

/-- The strand read at start `r` of the truth `AAATT`. -/
def strandTruth (r : Fin 5) : Strand3 :=
  [cyc5 truth r.val, cyc5 truth (r.val + 1), cyc5 truth (r.val + 2)]

/-- The strand read at start `r` of the competitor `AAAATT`. -/
def strandCompetitor (r : Fin 6) : Strand3 :=
  [cyc6 competitor r.val, cyc6 competitor (r.val + 1), cyc6 competitor (r.val + 2)]

/-- The truth's molecule spectrum, indexed by molecule class: the throughput
vector `d` that §6.2 requires, by Observation 7.  This is exactly the `Fin 8`
spectrum `dS` that the §6.1 objective consumes, relabelled by molecule class. -/
def dS' (w : Strand3) : Nat := dS (repCode w)

/-- The competitor's molecule spectrum, likewise relabelled by molecule class. -/
def dD' (w : Strand3) : Nat := dD (repCode w)

/-- The truth `AAATT` as a §6.2 spelled candidate: the strand read at each of its
five cyclic positions. -/
def spellTruth : Spelling Base Strand3 5 := ⟨strandTruth, by decide⟩

/-- The competitor `AAAATT` as a §6.2 spelled candidate. -/
def spellCompetitor : Spelling Base Strand3 6 := ⟨strandCompetitor, by decide⟩

/-- No supersource and no supersink is used, the situation for a genuine circuit:
MB09 §6.2 notes that "the original double-stranded genome corresponds to a
circuit", and a closed circuit needs no terminal. -/
def noTerm : SuperTerminals Strand3 := noTerminals Strand3

/-- The concrete `noTerm` uses neither the supersource nor the supersink, which is
the zero-terminal-usage conjunct of `Feasible62`. -/
theorem noTerm_usage_zero : ∀ v, noTerm.srcUse v = 0 ∧ noTerm.snkUse v = 0 :=
  fun _ => ⟨rfl, rfl⟩

/-! ### The explicit circuits -/

/-- A numeric key identifying an overlap edge by the binary codes of its two
strands.  The certificate flows below are written with these keys rather than
with whole-edge equality: for length-`3` strands the code is injective on
molecule classes, so the keyed form denotes the same flow, and it keeps the flow
cheap enough for the kernel to evaluate the feasibility checks. -/
def ekey (e : BdEdge Base Strand3) : Nat := 8 * code3 e.sx + code3 e.sy

/-- The key of the edge between the strands `x` and `y`. -/
def keyOf (x y : Strand3) : Nat := 8 * code3 x + code3 y

/-- The flow of the truth's bidirected circuit: flow `1` on each of the five
overlap edges its walk traverses, and `0` elsewhere.  The five edges are
`AAA → AAT`, `AAT → ATT`, `ATT → TTA`, `TTA → TAA`, `TAA → AAA`, the circuit of
`docs/section62-mb09-bidirected-graph-audit.md` §3.1. -/
def truthCircuitFlow : BdFlow Base Strand3 := fun e =>
  if ekey e = keyOf (m3 .A .A .A) (m3 .A .A .T) then 1 else
  if ekey e = keyOf (m3 .A .A .T) (m3 .A .T .T) then 1 else
  if ekey e = keyOf (m3 .A .T .T) (m3 .T .T .A) then 1 else
  if ekey e = keyOf (m3 .T .T .A) (m3 .T .A .A) then 1 else
  if ekey e = keyOf (m3 .T .A .A) (m3 .A .A .A) then 1 else
  0

/-- The flow of the competitor's bidirected circuit: flow `1` on each of the six
overlap edges its walk traverses, and `0` elsewhere.  These are the truth's five
edges together with the `AAA → AAA` self-overlap, the circuit of
`docs/section62-mb09-bidirected-graph-audit.md` §3.2. -/
def competitorCircuitFlow : BdFlow Base Strand3 := fun e =>
  if ekey e = keyOf (m3 .A .A .A) (m3 .A .A .A) then 1 else
  if ekey e = keyOf (m3 .A .A .A) (m3 .A .A .T) then 1 else
  if ekey e = keyOf (m3 .A .A .T) (m3 .A .T .T) then 1 else
  if ekey e = keyOf (m3 .A .T .T) (m3 .T .T .A) then 1 else
  if ekey e = keyOf (m3 .T .T .A) (m3 .T .A .A) then 1 else
  if ekey e = keyOf (m3 .T .A .A) (m3 .A .A .A) then 1 else
  0



/-! ### The graph -/

/-- The §6.2 graph on the three observed molecules has exactly the ten bidirected
overlap edges of length `2` listed in
`docs/section62-mb09-bidirected-graph-audit.md` §2. -/
theorem graph_has_ten_edges : graph.length = 10 := by decide

/-- There are three observed read molecules. -/
theorem readVerts_length : readVerts.length = 3 := by decide

/-- The molecule classes of the three observed reads are the codes `0`, `1`, `4`,
which are exactly the `relevant` coordinates used by the §6.1 objective. -/
theorem readVerts_codes :
    repCode (m3 .A .A .A) = 0 ∧ repCode (m3 .A .A .T) = 1 ∧
      repCode (m3 .T .A .A) = 4 := by decide

/-- Each observed read molecule is its own class representative, so the vertex set
really is a set of molecule classes. -/
theorem readVerts_are_reps :
    rep3 (m3 .A .A .A) = m3 .A .A .A ∧ rep3 (m3 .A .A .T) = m3 .A .A .T ∧
      rep3 (m3 .T .A .A) = m3 .T .A .A := by decide

/-! ### Explicit walk evidence -/

/-- The molecule classes visited by a cyclic spelling, in order. -/
def visitsList {n : Nat} (sp : Spelling Base Strand3 n) : List Strand3 :=
  (List.finRange n).map (fun i => rep3 (sp.strand i))

/-- The truth's cyclic window walk visits, in order, the molecule classes
`AAA, AAT, AAT, TAA, TAA`: the bidirected circuit of
`docs/section62-mb09-bidirected-graph-audit.md` §3.1. -/
theorem truth_walk :
    visitsList spellTruth =
      [m3 .A .A .A, m3 .A .A .T, m3 .A .A .T, m3 .T .A .A, m3 .T .A .A] := by
  decide

/-- The competitor's cyclic window walk visits, in order, the molecule classes
`AAA, AAA, AAT, AAT, TAA, TAA`: the circuit of
`docs/section62-mb09-bidirected-graph-audit.md` §3.2. -/
theorem competitor_walk :
    visitsList spellCompetitor =
      [m3 .A .A .A, m3 .A .A .A, m3 .A .A .T, m3 .A .A .T, m3 .T .A .A, m3 .T .A .A] := by
  decide

/-! ### §6.2 feasibility of the truth and of the competitor, clause by clause

The four §6.2 clauses are stated and checked separately, per read vertex, so that
each fact is small, explicit and separately readable. -/

/-! #### Truth `AAATT` -/

/-- §6.2 edge lower bounds hold on every edge of the graph for the truth's
circuit.  MB09 §6.2 sets the lower bound of every non-vertex bound to `0`. -/
theorem truth_edge_lower_bounds : ∀ e ∈ graphList, (0 : ℕ) ≤ truthCircuitFlow e := by
  decide

/-- The truth's vertex throughput at `AAA` is `1`. -/
theorem truth_throughput_AAA :
    throughput Base Strand3 rep3 truthCircuitFlow graphList (m3 .A .A .A) = 1 := by
  decide

/-- The truth's vertex throughput at `AAT` is `2`. -/
theorem truth_throughput_AAT :
    throughput Base Strand3 rep3 truthCircuitFlow graphList (m3 .A .A .T) = 2 := by
  decide

/-- The truth's vertex throughput at `TAA` is `2`. -/
theorem truth_throughput_TAA :
    throughput Base Strand3 rep3 truthCircuitFlow graphList (m3 .T .A .A) = 2 := by
  decide

/-- The truth's vertex throughputs meet the §6.2 vertex lower bound `1`. -/
theorem truth_vertex_lower_bounds :
    ∀ v ∈ readVerts, (1 : ℕ) ≤ throughput Base Strand3 rep3 truthCircuitFlow graphList v := by
  decide

/-- The §3.4 signed-incidence balance of the truth's circuit is `0` at every read
vertex, with no supersource/supersink usage. -/
theorem truth_balance_zero :
    ∀ v ∈ readVerts, balance Base Strand3 rep3 truthCircuitFlow noTerm graphList v = 0 := by
  decide

/-- The truth's vertex throughputs are the truth's molecule spectrum. -/
theorem truth_throughput_is_spectrum :
    ∀ v ∈ readVerts, throughput Base Strand3 rep3 truthCircuitFlow graphList v = dS' v := by
  decide

/-- The truth's hand-written circuit is a §6.2 feasible flow. -/
theorem truth_feasible62 :
    Feasible62 Base Strand3 rep3 readVerts graphList truthCircuitFlow noTerm dS' :=
  ⟨⟨truth_edge_lower_bounds, truth_vertex_lower_bounds, truth_balance_zero,
    truth_throughput_is_spectrum⟩, noTerm_usage_zero⟩

/-! #### Competitor `AAAATT` -/

/-- §6.2 edge lower bounds hold on every edge of the graph for the competitor's
circuit. -/
theorem competitor_edge_lower_bounds :
    ∀ e ∈ graphList, (0 : ℕ) ≤ competitorCircuitFlow e := by
  decide

/-- The competitor's vertex throughput at `AAA` is `2`. -/
theorem competitor_throughput_AAA :
    throughput Base Strand3 rep3 competitorCircuitFlow graphList (m3 .A .A .A) = 2 := by
  decide

/-- The competitor's vertex throughput at `AAT` is `2`. -/
theorem competitor_throughput_AAT :
    throughput Base Strand3 rep3 competitorCircuitFlow graphList (m3 .A .A .T) = 2 := by
  decide

/-- The competitor's vertex throughput at `TAA` is `2`. -/
theorem competitor_throughput_TAA :
    throughput Base Strand3 rep3 competitorCircuitFlow graphList (m3 .T .A .A) = 2 := by
  decide

/-- The competitor's vertex throughputs meet the §6.2 vertex lower bound `1`. -/
theorem competitor_vertex_lower_bounds :
    ∀ v ∈ readVerts, (1 : ℕ) ≤
      throughput Base Strand3 rep3 competitorCircuitFlow graphList v := by
  decide

/-- The §3.4 signed-incidence balance of the competitor's circuit is `0` at every
read vertex, with no supersource/supersink usage. -/
theorem competitor_balance_zero :
    ∀ v ∈ readVerts, balance Base Strand3 rep3 competitorCircuitFlow noTerm graphList v = 0 := by
  decide

/-- The competitor's vertex throughputs are the competitor's molecule spectrum. -/
theorem competitor_throughput_is_spectrum :
    ∀ v ∈ readVerts, throughput Base Strand3 rep3 competitorCircuitFlow graphList v = dD' v := by
  decide

/-- The competitor's hand-written circuit is a §6.2 feasible flow. -/
theorem competitor_feasible62 :
    Feasible62 Base Strand3 rep3 readVerts graphList competitorCircuitFlow noTerm dD' :=
  ⟨⟨competitor_edge_lower_bounds, competitor_vertex_lower_bounds,
    competitor_balance_zero, competitor_throughput_is_spectrum⟩, noTerm_usage_zero⟩

/-! #### The spelled-candidate components -/

/-- Every position of the truth's cyclic walk visits an observed read molecule,
so the walk lives on the observed molecules. -/
theorem truth_visits_observed : VisitsObserved rep3 spellTruth readVerts := by
  unfold VisitsObserved
  decide

theorem competitor_visits_observed : VisitsObserved rep3 spellCompetitor readVerts := by
  unfold VisitsObserved
  decide

/-- Every step of the truth's cyclic walk is a real edge of the §6.2 overlap
graph: the candidate is spelled by the observed reads. -/
theorem truth_steps_in_graph : StepsInGraph rep3 readLen spellTruth graphList := by
  unfold StepsInGraph
  decide

theorem competitor_steps_in_graph :
    StepsInGraph rep3 readLen spellCompetitor graphList := by
  unfold StepsInGraph
  decide

/-- Every step of the truth's cyclic walk survives the transitive edge
reduction, so the circuit lives on the *transitively reduced* graph that §6.2
requires. -/
theorem truth_steps_survive_reduction :
    StepsSurviveReduction Base Strand3 toList3 rep3 rc3 readLen readVerts spellTruth
      graphList := by
  unfold StepsSurviveReduction transitivelyReduced
  decide

theorem competitor_steps_survive_reduction :
    StepsSurviveReduction Base Strand3 toList3 rep3 rc3 readLen readVerts
      spellCompetitor graphList := by
  unfold StepsSurviveReduction transitivelyReduced
  decide

/-- At every interior vertex of the truth's walk the arriving and departing
incidences are opposite, MB09 §3.2: it is a genuine bidirected circuit. -/
theorem truth_bidirected_circuit : BidirectedCircuit rep3 readLen spellTruth := by
  unfold BidirectedCircuit OppositeAtInterior
  decide

theorem competitor_bidirected_circuit :
    BidirectedCircuit rep3 readLen spellCompetitor := by
  unfold BidirectedCircuit OppositeAtInterior
  decide

/-! #### The two as spelled §6.2 candidates -/

/-- The truth, as a *spelled* §6.2 candidate: its cyclic window walk is a
bidirected circuit in the overlap graph, every step is an edge of that graph and
survives the transitive reduction, every position visits an observed read
molecule, and the flow the walk carries is feasible with throughput `dS`. -/
theorem truth_spelled_feasible62 :
    SpelledFeasible62 Base Strand3 toList3 rep3 rc3 readLen oMin readVerts spellTruth
      truthCircuitFlow noTerm dS' :=
  ⟨truth_visits_observed, truth_steps_in_graph, truth_steps_survive_reduction,
    truth_bidirected_circuit, truth_feasible62⟩

/-- The competitor, as a spelled §6.2 candidate. -/
theorem competitor_spelled_feasible62 :
    SpelledFeasible62 Base Strand3 toList3 rep3 rc3 readLen oMin readVerts
      spellCompetitor competitorCircuitFlow noTerm dD' :=
  ⟨competitor_visits_observed, competitor_steps_in_graph,
    competitor_steps_survive_reduction, competitor_bidirected_circuit,
    competitor_feasible62⟩

/-! ### The hand-written circuits are the walks' own flows -/

/-- The hand-written truth circuit is exactly the flow its cyclic window walk
carries, on every edge of the graph.  So the certificate is not a separate
object: it is the flow of the candidate's own bidirected walk, one unit of flow
per traversal. -/
theorem truthCircuitFlow_eq_walkFlow :
    ∀ e ∈ graphList, truthCircuitFlow e = spellTruth.flow rep3 readLen e := by
  decide

/-- Likewise for the competitor circuit. -/
theorem competitorCircuitFlow_eq_walkFlow :
    ∀ e ∈ graphList, competitorCircuitFlow e = spellCompetitor.flow rep3 readLen e := by
  decide

/-- The circuit never carries more than one unit of flow on an edge, so the
five (resp. six) walk steps account for the whole flow. -/
theorem truth_circuit_at_most_one : ∀ e ∈ graphList, truthCircuitFlow e ≤ 1 := by
  decide

theorem competitor_circuit_at_most_one :
    ∀ e ∈ graphList, competitorCircuitFlow e ≤ 1 := by
  decide

/-- The walk's visit counts are the candidate's molecule spectrum.  This is MB09
Observation 7, and it is what makes the throughput vector the spectrum. -/
theorem truth_visits_eq_spectrum :
    ∀ v ∈ readVerts, spellTruth.visits rep3 v = dS' v := by
  decide

theorem competitor_visits_eq_spectrum :
    ∀ v ∈ readVerts, spellCompetitor.visits rep3 v = dD' v := by
  decide

/-! ### Transitive edge reduction -/

/-- The transitive edge reduction removes no edge of this graph at all, under the
literal §6.2 reading "remove any overlap that is spelled by two shorter
overlaps".  Every overlap here has length `L − 1 = 2`, and the composition law
`len₁ + len₂ − L = len` with `len₁, len₂ < len` forces `len₁ + len₂ = L + len = 5`
with both `≤ 1`, which is impossible. -/
theorem graph_reduction_vacuous :
    ReductionVacuous Base Strand3 toList3 rc3 readLen readVerts graphList := by
  unfold ReductionVacuous
  decide

/-- The same holds under the alternative longer-overlap reading: the maximal
proper overlap is `L − 1 = 2`, so no two-edge path of strictly longer proper
overlaps exists. -/
theorem graph_reduction_vacuous_longer :
    ReductionVacuousLonger Base Strand3 toList3 rc3 readLen readVerts graphList := by
  unfold ReductionVacuousLonger
  decide

/-! ### The throughput vector is the spectrum the §6.1 objective uses -/

/-- The certified truth throughput vector has coordinates `dS 0`, `dS 1`, `dS 4`
on the three graph vertices, i.e. exactly the truth spectrum already
kernel-checked above and consumed by `lik`. -/
theorem truth_throughput_is_truth_spectrum :
    dS' (m3 .A .A .A) = dS 0 ∧ dS' (m3 .A .A .T) = dS 1 ∧
      dS' (m3 .T .A .A) = dS 4 := by
  decide

/-- Likewise for the competitor. -/
theorem competitor_throughput_is_competitor_spectrum :
    dD' (m3 .A .A .A) = dD 0 ∧ dD' (m3 .A .A .T) = dD 1 ∧
      dD' (m3 .T .A .A) = dD 4 := by
  decide

/-- The certified truth throughputs are `1, 2, 2`, matching the `d_S` of
`docs/section62-mb09-bidirected-graph-audit.md` §3.1: these are the per-vertex
flow and per-vertex spectrum facts above, composed. -/
theorem truth_throughput_values :
    dS' (m3 .A .A .A) = 1 ∧ dS' (m3 .A .A .T) = 2 ∧ dS' (m3 .T .A .A) = 2 :=
  ⟨by
    rw [← truth_throughput_is_spectrum (m3 .A .A .A) (by decide)]
    exact truth_throughput_AAA,
   by
    rw [← truth_throughput_is_spectrum (m3 .A .A .T) (by decide)]
    exact truth_throughput_AAT,
   by
    rw [← truth_throughput_is_spectrum (m3 .T .A .A) (by decide)]
    exact truth_throughput_TAA⟩

/-- The certified competitor throughputs are `2, 2, 2`, matching the `d_D` of the
same note §3.2. -/
theorem competitor_throughput_values :
    dD' (m3 .A .A .A) = 2 ∧ dD' (m3 .A .A .T) = 2 ∧ dD' (m3 .T .A .A) = 2 :=
  ⟨by
    rw [← competitor_throughput_is_spectrum (m3 .A .A .A) (by decide)]
    exact competitor_throughput_AAA,
   by
    rw [← competitor_throughput_is_spectrum (m3 .A .A .T) (by decide)]
    exact competitor_throughput_AAT,
   by
    rw [← competitor_throughput_is_spectrum (m3 .T .A .A) (by decide)]
    exact competitor_throughput_TAA⟩

/-- Combining with the `Fin 8` spectrum values, the certified throughputs are the
already kernel-checked `d_S = { AAA:1, AAT:2, TAA:2 }`. -/
theorem truth_throughput_matches_dS_values :
    dS' (m3 .A .A .A) = dS 0 ∧ dS' (m3 .A .A .T) = dS 1 ∧
      dS' (m3 .T .A .A) = dS 4 := truth_throughput_is_truth_spectrum

theorem competitor_throughput_matches_dD_values :
    dD' (m3 .A .A .A) = dD 0 ∧ dD' (m3 .A .A .T) = dD 1 ∧
      dD' (m3 .T .A .A) = dD 4 := competitor_throughput_is_competitor_spectrum

/-! ## Main finite theorem -/

/-- Kernel-checked finite counterexample with the **literal MB09 §6.2**
feasibility endpoint: the instance satisfies the source-faithful `I_s`
certificate — the shared, authoritative
`SourceFaithfulIs.InformationFeasible`, proved at full strength by finite
`decide` on `truthGenome` with read length `3` and the realized placements
`{0, 1, 4}`, and *also* the module-local `SourceCertificate`; the truth `AAATT`
and the named competitor `AAAATT` are both
genuine §6.2 spelled candidates — bidirected circuits in the transitively
reduced bidirected overlap graph on the observed read molecules, with edge lower
bounds `0`, the §6.2 vertex lower bound `1`, signed-incidence balance `0`, no
supersource/supersink usage, and vertex throughput equal to the candidate's
molecule spectrum; and the competitor strictly beats the truth under the literal
§6.1 objective. -/
theorem se62_bridging_bidirected_flow_counterexample :
    SourceFaithfulIs.InformationFeasible truthGenome 3 realizedStarts ∧
      SourceCertificate ∧
      SpelledFeasible62 Base Strand3 toList3 rep3 rc3 readLen oMin readVerts spellTruth
        truthCircuitFlow noTerm dS' ∧
      SpelledFeasible62 Base Strand3 toList3 rep3 rc3 readLen oMin readVerts
        spellCompetitor competitorCircuitFlow noTerm dD' ∧
      lik obs dS < lik obs dD :=
  ⟨truth_information_feasible, truth_source_certificate, truth_spelled_feasible62,
    competitor_spelled_feasible62, competitor_strictly_better⟩

/-- The earlier sequence-level statement, retained: §6.2 feasibility holds
*alongside* the proxy `SeqSupportLB` for both candidates, and the strict
improvement.  The §6.2 theorem above is the one that uses the source object. -/
theorem se62_bridging_flow_counterexample :
    SourceCertificate ∧ SeqSupportLB dS obs ∧ SeqSupportLB dD obs ∧ lik obs dS < lik obs dD :=
  ⟨truth_source_certificate, truth_feasible, competitor_feasible, competitor_strictly_better⟩

end AssemblyP1.Section62BridgingCounterexample
