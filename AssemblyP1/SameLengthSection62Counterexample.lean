import Mathlib
import AssemblyP1.SourceFaithfulIs
import AssemblyP1.Section62BidirectedFlow

/-!
# A finite SAME-LENGTH Section 6.2 bridging counterexample

This file kernel-checks the finite witness recorded in
`docs/section62-same-length-bidirected-counterexample.md`, using the shared
hypothesis layer `AssemblyP1.SourceFaithfulIs` and the shared §6.2 flow layer
`AssemblyP1.Section62Flow`.  Under the
Medvedev–Brudno (2009) §6.2 reading in which the vertices of the bidirected
read-overlap graph are read *DNA molecules* (a word and its reverse complement
are one vertex, and identical molecules are one vertex), the truth-induced flow
need not be a maximum-likelihood maximizer, even when:

* the source-faithful bridging hypothesis `I_s` holds;
* the truth is an admissible §6.2 spelled circuit;
* the competing candidate is a single spelled molecule of the **same length**
  as the truth (`|D| = |S| = G`).

Instance:

* alphabet `{A, T}` with the DNA reverse-complement involution `A ↔ T`;
* true circular genome `truth = AAATAT` (length `6`);
* read length `L = 3`, realized starts `(0, 0, 1, 3, 5)` (`n = 5` reads, start
  `0` sampled twice);
* external known genome size `N = 6` (Medvedev–Brudno §6.1);
* observed read-molecule classes `x = { AAA:2, AAT:1, ATA:1, TAA:1 }`;
* truth spectrum `d_S = { AAA:1, AAT:1, ATA:3, TAA:1 }`;
* competitor `D = AAAAAT` (length `6`), `d_D = { AAA:3, AAT:1, ATA:1, TAA:1 }`.

What is kernel-checked here.  This file proves the **literal Medvedev–Brudno
§6.2 feasibility** of both candidates, via `AssemblyP1.Section62Flow`:

* the explicit bidirected read-overlap graph on the four observed read
  molecules, its sixteen edges written out and proved equal to the generated
  `overlapEdges`;
* the transitive edge reduction, vacuous on this graph under both readings;
* the §6.2 vertex lower bound `1` and edge lower bounds `0`, the §3.4
  signed-incidence balance `0` at every read vertex, and **no
  supersource/supersink usage**;
* the vertex throughputs, which by Observation 7 are `d_S` and `d_D` as already
  used by the objectives below;
* the **shared, authoritative** `SourceFaithfulIs.InformationFeasible` predicate
  `I_s` at full strength — coverage, *every* triple repeat all-bridged, and
  *every* interleaved pair of repeats bridged, quantified over all repeat lengths
  and all selected starts — proved by finite `decide` on the `Genome` object
  `truthGenome` with read length `3` and the realized placements `{0, 1, 3, 5}`.
  The sampling realization samples start `0` twice; the duplicate collapses
  because `Covers` and `BridgesCopy` quantify over placements, and the sampled
  multiplicity is recorded separately by the read-type counts `obs`.  The
  module-local `SourceCertificate` is retained as supporting evidence only;
* the exact candidate-length equality `genomeLength truth = genomeLength
  competitor`, so this remains the fixed-length sub-case `|D| = |S| = G`;
* the strict improvement under both same-length objectives:
  the literal §6.1 product-of-binomial-marginals ratio `L(D)/L(S) = 5`, and the
  candidate-intrinsic exact multinomial ratio `exact(D)/exact(S) = 3`.

The endpoint theorem is `samelength_se62_bidirected_flow_counterexample`, whose
feasibility clauses are `SpelledFeasible62`, not the `SeqSupport` proxy.
`SeqSupport` is retained as `samelength_se62_counterexample` only as supporting
evidence, and `scripts/verify_samelength_se62_counterexample.py` remains as a
second, implementation-independent check of the same graph and circuits.

Scope.  This file is about the finite instance only.  It does not settle which
Medvedev–Brudno object the Shomorony et al. (2016) sentence intends, nor the
per-occurrence strengthening or the single-strand reading.
-/

set_option maxHeartbeats 4000000

namespace AssemblyP1.SameLengthSection62Counterexample

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

/-- The true circular genome `AAATAT` of length `6`. -/
def truth : Fin 6 → Base := ![.A, .A, .A, .T, .A, .T]

/-- The competitor `AAAAAT` of length `6`. -/
def competitor : Fin 6 → Base := ![.A, .A, .A, .A, .A, .T]

/-! ### The truth as the shared source-faithful object

The hypothesis side of this counterexample is stated with the *shared* predicate
`SourceFaithfulIs.InformationFeasible`, the same object every other AssemblyP1
counterexample module uses, rather than with a module-local stand-in. -/

open SourceFaithfulIs

/-- The true circular genome `AAATAT` in the shared source-faithful
representation.  This is a reducible abbreviation, not an opaque `def`, so that the
`Fin`-indexed numerals and the `Decidable` instances of the shared layer are
found by instance search when `I_s` membership is decided. -/
abbrev truthGenome : SourceFaithfulIs.Genome Base where
  len := 6
  len_pos := by norm_num
  sym := truth

/-- The competing candidate `AAAAAT` in the shared source-faithful
representation, so that candidate-intrinsic length is intrinsic to the object. -/
abbrev competitorGenome : SourceFaithfulIs.Genome Base where
  len := 6
  len_pos := by norm_num
  sym := competitor

/-- The realized length-`3` read placements, as a set of distinct starts.

The sampling realization is `readStarts = [0, 0, 1, 3, 5]`: start `0` was sampled
twice.  Coverage and bridging are properties of the latent *placements*, and
`SourceFaithfulIs.Covers`/`BridgesCopy` quantify over a `Finset` of start
positions, so the repeated sampling collapses to a single placement here.  The
sampled multiplicity is not lost: it is recorded by the read-type counts `obs`,
which is what the likelihood consumes. -/
def realizedStarts : Finset (Fin 6) := {0, 1, 3, 5}

/-- The realized start set is exactly the set of distinct entries of the sampling
realization, so collapsing the duplicate sample loses no placement. -/
theorem realizedStarts_eq : realizedStarts = {0, 1, 3, 5} := rfl

/-- The shared `Genome` length of the truth is the length used everywhere else in
this file. -/
theorem truthGenome_len : truthGenome.len = 6 := rfl

/-- **The actual `I_s` hypothesis for this realization.**  This is
`SourceFaithfulIs.InformationFeasible` at full strength — coverage, *every*
triple repeat all-bridged, and *every* interleaved pair of repeats bridged,
quantified over all repeat lengths and all selected starts — discharged by finite
`decide` on `truthGenome` with read length `3` and the realized start set
`{0, 1, 3, 5}`.  No repeat is enumerated by hand and no clause is assumed. -/
theorem truth_information_feasible :
    SourceFaithfulIs.InformationFeasible truthGenome 3 realizedStarts := by
  decide

/-- Circular symbol access for a length-`6` genome. -/
def cyc6 (g : Fin 6 → Base) (i : Nat) : Base :=
  g ⟨i % 6, Nat.mod_lt _ (by norm_num)⟩

/-- Length-`3` circular window at start `r`. -/
def window6 (g : Fin 6 → Base) (r : Fin 6) : W3 :=
  ![cyc6 g r.val, cyc6 g (r.val + 1), cyc6 g (r.val + 2)]

/-- Number of starts of a length-`6` genome whose window has molecule class `c`. -/
def spec6 (g : Fin 6 → Base) (c : Fin 8) : Nat :=
  (Finset.univ.filter (fun r : Fin 6 => cls (window6 g r) = c)).card

/-- The realized read starts, with start `0` sampled twice. -/
def readStarts : List (Fin 6) := [0, 0, 1, 3, 5]

/-- Observed read-molecule class counts `x`. -/
def obs (c : Fin 8) : Nat :=
  (readStarts.filter (fun r => cls (window6 truth r) = c)).length

/-- Truth-induced spectrum `d_S`. -/
def dS (c : Fin 8) : Nat := spec6 truth c

/-- Competitor spectrum `d_D`. -/
def dD (c : Fin 8) : Nat := spec6 competitor c

/-! ## Spelled-circuit §6.2 feasibility

The source §6.2 lower bound is per read *vertex*.  A circular molecule `D` is
spelled by a walk of read vertices iff every length-`L` submolecule of `D` is an
observed read molecule and every observed read molecule occurs in `D`
(Observation 7).  For a spelled molecule this is exactly support equality. -/

/-- §6.2 spelled-circuit feasibility: the candidate spectrum and the observed
spectrum have the same support, so the cyclic window walk visits every observed
read vertex (vertex lower bound `1`). -/
def SeqSupport (d x : Fin 8 → Nat) : Prop :=
  ∀ c, 0 < d c ↔ 0 < x c

theorem truth_support : SeqSupport dS obs := by
  unfold SeqSupport dS obs spec6 window6 cyc6 cls code rc bitA comp truth readStarts
  decide

theorem competitor_support : SeqSupport dD obs := by
  unfold SeqSupport dD obs spec6 window6 cyc6 cls code rc bitA comp truth competitor
    readStarts
  decide

theorem dS_0 : dS 0 = 1 := by
  unfold dS spec6 window6 cyc6 cls code rc bitA comp truth; decide

theorem dS_1 : dS 1 = 1 := by
  unfold dS spec6 window6 cyc6 cls code rc bitA comp truth; decide

theorem dS_2 : dS 2 = 3 := by
  unfold dS spec6 window6 cyc6 cls code rc bitA comp truth; decide

theorem dS_4 : dS 4 = 1 := by
  unfold dS spec6 window6 cyc6 cls code rc bitA comp truth; decide

theorem dD_0 : dD 0 = 3 := by
  unfold dD spec6 window6 cyc6 cls code rc bitA comp competitor; decide

theorem dD_1 : dD 1 = 1 := by
  unfold dD spec6 window6 cyc6 cls code rc bitA comp competitor; decide

theorem dD_2 : dD 2 = 1 := by
  unfold dD spec6 window6 cyc6 cls code rc bitA comp competitor; decide

theorem dD_4 : dD 4 = 1 := by
  unfold dD spec6 window6 cyc6 cls code rc bitA comp competitor; decide

/-! ## Source-faithful `I_s` certificate -/

/-- A read starting at `r` occupies positions `r, r+1, r+2` modulo `6`. -/
def inRead (r : Fin 6) (p : Nat) : Bool :=
  decide (p % 6 = r.val) || decide (p % 6 = (r.val + 1) % 6) ||
    decide (p % 6 = (r.val + 2) % 6)

/-- Coverage: every position of the truth lies in some realized read. -/
def coversB : Bool :=
  (List.range 6).all (fun p => readStarts.any (fun r => inRead r p))

/-- Agreement of the length-`e` windows starting at `t1` and `t2`. -/
def eqWin (g : Fin 6 → Base) (e t1 t2 : Nat) : Bool :=
  (List.range e).all (fun j => decide (cyc6 g (t1 + j) = cyc6 g (t2 + j)))

/-- The preceding symbols of a triple are not all equal. -/
def notAllEqPre (g : Fin 6 → Base) (t1 t2 t3 : Nat) : Bool :=
  !(decide (cyc6 g (t1 + 5) = cyc6 g (t2 + 5)) &&
    decide (cyc6 g (t2 + 5) = cyc6 g (t3 + 5)))

/-- The following symbols of a triple (length `e`) are not all equal. -/
def notAllEqPost (g : Fin 6 → Base) (e t1 t2 t3 : Nat) : Bool :=
  !(decide (cyc6 g (t1 + e) = cyc6 g (t2 + e)) &&
    decide (cyc6 g (t2 + e) = cyc6 g (t3 + e)))

/-- A maximal triple repeat of length `e` at the three ordered starts. -/
def isTripleRepeat (e t1 t2 t3 : Nat) : Bool :=
  decide (1 ≤ e) && decide (t1 < t2) && decide (t2 < t3) && decide (t3 < 6) &&
  eqWin truth e t1 t2 && eqWin truth e t1 t3 &&
  notAllEqPre truth t1 t2 t3 && notAllEqPost truth e t1 t2 t3

/-- Strict copy bridging: a read bridges the length-`e` copy at `t` when it
strictly extends it on both sides, i.e. occupies positions `t-1` and `t+e`. -/
def bridgedCopy (e t : Nat) : Bool :=
  readStarts.any (fun r => inRead r (t + 5) && inRead r (t + e))

/-- Every maximal triple repeat is all-bridged. -/
def tripleAllBridgedB : Bool :=
  (List.range 6).all fun e =>
  (List.range 6).all fun t1 =>
  (List.range 6).all fun t2 =>
  (List.range 6).all fun t3 =>
    !(isTripleRepeat e t1 t2 t3) ||
      (bridgedCopy e t1 && bridgedCopy e t2 && bridgedCopy e t3)

/-- A maximal repeat pair of length `e` at starts `a < b`. -/
def isMaxPair (e a b : Nat) : Bool :=
  decide (1 ≤ e) && decide (e < 6) && decide (a < b) && decide (b < 6) &&
  eqWin truth e a b &&
  decide (cyc6 truth (a + 5) ≠ cyc6 truth (b + 5)) &&
  decide (cyc6 truth (a + e) ≠ cyc6 truth (b + e))

/-- Four pairwise-distinct starts. -/
def fourDistinct (a b c d : Nat) : Bool :=
  decide (a ≠ c) && decide (a ≠ d) && decide (b ≠ c) && decide (b ≠ d)

/-- Every interleaved pair of maximal repeats is bridged (at least one of the
four selected copies is bridged), where interleaving is the Bresler alternating
order. -/
def interleavedB : Bool :=
  (List.range 6).all fun e1 =>
  (List.range 6).all fun a =>
  (List.range 6).all fun b =>
  (List.range 6).all fun e2 =>
  (List.range 6).all fun c =>
  (List.range 6).all fun d =>
    !(isMaxPair e1 a b && isMaxPair e2 c d && fourDistinct a b c d &&
      (decide (a < c && c < b && b < d) || decide (c < a && a < d && d < b))) ||
      (bridgedCopy e1 a || bridgedCopy e1 b || bridgedCopy e2 c ||
        bridgedCopy e2 d)

/-- The kernel-checked source-faithful `I_s` hypothesis: coverage, every
maximal triple repeat all-bridged, and every interleaved pair bridged. -/
def SourceCertificate : Prop :=
  coversB = true ∧ tripleAllBridgedB = true ∧ interleavedB = true

theorem truth_source_certificate : SourceCertificate := by
  unfold SourceCertificate coversB tripleAllBridgedB interleavedB isTripleRepeat
    isMaxPair fourDistinct eqWin notAllEqPre notAllEqPost bridgedCopy inRead
    readStarts cyc6 truth
  decide

/-! ## Literal §6.1 product-of-binomial-marginals objective -/

/-- One §6.1 binomial marginal for molecule class `c`, with fixed external
`N = 6`, total reads `n = 5`, observed count `x c`, and candidate count `d c`. -/
def marginal (x d : Fin 8 → Nat) (c : Fin 8) : ℚ :=
  (Nat.choose 5 (x c) : ℚ) * ((d c : ℚ) / 6) ^ (x c) *
    (1 - (d c : ℚ) / 6) ^ (5 - x c)

/-- The literal §6.1 product of binomial marginals over the molecule-class
space (zero-count factors retained). -/
def lik (x d : Fin 8 → Nat) : ℚ :=
  ∏ c : Fin 8, marginal x d c

/-- The four molecule classes with positive observed or candidate count:
`AAA` (code `0`), `AAT` (code `1`), `ATA` (code `2`), `TAA` (code `4`). -/
def relevant : Finset (Fin 8) := {0, 1, 2, 4}

/-- A class with zero observed count and zero candidate multiplicity contributes
the factor `1` to the literal product. -/
lemma marginal_eq_one_of_zero (x d : Fin 8 → Nat) (c : Fin 8)
    (hx : x c = 0) (hd : d c = 0) : marginal x d c = 1 := by
  simp [marginal, hx, hd]

lemma lik_eq_relevant_prod (x d : Fin 8 → Nat)
    (h : ∀ c : Fin 8, c ∉ relevant → x c = 0 ∧ d c = 0) :
    lik x d = ∏ c ∈ relevant, marginal x d c := by
  unfold lik
  exact (Finset.prod_subset (s₁ := relevant) (s₂ := Finset.univ)
    (by intro c _; exact Finset.mem_univ c)
    (by intro c _ hc; exact marginal_eq_one_of_zero x d c (h c hc).1 (h c hc).2)).symm

theorem truth_zero_off :
    ∀ c : Fin 8, c ∉ relevant → obs c = 0 ∧ dS c = 0 := by
  unfold relevant obs dS spec6 window6 cyc6 cls code rc bitA comp truth readStarts
  decide

theorem competitor_zero_off :
    ∀ c : Fin 8, c ∉ relevant → obs c = 0 ∧ dD c = 0 := by
  unfold relevant obs dD spec6 window6 cyc6 cls code rc bitA comp truth competitor
    readStarts
  decide

/-- Expansion of a product over the four-element `relevant` set. -/
lemma relevant_prod_eq (f : Fin 8 → ℚ) :
    ∏ c ∈ relevant, f c = f 0 * (f 1 * (f 2 * f 4)) := by
  unfold relevant
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]

theorem obs_0 : obs 0 = 2 := by
  unfold obs window6 cyc6 cls code rc bitA comp truth readStarts; decide

theorem obs_1 : obs 1 = 1 := by
  unfold obs window6 cyc6 cls code rc bitA comp truth readStarts; decide

theorem obs_2 : obs 2 = 1 := by
  unfold obs window6 cyc6 cls code rc bitA comp truth readStarts; decide

theorem obs_4 : obs 4 = 1 := by
  unfold obs window6 cyc6 cls code rc bitA comp truth readStarts; decide

theorem lik_truth :
    lik obs dS = (marginal obs dS 0) * ((marginal obs dS 1) *
      ((marginal obs dS 2) * (marginal obs dS 4))) := by
  rw [lik_eq_relevant_prod obs dS truth_zero_off, relevant_prod_eq]

theorem lik_competitor :
    lik obs dD = (marginal obs dD 0) * ((marginal obs dD 1) *
      ((marginal obs dD 2) * (marginal obs dD 4))) := by
  rw [lik_eq_relevant_prod obs dD competitor_zero_off, relevant_prod_eq]

theorem lik_truth_pos : 0 < lik obs dS := by
  rw [lik_truth]
  norm_num [marginal, obs_0, obs_1, obs_2, obs_4, dS_0, dS_1, dS_2, dS_4,
    Nat.choose]

/-- The competitor strictly beats the truth under the literal §6.1 objective:
ratio `5`. -/
theorem lik_competitor_over_truth : lik obs dD / lik obs dS = 5 := by
  rw [lik_truth, lik_competitor]
  norm_num [marginal, obs_0, obs_1, obs_2, obs_4, dS_0, dS_1, dS_2, dS_4,
    dD_0, dD_1, dD_2, dD_4, Nat.choose]

theorem competitor_strictly_better : lik obs dS < lik obs dD := by
  have h := lik_competitor_over_truth
  have hpos := lik_truth_pos
  rw [div_eq_iff (ne_of_gt hpos)] at h
  rw [h]
  nlinarith [hpos]

/-! ## Candidate-intrinsic exact multinomial (same-length) -/

/-- One exact-multinomial factor for molecule class `c`: `(d c)^{x c}`. -/
def exactFactor (d x : Fin 8 → Nat) (c : Fin 8) : ℚ :=
  (d c : ℚ) ^ (x c)

/-- The exact multinomial likelihood up to the constants that cancel between
two same-length candidates: `∏_c (d c)^{x c}`. -/
def exactLik (d x : Fin 8 → Nat) : ℚ :=
  ∏ c : Fin 8, exactFactor d x c

lemma exactFactor_eq_one_of_zero (d x : Fin 8 → Nat) (c : Fin 8)
    (hx : x c = 0) : exactFactor d x c = 1 := by
  simp [exactFactor, hx]

/-- Outside `relevant` the observed count vanishes, so the corresponding factor
is `1`. -/
lemma exactLik_eq_relevant (d x : Fin 8 → Nat)
    (h : ∀ c : Fin 8, c ∉ relevant → x c = 0) :
    exactLik d x = ∏ c ∈ relevant, exactFactor d x c := by
  unfold exactLik
  exact (Finset.prod_subset (s₁ := relevant) (s₂ := Finset.univ)
    (by intro c _; exact Finset.mem_univ c)
    (by intro c _ hc; exact exactFactor_eq_one_of_zero d x c (h c hc))).symm

theorem exactLik_truth : exactLik dS obs = 3 := by
  rw [exactLik_eq_relevant dS obs (fun c hc => (truth_zero_off c hc).1),
    relevant_prod_eq]
  norm_num [exactFactor, dS_0, dS_1, dS_2, dS_4, obs_0, obs_1, obs_2, obs_4]

theorem exactLik_competitor : exactLik dD obs = 9 := by
  rw [exactLik_eq_relevant dD obs (fun c hc => (competitor_zero_off c hc).1),
    relevant_prod_eq]
  norm_num [exactFactor, dD_0, dD_1, dD_2, dD_4, obs_0, obs_1, obs_2, obs_4]

/-- The competitor strictly beats the truth under the exact same-length
multinomial objective: ratio `3`. -/
theorem exactLik_over_truth : exactLik dD obs / exactLik dS obs = 3 := by
  rw [exactLik_truth, exactLik_competitor]; norm_num

/-! ## Literal §6.2 bidirected-flow feasibility (MB09 §6.2)

Everything below replaces the `SeqSupport` proxy by the actual §6.2 object: the
explicit bidirected read-overlap graph on the observed read *molecules*, its
transitive edge reduction, the vertex and edge lower bounds, the §3.4
signed-incidence balance, and the supersource/supersink circulation conversion.

Strand and candidate semantics are unchanged: vertices are molecule classes
(MB09 §3.1, §4.1) and the candidates are still the circular sequences `truth` and
`competitor`, both of length `6`.  Only the feasibility predicate is replaced, and
the exact candidate-length equality `|S| = |D| = 6` is preserved throughout. -/

open AssemblyP1.Section62Flow

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

/-- A *strand*: one single-stranded DNA sequence, as the list of its symbols. -/
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
reverse-complement pair.  This is the indexing used by the already kernel-checked
spectra `dS`, `dD` and by the §6.1 and exact-multinomial objectives. -/
def repCode (w : Strand3) : Fin 8 :=
  if h : min (code3 w) (code3 (rc3 w)) < 8 then ⟨min (code3 w) (code3 (rc3 w)), h⟩
  else 0

/-- The four observed read DNA molecules, the vertices of the §6.2 graph. -/
def readVerts : List Strand3 :=
  [m3 .A .A .A, m3 .A .A .T, m3 .A .T .A, m3 .T .A .A]

/-- The read length `L = 3`. -/
def readLen : Nat := 3

/-- The §6.2 overlap threshold for this instance, `o_min = L − 1 = 2`. -/
def oMin : Nat := 2

/-- The explicit bidirected overlap graph of MB09 §6.2 on the observed read
molecules. -/
def graph : List (BdEdge Base Strand3) :=
  overlapEdges Base Strand3 toList3 rep3 rc3 readLen oMin readVerts

/-- The sixteen §6.2 overlap edges, written out, in the order `overlapEdges`
generates them.  The feasibility checks below use this explicit list so that they
stay shallow enough for the kernel to evaluate; `graph_eq` identifies it with the
generated graph. -/
def graphList : List (BdEdge Base Strand3) :=
  [ e2 (m3 .A .A .A) (m3 .A .A .A), e2 (m3 .A .A .A) (m3 .A .A .T),
    e2 (m3 .A .A .T) (m3 .A .T .A), e2 (m3 .A .A .T) (m3 .A .T .T),
    e2 (m3 .A .T .A) (m3 .T .A .A), e2 (m3 .A .T .A) (m3 .T .A .T),
    e2 (m3 .T .A .A) (m3 .A .A .A), e2 (m3 .T .A .A) (m3 .A .A .T),
    e2 (m3 .T .T .T) (m3 .T .T .T), e2 (m3 .T .T .T) (m3 .T .T .A),
    e2 (m3 .A .T .T) (m3 .T .T .T), e2 (m3 .A .T .T) (m3 .T .T .A),
    e2 (m3 .T .A .T) (m3 .A .T .A), e2 (m3 .T .A .T) (m3 .A .T .T),
    e2 (m3 .T .T .A) (m3 .T .A .A), e2 (m3 .T .T .A) (m3 .T .A .T) ]

/-- The written-out edge list is exactly the generated §6.2 overlap graph. -/
theorem graph_eq : graph = graphList := by decide

/-- The strand read at start `r` of the truth `AAATAT`. -/
def strandTruth (r : Fin 6) : Strand3 :=
  [cyc6 truth r.val, cyc6 truth (r.val + 1), cyc6 truth (r.val + 2)]

/-- The strand read at start `r` of the competitor `AAAAAT`. -/
def strandCompetitor (r : Fin 6) : Strand3 :=
  [cyc6 competitor r.val, cyc6 competitor (r.val + 1), cyc6 competitor (r.val + 2)]

/-- The truth's molecule spectrum indexed by molecule class: the throughput vector
`d` that §6.2 requires, by Observation 7.  This is exactly the `Fin 8` spectrum
`dS` consumed by the objectives above, relabelled by molecule class. -/
def dS' (w : Strand3) : Nat := dS (repCode w)

/-- The competitor's molecule spectrum, likewise relabelled by molecule class. -/
def dD' (w : Strand3) : Nat := dD (repCode w)

/-- The truth `AAATAT` as a §6.2 spelled candidate. -/
def spellTruth : Spelling Base Strand3 6 := ⟨strandTruth, by decide⟩

/-- The competitor `AAAAAT` as a §6.2 spelled candidate.  It has the same length
`6` as the truth, which is what makes this the fixed-candidate-length sub-case. -/
def spellCompetitor : Spelling Base Strand3 6 := ⟨strandCompetitor, by decide⟩

/-- No supersource and no supersink is used: both candidates are genuine circuits. -/
def noTerm : SuperTerminals Strand3 := noTerminals Strand3

/-- The concrete `noTerm` uses neither the supersource nor the supersink, which is
the zero-terminal-usage conjunct of `Feasible62`. -/
theorem noTerm_usage_zero : ∀ v, noTerm.srcUse v = 0 ∧ noTerm.snkUse v = 0 :=
  fun _ => ⟨rfl, rfl⟩

/-- A numeric key identifying an overlap edge by the binary codes of its two
strands.  The certificate flows below use these keys so that they stay cheap
enough for the kernel to evaluate the feasibility checks. -/
def ekey (e : BdEdge Base Strand3) : Nat := 8 * code3 e.sx + code3 e.sy

/-- The key of the edge between the strands `x` and `y`. -/
def keyOf (x y : Strand3) : Nat := 8 * code3 x + code3 y

/-- The flow of the truth's bidirected circuit: flow `1` on each of the six
overlap edges its walk traverses, and `0` elsewhere.  The edges are
`AAA → AAT`, `AAT → ATA`, `ATA → TAT`, `TAT → ATA`, `ATA → TAA`, `TAA → AAA`. -/
def truthCircuitFlow : BdFlow Base Strand3 := fun e =>
  if ekey e = keyOf (m3 .A .A .A) (m3 .A .A .T) then 1 else
  if ekey e = keyOf (m3 .A .A .T) (m3 .A .T .A) then 1 else
  if ekey e = keyOf (m3 .A .T .A) (m3 .T .A .T) then 1 else
  if ekey e = keyOf (m3 .T .A .T) (m3 .A .T .A) then 1 else
  if ekey e = keyOf (m3 .A .T .A) (m3 .T .A .A) then 1 else
  if ekey e = keyOf (m3 .T .A .A) (m3 .A .A .A) then 1 else
  0

/-- The flow of the competitor's bidirected circuit.  The walk visits `AAA` three
times but traverses the `AAA → AAA` self-overlap only twice, so that edge carries
flow `2`; the other four edges carry `1`. -/
def competitorCircuitFlow : BdFlow Base Strand3 := fun e =>
  if ekey e = keyOf (m3 .A .A .A) (m3 .A .A .A) then 2 else
  if ekey e = keyOf (m3 .A .A .A) (m3 .A .A .T) then 1 else
  if ekey e = keyOf (m3 .A .A .T) (m3 .A .T .A) then 1 else
  if ekey e = keyOf (m3 .A .T .A) (m3 .T .A .A) then 1 else
  if ekey e = keyOf (m3 .T .A .A) (m3 .A .A .A) then 1 else
  0

/-! ### The graph and the candidate-length equality -/

/-- The §6.2 graph on the four observed molecules has exactly the sixteen
bidirected overlap edges of length `2`. -/
theorem graph_has_sixteen_edges : graph.length = 16 := by decide

/-- There are four observed read molecules. -/
theorem readVerts_length : readVerts.length = 4 := by decide

/-- The genome length of a circular candidate presented as `Fin n → Base`: it is
`n`, the number of cyclic positions. -/
def genomeLength {n : Nat} (_g : Fin n → Base) : Nat := n

/-- The truth has length `G = 6`. -/
theorem truth_genome_length : genomeLength truth = 6 := rfl

/-- The competitor also has length `6`. -/
theorem competitor_genome_length : genomeLength competitor = 6 := rfl

/-- The exact candidate-length equality of this sub-case, kept explicit: the
competing candidate is a single spelled molecule of the same length as the truth,
so this is the fixed-length case `|D| = |S| = G`. -/
theorem same_candidate_length : genomeLength truth = genomeLength competitor := rfl

/-! ### Explicit walk evidence -/

/-- The molecule classes visited by a cyclic spelling, in order. -/
def visitsList {n : Nat} (sp : Spelling Base Strand3 n) : List Strand3 :=
  (List.finRange n).map (fun i => rep3 (sp.strand i))

/-- The truth's cyclic window walk visits `AAA, AAT, ATA, ATA, ATA, TAA`. -/
theorem truth_walk :
    visitsList spellTruth =
      [m3 .A .A .A, m3 .A .A .T, m3 .A .T .A, m3 .A .T .A, m3 .A .T .A, m3 .T .A .A] := by
  decide

/-- The competitor's cyclic window walk visits `AAA, AAA, AAA, AAT, ATA, TAA`. -/
theorem competitor_walk :
    visitsList spellCompetitor =
      [m3 .A .A .A, m3 .A .A .A, m3 .A .A .A, m3 .A .A .T, m3 .A .T .A, m3 .T .A .A] := by
  decide

/-! ### §6.2 feasibility, clause by clause -/

/-- §6.2 edge lower bounds hold on every edge for the truth's circuit. -/
theorem truth_edge_lower_bounds : ∀ e ∈ graphList, (0 : ℕ) ≤ truthCircuitFlow e := by
  decide

/-- The truth's vertex throughput at `AAA` is `1`. -/
theorem truth_throughput_AAA :
    throughput Base Strand3 rep3 truthCircuitFlow graphList (m3 .A .A .A) = 1 := by
  decide

/-- The truth's vertex throughput at `AAT` is `1`. -/
theorem truth_throughput_AAT :
    throughput Base Strand3 rep3 truthCircuitFlow graphList (m3 .A .A .T) = 1 := by
  decide

/-- The truth's vertex throughput at `ATA` is `3`. -/
theorem truth_throughput_ATA :
    throughput Base Strand3 rep3 truthCircuitFlow graphList (m3 .A .T .A) = 3 := by
  decide

/-- The truth's vertex throughput at `TAA` is `1`. -/
theorem truth_throughput_TAA :
    throughput Base Strand3 rep3 truthCircuitFlow graphList (m3 .T .A .A) = 1 := by
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

/-- §6.2 edge lower bounds hold on every edge for the competitor's circuit. -/
theorem competitor_edge_lower_bounds :
    ∀ e ∈ graphList, (0 : ℕ) ≤ competitorCircuitFlow e := by
  decide

/-- The competitor's vertex throughput at `AAA` is `3`. -/
theorem competitor_throughput_AAA :
    throughput Base Strand3 rep3 competitorCircuitFlow graphList (m3 .A .A .A) = 3 := by
  decide

/-- The competitor's vertex throughput at `AAT` is `1`. -/
theorem competitor_throughput_AAT :
    throughput Base Strand3 rep3 competitorCircuitFlow graphList (m3 .A .A .T) = 1 := by
  decide

/-- The competitor's vertex throughput at `ATA` is `1`. -/
theorem competitor_throughput_ATA :
    throughput Base Strand3 rep3 competitorCircuitFlow graphList (m3 .A .T .A) = 1 := by
  decide

/-- The competitor's vertex throughput at `TAA` is `1`. -/
theorem competitor_throughput_TAA :
    throughput Base Strand3 rep3 competitorCircuitFlow graphList (m3 .T .A .A) = 1 := by
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

/-! ### The spelled-candidate components -/

/-- Every position of the truth's walk visits an observed read molecule. -/
theorem truth_visits_observed : VisitsObserved rep3 spellTruth readVerts := by
  unfold VisitsObserved
  decide

theorem competitor_visits_observed : VisitsObserved rep3 spellCompetitor readVerts := by
  unfold VisitsObserved
  decide

/-- Every step of the truth's walk is a real edge of the §6.2 overlap graph. -/
theorem truth_steps_in_graph : StepsInGraph rep3 readLen spellTruth graphList := by
  unfold StepsInGraph
  decide

theorem competitor_steps_in_graph : StepsInGraph rep3 readLen spellCompetitor graphList := by
  unfold StepsInGraph
  decide

/-- Every step of the truth's walk survives the transitive edge reduction, so the
circuit lives on the *transitively reduced* graph §6.2 requires. -/
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

/-- At every interior vertex of each walk the arriving and departing incidences
are opposite (MB09 §3.2): both are genuine bidirected circuits. -/
theorem truth_bidirected_circuit : BidirectedCircuit rep3 readLen spellTruth := by
  unfold BidirectedCircuit OppositeAtInterior
  decide

theorem competitor_bidirected_circuit : BidirectedCircuit rep3 readLen spellCompetitor := by
  unfold BidirectedCircuit OppositeAtInterior
  decide

/-- The truth, as a *spelled* §6.2 candidate. -/
theorem truth_spelled_feasible62 :
    SpelledFeasible62 Base Strand3 toList3 rep3 rc3 readLen oMin readVerts spellTruth
      truthCircuitFlow noTerm dS' :=
  ⟨truth_visits_observed, truth_steps_in_graph, truth_steps_survive_reduction,
    truth_bidirected_circuit, truth_feasible62⟩

/-- The competitor, as a spelled §6.2 candidate of the *same* length. -/
theorem competitor_spelled_feasible62 :
    SpelledFeasible62 Base Strand3 toList3 rep3 rc3 readLen oMin readVerts
      spellCompetitor competitorCircuitFlow noTerm dD' :=
  ⟨competitor_visits_observed, competitor_steps_in_graph,
    competitor_steps_survive_reduction, competitor_bidirected_circuit,
    competitor_feasible62⟩

/-! ### The hand-written circuits are the walks' own flows -/

/-- The hand-written truth circuit is exactly the flow its cyclic window walk
carries, on every edge of the graph. -/
theorem truthCircuitFlow_eq_walkFlow :
    ∀ e ∈ graphList, truthCircuitFlow e = spellTruth.flow rep3 readLen e := by
  decide

/-- Likewise for the competitor circuit. -/
theorem competitorCircuitFlow_eq_walkFlow :
    ∀ e ∈ graphList, competitorCircuitFlow e = spellCompetitor.flow rep3 readLen e := by
  decide

/-- The walk's visit counts are the candidate's molecule spectrum (Observation 7). -/
theorem truth_visits_eq_spectrum :
    ∀ v ∈ readVerts, spellTruth.visits rep3 v = dS' v := by
  decide

theorem competitor_visits_eq_spectrum :
    ∀ v ∈ readVerts, spellCompetitor.visits rep3 v = dD' v := by
  decide

/-! ### Transitive edge reduction -/

/-- The transitive edge reduction removes no edge of this graph, under the literal
§6.2 reading.  Every overlap has length `L − 1 = 2`, and the composition law
`len₁ + len₂ − L = len` with `len₁, len₂ < len` is unsatisfiable here. -/
theorem graph_reduction_vacuous :
    ReductionVacuous Base Strand3 toList3 rc3 readLen readVerts graphList := by
  unfold ReductionVacuous
  decide

/-- The same under the alternative longer-overlap reading. -/
theorem graph_reduction_vacuous_longer :
    ReductionVacuousLonger Base Strand3 toList3 rc3 readLen readVerts graphList := by
  unfold ReductionVacuousLonger
  decide

/-! ### The throughput vector is the spectrum the objectives use -/

/-- The certified truth throughputs are the already kernel-checked
`d_S = { AAA:1, AAT:1, ATA:3, TAA:1 }`. -/
theorem truth_throughput_values :
    dS' (m3 .A .A .A) = 1 ∧ dS' (m3 .A .A .T) = 1 ∧ dS' (m3 .A .T .A) = 3 ∧
      dS' (m3 .T .A .A) = 1 :=
  ⟨by
    rw [← truth_throughput_is_spectrum (m3 .A .A .A) (by decide)]
    exact truth_throughput_AAA,
   by
    rw [← truth_throughput_is_spectrum (m3 .A .A .T) (by decide)]
    exact truth_throughput_AAT,
   by
    rw [← truth_throughput_is_spectrum (m3 .A .T .A) (by decide)]
    exact truth_throughput_ATA,
   by
    rw [← truth_throughput_is_spectrum (m3 .T .A .A) (by decide)]
    exact truth_throughput_TAA⟩

/-- The certified competitor throughputs are the already kernel-checked
`d_D = { AAA:3, AAT:1, ATA:1, TAA:1 }`. -/
theorem competitor_throughput_values :
    dD' (m3 .A .A .A) = 3 ∧ dD' (m3 .A .A .T) = 1 ∧ dD' (m3 .A .T .A) = 1 ∧
      dD' (m3 .T .A .A) = 1 :=
  ⟨by
    rw [← competitor_throughput_is_spectrum (m3 .A .A .A) (by decide)]
    exact competitor_throughput_AAA,
   by
    rw [← competitor_throughput_is_spectrum (m3 .A .A .T) (by decide)]
    exact competitor_throughput_AAT,
   by
    rw [← competitor_throughput_is_spectrum (m3 .A .T .A) (by decide)]
    exact competitor_throughput_ATA,
   by
    rw [← competitor_throughput_is_spectrum (m3 .T .A .A) (by decide)]
    exact competitor_throughput_TAA⟩

/-- The certified spectra are literally the `Fin 8` spectra the objectives use. -/
theorem truth_throughput_matches_dS :
    dS' (m3 .A .A .A) = dS 0 ∧ dS' (m3 .A .A .T) = dS 1 ∧
      dS' (m3 .A .T .A) = dS 2 ∧ dS' (m3 .T .A .A) = dS 4 := by
  decide

theorem competitor_throughput_matches_dD :
    dD' (m3 .A .A .A) = dD 0 ∧ dD' (m3 .A .A .T) = dD 1 ∧
      dD' (m3 .A .T .A) = dD 2 ∧ dD' (m3 .T .A .A) = dD 4 := by
  decide

/-! ## Main finite theorem -/

/-- Kernel-checked finite same-length counterexample with the **literal MB09 §6.2**
feasibility endpoint.

In substance: the instance satisfies the **shared, authoritative**
`SourceFaithfulIs.InformationFeasible` predicate `I_s` at full strength, proved by
finite `decide` on the `Genome` object `truthGenome` with read length `3` and the
realized length-`3` placements `{0, 1, 3, 5}` (the sampling realization samples
start `0` twice, and the duplicate collapses because coverage and bridging
quantify over placements; the sampled multiplicity is recorded separately by the
read-type counts `obs`); the competing candidate is a single spelled molecule of
exactly the same length as
the truth (`same_candidate_length`, i.e. the fixed-length sub-case `|D| = |S| = G`
with `G = 6`); the truth `AAATAT` and that competitor are both genuine §6.2
spelled candidates — bidirected circuits in the transitively reduced bidirected
overlap graph on the four observed read molecules, every step a real graph edge
surviving the transitive reduction, every position an observed read molecule,
edge lower bounds `0`, the §6.2 vertex lower bound `1`, signed-incidence balance
`0`, no supersource/supersink usage, and vertex throughput equal to the
candidate's own molecule spectrum; and the competitor strictly beats the truth
under both the literal §6.1 binomial objective (ratio `5`) and the exact
same-length multinomial objective (ratio `3`). -/
theorem samelength_se62_bidirected_flow_counterexample :
    SourceFaithfulIs.InformationFeasible truthGenome 3 realizedStarts ∧
      (genomeLength truth = genomeLength competitor) ∧
      (SpelledFeasible62 Base Strand3 toList3 rep3 rc3 readLen oMin readVerts spellTruth
          truthCircuitFlow noTerm dS' ∧
        (SpelledFeasible62 Base Strand3 toList3 rep3 rc3 readLen oMin readVerts
            spellCompetitor competitorCircuitFlow noTerm dD' ∧
          (lik obs dS < lik obs dD ∧ exactLik dD obs / exactLik dS obs = 3))) :=
  ⟨truth_information_feasible, ⟨same_candidate_length,
    ⟨truth_spelled_feasible62, ⟨competitor_spelled_feasible62,
      ⟨competitor_strictly_better, exactLik_over_truth⟩⟩⟩⟩⟩

/-- The earlier sequence-level statement, retained: §6.2 feasibility holds
*alongside* the proxy `SeqSupport` for both candidates, and both strict
improvements.  The §6.2 theorem above is the one that uses the source object. -/
theorem samelength_se62_counterexample :
    SourceCertificate ∧ SeqSupport dS obs ∧ SeqSupport dD obs ∧
      lik obs dS < lik obs dD ∧ exactLik dD obs / exactLik dS obs = 3 :=
  ⟨truth_source_certificate, truth_support, competitor_support,
    competitor_strictly_better, exactLik_over_truth⟩

end AssemblyP1.SameLengthSection62Counterexample
