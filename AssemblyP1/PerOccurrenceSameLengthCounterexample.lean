import Mathlib
import AssemblyP1.SourceFaithfulIs
import AssemblyP1.Section62BidirectedFlow

/-!
# A same-length counterexample under the PER-OCCURRENCE strengthening

This file kernel-checks the finite witness recorded in
`docs/peroccurrence-samelength-dna-counterexample-212.md`.  It refutes the
following strengthening of the Medvedev–Brudno (2009) §6.2 statement:

> `I_s` holds **and** the truth-induced flow is an admissible MB09 §6.2
> bidirected **spelled** candidate **and** the competing candidate is a single
> spelled molecule `D` with `|D| = |S|` **and every observed read molecule
> occurs in the candidate at least as often as it was observed** (`d_w ≥ x_w`
> for every observed read molecule class `w`, the *per-occurrence*
> strengthening of the §6.2 rule) `⇒` the truth-induced flow maximizes the
> likelihood.

Instance:

* alphabet `{A, C, G, T}` with the DNA reverse-complement involution `A ↔ T`,
  `C ↔ G` (no self-complementary base, so every `3`-mer pairs with a distinct
  reverse complement);
* true circular genome `truth = ATATACAC` (length `8`);
* competitor `D = ATACACAC` (length `8`, **same length**);
* read length `L = 3`, realized placements `{1, 3, 4, 5, 6, 7}` (`n = 6` reads);
* external genome size `N = 8` (Medvedev–Brudno §6.1);
* observed read-molecule classes `x = { ACA/TGT:2, ATA/TAT:1, ATG/CAT:1,
  CAC/GTG:1, GTA/TAC:1 }`;
* truth spectrum `d_S = { ACA/TGT:2, ATA/TAT:3, ATG/CAT:1, CAC/GTG:1,
  GTA/TAC:1 }`;
* competitor spectrum `d_D = { ACA/TGT:3, ATA/TAT:1, ATG/CAT:1, CAC/GTG:2,
  GTA/TAC:1 }`.

**Both candidates are per-occurrence feasible**: `x_w ≤ d_S(w)` and `x_w ≤
d_D(w)` for every class `w` (the tight coordinate is `ACA/TGT`, where `x = d_S =
2`), and `n = 6 < G = 8`, so the strengthening does not collapse to
read-tiling.  The competitor strictly beats the truth under both same-length
objectives:

```text
literal §6.1 product of binomial marginals   L(D)/L(S) = 9/5
candidate-intrinsic exact multinomial        L(D)/L(S) = 3/2
```

What is kernel-checked here.  The shared, authoritative
`SourceFaithfulIs.InformationFeasible` predicate `I_s` at full strength
(coverage, *every* maximal triple repeat all-bridged, *every* interleaved pair
of repeats bridged, quantified over all repeat lengths and all selected
starts) by finite `decide` on the `Genome` object `truthGenome` with read
length `3` and the realized placements `{1, 3, 4, 5, 6, 7}`; the exact
candidate-length equality `|D| = |S| = 8`; the per-occurrence feasibility of
both candidates and the support equality of both spectra with the observation;
the literal MB09 §6.2 feasibility of both candidates via
`AssemblyP1.Section62BidirectedFlow`: the explicit bidirected overlap graph on
the five observed read molecules, its sixteen edges written out and proved equal
to the generated `overlapEdges`, the transitive edge reduction vacuous under both
readings, the vertex lower bound `1`, the edge lower bounds `0`, the §3.4
signed-incidence balance `0` at every read vertex, no supersource/supersink
usage, the vertex throughput equal to each candidate's own molecule spectrum,
every step a real edge surviving the transitive reduction, every visited vertex
an observed read molecule, and both walks genuine bidirected circuits; and the
strict improvement under both objectives.  The endpoint theorem
`peroccurrence_samelength_se62_bidirected_flow_counterexample` refutes the
per-occurrence sentence
(`peroccurrence_samelength_maximality_refuted`).

**Epistemic status and scope.**  This is a **kernel-checked result** about one
finite instance, under one explicit reading of the candidate rule.  The
per-occurrence condition `d_w ≥ x_w` is a **project-level strengthening** of the
Medvedev–Brudno §6.2 rule, *not* the source definition: §6.2 gives each read
*vertex* a lower bound of `1` because it represents a read that must be present
at least once, and §4.1 says each `k`-molecule is represented only once, so a
duplicated observation enters as a single vertex.  The earlier, source-reading
witness `AAATAT → AAAAAT`
([`SameLengthSection62Counterexample`](SameLengthSection62Counterexample.lean))
refutes the per-vertex reading and is **not** per-occurrence feasible
(`d_S(AAA) = 1 < x_AAA = 2`), so the two refutations are logically independent;
the DNA alphabet here is what makes the truth itself per-occurrence feasible.
This module refutes the strengthened statement: the strengthening does not
rescue ML maximality at fixed length.

This file does not settle which Medvedev–Brudno object the Shomorony et al.
(2016) sentence intends, and does not address single-strand indexing, the
variable-length case, or tie/equivalence semantics.

## Provenance

This module was produced by leaf #212 (agent `cedd79adfeae`, worktree
`/workspace/assemblyp1-finite-212`, branch `agent/board-212-37b45b`) and
integrated by front #217 on 2026-10-09. It was **copied** into this worktree,
not cherry-picked, merged, or referenced from the leaf's tree. Its two
non-Mathlib imports (`AssemblyP1.SourceFaithfulIs`,
`AssemblyP1.Section62BidirectedFlow`) are byte-identical in both worktrees, and
it was rebuilt, replayed through the kernel, and axiom-checked here after the
copy. No `sorry`, `axiom`, `admit`, or `native_decide` appears in the file, and
the sentence it refutes is a `Prop`
(`PerOccurrenceSameLengthMaximality`), not a theorem, so no definition was changed
to make the refutation go through. It resolves row R13 of
`docs/source-notes/interpretation-matrix-217.md`.
-/

set_option maxHeartbeats 4000000

namespace AssemblyP1.PerOccurrenceSameLengthCounterexample

/-! ## The alphabet, strands and molecule classes -/

/-- The four DNA bases; the reverse-complement involution is `A ↔ T`, `C ↔ G`. -/
inductive Base where
  | A
  | C
  | G
  | T
  deriving DecidableEq, Inhabited, Repr

instance : Fintype Base where
  elems := {Base.A, Base.C, Base.G, Base.T}
  complete := by intro x; cases x <;> simp

/-- DNA reverse complement on the four-letter alphabet. -/
def comp : Base → Base
  | .A => .T
  | .T => .A
  | .C => .G
  | .G => .C

/-- Two-bit encoding of a base (`A ↦ 0`, `C ↦ 1`, `G ↦ 2`, `T ↦ 3`). -/
def bit : Base → Nat
  | .A => 0
  | .C => 1
  | .G => 2
  | .T => 3

/-- A length-`3` strand: one single-stranded DNA word, as its three symbols.

A DNA molecule is an unordered reverse-complement pair of strands (MB09 §3.1),
and each `k`-molecule is represented only once (MB09 §4.1), so the vertices of
the §6.2 graph are these strands modulo the involution. -/
abbrev W3 := Fin 3 → Base

/-- A length-`3` strand written symbol by symbol. -/
def mW (a b c : Base) : W3 := ![a, b, c]

/-- The six-bit code of a length-`3` strand, most significant symbol first. -/
def codeW (w : W3) : Nat := bit (w 0) * 16 + bit (w 1) * 4 + bit (w 2)

lemma bit_le_three (b : Base) : bit b ≤ 3 := by cases b <;> decide

lemma codeW_lt (w : W3) : codeW w < 64 := by
  have h0 : bit (w 0) ≤ 3 := bit_le_three _
  have h1 : bit (w 1) ≤ 3 := bit_le_three _
  have h2 : bit (w 2) ≤ 3 := bit_le_three _
  unfold codeW
  omega

/-- The DNA reverse complement of a length-`3` strand (MB09 §3.1). -/
def rc3 (w : W3) : W3 := ![comp (w 2), comp (w 1), comp (w 0)]

/-- The molecule-class representative of a strand: the strand itself when its
code is the smaller of the two strand codes, and its reverse complement
otherwise.  MB09 §4.1 represents each `k`-molecule only once, so this is the
vertex label of the §6.2 graph. -/
def rep3 (w : W3) : W3 := if codeW w ≤ codeW (rc3 w) then w else rc3 w

/-- The `Fin 64` label of the reverse-complement pair of a strand: the smaller of
the two strand codes.  Because no base is self-complementary, the two strands of
a class always have distinct codes, so this label identifies the class. -/
def cls (w : W3) : Fin 64 :=
  ⟨min (codeW w) (codeW (rc3 w)),
    Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (codeW_lt w)⟩

/-- The five observed molecule classes, by representative:
`ACA/TGT` (code `4`), `ATA/TAT` (`12`), `ATG/CAT` (`14`), `CAC/GTG` (`17`),
`GTA/TAC` (`44`).  These are the molecule-class representatives because the
reverse complement always carries the larger code. -/
def readVerts : List W3 :=
  [mW .A .C .A, mW .A .T .A, mW .A .T .G, mW .C .A .C, mW .G .T .A]

/-- Every element of `readVerts` is its own molecule-class representative, so the
five vertices are the five classes rather than five strands of four classes. -/
theorem readVerts_rep :
    rep3 (mW .A .C .A) = mW .A .C .A ∧ rep3 (mW .A .T .A) = mW .A .T .A ∧
      rep3 (mW .A .T .G) = mW .A .T .G ∧ rep3 (mW .C .A .C) = mW .C .A .C ∧
      rep3 (mW .G .T .A) = mW .G .T .A := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem readVerts_cls :
    cls (mW .A .C .A) = 4 ∧ cls (mW .A .T .A) = 12 ∧ cls (mW .A .T .G) = 14 ∧
      cls (mW .C .A .C) = 17 ∧ cls (mW .G .T .A) = 44 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-! ## The genomes -/

/-- The true circular genome `ATATACAC` of length `8`. -/
def truth : Fin 8 → Base := ![.A, .T, .A, .T, .A, .C, .A, .C]

/-- The competitor `ATACACAC` of length `8`. -/
def competitor : Fin 8 → Base := ![.A, .T, .A, .C, .A, .C, .A, .C]

/-- The truth as a `SourceFaithfulIs.Genome`, the substrate `I_s` is stated on. -/
abbrev truthGenome : SourceFaithfulIs.Genome Base := ⟨8, by decide, truth⟩

/-- The symbol at an arbitrary integer position of a length-`8` circle. -/
def cyc8 (g : Fin 8 → Base) (i : Nat) : Base := g ⟨i % 8, Nat.mod_lt _ (by decide)⟩

/-- The strand read at cyclic position `r` of a length-`8` genome. -/
def strandOf (g : Fin 8 → Base) (r : Fin 8) : W3 :=
  ![cyc8 g r.val, cyc8 g (r.val + 1), cyc8 g (r.val + 2)]

/-- The reads of the truth induced by the competitor, position by position. -/
def strandCompetitor (r : Fin 8) : W3 := strandOf competitor r

/-- The reads of the truth, position by position. -/
def strandTruth (r : Fin 8) : W3 := strandOf truth r

/-- The realized length-`3` read placements of the truth. -/
def realizedStarts : Finset (Fin 8) := {1, 3, 4, 5, 6, 7}

/-- The realized read placements, as a list carrying the reads' multiplicities. -/
def readStarts : List (Fin 8) := [1, 3, 4, 5, 6, 7]

/-- The source-faithful bridging hypothesis `I_s` holds for this instance:
coverage, every maximal triple repeat all-bridged, and every interleaved pair of
repeats bridged.  This is the shared, authoritative `InformationFeasible`
predicate, discharged by finite `decide`; no repeat is enumerated by hand and no
clause is assumed. -/
theorem truth_information_feasible :
    SourceFaithfulIs.InformationFeasible truthGenome 3 realizedStarts := by
  decide

/-! ## The observation and the two spectra -/

/-- The observed read-molecule multiplicities `x`, indexed by molecule class. -/
def obs (c : Fin 64) : Nat :=
  (readStarts.filter (fun r => cls (strandTruth r) = c)).length

/-- The truth's molecule spectrum `d_S`. -/
def dS (c : Fin 64) : Nat :=
  ((List.finRange 8).filter (fun r => cls (strandTruth r) = c)).length

/-- The competitor's molecule spectrum `d_D`. -/
def dD (c : Fin 64) : Nat :=
  ((List.finRange 8).filter (fun r => cls (strandCompetitor r) = c)).length

/-! ## The candidate rule: per-vertex (source) and per-occurrence (strengthened) -/

/-- Support equality: exactly the observed classes occur in the candidate.  For
a spelled candidate this is the literal §6.2 per-vertex lower bound `1`
(MB09 §6.2: "each vertex has a lower bound of 1 since it represents a read that
must be present in the genome at least once"). -/
def SupportEquality (d x : Fin 64 → Nat) : Prop :=
  (∀ c, x c > 0 → d c > 0) ∧ (∀ c, d c > 0 → x c > 0)

/-- **Per-occurrence feasibility** (the strengthened candidate rule): every
observed read molecule class `c` occurs in the candidate at least as often as it
was observed.

This is the strengthening under test.  The source's §6.2 rule is weaker: each
read *vertex* carries a lower bound of `1`, which for a spelled molecule is
support equality.  The strengthening is a project-level hypothesis, **not** a
source definition; see the module docstring. -/
def PerOccurrenceFeasible (d x : Fin 64 → Nat) : Prop := ∀ c, x c ≤ d c

/-! ### The five observed molecule classes, and the zeros outside them -/

/-- The molecule classes with positive observed count. -/
def relevant : Finset (Fin 64) := {4, 12, 14, 17, 44}

theorem mem_relevant_iff (c : Fin 64) :
    c ∈ relevant ↔ (c = 4 ∨ c = 12 ∨ c = 14 ∨ c = 17 ∨ c = 44) := by
  unfold relevant
  simp

theorem obs_values :
    obs 4 = 2 ∧ obs 12 = 1 ∧ obs 14 = 1 ∧ obs 17 = 1 ∧ obs 44 = 1 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem dS_values :
    dS 4 = 2 ∧ dS 12 = 3 ∧ dS 14 = 1 ∧ dS 17 = 1 ∧ dS 44 = 1 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem dD_values :
    dD 4 = 3 ∧ dD 12 = 1 ∧ dD 14 = 1 ∧ dD 17 = 2 ∧ dD 44 = 1 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- A class outside `relevant` has zero observed count and zero multiplicity in
both candidates. -/
theorem zero_off_relevant :
    ∀ c : Fin 64, c ∉ relevant → obs c = 0 ∧ dS c = 0 ∧ dD c = 0 := by
  unfold relevant obs dS dD readStarts strandTruth strandCompetitor strandOf
    cyc8 truth competitor cls codeW bit rc3 comp
  decide

/-- Expansion of a product over the five-element `relevant` set. -/
lemma relevant_prod_eq (f : Fin 64 → ℚ) :
    ∏ c ∈ relevant, f c = f 4 * (f 12 * (f 14 * (f 17 * f 44))) := by
  unfold relevant
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]

/-! ### Both candidates satisfy the source rule and the strengthened rule -/

theorem truth_support : SupportEquality dS obs := by
  unfold SupportEquality
  decide

theorem competitor_support : SupportEquality dD obs := by
  unfold SupportEquality
  decide

/-- The truth is per-occurrence feasible: every observed class is present in the
truth at least as often as it was observed.  The tight coordinate is
`ACA/TGT`, where `x = d_S = 2`. -/
theorem truth_peroccurrence : PerOccurrenceFeasible dS obs := by
  unfold PerOccurrenceFeasible
  decide

/-- The competitor is per-occurrence feasible as well; the tight coordinate for
it is `ATA/TAT`, where `x = d_S = 3 > d_D = 1` bounds how far the competitor
could go. -/
theorem competitor_peroccurrence : PerOccurrenceFeasible dD obs := by
  unfold PerOccurrenceFeasible
  decide

/-- The realization is not read-tiling: some class is observed fewer times than
the truth contains it (`n = 6 < G = 8`), so the strengthened rule really is
stronger than "the candidate spells exactly the observation". -/
theorem not_read_tiled : ∃ c, obs c < dS c := by
  refine ⟨12, ?_⟩
  have h1 := obs_values.2.1
  have h2 := dS_values.2.1
  omega

/-! ## Literal §6.1 product-of-binomial-marginals objective (Variant A) -/

/-- The external genome size `N` of MB09 §6.1: here `N = |S| = G = 8`. -/
def N : Nat := 8

/-- The number of realized reads. -/
def n : Nat := 6

theorem n_eq : n = readStarts.length := rfl

/-- One §6.1 binomial marginal for molecule class `c`, with fixed external
`N = 8`, total reads `n = 6`, observed count `x c`, and candidate count `d c`. -/
def marginal (x d : Fin 64 → Nat) (c : Fin 64) : ℚ :=
  (Nat.choose 6 (x c) : ℚ) * ((d c : ℚ) / 8) ^ (x c) *
    (1 - (d c : ℚ) / 8) ^ (6 - x c)

/-- The literal §6.1 product of binomial marginals over the molecule-class
space (zero-count factors retained). -/
def lik (x d : Fin 64 → Nat) : ℚ :=
  ∏ c : Fin 64, marginal x d c

/-! ## Candidate-intrinsic exact multinomial objective (Variant E) -/

/-- One exact-multinomial factor for molecule class `c`: `(d c)^{x c}`.  Up to
the constants `n! / ∏ x_c!` and `N^{-n}`, which cancel between two same-length
candidates, this is the MB09 §6.1 exact multinomial. -/
def exactFactor (d x : Fin 64 → Nat) (c : Fin 64) : ℚ := (d c : ℚ) ^ (x c)

/-- The exact same-length multinomial objective. -/
def exactLik (d x : Fin 64 → Nat) : ℚ :=
  ∏ c : Fin 64, exactFactor d x c

/-! ### Reduction of both objectives to the observed classes -/

lemma marginal_eq_one_of_zero (x d : Fin 64 → Nat) (c : Fin 64)
    (hx : x c = 0) (hd : d c = 0) : marginal x d c = 1 := by
  simp [marginal, hx, hd]

lemma exactFactor_eq_one_of_zero (d x : Fin 64 → Nat) (c : Fin 64)
    (hx : x c = 0) : exactFactor d x c = 1 := by
  simp [exactFactor, hx]

lemma lik_eq_relevant (x d : Fin 64 → Nat)
    (h : ∀ c : Fin 64, c ∉ relevant → x c = 0 ∧ d c = 0) :
    lik x d = ∏ c ∈ relevant, marginal x d c := by
  unfold lik
  exact (Finset.prod_subset (s₁ := relevant) (s₂ := Finset.univ)
    (by intro c _; exact Finset.mem_univ c)
    (by intro c _ hc; exact marginal_eq_one_of_zero x d c (h c hc).1 (h c hc).2)).symm

lemma exactLik_eq_relevant (d x : Fin 64 → Nat)
    (h : ∀ c : Fin 64, c ∉ relevant → x c = 0) :
    exactLik d x = ∏ c ∈ relevant, exactFactor d x c := by
  unfold exactLik
  exact (Finset.prod_subset (s₁ := relevant) (s₂ := Finset.univ)
    (by intro c _; exact Finset.mem_univ c)
    (by intro c _ hc; exact exactFactor_eq_one_of_zero d x c (h c hc))).symm

theorem lik_truth :
    lik obs dS = marginal obs dS 4 * (marginal obs dS 12 *
      (marginal obs dS 14 * (marginal obs dS 17 * marginal obs dS 44))) := by
  rw [lik_eq_relevant obs dS (fun c hc =>
    ⟨(zero_off_relevant c hc).1, (zero_off_relevant c hc).2.1⟩),
    relevant_prod_eq]

theorem lik_competitor :
    lik obs dD = marginal obs dD 4 * (marginal obs dD 12 *
      (marginal obs dD 14 * (marginal obs dD 17 * marginal obs dD 44))) := by
  rw [lik_eq_relevant obs dD (fun c hc =>
    ⟨(zero_off_relevant c hc).1, (zero_off_relevant c hc).2.2⟩),
    relevant_prod_eq]

theorem exactLik_truth :
    exactLik dS obs = exactFactor dS obs 4 * (exactFactor dS obs 12 *
      (exactFactor dS obs 14 * (exactFactor dS obs 17 * exactFactor dS obs 44))) := by
  rw [exactLik_eq_relevant dS obs (fun c hc => (zero_off_relevant c hc).1),
    relevant_prod_eq]

theorem exactLik_competitor :
    exactLik dD obs = exactFactor dD obs 4 * (exactFactor dD obs 12 *
      (exactFactor dD obs 14 * (exactFactor dD obs 17 * exactFactor dD obs 44))) := by
  rw [exactLik_eq_relevant dD obs (fun c hc => (zero_off_relevant c hc).1),
    relevant_prod_eq]

/-! ### The two objectives -/

theorem lik_truth_pos : 0 < lik obs dS := by
  rw [lik_truth]
  norm_num [marginal, obs_values, dS_values, Nat.choose]

theorem lik_competitor_over_truth : lik obs dD / lik obs dS = 9 / 5 := by
  rw [lik_truth, lik_competitor]
  norm_num [marginal, obs_values, dS_values, dD_values, Nat.choose]

theorem competitor_strictly_better : lik obs dS < lik obs dD := by
  have h := lik_competitor_over_truth
  have hpos := lik_truth_pos
  rw [div_eq_iff (ne_of_gt hpos)] at h
  rw [h]
  nlinarith [hpos]

theorem exactLik_truth_value : exactLik dS obs = 12 := by
  rw [exactLik_truth]
  norm_num [exactFactor, obs_values, dS_values]

theorem exactLik_competitor_value : exactLik dD obs = 18 := by
  rw [exactLik_competitor]
  norm_num [exactFactor, obs_values, dD_values]

theorem exactLik_over_truth : exactLik dD obs / exactLik dS obs = 3 / 2 := by
  rw [exactLik_truth_value, exactLik_competitor_value]
  norm_num

theorem exact_competitor_strictly_better : exactLik dS obs < exactLik dD obs := by
  rw [exactLik_truth_value, exactLik_competitor_value]
  norm_num

/-! ## Literal §6.2 bidirected-flow feasibility (MB09 §6.2)

Everything below replaces a proxy support predicate by the actual §6.2 object:
the explicit bidirected overlap graph on the five observed read *molecules*, its
transitive edge reduction, the vertex and edge lower bounds, the §3.4
signed-incidence balance, and the supersource/supersink conversion.

Vertices are molecule classes (MB09 §3.1, §4.1) and the candidates are still the
circular sequences `truth` and `competitor`, both of length `8`.  Only the
feasibility predicate is the source object, and the exact candidate-length
equality `|S| = |D| = 8` is preserved throughout. -/

open AssemblyP1.Section62Flow

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

/-- The linearization of a strand. -/
def toList3 (w : W3) : List Base := [w 0, w 1, w 2]

/-- The read length `L = 3`. -/
def readLen : Nat := 3

/-- The §6.2 overlap threshold for this instance, `o_min = L − 1 = 2`. -/
def oMin : Nat := 2

/-- A numeric key identifying an overlap edge by the codes of its two strands:
each strand code is `< 64`, so the key is injective on pairs.  The certificate
flows below use these keys so that the feasibility checks stay cheap enough for
the kernel to evaluate. -/
def ekey (e : BdEdge Base W3) : Nat := codeW e.sx * 64 + codeW e.sy

/-- The key of the edge between the strands `x` and `y`. -/
def keyOf (x y : W3) : Nat := codeW x * 64 + codeW y

/-- The bidirected overlap edge of length `L − 1 = 2` between two strands. -/
def e2 (x y : W3) : BdEdge Base W3 := bdEdge rep3 x y 2

/-- The genome length of a circular candidate presented as `Fin n → Base`: it is
`n`, the number of cyclic positions. -/
def genomeLength {n : Nat} (_g : Fin n → Base) : Nat := n

/-- The explicit bidirected overlap graph of MB09 §6.2 on the five observed read
molecules. -/
def graph : List (BdEdge Base W3) :=
  overlapEdges Base W3 toList3 rep3 rc3 readLen oMin readVerts

/-- The sixteen §6.2 overlap edges, written out in the order `overlapEdges`
generates them: for overlap length `2`, over the ten strands
`verts ++ verts.map rc3` = `ACA, ATA, ATG, CAC, GTA, TGT, TAT, CAT, GTG, TAC`,
an edge `sx → sy` exists exactly when the length-`2` suffix of `sx` is the
length-`2` prefix of `sy`.  The feasibility checks below use this explicit list
so that they stay shallow enough for the kernel to evaluate; `graph_eq`
identifies it with the generated graph. -/
def graphList : List (BdEdge Base W3) :=
  [ e2 (mW .A .C .A) (mW .C .A .C), -- ACA → CAC   (suffix CA / prefix CA)
    e2 (mW .A .C .A) (mW .C .A .T), -- ACA → CAT   (CA / CA)
    e2 (mW .A .T .A) (mW .T .A .T), -- ATA → TAT   (TA / TA)
    e2 (mW .A .T .A) (mW .T .A .C), -- ATA → TAC   (TA / TA)
    e2 (mW .A .T .G) (mW .T .G .T), -- ATG → TGT   (TG / TG)
    e2 (mW .C .A .C) (mW .A .C .A), -- CAC → ACA   (AC / AC)
    e2 (mW .G .T .A) (mW .T .A .T), -- GTA → TAT   (TA / TA)
    e2 (mW .G .T .A) (mW .T .A .C), -- GTA → TAC   (TA / TA)
    e2 (mW .T .G .T) (mW .G .T .A), -- TGT → GTA   (GT / GT)
    e2 (mW .T .G .T) (mW .G .T .G), -- TGT → GTG   (GT / GT)
    e2 (mW .T .A .T) (mW .A .T .A), -- TAT → ATA   (AT / AT)
    e2 (mW .T .A .T) (mW .A .T .G), -- TAT → ATG   (AT / AT)
    e2 (mW .C .A .T) (mW .A .T .A), -- CAT → ATA   (AT / AT)
    e2 (mW .C .A .T) (mW .A .T .G), -- CAT → ATG   (AT / AT)
    e2 (mW .G .T .G) (mW .T .G .T), -- GTG → TGT   (TG / TG)
    e2 (mW .T .A .C) (mW .A .C .A) ] -- TAC → ACA  (AC / AC)

/-- The written-out edge list is exactly the generated §6.2 overlap graph. -/
theorem graph_eq : graph = graphList := by
  decide

/-- The §6.2 graph on the five observed molecules has exactly the sixteen
bidirected overlap edges of length `2`. -/
theorem graph_has_sixteen_edges : graphList.length = 16 := by
  decide

/-- There are five observed read molecules. -/
theorem readVerts_length : readVerts.length = 5 := by
  decide

/-- Every overlap edge is a *proper* overlap: its length is `o_min = 2` and hence
`< readLen = 3`. -/
theorem edge_length : ∀ e ∈ graphList, e.len = 2 := by
  decide

/-- The truth, as a §6.2 spelling: the strand read at each of its eight cyclic
positions. -/
def spellTruth : Spelling Base W3 8 := ⟨strandTruth, by decide⟩

/-- The competitor, as a §6.2 spelling of the *same* length. -/
def spellCompetitor : Spelling Base W3 8 := ⟨strandCompetitor, by decide⟩

/-- The truth's spectrum, indexed by strand rather than by class code: the
throughput vector §6.2 requires, by Observation 7. -/
def dS' (w : W3) : Nat := dS (cls w)

/-- The competitor's spectrum, likewise relabelled by molecule class. -/
def dD' (w : W3) : Nat := dD (cls w)

/-- No supersource and no supersink is used: both candidates are genuine
circuits, as MB09 §6.2 observes the double-stranded genome is. -/
def noTerm : SuperTerminals W3 := noTerminals W3

/-- The concrete `noTerm` uses neither the supersource nor the supersink, which is
the zero-terminal-usage conjunct of `Feasible62`. -/
theorem noTerm_usage_zero : ∀ v, noTerm.srcUse v = 0 ∧ noTerm.snkUse v = 0 :=
  fun _ => ⟨rfl, rfl⟩

/-- The flow of the truth's bidirected circuit: flow `1` on each of the eight
overlap edges its cyclic window walk
`ATA → TAT → ATA → TAC → ACA → CAC → ACA → CAT → ATA` traverses, and `0`
elsewhere. -/
def truthCircuitFlow : BdFlow Base W3 := fun e =>
  if ekey e = keyOf (mW .A .T .A) (mW .T .A .T) then 1 else
  if ekey e = keyOf (mW .T .A .T) (mW .A .T .A) then 1 else
  if ekey e = keyOf (mW .A .T .A) (mW .T .A .C) then 1 else
  if ekey e = keyOf (mW .T .A .C) (mW .A .C .A) then 1 else
  if ekey e = keyOf (mW .A .C .A) (mW .C .A .C) then 1 else
  if ekey e = keyOf (mW .C .A .C) (mW .A .C .A) then 1 else
  if ekey e = keyOf (mW .A .C .A) (mW .C .A .T) then 1 else
  if ekey e = keyOf (mW .C .A .T) (mW .A .T .A) then 1 else
  0

/-- The flow of the competitor's bidirected circuit.  Its walk
`ATA → TAC → ACA → CAC → ACA → CAC → ACA → CAT → ATA` traverses the
`ACA → CAC` and `CAC → ACA` overlaps twice each, so those edges carry flow `2`;
the other four carry `1`. -/
def competitorCircuitFlow : BdFlow Base W3 := fun e =>
  if ekey e = keyOf (mW .A .C .A) (mW .C .A .C) then 2 else
  if ekey e = keyOf (mW .C .A .C) (mW .A .C .A) then 2 else
  if ekey e = keyOf (mW .A .T .A) (mW .T .A .C) then 1 else
  if ekey e = keyOf (mW .T .A .C) (mW .A .C .A) then 1 else
  if ekey e = keyOf (mW .A .C .A) (mW .C .A .T) then 1 else
  if ekey e = keyOf (mW .C .A .T) (mW .A .T .A) then 1 else
  0

/-- The candidate-length equality of this sub-case: the competing candidate is a
single spelled molecule of exactly the same length as the truth, so this is the
fixed-length case `|D| = |S| = 8`. -/
theorem same_candidate_length : genomeLength truth = genomeLength competitor := rfl

/-! ### The explicit walk transcripts -/

/-- The molecule classes visited by a cyclic spelling, in order. -/
def visitsList {n : Nat} (sp : Spelling Base W3 n) : List W3 :=
  (List.finRange n).map (fun i => rep3 (sp.strand i))

/-- The truth's cyclic window walk visits
`ATA, ATA, ATA, GTA, ACA, CAC, ACA, ATG`, i.e. `d_S`. -/
theorem truth_walk :
    visitsList spellTruth =
      [mW .A .T .A, mW .A .T .A, mW .A .T .A, mW .G .T .A, mW .A .C .A,
        mW .C .A .C, mW .A .C .A, mW .A .T .G] := by
  decide

/-- The competitor's cyclic window walk visits
`ATA, GTA, ACA, CAC, ACA, CAC, ACA, ATG`, i.e. `d_D`. -/
theorem competitor_walk :
    visitsList spellCompetitor =
      [mW .A .T .A, mW .G .T .A, mW .A .C .A, mW .C .A .C, mW .A .C .A,
        mW .C .A .C, mW .A .C .A, mW .A .T .G] := by
  decide

/-! ### §6.2 feasibility, clause by clause -/

/-- §6.2 edge lower bounds (`0`) hold on every edge for the truth's circuit. -/
theorem truth_edge_lower_bounds : ∀ e ∈ graphList, (0 : ℕ) ≤ truthCircuitFlow e := by
  decide

/-- The truth's vertex throughput at `ATA/TAT` is `3`. -/
theorem truth_throughput_ATA :
    throughput Base W3 rep3 truthCircuitFlow graphList (mW .A .T .A) = 3 := by
  decide

/-- The truth's vertex throughput at `ACA/TGT` is `2`. -/
theorem truth_throughput_ACA :
    throughput Base W3 rep3 truthCircuitFlow graphList (mW .A .C .A) = 2 := by
  decide

/-- The truth's vertex throughput at `ATG/CAT` is `1`. -/
theorem truth_throughput_ATG :
    throughput Base W3 rep3 truthCircuitFlow graphList (mW .A .T .G) = 1 := by
  decide

/-- The truth's vertex throughput at `CAC/GTG` is `1`. -/
theorem truth_throughput_CAC :
    throughput Base W3 rep3 truthCircuitFlow graphList (mW .C .A .C) = 1 := by
  decide

/-- The truth's vertex throughput at `GTA/TAC` is `1`. -/
theorem truth_throughput_GTA :
    throughput Base W3 rep3 truthCircuitFlow graphList (mW .G .T .A) = 1 := by
  decide

/-- The truth's vertex throughputs meet the §6.2 vertex lower bound `1` at every
read vertex. -/
theorem truth_vertex_lower_bounds :
    ∀ v ∈ readVerts, (1 : ℕ) ≤ throughput Base W3 rep3 truthCircuitFlow graphList v := by
  decide

/-- The §3.4 signed-incidence balance of the truth's circuit is `0` at every read
vertex, with no supersource/supersink usage. -/
theorem truth_balance_zero :
    ∀ v ∈ readVerts, balance Base W3 rep3 truthCircuitFlow noTerm graphList v = 0 := by
  decide

/-- The truth's vertex throughputs are the truth's molecule spectrum. -/
theorem truth_throughput_is_spectrum :
    ∀ v ∈ readVerts, throughput Base W3 rep3 truthCircuitFlow graphList v = dS' v := by
  decide

/-- The truth's circuit is a §6.2 feasible flow. -/
theorem truth_feasible62 :
    Feasible62 Base W3 rep3 readVerts graphList truthCircuitFlow noTerm dS' :=
  ⟨⟨truth_edge_lower_bounds, truth_vertex_lower_bounds, truth_balance_zero,
    truth_throughput_is_spectrum⟩, noTerm_usage_zero⟩

/-- §6.2 edge lower bounds (`0`) hold on every edge for the competitor's
circuit. -/
theorem competitor_edge_lower_bounds :
    ∀ e ∈ graphList, (0 : ℕ) ≤ competitorCircuitFlow e := by
  decide

/-- The competitor's vertex throughput at `ACA/TGT` is `3`. -/
theorem competitor_throughput_ACA :
    throughput Base W3 rep3 competitorCircuitFlow graphList (mW .A .C .A) = 3 := by
  decide

/-- The competitor's vertex throughput at `ATA/TAT` is `1`. -/
theorem competitor_throughput_ATA :
    throughput Base W3 rep3 competitorCircuitFlow graphList (mW .A .T .A) = 1 := by
  decide

/-- The competitor's vertex throughput at `CAC/GTG` is `2`. -/
theorem competitor_throughput_CAC :
    throughput Base W3 rep3 competitorCircuitFlow graphList (mW .C .A .C) = 2 := by
  decide

/-- The competitor's vertex throughput at `ATG/CAT` is `1`. -/
theorem competitor_throughput_ATG :
    throughput Base W3 rep3 competitorCircuitFlow graphList (mW .A .T .G) = 1 := by
  decide

/-- The competitor's vertex throughput at `GTA/TAC` is `1`. -/
theorem competitor_throughput_GTA :
    throughput Base W3 rep3 competitorCircuitFlow graphList (mW .G .T .A) = 1 := by
  decide

/-- The competitor's vertex throughputs meet the §6.2 vertex lower bound `1`. -/
theorem competitor_vertex_lower_bounds :
    ∀ v ∈ readVerts, (1 : ℕ) ≤
      throughput Base W3 rep3 competitorCircuitFlow graphList v := by
  decide

/-- The §3.4 signed-incidence balance of the competitor's circuit is `0` at every
read vertex. -/
theorem competitor_balance_zero :
    ∀ v ∈ readVerts, balance Base W3 rep3 competitorCircuitFlow noTerm graphList v = 0 := by
  decide

/-- The competitor's vertex throughputs are the competitor's molecule
spectrum. -/
theorem competitor_throughput_is_spectrum :
    ∀ v ∈ readVerts, throughput Base W3 rep3 competitorCircuitFlow graphList v = dD' v := by
  decide

/-- The competitor's circuit is a §6.2 feasible flow. -/
theorem competitor_feasible62 :
    Feasible62 Base W3 rep3 readVerts graphList competitorCircuitFlow noTerm dD' :=
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
    StepsSurviveReduction Base W3 toList3 rep3 rc3 readLen readVerts spellTruth
      graphList := by
  unfold StepsSurviveReduction transitivelyReduced
  decide

theorem competitor_steps_survive_reduction :
    StepsSurviveReduction Base W3 toList3 rep3 rc3 readLen readVerts
      spellCompetitor graphList := by
  unfold StepsSurviveReduction transitivelyReduced
  decide

/-- At every interior vertex of each walk the arriving and departing incidences
are opposite (MB09 §3.2): both are genuine bidirected circuits. -/
theorem truth_bidirected_circuit : BidirectedCircuit rep3 readLen spellTruth := by
  unfold BidirectedCircuit OppositeAtInterior
  decide

theorem competitor_bidirected_circuit :
    BidirectedCircuit rep3 readLen spellCompetitor := by
  unfold BidirectedCircuit OppositeAtInterior
  decide

/-- The truth, as a *spelled* §6.2 candidate. -/
theorem truth_spelled_feasible62 :
    SpelledFeasible62 Base W3 toList3 rep3 rc3 readLen oMin readVerts spellTruth
      truthCircuitFlow noTerm dS' :=
  ⟨truth_visits_observed, truth_steps_in_graph, truth_steps_survive_reduction,
    truth_bidirected_circuit, truth_feasible62⟩

/-- The competitor, as a spelled §6.2 candidate of the *same* length. -/
theorem competitor_spelled_feasible62 :
    SpelledFeasible62 Base W3 toList3 rep3 rc3 readLen oMin readVerts
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

/-- The walk's visit counts are the candidate's molecule spectrum (Observation
7). -/
theorem truth_visits_eq_spectrum :
    ∀ v ∈ readVerts, spellTruth.visits rep3 v = dS' v := by
  decide

theorem competitor_visits_eq_spectrum :
    ∀ v ∈ readVerts, spellCompetitor.visits rep3 v = dD' v := by
  decide

/-! ### Transitive edge reduction -/

/-- The transitive edge reduction removes no edge of this graph under the literal
§6.2 reading.  Every overlap has length `L − 1 = 2`, and the composition law
`len₁ + len₂ − L = len` with `len₁, len₂ < len` is unsatisfiable there. -/
theorem graph_reduction_vacuous :
    ReductionVacuous Base W3 toList3 rc3 readLen readVerts graphList := by
  unfold ReductionVacuous
  decide

/-- The same under the alternative longer-overlap reading: no edge of the graph is
spelled by a two-step path of strictly longer proper overlaps, because the
longest proper overlap between two observed strands is `L − 1 = 2`, which is
not longer than any edge of the graph. -/
theorem graph_reduction_vacuous_longer :
    ReductionVacuousLonger Base W3 toList3 rc3 readLen readVerts graphList := by
  unfold ReductionVacuousLonger
  decide

/-! ### The throughput vector is the spectrum the objectives use -/

/-- The certified truth throughputs are `d_S = { ACA/TGT:2, ATA/TAT:3, ATG/CAT:1,
CAC/GTG:1, GTA/TAC:1 }`. -/
theorem truth_throughput_values :
    dS' (mW .A .T .A) = 3 ∧ dS' (mW .A .C .A) = 2 ∧ dS' (mW .A .T .G) = 1 ∧
      dS' (mW .C .A .C) = 1 ∧ dS' (mW .G .T .A) = 1 :=
  ⟨by
    rw [← truth_throughput_is_spectrum (mW .A .T .A) (by decide)]
    exact truth_throughput_ATA,
   by
    rw [← truth_throughput_is_spectrum (mW .A .C .A) (by decide)]
    exact truth_throughput_ACA,
   by
    rw [← truth_throughput_is_spectrum (mW .A .T .G) (by decide)]
    exact truth_throughput_ATG,
   by
    rw [← truth_throughput_is_spectrum (mW .C .A .C) (by decide)]
    exact truth_throughput_CAC,
   by
    rw [← truth_throughput_is_spectrum (mW .G .T .A) (by decide)]
    exact truth_throughput_GTA⟩

/-- The certified competitor throughputs are `d_D = { ACA/TGT:3, ATA/TAT:1,
ATG/CAT:1, CAC/GTG:2, GTA/TAC:1 }`. -/
theorem competitor_throughput_values :
    dD' (mW .A .T .A) = 1 ∧ dD' (mW .A .C .A) = 3 ∧ dD' (mW .A .T .G) = 1 ∧
      dD' (mW .C .A .C) = 2 ∧ dD' (mW .G .T .A) = 1 :=
  ⟨by
    rw [← competitor_throughput_is_spectrum (mW .A .T .A) (by decide)]
    exact competitor_throughput_ATA,
   by
    rw [← competitor_throughput_is_spectrum (mW .A .C .A) (by decide)]
    exact competitor_throughput_ACA,
   by
    rw [← competitor_throughput_is_spectrum (mW .A .T .G) (by decide)]
    exact competitor_throughput_ATG,
   by
    rw [← competitor_throughput_is_spectrum (mW .C .A .C) (by decide)]
    exact competitor_throughput_CAC,
   by
    rw [← competitor_throughput_is_spectrum (mW .G .T .A) (by decide)]
    exact competitor_throughput_GTA⟩

/-- The certified spectra are literally the `Fin 64` spectra the objectives
use. -/
theorem truth_throughput_matches_dS :
    dS' (mW .A .C .A) = dS 4 ∧ dS' (mW .A .T .A) = dS 12 ∧
      dS' (mW .A .T .G) = dS 14 ∧ dS' (mW .C .A .C) = dS 17 ∧
      dS' (mW .G .T .A) = dS 44 := by
  decide

theorem competitor_throughput_matches_dD :
    dD' (mW .A .C .A) = dD 4 ∧ dD' (mW .A .T .A) = dD 12 ∧
      dD' (mW .A .T .G) = dD 14 ∧ dD' (mW .C .A .C) = dD 17 ∧
      dD' (mW .G .T .A) = dD 44 := by
  decide

/-! ## Main finite theorem -/

/-- The per-occurrence version of the same-length ML-maximality sentence, stated
for this instance's objects: whenever `I_s` holds, the truth's flow is an
admissible §6.2 spelled candidate, and a single spelled molecule `D` of the same
length is likewise admissible *and* per-occurrence feasible, the truth's
likelihood is at least that of the competitor. -/
def PerOccurrenceSameLengthMaximality : Prop :=
  (SourceFaithfulIs.InformationFeasible truthGenome 3 realizedStarts ∧
    PerOccurrenceFeasible dS obs ∧ genomeLength truth = genomeLength competitor ∧
    SpelledFeasible62 Base W3 toList3 rep3 rc3 readLen oMin readVerts spellTruth
      truthCircuitFlow noTerm dS' ∧
      PerOccurrenceFeasible dD obs ∧
      SpelledFeasible62 Base W3 toList3 rep3 rc3 readLen oMin readVerts
        spellCompetitor competitorCircuitFlow noTerm dD') →
    lik obs dD ≤ lik obs dS

/-- Kernel-checked finite same-length counterexample whose feasibility endpoint is
the **literal MB09 §6.2** predicate, under the per-occurrence strengthening.

In substance: the instance satisfies the **shared, authoritative**
`SourceFaithfulIs.InformationFeasible` predicate `I_s` at full strength, proved
by finite `decide` on the `Genome` object `truthGenome` with read length `3` and
the realized length-`3` placements `{1, 3, 4, 5, 6, 7}`; the competing candidate
is a single spelled molecule of exactly the same length as the truth
(`same_candidate_length`); **both** the truth and the competitor satisfy the
per-occurrence strengthening `d_w ≥ x_w`; both are genuine §6.2 spelled
candidates — bidirected circuits in the transitively reduced bidirected overlap
graph on the five observed read molecules, every step a real graph edge
surviving the transitive reduction, every position an observed read molecule,
edge lower bounds `0`, the §6.2 vertex lower bound `1`, signed-incidence balance
`0`, no supersource/supersink usage, and vertex throughput equal to the
candidate's own molecule spectrum; and the competitor strictly beats the truth
under both the literal §6.1 binomial objective (ratio `9/5`) and the exact
same-length multinomial objective (ratio `3/2`). -/
theorem peroccurrence_samelength_se62_bidirected_flow_counterexample :
    SourceFaithfulIs.InformationFeasible truthGenome 3 realizedStarts ∧
      (genomeLength truth = genomeLength competitor) ∧
      (PerOccurrenceFeasible dS obs ∧ PerOccurrenceFeasible dD obs) ∧
      SpelledFeasible62 Base W3 toList3 rep3 rc3 readLen oMin readVerts spellTruth
        truthCircuitFlow noTerm dS' ∧
      (SpelledFeasible62 Base W3 toList3 rep3 rc3 readLen oMin readVerts
          spellCompetitor competitorCircuitFlow noTerm dD' ∧
        (lik obs dS < lik obs dD ∧ exactLik dD obs / exactLik dS obs = 3 / 2)) :=
  ⟨truth_information_feasible, ⟨same_candidate_length,
    ⟨truth_peroccurrence, competitor_peroccurrence⟩, truth_spelled_feasible62,
    ⟨competitor_spelled_feasible62, ⟨competitor_strictly_better,
      exactLik_over_truth⟩⟩⟩⟩

/-- **The per-occurrence strengthened sentence is false.**  The strengthened
candidate rule does not rescue ML maximality at fixed length: this witness
satisfies every hypothesis of
`PerOccurrenceSameLengthMaximality` and the competitor nevertheless strictly
beats the truth under the literal §6.1 binomial objective. -/
theorem peroccurrence_samelength_maximality_refuted :
    ¬ PerOccurrenceSameLengthMaximality := by
  intro h
  have h' := h ⟨truth_information_feasible, truth_peroccurrence, same_candidate_length,
    truth_spelled_feasible62, competitor_peroccurrence, competitor_spelled_feasible62⟩
  have := competitor_strictly_better
  linarith

/-! ## Relation to the source per-vertex reading -/

/-! The witness retained for the source's own per-vertex §6.2 rule is the
`AAATAT → AAAAAT` pair kernel-checked in
`AssemblyP1.SameLengthSection62Counterexample` and recorded in
`docs/section62-same-length-bidirected-counterexample.md`.  Its truth is **not**
per-occurrence feasible (`d_S(AAA) = 1 < x_AAA = 2`), so that refutation does not
transfer here and this witness is logically independent of it: that module
refutes the source statement, this one refutes the strengthened statement.  The
comparison is worked out in
`docs/peroccurrence-samelength-dna-counterexample-212.md` §4. -/

end AssemblyP1.PerOccurrenceSameLengthCounterexample
