import Mathlib
import AssemblyP1.SourceFaithfulIs

/-!
# Oriented single-strand Section 6.2 with unrestricted candidate length

This module kernel-checks the finite witness recorded in
`docs/source-notes/oriented-variable-length-se62.md`.

Under the **source-faithful Medvedev–Brudno §6.2 feasibility reading** — read
*types* are the oriented length-`L` circular windows of the truth, and the only
feasibility constraint §6.2 states is the per-vertex lower bound `1`, i.e. every
observed read type occurs in the candidate at least once (MB09 §6.2: "Each
vertex has a lower bound of `1` since it represents a read that must be present
in the genome at least once") — the truth need **not** be a §6.1
maximum-likelihood maximizer once the candidate length is not pinned to `G`,
even though the bridging hypothesis `I_s` holds and both candidates are
genuinely §6.2-feasible.

The instance (this module):

* alphabet `{A, T}`, **oriented** length-`3` read types (no reverse-complement
  collapse; the 8 oriented types are coded by `code`);
* true circular genome `AAATT` (`G = 5`);
* read length `L = 3`, realized placements `{0, 1, 2, 3, 4}` each once plus one
  extra copy of placement `0` (`n = 6` reads), so the observed type counts are
  `x = spec_3(S) + e_AAA`;
* external known genome size `N = 5` (Medvedev–Brudno §6.1);
* truth spectrum `d_S = {AAA:1, AAT:1, ATT:1, TTA:1, TAA:1}`;
* candidate `D = AAAATT` (`|D| = 6`), `d_D = {AAA:2, AAT:1, ATT:1, TTA:1,
  TAA:1}`;
* a second instance with two extra reads `x₂ = spec_3(S) + 2 e_AAA` (`n = 7`)
  and `D₂ = AAAATTA` (`|D₂| = 7`).

What is kernel-checked here:

* the **shared, authoritative** `SourceFaithfulIs.InformationFeasible` predicate
  `I_s` at full strength — coverage, *every* maximal triple repeat all-bridged,
  and *every* interleaved pair of repeats bridged, quantified over all repeat
  lengths and all selected starts — discharged by finite `decide` on the
  `Genome` object `truthGenome` with read length `3` and the realized
  placements `{0, 1, 2, 3, 4}`.  No repeat is enumerated by hand and no clause is
  assumed; the interleaved clause is discharged by exhibiting that this truth has
  no interleaved pair of maximal repeats at all;
* the **literal §6.2 per-vertex lower bound `1`** (`PerVertexFeasible`) of both
  the truth and each competitor: every observed read type occurs at least once;
* the **spelled** support-equality form `SpelledFeasible62` (the candidate's
  window support equals the observed support), a strictly stronger certificate
  that both competitors satisfy, so the witness survives both readings;
* the **§6.2 flow/circuit certificate**: both the truth and each competitor are
  realized by an explicit *closed walk* of the oriented read-overlap graph on the
  observed read types whose multiplicity of every read type equals that
  candidate's spectrum (`Section62Circuit`, `§6.2` below).  This is the literal
  §6.2 object — a flow that decomposes into walks, with per-vertex value `d_i`
  by Observation 7 — restricted to the single-circuit case, so the competitor is
  a genuinely §6.2-admissible spelled candidate, not merely a word that happens
  to contain the observed reads;
* the exact §6.1 objective (candidate-intrinsic `N(D) = |D|`) and the §6.1
  product-of-binomial-marginals objective with external known `N`, both with the
  `0 ≤ d_w ≤ N` domain respected;
* the **strict** likelihood inequalities, with the ratios
  `15625/11664` (exact, `n = 6`), `81/64` (binomial, `N = 5`, `n = 6`),
  `2109375/823543` (exact, `n = 7`) and `27/16` (binomial, `N = 5`, `n = 7`);
* that each competitor's exact objective equals the **AM-GM upper bound**
  `L* (x)` of the exact objective over all probability vectors of read-type
  frequencies, so the competitor attains the value that
  `docs/source-notes/oriented-variable-length-se62.md` §3 proves nothing can
  exceed (that domination is prose mathematics there; here only the
  instance-level value is computed).

Scope. This file is about this class of finite instances. It does not settle
which Medvedev–Brudno object the Shomorony et al. (2016) sentence intends, nor
the bidirected (reverse-complement-collapsed) sub-case settled elsewhere, nor
the stronger per-occurrence feasibility reading `d ≥ x`, which the companion
note treats separately.
-/

namespace AssemblyP1.OrientedVariableLengthSe62

/-! ## The instance -/

/-- Two-symbol alphabet. -/
inductive Base where
  | A
  | T
  deriving DecidableEq, Inhabited, Repr

instance : Fintype Base where
  elems := {Base.A, Base.T}
  complete := by intro x; cases x <;> simp

/-- Bit encoding of a symbol (`A ↦ 0`, `T ↦ 1`). -/
def bitA : Base → Nat
  | .A => 0
  | .T => 1

/-- A length-`3` oriented read type / window. -/
abbrev W3 := Fin 3 → Base

/-- Binary code of a length-`3` oriented word, in `[0, 8)`.  This is the
**oriented** type index: `AAA = 0, AAT = 1, ATA = 2, ATT = 3, TAA = 4, TAT = 5,
TTA = 6, TTT = 7`.  No reverse complement is identified anywhere in this
module, in contrast with the bidirected witness of
`AssemblyP1.Section62BridgingCounterexample`. -/
def code (w : W3) : Nat := bitA (w 0) * 4 + bitA (w 1) * 2 + bitA (w 2)

lemma bitA_le (b : Base) : bitA b ≤ 1 := by cases b <;> decide

lemma code_lt (w : W3) : code w < 8 := by
  have h0 : bitA (w 0) ≤ 1 := bitA_le _
  have h1 : bitA (w 1) ≤ 1 := bitA_le _
  have h2 : bitA (w 2) ≤ 1 := bitA_le _
  unfold code; omega

/-- The oriented type index of a length-`3` window. -/
def idx (w : W3) : Fin 8 :=
  ⟨code w, by
    have h0 : bitA (w 0) ≤ 1 := bitA_le _
    have h1 : bitA (w 1) ≤ 1 := bitA_le _
    have h2 : bitA (w 2) ≤ 1 := bitA_le _
    unfold code; omega⟩

/-- Symbol of a bit. -/
def bitB : Nat → Base
  | 0 => .A
  | 1 => .T
  | _ => .A

/-- The length-`3` oriented word coded by `c`: the inverse of `code`/`idx` on all
eight oriented types, so `overlap` below can be evaluated on type *indices*. -/
def decode (c : Fin 8) : W3 :=
  ![bitB (c.val / 4), bitB ((c.val / 2) % 2), bitB (c.val % 2)]

/-- Sanity check of the coding: `decode` is a right inverse of `idx` on the
eight oriented types. -/
theorem idx_decode (c : Fin 8) : idx (decode c) = c := by
  fin_cases c <;> decide

/-- The true circular genome `AAATT` of length `5`. -/
def truth : Fin 5 → Base := ![.A, .A, .A, .T, .T]

/-- The candidate `AAAATT` of length `6`: the truth with one extra `A` inserted
inside its maximal `A³` run. -/
def competitor : Fin 6 → Base := ![.A, .A, .A, .A, .T, .T]

/-- The candidate `AAAATTA` of length `7`: the truth with two extra `A`s
inserted inside its maximal `A³` run. -/
def competitor2 : Fin 7 → Base := ![.A, .A, .A, .A, .T, .T, .A]

section Windows

variable {n : ℕ} (g : Fin n → Base) [NeZero n]

/-- Circular symbol access. -/
def cyc (i : Nat) : Base := g ⟨i % n, Nat.mod_lt _ (NeZero.pos n)⟩

/-- Length-`3` circular window at start `r`. -/
def window (r : Fin n) : W3 := ![cyc g r.val, cyc g (r.val + 1), cyc g (r.val + 2)]

/-- Multiplicity of the oriented type `c` in the length-`3` window spectrum of
`g`: the number of starts whose window is `c`. -/
def spec (c : Fin 8) : Nat :=
  (Finset.univ.filter (fun r : Fin n => idx (window g r) = c)).card

end Windows

/-- The eight oriented length-`3` type codes, as a list so that the objective
products below unfold definitionally. -/
def codes : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- Realized length-`3` read placements: the **set** of distinct starts used by
coverage and bridging (read multiplicity does not enter `I_s`). -/
def realizedStarts : Finset (Fin 5) := {0, 1, 2, 3, 4}

/-- The realized read multiset of the `n = 6` observation: all five starts once,
plus one extra copy of start `0`, whose window is `AAA`. -/
def reads1 : List (Fin 5) := [0, 1, 2, 3, 4, 0]

/-- The realized read multiset of the `n = 7` observation: all five starts once,
plus two extra copies of start `0`. -/
def reads2 : List (Fin 5) := [0, 1, 2, 3, 4, 0, 0]

/-- Observed oriented type counts `x₁ = spec₃(S) + e_AAA` (`n = 6`). -/
def obs1 (c : Fin 8) : Nat :=
  (reads1.filter (fun r => idx (window truth r) = c)).length

/-- Observed oriented type counts `x₂ = spec₃(S) + 2 e_AAA` (`n = 7`). -/
def obs2 (c : Fin 8) : Nat :=
  (reads2.filter (fun r => idx (window truth r) = c)).length

/-- Truth spectrum `d_S`. -/
abbrev dS (c : Fin 8) : Nat := spec truth c

/-- First-candidate spectrum `d_D`. -/
abbrev dD (c : Fin 8) : Nat := spec competitor c

/-- Second-candidate spectrum `d_D2`. -/
abbrev dD2 (c : Fin 8) : Nat := spec competitor2 c

/-- The instance's observed type counts (`n = 6`). -/
theorem obs1_eq :
    obs1 0 = 2 ∧ obs1 1 = 1 ∧ obs1 2 = 0 ∧ obs1 3 = 1 ∧
      obs1 4 = 1 ∧ obs1 5 = 0 ∧ obs1 6 = 1 ∧ obs1 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The instance's observed type counts (`n = 7`). -/
theorem obs2_eq :
    obs2 0 = 3 ∧ obs2 1 = 1 ∧ obs2 2 = 0 ∧ obs2 3 = 1 ∧
      obs2 4 = 1 ∧ obs2 5 = 0 ∧ obs2 6 = 1 ∧ obs2 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The truth's spectrum. -/
theorem dS_eq :
    dS 0 = 1 ∧ dS 1 = 1 ∧ dS 2 = 0 ∧ dS 3 = 1 ∧
      dS 4 = 1 ∧ dS 5 = 0 ∧ dS 6 = 1 ∧ dS 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The first candidate's spectrum: the truth's spectrum with one extra
`AAA` (`AAA` is code `0`). -/
theorem dD_eq :
    dD 0 = 2 ∧ dD 1 = 1 ∧ dD 2 = 0 ∧ dD 3 = 1 ∧
      dD 4 = 1 ∧ dD 5 = 0 ∧ dD 6 = 1 ∧ dD 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The second candidate's spectrum: the truth's spectrum with two extra
`AAA`. -/
theorem dD2_eq :
    dD2 0 = 3 ∧ dD2 1 = 1 ∧ dD2 2 = 0 ∧ dD2 3 = 1 ∧
      dD2 4 = 1 ∧ dD2 5 = 0 ∧ dD2 6 = 1 ∧ dD2 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Total observed multiplicity of the first observation, `n₁ = 6`. -/
theorem n1 : ∑ c : Fin 8, obs1 c = 6 := by
  decide

/-- Total observed multiplicity of the second observation, `n₂ = 7`. -/
theorem n2 : ∑ c : Fin 8, obs2 c = 7 := by
  decide

/-! ## The source-faithful bridging hypothesis -/

open SourceFaithfulIs

/-- The true circular genome `AAATT` in the shared source-faithful
representation, so that the candidate-intrinsic length is intrinsic to the
object. -/
abbrev truthGenome : SourceFaithfulIs.Genome Base where
  len := 5
  len_pos := by norm_num
  sym := truth

/-- **The actual `I_s` hypothesis of this realization.**
`SourceFaithfulIs.InformationFeasible` at full strength — coverage, *every*
maximal triple repeat all-bridged, and *every* interleaved pair of repeats
bridged, quantified over all repeat lengths and all selected starts — discharged
by finite `decide` on `truthGenome` with read length `3` and the realized
placements `{0, 1, 2, 3, 4}`.  No repeat is enumerated by hand and no clause is
assumed: the unique maximal triple repeat of `AAATT` is the length-`1` triple of
`A`s at starts `0, 1, 2` (each copy bridged by the read started one position
earlier, since `1 = L - 2`), and the interleaved clause is discharged by
exhibiting that this truth has no interleaved pair of maximal repeats at all. -/
theorem truth_information_feasible :
    SourceFaithfulIs.InformationFeasible truthGenome 3 realizedStarts := by
  decide

/-! ## Section 6.2 feasibility

Three certificates are kept distinct, in increasing strength.  All three are
discharged below for the truth and for both competitors, so the witness does
not depend on which reading of "genuinely feasible §6.2" is adopted. -/

/-- **The literal Medvedev–Brudno §6.2 feasibility condition** (per-vertex
lower bound `1`): every observed read type occurs in the candidate at least
once.  This is exactly the bound the source states ("Each vertex has a lower
bound of `1` since it represents a read that must be present in the genome at
least once", MB09 §6.2); it is *not* the stronger per-occurrence condition
`d ≥ x`. -/
def PerVertexFeasible (d x : Fin 8 → Nat) : Prop :=
  ∀ c : Fin 8, 0 < x c → 1 ≤ d c

/-- The spelled support-equality form: the candidate's window support is exactly
the observed support.  Strictly stronger than `PerVertexFeasible`; both
candidates below satisfy it. -/
def SpelledFeasible62 (d x : Fin 8 → Nat) : Prop :=
  (∀ c : Fin 8, 0 < d c ↔ 0 < x c) ∧ PerVertexFeasible d x

theorem truth_perVertex_feasible1 : PerVertexFeasible dS obs1 := by
  unfold PerVertexFeasible; decide

theorem truth_perVertex_feasible2 : PerVertexFeasible dS obs2 := by
  unfold PerVertexFeasible; decide

theorem competitor_perVertex_feasible1 : PerVertexFeasible dD obs1 := by
  unfold PerVertexFeasible; decide

theorem competitor_perVertex_feasible2 : PerVertexFeasible dD2 obs2 := by
  unfold PerVertexFeasible; decide

theorem truth_spelled_feasible1 : SpelledFeasible62 dS obs1 := by
  unfold SpelledFeasible62 PerVertexFeasible; decide

theorem competitor_spelled_feasible1 : SpelledFeasible62 dD obs1 := by
  unfold SpelledFeasible62 PerVertexFeasible; decide

theorem truth_spelled_feasible2 : SpelledFeasible62 dS obs2 := by
  unfold SpelledFeasible62 PerVertexFeasible; decide

theorem competitor_spelled_feasible2 : SpelledFeasible62 dD2 obs2 := by
  unfold SpelledFeasible62 PerVertexFeasible; decide

/-! ### The §6.2 flow, as a closed walk in the read-overlap graph

Medvedev–Brudno's §6.2 feasible objects are flows on the read-overlap graph;
Observation 7 identifies the value of the flow through vertex `i` with the copy
count `d_i`, and any flow decomposes into a collection of walks.  Here each
candidate is realized by a *single* closed walk — the single-circuit case — so
the certificate below is strictly stronger than the per-vertex lower bound. -/

/-- The oriented read-overlap relation on the eight length-`3` types: read `c`
can be followed by read `e` in a walk exactly when the length-`2` suffix of `c`
equals the length-`2` prefix of `e`. -/
def overlap (c e : Fin 8) : Bool :=
  decide (decode c 1 = decode e 0 ∧ decode c 2 = decode e 1)

/-- Consecutive elements of a list are related by `R` (and a one-element or empty
list vacuously so). -/
def consec (R : Fin 8 → Fin 8 → Bool) : List (Fin 8) → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => R a b && consec R (b :: t)

/-- A closed walk in the read-overlap graph: consecutive reads overlap, and the
last read overlaps the first, so the walk spells a circular word. -/
def isCircuit (w : List (Fin 8)) : Bool :=
  decide (w ≠ []) && consec (fun c e => overlap c e) (w ++ w.take 1)

/-- The `Prop` form of `isCircuit`. -/
def IsCircuit (w : List (Fin 8)) : Prop := isCircuit w = true

instance (w : List (Fin 8)) : Decidable (IsCircuit w) :=
  inferInstanceAs (Decidable (isCircuit w = true))

/-- The truth's §6.2 walk: each observed read once. -/
def walkS : List (Fin 8) := [0, 1, 3, 6, 4]

/-- The first competitor's §6.2 walk: the read `AAA` twice, every other observed
read once.  It spells `AAAATT`. -/
def walkD : List (Fin 8) := [0, 0, 1, 3, 6, 4]

/-- The second competitor's §6.2 walk: the read `AAA` three times.  It spells
`AAAATTA`. -/
def walkD2 : List (Fin 8) := [0, 0, 0, 1, 3, 6, 4]

/-- The observed support, as a list of type codes. -/
abbrev support1 : List (Fin 8) := [0, 1, 3, 4, 6]

theorem walkS_isCircuit : IsCircuit walkS := by
  decide

theorem walkD_isCircuit : IsCircuit walkD := by
  decide

theorem walkD2_isCircuit : IsCircuit walkD2 := by
  decide

/-- The truth's walk uses each read type exactly as often as the truth's
spectrum does, hence at least once at every observed type. -/
theorem walkS_counts : ∀ c : Fin 8, walkS.count c = dS c := by
  decide

theorem walkD_counts : ∀ c : Fin 8, walkD.count c = dD c := by
  decide

theorem walkD2_counts : ∀ c : Fin 8, walkD2.count c = dD2 c := by
  decide

/-- The truth's walk covers every observed read type (per-vertex lower bound
`1` realized by an admissible §6.2 circuit). -/
theorem walkS_covers1 : ∀ c ∈ walkS, c ∈ support1 := by
  decide

theorem walkD_covers1 : ∀ c ∈ walkD, c ∈ support1 := by
  decide

/-- A candidate is genuinely §6.2-feasible when a closed walk of the
read-overlap graph realizes its copy counts and uses every observed read type
at least once. -/
def Section62Feasible (w : List (Fin 8)) (d x : Fin 8 → Nat) : Prop :=
  IsCircuit w ∧ (∀ c : Fin 8, w.count c = d c) ∧ (∀ c ∈ w, 0 < x c)

theorem truth_section62_feasible1 : Section62Feasible walkS dS obs1 :=
  ⟨walkS_isCircuit, walkS_counts, by decide⟩

theorem truth_section62_feasible2 : Section62Feasible walkS dS obs2 :=
  ⟨walkS_isCircuit, walkS_counts, by decide⟩

theorem competitor_section62_feasible1 : Section62Feasible walkD dD obs1 :=
  ⟨walkD_isCircuit, walkD_counts, by decide⟩

theorem competitor_section62_feasible2 : Section62Feasible walkD2 dD2 obs2 :=
  ⟨walkD2_isCircuit, walkD2_counts, by decide⟩

/-! ## The §6.1 objectives -/

/-- The exact §6.1 objective with **candidate-intrinsic** length `N(D) = t`:
the multinomial probability of the observed type counts, as a product over the
eight oriented types. -/
def exactLik (x d : Fin 8 → Nat) (t : ℕ) : ℚ :=
  ((Nat.factorial (∑ c : Fin 8, x c) : ℚ) /
      (codes.map (fun c => (Nat.factorial (x c) : ℚ))).prod) *
    (codes.map (fun c => (((d c : ℚ) / (t : ℚ)) ^ (x c)))).prod

/-- The §6.1 product of binomial marginals with the external known genome size
`N`, as a product over the eight oriented types (zero-count factors retained). -/
def binomLik (N n : ℕ) (x d : Fin 8 → Nat) : ℚ :=
  (codes.map (fun c =>
    ((Nat.choose n (x c) : ℚ) *
      ((d c : ℚ) / (N : ℚ)) ^ (x c) *
      (1 - (d c : ℚ) / (N : ℚ)) ^ (n - x c)))).prod

/-- The source's binomial domain `0 ≤ d_w ≤ N`. -/
def binomDomain (N : ℕ) (d : Fin 8 → Nat) : Prop := ∀ c : Fin 8, d c ≤ N

/-- The AM-GM upper bound of the exact objective for observation `x`: the value
each competitor below attains exactly, because its normalized spectrum equals
`x / n`.  That no candidate can exceed it is
`docs/source-notes/oriented-variable-length-se62.md` §3 (prose). -/
def lstar (x : Fin 8 → Nat) : ℚ :=
  ((Nat.factorial (∑ c : Fin 8, x c) : ℚ) /
      (codes.map (fun c => (Nat.factorial (x c) : ℚ))).prod) *
    (codes.map (fun c => ((x c : ℚ) / (∑ c' : Fin 8, x c')) ^ (x c))).prod

theorem truth_domain : binomDomain 5 dS := by
  unfold binomDomain; decide

theorem competitor_domain : binomDomain 5 dD := by
  unfold binomDomain; decide

theorem competitor2_domain : binomDomain 5 dD2 := by
  unfold binomDomain; decide

/-! ## The exact (candidate-intrinsic length) objective -/

theorem exact_truth1 : exactLik obs1 dS 5 = 72 / 3125 := by
  unfold exactLik
  simp only [codes, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := obs1_eq
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := dS_eq
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, g0, g1, g2, g3, g4, g5, g6, g7, n1]
  norm_num

theorem exact_competitor1 : exactLik obs1 dD 6 = 5 / 162 := by
  unfold exactLik
  simp only [codes, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := obs1_eq
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := dD_eq
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, g0, g1, g2, g3, g4, g5, g6, g7, n1]
  norm_num

theorem exact_truth2 : exactLik obs2 dS 5 = 168 / 15625 := by
  unfold exactLik
  simp only [codes, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := obs2_eq
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := dS_eq
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, g0, g1, g2, g3, g4, g5, g6, g7, n2]
  norm_num

theorem exact_competitor2 : exactLik obs2 dD2 7 = 3240 / 117649 := by
  unfold exactLik
  simp only [codes, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := obs2_eq
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := dD2_eq
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, g0, g1, g2, g3, g4, g5, g6, g7, n2]
  norm_num

/-- The binomial coefficients of the first observation, evaluated so that the
`ℚ` products below are arithmetic. -/
theorem binomLik_truth1 : binomLik 5 6 obs1 dS = 1094374709451030528 / 186264514923095703125 := by
  unfold binomLik
  simp only [codes, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := obs1_eq
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := dS_eq
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, g0, g1, g2, g3, g4, g5, g6, g7,
    show ((Nat.choose 6 0) : ℚ) = 1 from by decide,
    show ((Nat.choose 6 1) : ℚ) = 6 from by decide,
    show ((Nat.choose 6 2) : ℚ) = 15 from by decide]
  norm_num

theorem binomLik_competitor1 : binomLik 5 6 obs1 dD = 1385067991648960512 / 186264514923095703125 := by
  unfold binomLik
  simp only [codes, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := obs1_eq
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := dD_eq
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, g0, g1, g2, g3, g4, g5, g6, g7,
    show ((Nat.choose 6 0) : ℚ) = 1 from by decide,
    show ((Nat.choose 6 1) : ℚ) = 6 from by decide,
    show ((Nat.choose 6 2) : ℚ) = 15 from by decide]
  norm_num

theorem binomLik_truth2 : binomLik 5 7 obs2 dS = 1211071982995454820352 / 582076609134674072265625 := by
  unfold binomLik
  simp only [codes, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := obs2_eq
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := dS_eq
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, g0, g1, g2, g3, g4, g5, g6, g7,
    show ((Nat.choose 7 0) : ℚ) = 1 from by decide,
    show ((Nat.choose 7 1) : ℚ) = 7 from by decide,
    show ((Nat.choose 7 3) : ℚ) = 35 from by decide]
  norm_num

theorem binomLik_competitor2 : binomLik 5 7 obs2 dD2 = 2043683971304830009344 / 582076609134674072265625 := by
  unfold binomLik
  simp only [codes, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := obs2_eq
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := dD2_eq
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, g0, g1, g2, g3, g4, g5, g6, g7,
    show ((Nat.choose 7 0) : ℚ) = 1 from by decide,
    show ((Nat.choose 7 1) : ℚ) = 7 from by decide,
    show ((Nat.choose 7 3) : ℚ) = 35 from by decide]
  norm_num

/-- The first competitor attains the AM-GM upper bound of the exact objective
for `obs1`, so its normalized spectrum is `x / n`. -/
theorem lstar_obs1 : lstar obs1 = 5 / 162 := by
  unfold lstar
  simp only [codes, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := obs1_eq
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, n1]
  norm_num

/-- The second competitor attains the AM-GM upper bound of the exact objective
for `obs2`. -/
theorem lstar_obs2 : lstar obs2 = 3240 / 117649 := by
  unfold lstar
  simp only [codes, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := obs2_eq
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, n2]
  norm_num

/-- The first competitor's exact objective equals the AM-GM upper bound for
`obs1`, because its normalized spectrum equals `x / n`. -/
theorem exact_competitor1_attains_bound : exactLik obs1 dD 6 = lstar obs1 := by
  unfold exactLik lstar
  simp only [codes, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := obs1_eq
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := dD_eq
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, g0, g1, g2, g3, g4, g5, g6, g7, n1]

/-- The second competitor's exact objective equals the AM-GM upper bound for
`obs2`. -/
theorem exact_competitor2_attains_bound : exactLik obs2 dD2 7 = lstar obs2 := by
  unfold exactLik lstar
  simp only [codes, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := obs2_eq
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := dD2_eq
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, g0, g1, g2, g3, g4, g5, g6, g7, n2]

/-- The truth stays strictly below the bound, so the truth's normalized
spectrum is not `x / n`. -/
theorem exact_truth1_below_bound : exactLik obs1 dS 5 < lstar obs1 := by
  rw [exact_truth1, lstar_obs1]
  norm_num

theorem exact_truth2_below_bound : exactLik obs2 dS 5 < lstar obs2 := by
  rw [exact_truth2, lstar_obs2]
  norm_num

/-- The exact-objective ratio for `n = 6`. -/
theorem exact_ratio1 : exactLik obs1 dD 6 / exactLik obs1 dS 5 = 15625 / 11664 := by
  rw [exact_truth1, exact_competitor1]
  norm_num

/-- The exact-objective ratio for `n = 7`. -/
theorem exact_ratio2 : exactLik obs2 dD2 7 / exactLik obs2 dS 5 = 2109375 / 823543 := by
  rw [exact_truth2, exact_competitor2]
  norm_num

/-- The first candidate strictly beats the truth under the exact §6.1 objective
(candidate-intrinsic length `N(D) = |D|`): ratio `15625/11664 > 1`. -/
theorem competitor_strictly_better_exact1 :
    exactLik obs1 dS 5 < exactLik obs1 dD 6 := by
  rw [exact_truth1, exact_competitor1]
  norm_num

/-- The second candidate strictly beats the truth under the exact §6.1
objective: ratio `2109375/823543 > 1`. -/
theorem competitor2_strictly_better_exact2 :
    exactLik obs2 dS 5 < exactLik obs2 dD2 7 := by
  rw [exact_truth2, exact_competitor2]
  norm_num

/-! ## The product-of-binomial-marginals objective -/

/-- The binomial-objective ratio for `n = 6`, `N = 5`: `81/64 > 1`.  Only the
`AAA` coordinate differs between the truth and the candidate, so the remaining
seven factors cancel. -/
theorem binom_ratio1 : binomLik 5 6 obs1 dD / binomLik 5 6 obs1 dS = 81 / 64 := by
  rw [binomLik_truth1, binomLik_competitor1]
  norm_num

/-- The binomial-objective ratio for `n = 7`, `N = 5`: `27/16 > 1`. -/
theorem binom_ratio2 : binomLik 5 7 obs2 dD2 / binomLik 5 7 obs2 dS = 27 / 16 := by
  rw [binomLik_truth2, binomLik_competitor2]
  norm_num

/-- The first candidate strictly beats the truth under the §6.1
product-of-binomial-marginals objective with external known `N = 5`: ratio
`81/64 > 1`. -/
theorem competitor_strictly_better_binom1 :
    binomLik 5 6 obs1 dS < binomLik 5 6 obs1 dD := by
  rw [binomLik_truth1, binomLik_competitor1]
  norm_num

/-- The second candidate strictly beats the truth under the §6.1
product-of-binomial-marginals objective: ratio `27/16 > 1`. -/
theorem competitor2_strictly_better_binom2 :
    binomLik 5 7 obs2 dS < binomLik 5 7 obs2 dD2 := by
  rw [binomLik_truth2, binomLik_competitor2]
  norm_num

/-! ## The endpoint -/

/-- **The oriented §6.2 unrestricted-length counterexample.**  Under the
source-faithful per-vertex feasibility reading (and under the strictly stronger
spelled support-equality reading), with the bridging hypothesis `I_s` at full
strength and both candidates genuinely §6.2-feasible (realized by closed walks
of the read-overlap graph), the truth is strictly beaten by a candidate of
**different length** (`|D| = 6 ≠ G = 5`) under the exact candidate-intrinsic
§6.1 objective and under the external-`N` product-of-binomial-marginals
objective.  Both objectives respect the source's `0 ≤ d_w ≤ N` domain. -/
theorem oriented_variable_length_se62_counterexample :
    SourceFaithfulIs.InformationFeasible truthGenome 3 realizedStarts ∧
      Section62Feasible walkS dS obs1 ∧ Section62Feasible walkD dD obs1 ∧
      SpelledFeasible62 dS obs1 ∧ SpelledFeasible62 dD obs1 ∧
      binomDomain 5 dS ∧ binomDomain 5 dD ∧
      exactLik obs1 dS 5 < exactLik obs1 dD 6 ∧
      binomLik 5 6 obs1 dS < binomLik 5 6 obs1 dD ∧
      exactLik obs1 dS 5 < lstar obs1 ∧ exactLik obs1 dD 6 = lstar obs1 :=
  ⟨truth_information_feasible, truth_section62_feasible1,
    competitor_section62_feasible1, truth_spelled_feasible1,
    competitor_spelled_feasible1, truth_domain, competitor_domain,
    competitor_strictly_better_exact1, competitor_strictly_better_binom1,
    exact_truth1_below_bound, exact_competitor1_attains_bound⟩

/-- The `n = 7` variant of the same mechanism. -/
theorem oriented_variable_length_se62_counterexample' :
    SourceFaithfulIs.InformationFeasible truthGenome 3 realizedStarts ∧
      Section62Feasible walkS dS obs2 ∧ Section62Feasible walkD2 dD2 obs2 ∧
      SpelledFeasible62 dS obs2 ∧ SpelledFeasible62 dD2 obs2 ∧
      binomDomain 5 dS ∧ binomDomain 5 dD2 ∧
      exactLik obs2 dS 5 < exactLik obs2 dD2 7 ∧
      binomLik 5 7 obs2 dS < binomLik 5 7 obs2 dD2 ∧
      exactLik obs2 dS 5 < lstar obs2 ∧ exactLik obs2 dD2 7 = lstar obs2 :=
  ⟨truth_information_feasible, truth_section62_feasible2,
    competitor_section62_feasible2, truth_spelled_feasible2,
    competitor_spelled_feasible2, truth_domain, competitor2_domain,
    competitor2_strictly_better_exact2, competitor2_strictly_better_binom2,
    exact_truth2_below_bound, exact_competitor2_attains_bound⟩

end AssemblyP1.OrientedVariableLengthSe62
