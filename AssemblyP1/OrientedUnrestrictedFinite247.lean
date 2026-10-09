import Mathlib
import AssemblyP1.SourceFaithfulIs

/-!
# Oriented unrestricted finite ML counterexample (board issue #247, lane 247b)

This module kernel-checks the NEW oriented unrestricted finite
historical-coverage ML counterexample proposed in board issue #247 parts 7-8.

## The instance

* alphabet `{A, B}` (rename `B → C` for literal DNA; the 4-letter DNA binomial
  endpoint below uses `{A, C, G, T}` directly), **oriented** length-`3` read
  types (no reverse-complement collapse; the 8 oriented types are coded by
  `code`);
* truth `S = AAABBABB` (circular, `G = 8`);
* competitor `D = AAAABABB` (circular, the **same** length `8`);
* read length `L = 3`;
* sample: each of the `8` starts of `S` sampled **once**, plus **four** extra
  copies of start `0` (whose window is `AAA`), total `n = 12` reads;
* observed oriented type counts `x = {AAA:5, AAB:1, ABB:2, BBA:2, BAB:1, BAA:1}`;
* truth spectrum `d_S = {AAA:1, AAB:1, ABB:2, BBA:2, BAB:1, BAA:1}`;
* competitor spectrum `d_D = {AAA:2, AAB:1, ABA:1, ABB:1, BBA:1, BAB:1, BAA:1}`.

## What is kernel-checked here

* the shared `SourceFaithfulIs.InformationFeasible` predicate `I_s` (old
  base-coverage `Covers`, every maximal triple repeat all-bridged, every
  interleaved pair bridged) for the **truth** with all `8` realized starts,
  discharged by finite `decide`.  Because every start is sampled, the old base
  coverage holds, and the sample is start-dense.
* the **exact intrinsic multinomial** §6.1 objective (candidate-intrinsic length
  `N(D) = |D| = 8`): the strict ratio `Lik(D)/Lik(S) = 2`.
* the **fixed-`N = 8` product-of-binomial-marginals** §6.1 objective with
  zero-count factors retained over all eight oriented types (including the
  unobserved `ABA` of `D`): the strict ratio
  `1341068619663964900807/448762029294263205888 = 2.9883736415…`.
* the **4-letter DNA** binomial objective (alphabet `{A, C, G, T}`, 64 oriented
  types, zero-count factors retained): the **same** ratio, because every type
  containing `G` or `T` has `x = d_S = d_D = 0` and hence contributes factor `1`.
* that `D` satisfies the **weak** §6.2 per-vertex lower bound `1` (every
  observed type occurs in `D`), but **fails this module's oriented full-overlap support-equality proxy**:
  `D` contains the unobserved oriented window `ABA`. This does **not**
  exclude a genuine reverse-complement DNA-molecule §6.2 flow.

## Scope and coordination

This is a counterexample among **all circular candidates of the true length**
(the unrestricted candidate class `F0`): its oriented support failure is **not** a theorem about the source's
bidirected DNA-molecule flow class, which identifies reverse complements.

The historical read-string coverage predicate `HistoricalCovers`, the
`DenseSampledStarts` certificate, and the `DenseSampledStarts ⇒ HistoricalCovers`
adapter are owned by lane 247a and are **not** defined here (this module does not
duplicate them).  The sample here is start-dense (every start sampled), so the
historical coverage predicate of 247a holds trivially; the coordination note is
`docs/source-notes/oriented-unrestricted-finite-247.md`.

All original proofs are preserved; this module is purely additive.  No `sorry`,
`admit`, or `axiom` is used; the axiom audit is at the bottom of `AssemblyP1.lean`.
-/

namespace AssemblyP1.OrientedUnrestrictedFinite247

set_option maxHeartbeats 800000

/-! ## The two-symbol alphabet and oriented type codes -/

/-- Two-symbol alphabet. -/
inductive Base where
  | A
  | B
  deriving DecidableEq, Inhabited, Repr

instance : Fintype Base where
  elems := {Base.A, Base.B}
  complete := by intro x; cases x <;> simp

/-- Bit encoding of a symbol (`A ↦ 0`, `B ↦ 1`). -/
def bitA : Base → Nat
  | .A => 0
  | .B => 1

/-- A length-`3` oriented read type / window. -/
abbrev W3 := Fin 3 → Base

/-- Binary code of a length-`3` oriented word, in `[0, 8)`.  This is the
**oriented** type index: `AAA = 0, AAB = 1, ABA = 2, ABB = 3, BAA = 4, BAB = 5,
BBA = 6, BBB = 7`. -/
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
  | 1 => .B
  | _ => .A

/-- The length-`3` oriented word coded by `c`: the inverse of `code`/`idx`. -/
def decode (c : Fin 8) : W3 :=
  ![bitB (c.val / 4), bitB ((c.val / 2) % 2), bitB (c.val % 2)]

/-- Sanity check of the coding. -/
theorem idx_decode (c : Fin 8) : idx (decode c) = c := by
  fin_cases c <;> decide

/-! ## The instance -/

/-- The true circular genome `AAABBABB` of length `8`. -/
def truth : Fin 8 → Base := ![.A, .A, .A, .B, .B, .A, .B, .B]

/-- The competitor `AAAABABB` of length `8`: the truth with one extra `A` inserted
inside its maximal `A³` run. -/
def competitor : Fin 8 → Base := ![.A, .A, .A, .A, .B, .A, .B, .B]

section Windows

variable {n : ℕ} (g : Fin n → Base) [NeZero n]

/-- Circular symbol access. -/
def cyc (i : Nat) : Base := g ⟨i % n, Nat.mod_lt _ (NeZero.pos n)⟩

/-- Length-`3` circular window at start `r`. -/
def window (r : Fin n) : W3 := ![cyc g r.val, cyc g (r.val + 1), cyc g (r.val + 2)]

/-- Multiplicity of the oriented type `c` in the length-`3` window spectrum of
`g`. -/
def spec (c : Fin 8) : Nat :=
  (Finset.univ.filter (fun r : Fin n => idx (window g r) = c)).card

end Windows

/-- The eight oriented length-`3` type codes, as a list so that the objective
products below unfold definitionally. -/
def codes : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- Realized length-`3` read placements: **all** eight starts, each sampled once.
Read multiplicity does not enter `I_s`; the observed counts below record the
four extra copies of start `0` separately. -/
def realizedStarts : Finset (Fin 8) := {0, 1, 2, 3, 4, 5, 6, 7}

/-- The realized read multiset of the `n = 12` observation: all eight starts
once, plus four extra copies of start `0`, whose window is `AAA`. -/
def reads : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7, 0, 0, 0, 0]

/-- Observed oriented type counts `x = spec₃(S) + 4·e_AAA` (`n = 12`). -/
def obs (c : Fin 8) : Nat :=
  (reads.filter (fun r => idx (window truth r) = c)).length

/-- Truth spectrum `d_S`. -/
abbrev dS (c : Fin 8) : Nat := spec truth c

/-- Competitor spectrum `d_D`. -/
abbrev dD (c : Fin 8) : Nat := spec competitor c

/-- The instance's observed type counts (`n = 12`). -/
theorem obs_eq :
    obs 0 = 5 ∧ obs 1 = 1 ∧ obs 2 = 0 ∧ obs 3 = 2 ∧
      obs 4 = 1 ∧ obs 5 = 1 ∧ obs 6 = 2 ∧ obs 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The truth's spectrum. -/
theorem dS_eq :
    dS 0 = 1 ∧ dS 1 = 1 ∧ dS 2 = 0 ∧ dS 3 = 2 ∧
      dS 4 = 1 ∧ dS 5 = 1 ∧ dS 6 = 2 ∧ dS 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The competitor's spectrum: the truth's spectrum with one extra `AAA` and
the two-copy repeats `ABB`, `BBA` collapsed to one copy each, plus the new
unobserved window `ABA` (`ABA` is code `2`). -/
theorem dD_eq :
    dD 0 = 2 ∧ dD 1 = 1 ∧ dD 2 = 1 ∧ dD 3 = 1 ∧
      dD 4 = 1 ∧ dD 5 = 1 ∧ dD 6 = 1 ∧ dD 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Total observed multiplicity, `n = 12`. -/
theorem nobs : ∑ c : Fin 8, obs c = 12 := by
  decide

/-! ## The source-faithful bridging hypothesis -/

open SourceFaithfulIs

/-- The true circular genome `AAABBABB` in the shared source-faithful
representation. -/
abbrev truthGenome : SourceFaithfulIs.Genome Base where
  len := 8
  len_pos := by norm_num
  sym := truth

/-- **The actual `I_s` hypothesis of this realization**, at full strength, for
the truth with **all eight** realized starts.  Discharged by finite `decide`:
every maximal triple repeat of `AAABBABB` is all-bridged (they are all length
`1`), and every interleaved pair of maximal repeats is bridged; coverage holds
because every start is sampled.  No repeat is enumerated by hand and no clause
is assumed. -/
theorem truth_information_feasible :
    SourceFaithfulIs.InformationFeasible truthGenome 3 realizedStarts := by
  decide

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

theorem truth_domain : binomDomain 8 dS := by
  unfold binomDomain; decide

theorem competitor_domain : binomDomain 8 dD := by
  unfold binomDomain; decide

/-! ## The exact (candidate-intrinsic length) objective -/

theorem exact_truth : exactLik obs dS 8 = 31185 / 134217728 := by
  unfold exactLik
  simp only [codes, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := obs_eq
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := dS_eq
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, g0, g1, g2, g3, g4, g5, g6, g7, nobs]
  norm_num

theorem exact_competitor : exactLik obs dD 8 = 31185 / 67108864 := by
  unfold exactLik
  simp only [codes, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := obs_eq
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := dD_eq
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, g0, g1, g2, g3, g4, g5, g6, g7, nobs]
  norm_num

/-- The exact-objective ratio: `Lik(D)/Lik(S) = 2 > 1`. -/
theorem exact_ratio : exactLik obs dD 8 / exactLik obs dS 8 = 2 := by
  rw [exact_truth, exact_competitor]
  norm_num

/-- The competitor strictly beats the truth under the exact §6.1 objective
(candidate-intrinsic length `N(D) = 8`): ratio `2 > 1`. -/
theorem competitor_strictly_better_exact :
    exactLik obs dS 8 < exactLik obs dD 8 := by
  rw [exact_truth, exact_competitor]
  norm_num

/-! ## The product-of-binomial-marginals objective -/

theorem binomLik_truth : binomLik 8 12 obs dS =
    64620979035056662067120645457503705061389099645697 /
      3064991081731777716716694054300618367237478244367204352 := by
  unfold binomLik
  simp only [codes, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := obs_eq
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := dS_eq
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, g0, g1, g2, g3, g4, g5, g6, g7,
    show ((Nat.choose 12 0) : ℚ) = 1 from by decide,
    show ((Nat.choose 12 1) : ℚ) = 12 from by decide,
    show ((Nat.choose 12 2) : ℚ) = 66 from by decide,
    show ((Nat.choose 12 5) : ℚ) = 792 from by decide]
  norm_num

theorem binomLik_competitor : binomLik 8 12 obs dD =
    54356091680216275071090232352605711559924590405098880511871965373 /
      862718293348820473429344482784628181556388621521298319395315527974912 := by
  unfold binomLik
  simp only [codes, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := obs_eq
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := dD_eq
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, g0, g1, g2, g3, g4, g5, g6, g7,
    show ((Nat.choose 12 0) : ℚ) = 1 from by decide,
    show ((Nat.choose 12 1) : ℚ) = 12 from by decide,
    show ((Nat.choose 12 2) : ℚ) = 66 from by decide,
    show ((Nat.choose 12 5) : ℚ) = 792 from by decide]
  norm_num

/-- The binomial-objective ratio for `N = 8`, `n = 12`, zero-count factors
retained: `1341068619663964900807/448762029294263205888 = 2.9883736415… > 1`. -/
theorem binom_ratio :
    binomLik 8 12 obs dD / binomLik 8 12 obs dS =
      1341068619663964900807 / 448762029294263205888 := by
  rw [binomLik_truth, binomLik_competitor]
  norm_num

/-- The competitor strictly beats the truth under the §6.1
product-of-binomial-marginals objective with external known `N = 8`: ratio
`≈ 2.988 > 1`. -/
theorem competitor_strictly_better_binom :
    binomLik 8 12 obs dS < binomLik 8 12 obs dD := by
  rw [binomLik_truth, binomLik_competitor]
  norm_num

/-! ## The competitor fails the oriented full-overlap support proxy -/

/-- The **oriented analogue** of MB09 §6.2's per-vertex lower bound `1`:
every observed oriented read type occurs in the candidate at least once.
This is not the original reverse-complement molecule-vertex predicate. -/
def PerVertexFeasible (d x : Fin 8 → Nat) : Prop :=
  ∀ c : Fin 8, 0 < x c → 1 ≤ d c

/-- A project-level **oriented full-overlap support-equality proxy**:
the candidate's oriented window support equals the observed oriented support.
It is not the full original §6.2 bidirected-flow predicate.  The competitor
fails this proxy because oriented `ABA` was unobserved. -/
def SpelledFeasible62 (d x : Fin 8 → Nat) : Prop :=
  (∀ c : Fin 8, 0 < d c ↔ 0 < x c) ∧ PerVertexFeasible d x

theorem competitor_perVertex_feasible : PerVertexFeasible dD obs := by
  unfold PerVertexFeasible; decide

theorem truth_spelled_feasible : SpelledFeasible62 dS obs := by
  unfold SpelledFeasible62 PerVertexFeasible; decide

/-- **The unobserved `ABA` window of `D`.**  `ABA` is code `2`: it occurs once in
`D` (`d_D(ABA) = 1`) but was never observed (`x(ABA) = 0`).  This is the single
fact that excludes `D` from this module's oriented support-equality
proxy, not from the original reverse-complement molecule-flow class. -/
theorem aba_unobserved : dD 2 = 1 ∧ obs 2 = 0 := by
  obtain ⟨_, _, g2, _, _, _, _, _⟩ := dD_eq
  obtain ⟨_, _, h2, _, _, _, _, _⟩ := obs_eq
  exact ⟨g2, h2⟩

theorem competitor_not_spelled_feasible : ¬ SpelledFeasible62 dD obs := by
  rintro ⟨hs, _⟩
  have := hs 2
  obtain ⟨g2, h2⟩ := aba_unobserved
  rw [g2, h2] at this
  exact absurd this (by decide)

/-! ## The 4-letter DNA binomial endpoint -/

/-- The DNA alphabet `{A, C, G, T}`. -/
inductive Dna where
  | A
  | C
  | G
  | T
  deriving DecidableEq, Inhabited, Repr

instance : Fintype Dna where
  elems := {Dna.A, Dna.C, Dna.G, Dna.T}
  complete := by intro x; cases x <;> simp

/-- A length-`3` oriented DNA read type / window. -/
abbrev W3D := Fin 3 → Dna

/-- The true circular DNA genome `AAACCACC` (= `S` with `B ↦ C`), length `8`. -/
def truthD : Fin 8 → Dna := ![.A, .A, .A, .C, .C, .A, .C, .C]

/-- The competitor `AAAACACC` (= `D` with `B ↦ C`), length `8`. -/
def competitorD : Fin 8 → Dna := ![.A, .A, .A, .A, .C, .A, .C, .C]

/-- The `i`-th symbol of a circular DNA genome of length `8`. -/
def cycD (g : Fin 8 → Dna) (i : Nat) : Dna :=
  g ⟨i % 8, Nat.mod_lt _ (by norm_num)⟩

/-- The length-`3` circular window of `g` beginning at start `r`. -/
def windowD (g : Fin 8 → Dna) (r : Fin 8) : W3D :=
  fun d => cycD g (r.val + d.val)

/-- Number of circular start positions of `g` whose length-`3` window is `w`. -/
def occD (g : Fin 8 → Dna) (w : W3D) : Nat :=
  (Finset.univ.filter (fun r : Fin 8 => windowD g r = w)).card

/-- Read type `AAA`. -/
def readAAA : W3D := ![Dna.A, Dna.A, Dna.A]

/-- Read type `AAC`. -/
def readAAC : W3D := ![Dna.A, Dna.A, Dna.C]

/-- Read type `ACC`. -/
def readACC : W3D := ![Dna.A, Dna.C, Dna.C]

/-- Read type `CCA`. -/
def readCCA : W3D := ![Dna.C, Dna.C, Dna.A]

/-- Read type `CAC`. -/
def readCAC : W3D := ![Dna.C, Dna.A, Dna.C]

/-- Read type `CAA`. -/
def readCAA : W3D := ![Dna.C, Dna.A, Dna.A]

/-- Read type `ACA` (unobserved, has positive multiplicity in the competitor). -/
def readACA : W3D := ![Dna.A, Dna.C, Dna.A]

/-- The realized DNA read multiset: all eight starts once, plus four extra copies
of start `0` (`AAA`). -/
def readsD : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7, 0, 0, 0, 0]

/-- Observed count `x_w` of read type `w`: the eight starts of `S` once each,
plus four extra copies of start `0` (`AAA`), total `n = 12`. -/
def obsDCount (w : W3D) : Nat :=
  (readsD.filter (fun r => windowD truthD r = w)).length

/-- The literal binomial marginal for read type `w` under candidate `g`, with
the fixed external length `N = 8` and total read count `n = 12`:
`Binom(12, x_w) (d_w / 8)^{x_w} (1 - d_w / 8)^{12 - x_w}`, where `d_w = occD g w`.
Zero observed counts thus retain the factor `(1 - d_w / 8)^12`. -/
def marginalD (g : Fin 8 → Dna) (w : W3D) : ℚ :=
  (Nat.choose 12 (obsDCount w) : ℚ) * ((occD g w : ℚ) / 8) ^ (obsDCount w) *
    (1 - (occD g w : ℚ) / 8) ^ (12 - obsDCount w)

/-- The 4-letter DNA Section 6.1 approximation: the product of the individual
binomial marginals over the whole DNA read-type space (`4³ = 64` oriented
types), zero-count factors retained. -/
def likelihoodD (g : Fin 8 → Dna) : ℚ :=
  ∏ w : W3D, marginalD g w

/-- The seven `{A, C}`-words that carry the same bits as the `{A, B}`-witness
types with positive observed count or positive multiplicity in `truth` or
`competitor`.  Every other DNA type has `x = d_S = d_D = 0` and contributes
factor `1`. -/
def relevantD : Finset W3D :=
  {readAAA, readAAC, readACC, readCCA, readCAC, readCAA, readACA}

/-- Every read type outside `relevantD` has observed count zero. -/
theorem obsDCount_eq_zero_of_not_relevantD :
    ∀ w : W3D, w ∉ relevantD → obsDCount w = 0 := by decide

/-- Every read type outside `relevantD` has multiplicity zero in the truth. -/
theorem occD_truth_eq_zero_of_not_relevantD :
    ∀ w : W3D, w ∉ relevantD → occD truthD w = 0 := by decide

/-- Every read type outside `relevantD` has multiplicity zero in the competitor. -/
theorem occD_competitor_eq_zero_of_not_relevantD :
    ∀ w : W3D, w ∉ relevantD → occD competitorD w = 0 := by decide

/-- A type with `x_w = 0` and `d_w = 0` contributes the factor `1` to the
product. -/
theorem marginalD_eq_one_of_occD_eq_zero (g : Fin 8 → Dna) (w : W3D)
    (hocc : occD g w = 0) (hobs : obsDCount w = 0) : marginalD g w = 1 := by
  simp [marginalD, hocc, hobs]

/-- For a candidate all of whose support lies in `relevantD`, the full product
of binomial marginals equals the product over `relevantD`. -/
theorem likelihoodD_eq_relevantD_prod (g : Fin 8 → Dna)
    (h : ∀ w : W3D, w ∉ relevantD → occD g w = 0) :
    likelihoodD g = ∏ w ∈ relevantD, marginalD g w := by
  unfold likelihoodD
  exact (Finset.prod_subset (s₁ := relevantD) (s₂ := Finset.univ)
    (by intro x _; exact Finset.mem_univ x)
    (by
      intro w _ hw
      exact marginalD_eq_one_of_occD_eq_zero g w (h w hw)
        (obsDCount_eq_zero_of_not_relevantD w hw))).symm

/-- The product over the seven-element `relevantD` set written as an explicit
nested product. -/
theorem relevantD_prod_eq (f : W3D → ℚ) :
    ∏ w ∈ relevantD, f w =
      f readAAA * (f readAAC * (f readACC * (f readCCA *
        (f readCAC * (f readCAA * f readACA))))) := by
  unfold relevantD
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]

/-! ## Exact arithmetic for the DNA binomial -/

theorem obsDCount_AAA : obsDCount readAAA = 5 := by decide

theorem obsDCount_AAC : obsDCount readAAC = 1 := by decide

theorem obsDCount_ACC : obsDCount readACC = 2 := by decide

theorem obsDCount_CCA : obsDCount readCCA = 2 := by decide

theorem obsDCount_CAC : obsDCount readCAC = 1 := by decide

theorem obsDCount_CAA : obsDCount readCAA = 1 := by decide

theorem obsDCount_ACA : obsDCount readACA = 0 := by decide

theorem occD_truth_AAA : occD truthD readAAA = 1 := by decide

theorem occD_truth_AAC : occD truthD readAAC = 1 := by decide

theorem occD_truth_ACC : occD truthD readACC = 2 := by decide

theorem occD_truth_CCA : occD truthD readCCA = 2 := by decide

theorem occD_truth_CAC : occD truthD readCAC = 1 := by decide

theorem occD_truth_CAA : occD truthD readCAA = 1 := by decide

theorem occD_truth_ACA : occD truthD readACA = 0 := by decide

theorem occD_competitor_AAA : occD competitorD readAAA = 2 := by decide

theorem occD_competitor_AAC : occD competitorD readAAC = 1 := by decide

theorem occD_competitor_ACC : occD competitorD readACC = 1 := by decide

theorem occD_competitor_CCA : occD competitorD readCCA = 1 := by decide

theorem occD_competitor_CAC : occD competitorD readCAC = 1 := by decide

theorem occD_competitor_CAA : occD competitorD readCAA = 1 := by decide

theorem occD_competitor_ACA : occD competitorD readACA = 1 := by decide

/-- Exact 4-letter DNA product-of-binomial-marginals likelihood of the observed
reads under the truth, including the zero-count factors. -/
theorem likelihoodD_truth : likelihoodD truthD =
    64620979035056662067120645457503705061389099645697 /
      3064991081731777716716694054300618367237478244367204352 := by
  rw [likelihoodD_eq_relevantD_prod truthD occD_truth_eq_zero_of_not_relevantD,
    relevantD_prod_eq]
  simp only [marginalD]
  rw [obsDCount_AAA, obsDCount_AAC, obsDCount_ACC, obsDCount_CCA, obsDCount_CAC,
    obsDCount_CAA, obsDCount_ACA, occD_truth_AAA, occD_truth_AAC, occD_truth_ACC,
    occD_truth_CCA, occD_truth_CAC, occD_truth_CAA, occD_truth_ACA]
  simp only [show ((Nat.choose 12 0) : ℚ) = 1 from by decide,
    show ((Nat.choose 12 1) : ℚ) = 12 from by decide,
    show ((Nat.choose 12 2) : ℚ) = 66 from by decide,
    show ((Nat.choose 12 5) : ℚ) = 792 from by decide]
  norm_num

/-- Exact 4-letter DNA product-of-binomial-marginals likelihood of the observed
reads under the competitor, including the zero-count factor for `ACA`. -/
theorem likelihoodD_competitor : likelihoodD competitorD =
    54356091680216275071090232352605711559924590405098880511871965373 /
      862718293348820473429344482784628181556388621521298319395315527974912 := by
  rw [likelihoodD_eq_relevantD_prod competitorD occD_competitor_eq_zero_of_not_relevantD,
    relevantD_prod_eq]
  simp only [marginalD]
  rw [obsDCount_AAA, obsDCount_AAC, obsDCount_ACC, obsDCount_CCA, obsDCount_CAC,
    obsDCount_CAA, obsDCount_ACA, occD_competitor_AAA, occD_competitor_AAC,
    occD_competitor_ACC, occD_competitor_CCA, occD_competitor_CAC,
    occD_competitor_CAA, occD_competitor_ACA]
  simp only [show ((Nat.choose 12 0) : ℚ) = 1 from by decide,
    show ((Nat.choose 12 1) : ℚ) = 12 from by decide,
    show ((Nat.choose 12 2) : ℚ) = 66 from by decide,
    show ((Nat.choose 12 5) : ℚ) = 792 from by decide]
  norm_num

/-- The 4-letter DNA binomial ratio, zero-count factors retained: the **same**
`1341068619663964900807/448762029294263205888`, because the fifty-seven types
outside `relevantD` all have `x = d_S = d_D = 0` and contribute factor `1`. -/
theorem binomD_ratio :
    likelihoodD competitorD / likelihoodD truthD =
      1341068619663964900807 / 448762029294263205888 := by
  rw [likelihoodD_truth, likelihoodD_competitor]
  norm_num

/-! ## The endpoint -/

/-- **The oriented unrestricted finite counterexample (issue #247, lane 247b).**

Under the source-faithful bridging hypothesis `I_s` (old base coverage, all
triple repeats all-bridged, all interleaved pairs bridged) for the start-dense
sample of the truth `S = AAABBABB`, the competitor `D = AAAABABB` — a circular
candidate of the **same** length, hence a member of the **unrestricted**
candidate class `F0` — **strictly beats the truth** under

* the exact candidate-intrinsic §6.1 objective: ratio `2 > 1`;
* the fixed-`N = 8` product-of-binomial-marginals objective (zero-count factors
  retained): ratio `1341068619663964900807/448762029294263205888 ≈ 2.988 > 1`;
* the 4-letter DNA binomial objective (zero-count factors retained): the same
  ratio `1341068619663964900807/448762029294263205888`.

The competitor `D` contains the **unobserved** window `ABA`; it satisfies the
weak oriented per-vertex lower bound `1` but fails the oriented full-overlap
support-equality proxy.  This is a legitimate unrestricted same-length
finite counterexample; it makes **no negative candidacy claim** about original
reverse-complement §6.2 molecule flows (where `ABA = rc(BAB)`). -/
theorem oriented_unrestricted_finite247_counterexample :
    SourceFaithfulIs.InformationFeasible truthGenome 3 realizedStarts ∧
      binomDomain 8 dS ∧ binomDomain 8 dD ∧
      exactLik obs dS 8 < exactLik obs dD 8 ∧
      binomLik 8 12 obs dS < binomLik 8 12 obs dD ∧
      PerVertexFeasible dD obs ∧ ¬ SpelledFeasible62 dD obs ∧
      likelihoodD truthD < likelihoodD competitorD :=
  ⟨truth_information_feasible, truth_domain, competitor_domain,
    competitor_strictly_better_exact, competitor_strictly_better_binom,
    competitor_perVertex_feasible, competitor_not_spelled_feasible, by
      rw [likelihoodD_truth, likelihoodD_competitor]
      norm_num⟩

end AssemblyP1.OrientedUnrestrictedFinite247
