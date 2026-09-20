import Mathlib

/-!
# A finite SAME-LENGTH Section 6.2 bridging counterexample

This file kernel-checks the finite witness recorded in
`docs/section62-same-length-bidirected-counterexample.md`.  Under the
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

What is kernel-checked here:

* the source-faithful `I_s` certificate (coverage, every maximal triple repeat
  all-bridged, every interleaved repeat pair bridged — for this truth the
  interleaving conjunct is **non-vacuous**: the `A`-copies `{0,2}` and `{1,4}`
  interleave, and both pairs are bridged);
* the §6.2 *spelled-circuit* feasibility predicate `SeqSupport` (support
  equality: a circular molecule has every observed read molecule as a
  length-`L` submolecule, so its cyclic window walk visits every read vertex,
  satisfying the source vertex lower bound `1`);
* the strict improvement under both same-length objectives:
  the literal §6.1 product-of-binomial-marginals ratio `L(D)/L(S) = 5`, and the
  candidate-intrinsic exact multinomial ratio `exact(D)/exact(S) = 3`.

Scope.  The explicit bidirected overlap graph, its transitive reduction, the
edge-incidence/balance conditions and the absence of supersource/supersink
usage for the two walks are checked computationally (not in Lean) by
`scripts/verify_samelength_se62_counterexample.py` and the companion note.  The
Lean file checks the finite `I_s`, `SeqSupport` and likelihood claims.  It does
not settle which Medvedev–Brudno object the Shomorony et al. (2016) sentence
intends, nor the per-occurrence strengthening or the single-strand reading.
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

/-! ## Main finite theorem -/

/-- Kernel-checked finite same-length counterexample: the instance satisfies the
source-faithful `I_s` certificate, the truth and a same-length competitor both
satisfy the §6.2 spelled-circuit feasibility predicate `SeqSupport`, and the
competitor strictly beats the truth under both the literal §6.1 binomial
objective (`5 > 1`) and the exact same-length multinomial objective (`3 > 1`).
The explicit bidirected-graph/flow admissibility of both circuits is checked
computationally in `scripts/verify_samelength_se62_counterexample.py`. -/
theorem samelength_se62_counterexample :
    SourceCertificate ∧ SeqSupport dS obs ∧ SeqSupport dD obs ∧
      lik obs dS < lik obs dD ∧ exactLik dD obs / exactLik dS obs = 3 :=
  ⟨truth_source_certificate, truth_support, competitor_support,
    competitor_strictly_better, exactLik_over_truth⟩

end AssemblyP1.SameLengthSection62Counterexample
