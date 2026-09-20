import Mathlib

/-!
# A lower-bound-1 Section 6.2 counterexample under bridging conditions

This file kernel-checks the finite witness recorded in
`docs/section62-bidirected-lowerbound1-determination.md`, under the corrected
Medvedev–Brudno §6.2 reading: the vertices of the bidirected read-overlap graph
are read *DNA molecules* (a word and its reverse complement are one vertex) and
the vertex lower bound is `1` — a read type must be present at least once, and
an observed multiplicity `x_w > 1` does **not** force `d_w ≥ x_w`.

Instance:

* alphabet `{A, T}` with the DNA reverse-complement involution `A ↔ T`;
* true circular genome `truth = AAATT` (length `5`);
* read length `L = 3`, realized starts `(0, 1, 4)` (`n = 3` reads);
* external known genome size `N = 5` (Medvedev–Brudno §6.1);
* observed read-molecule classes `x    = { AAA:1, AAT:1, TAA:1 }`;
* truth-induced flow             `d_S  = { AAA:1, AAT:2, TAA:2 }`  (`x ≤ d_S`);
* competitor `D = AAAATT` (length `6`), `d_D = { AAA:2, AAT:2, TAA:2 }`.

The source-faithful predicate `FeasibleType` below only requires support equality
and the *lower bound `1`* per observed read vertex; both `truth` and `competitor`
satisfy it.  They also happen to satisfy the stronger per-occurrence predicate
`Feasible` (`x ≤ d`), so the per-type statement holds a fortiori.  Both are
spelled by their cyclic length-`3` window walks, hence are admissible §6.2
flow candidates (Medvedev–Brudno Observation 7).  The strict `I_s` certificate
(coverage, the maximal length-`1` triple repeat of `A` all-bridged by reads that
contain the copy and extend on both sides, and the vacuous interleaving conjunct)
is checked below.  The §6.1 product-of-binomial-marginals objective with the
fixed external `N = 5` and `n = 3` is strictly larger for the competitor:
ratio `9/8`.

Scope.  This file is about the finite instance only.  It does not settle which
Medvedev–Brudno object the Shomorony et al. (2016) sentence intends, nor the
single-strand or fixed-candidate-length sub-cases.
-/

namespace AssemblyP1.Section62LowerBoundOneCounterexample

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

/-! ## Sequence-level §6.2 feasibility -/

/-- The source-faithful Medvedev–Brudno §6.2 feasibility predicate for a
molecule spectrum `d` against observed counts `x`: the support equals the
observed support, and every observed read vertex carries at least one unit of
flow.  This is the lower bound `1` of §6.2; the observed multiplicity `x` is not
a lower bound on `d`. -/
def FeasibleType (d x : Fin 8 → Nat) : Prop :=
  (∀ c, 0 < d c ↔ 0 < x c) ∧ ∀ c, 0 < x c → 1 ≤ d c

/-- Stronger predicate used by the older note: support equality together with the
per-occurrence lower bound `x ≤ d`.  It implies `FeasibleType`. -/
def Feasible (d x : Fin 8 → Nat) : Prop :=
  (∀ c, 0 < d c ↔ 0 < x c) ∧ ∀ c, x c ≤ d c

lemma feasible_implies_feasibleType {d x : Fin 8 → Nat} (h : Feasible d x) :
    FeasibleType d x := by
  constructor
  · exact h.1
  · intro c hc
    exact Nat.succ_le_of_lt (lt_of_lt_of_le hc (h.2 c))

theorem truth_feasible : Feasible dS obs := by
  unfold Feasible dS obs spec5 window5 cyc5 cls code rc bitA comp truth readStarts
  decide

theorem competitor_feasible : Feasible dD obs := by
  unfold Feasible dD obs spec6 window6 window5 cyc6 cyc5 cls code rc bitA comp
    truth competitor readStarts
  decide

theorem truth_feasibleType : FeasibleType dS obs :=
  feasible_implies_feasibleType truth_feasible

theorem competitor_feasibleType : FeasibleType dD obs :=
  feasible_implies_feasibleType competitor_feasible

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

/-! ## Main finite theorem -/

/-- Kernel-checked finite counterexample to statement (P): the instance
satisfies the source-faithful `I_s` certificate, the truth is a sequence-level
§6.2 feasible candidate, a competitor is also a sequence-level §6.2 feasible
candidate, and the competitor strictly beats the truth-induced flow under the
literal §6.1 objective. -/
theorem se62_bridging_flow_counterexample :
    SourceCertificate ∧ Feasible dS obs ∧ Feasible dD obs ∧ lik obs dS < lik obs dD :=
  ⟨truth_source_certificate, truth_feasible, competitor_feasible,
    competitor_strictly_better⟩

/-- The same finite counterexample under the source-faithful lower-bound-`1`
per-type §6.2 predicate `FeasibleType`: the truth and the competitor are both
admissible (each observed read vertex has flow at least `1`), while the
competitor strictly beats the truth under the literal §6.1 objective. -/
theorem se62_lower_bound_one_counterexample :
    SourceCertificate ∧ FeasibleType dS obs ∧ FeasibleType dD obs ∧
      lik obs dS < lik obs dD :=
  ⟨truth_source_certificate, truth_feasibleType, competitor_feasibleType,
    competitor_strictly_better⟩

end AssemblyP1.Section62LowerBoundOneCounterexample
