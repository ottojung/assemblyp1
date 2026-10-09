import Mathlib
import AssemblyP1.SourceFaithfulIs
import AssemblyP1.Section62BidirectedFlow
import AssemblyP1.Section62BridgingCounterexample
import AssemblyP1.SameLengthSection62Counterexample

/-!
# The general (non-spelled) Medvedev–Brudno §6.2 flow domain

This module resolves the three questions issue #214 asks about the literal
Medvedev–Brudno (2009) §6.2 object, under the strand convention in which the
vertices of the bidirected read-overlap graph are read *DNA molecules*
(MB09 §3.1, §4.1, §6.2) and the objective is the §6.1 separable binomial with
external known genome size `N`.

**(A) Refutation over the whole feasible set needs no additional witness.** The
`Feasible62` predicate of `AssemblyP1/Section62BidirectedFlow.lean` is the
*general* §6.2 feasibility predicate: it constrains a flow only by the edge lower
bounds, the §6.2 vertex lower bound `1`, the §3.4 signed-incidence balance and the
Observation-7 throughput identity — it says nothing about the flow being spelled
by a genome.  A spelled candidate is a general feasible flow
(`spelled_subset_general` below), so the already kernel-checked spelled witnesses
of `AssemblyP1/Section62BridgingCounterexample.lean` and
`AssemblyP1/SameLengthSection62Counterexample.lean` each certify, in their last
conjuncts, admissibility inside the *general* flow feasible set.  Their strict
likelihood inequalities therefore already refute dominance over the whole flow
domain; no non-spellable flow is required for that refutation.  Both witnesses are
packaged, in their own module namespaces, as the single kernel-checked objects
`bridging_spelled_witnesses_general` and `samelength_spelled_witnesses_general`
below.

**(B) The general feasible set strictly contains the spelled circuits, and in this
instance its maximizers are exactly non-spelled ones.** The instance below has a
genuine §6.2 admissible flow whose vertex throughputs are *not* the spectrum of any
circular molecule — of no length at all — and which strictly beats the bridged
truth:

```text
alphabet          {A, T}, reverse-complement involution A ↔ T
truth             S = AAATT            (G = 5)
read length       L = 3,  o_min = 1    (overlaps of length ≥ 1)
realized starts   (0, 1, 4), start 0 sampled twice   (n = 4)
external size     N = |S| = 5
observed          x = { AAA:2, AAT:1, TAA:1 }
truth spectrum    d_S = { AAA:1, AAT:2, TAA:2 }
flow optima       d* = { AAA:2, AAT:1, TAA:1 }   and   { AAA:3, AAT:1, TAA:1 }
ratio             L(d*)/L(d_S) = 256/81 > 1
```

The `{AAA:2, AAT:1, TAA:1}` flow is a single bidirected circuit through the four
edges `AAA.p → AAA.p`, `AAA.p → AAT.p`, `AAT.p → TAA.p` (overlap length **1**) and
`TAA.p → AAA.p`; `{AAA:3, AAT:1, TAA:1}` adds one traversal of the `AAA.p → AAA.p`
self-overlap.  Consecutive windows of a circular molecule overlap in exactly
`L−1 = 2` symbols, so no window walk ever uses a length-`1` overlap.  The
throughput-level statement is proved in full generality by
`no_sequence_has_star_spectrum`: a spectrum's total mass is the candidate length,
so a molecule with throughputs `d*` would have length `4`, and the `2⁴` molecules
of that length are exhaustively checked.

**(C) Hence the §6.2 feasible set has no "maximum-likelihood sequence" for this
instance.** `lik_le_star` proves that `d*` maximizes the §6.1 objective over the
whole domain `1 ≤ d ≤ N`, and `star_argmax` identifies the complete maximizer set
inside that domain as `{d*, d*₃}`; `no_sequence_has_star_spectrum` says neither of
them is a genome spectrum.  So any reading of the published sentence "the
maximum-likelihood sequence is the true sequence" over the §6.2 flow domain needs
an extra flow-to-sequence rule, and the rule changes the answer: restricting the
candidate set to flows that do spell a genome excludes the optimum, and every
  spelled candidate is strictly worse (the sequence-side comparison of the
  companion note §4, a bounded certificate checked by
  `scripts/verify_se62_nonspelled_flow_domain.py`).

What is *not* claimed here.  The module does not decide which Medvedev–Brudno
layer the Shomorony et al. (2016) sentence denotes.  It also does not decide
whether a non-spellable maximizer exists at `o_min = L−1`, the setting of the
merged witnesses: for that setting and this read support the circulation cone is
`{(a, 2b, 2b)}`, which is contained in the sequence spectra, and the bounded
search in the companion note §7 found no non-spellable maximizer in scope.  Both
`o_min` readings are reported, neither is selected.

## Source correspondence

| Lean object | MB09 clause |
|---|---|
| `Base`, `comp`, `rc`, `cls` | §3.1: a DNA molecule is an unordered reverse-complement strand pair |
| `readVerts`, `rep3`, `graph1`, `overlapEdges` | §6.2: "the vertices of this graph are the reads"; §4.1: "each k-molecule is represented only once" |
| `ov`, `bdEdge`, `sgnRep`/`sgnTgt` | §3.3: a bidirected edge carries a signed incidence at each endpoint |
| `reducedList`, `transitivelyReducedLonger` | §6.2: "we remove any overlap that is spelled by two shorter overlaps", read as the Myers 2005 reduction; the literal shorter-overlaps reading is vacuous at `L = 3` (`reduction_vacuous_literal`) |
| `starFlow21`, `starFlow31` | §6.2: the flow is "a (non-contiguous) assembly"; §5.2: `dᵢ` is the flow through vertex `i` |
| `Feasible62`, `noTerm` | §6.2: vertex lower bound `1`, other lower bounds `0`, upper bounds `∞`; §3.4: `pos(f)(v) − neg(f)(v) = b(v)`; supersource/supersink at prohibitive cost |
| `portOut`, `portIn`, `PortBalanced` | §3.3/§3.4 read at strand (port) level: the departing and arriving flow agree at every strand |
| `marginal`, `lik` | §6.1: product of per-type binomials with external `N` |

Everything is decidable and kernel-checked: the module contains no `sorry`,
`axiom`, `admit` or `native_decide`.
-/

namespace AssemblyP1.Section62NonSpelledFlow

set_option maxHeartbeats 4000000

/-! ## The molecule-class labels -/

/-- Two-symbol alphabet; the reverse-complement involution is `A ↔ T`. -/
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

lemma code_lt (w : W3) : code w < 8 := by
  have h0 : bitA (w 0) ≤ 1 := by cases w 0 <;> decide
  have h1 : bitA (w 1) ≤ 1 := by cases w 1 <;> decide
  have h2 : bitA (w 2) ≤ 1 := by cases w 2 <;> decide
  unfold code
  omega

/-- Reverse complement of a length-`3` word. -/
def rc (w : W3) : W3 := ![comp (w 2), comp (w 1), comp (w 0)]

/-- Molecule class of a word: the smaller of its own code and the code of its
reverse complement.  The four realizable classes are `AAA` (code `0`),
`AAT` (code `1`), `ATA` (code `2`) and `TAA` (code `4`). -/
def cls (w : W3) : Fin 8 :=
  ⟨min (code w) (code (rc w)), Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (code_lt w)⟩

/-- The three molecule classes of the observed reads, in class-code order. -/
abbrev suppClasses : Finset (Fin 8) := {0, 1, 4}

/-! ## The instance -/

/-- The true circular genome `AAATT` of length `5`. -/
def truth : Fin 5 → Base := ![.A, .A, .A, .T, .T]

/-- Circular symbol access for a length-`5` genome. -/
def cyc5 (g : Fin 5 → Base) (i : Nat) : Base :=
  g ⟨i % 5, Nat.mod_lt _ (by norm_num)⟩

/-- Length-`3` circular window at start `r`. -/
def window5 (g : Fin 5 → Base) (r : Fin 5) : W3 :=
  ![cyc5 g r.val, cyc5 g (r.val + 1), cyc5 g (r.val + 2)]

/-- Number of starts of a length-`5` genome whose window has molecule class `c`. -/
def spec5 (g : Fin 5 → Base) (c : Fin 8) : Nat :=
  (Finset.univ.filter (fun r : Fin 5 => cls (window5 g r) = c)).card

/-- The realized start set: the distinct placements of the `n = 4` sampled reads.
Start `0` is sampled twice; coverage and bridging quantify over placements, so the
duplicate collapses there and the sampled multiplicity is recorded separately by
`obs`. -/
def realizedStarts : Finset (Fin 5) := {0, 1, 4}

/-- The sampling realization, with multiplicities. -/
def readStarts : List (Fin 5) := [0, 0, 1, 4]

/-- Observed read-molecule class counts `x`. -/
def obs (c : Fin 8) : Nat :=
  (readStarts.filter (fun r => cls (window5 truth r) = c)).length

/-- Truth-induced spectrum `d_S`. -/
def dS (c : Fin 8) : Nat := spec5 truth c

/-- The throughput vector of the non-spellable optimizing flow `d*`. -/
def dStar (c : Fin 8) : Nat :=
  if c = (0 : Fin 8) then 2 else if c = (1 : Fin 8) then 1 else if c = (4 : Fin 8) then 1 else 0

/-- The other optimal throughput vector, `d*` with one extra `AAA` self-overlap. -/
def dStar3 (c : Fin 8) : Nat :=
  if c = (0 : Fin 8) then 3 else if c = (1 : Fin 8) then 1 else if c = (4 : Fin 8) then 1 else 0

theorem obs_0 : obs 0 = 2 := by
  unfold obs readStarts window5 cyc5 cls code rc bitA comp truth
  decide

theorem obs_1 : obs 1 = 1 := by
  unfold obs readStarts window5 cyc5 cls code rc bitA comp truth
  decide

theorem obs_4 : obs 4 = 1 := by
  unfold obs readStarts window5 cyc5 cls code rc bitA comp truth
  decide

theorem obs_off : ∀ c : Fin 8, c ∉ suppClasses → obs c = 0 := by
  unfold suppClasses obs readStarts window5 cyc5 cls code rc bitA comp truth
  decide

theorem dS_0 : dS 0 = 1 := by
  unfold dS spec5 window5 cyc5 cls code rc bitA comp truth
  decide

theorem dS_1 : dS 1 = 2 := by
  unfold dS spec5 window5 cyc5 cls code rc bitA comp truth
  decide

theorem dS_4 : dS 4 = 2 := by
  unfold dS spec5 window5 cyc5 cls code rc bitA comp truth
  decide

theorem dS_off : ∀ c : Fin 8, c ∉ suppClasses → dS c = 0 := by
  unfold suppClasses dS spec5 window5 cyc5 cls code rc bitA comp truth
  decide

theorem star_0 : dStar 0 = 2 := rfl

theorem star_1 : dStar 1 = 1 := rfl

theorem star_4 : dStar 4 = 1 := rfl

theorem star_off : ∀ c : Fin 8, c ∉ suppClasses → dStar c = 0 := by
  unfold suppClasses dStar
  decide

theorem star3_off : ∀ c : Fin 8, c ∉ suppClasses → dStar3 c = 0 := by
  unfold suppClasses dStar3
  decide

theorem star3_0 : dStar3 0 = 3 := rfl

theorem star3_1 : dStar3 1 = 1 := rfl

theorem star3_4 : dStar3 4 = 1 := rfl

/-! ## The source-faithful bridging hypothesis

The hypothesis side uses the *shared, authoritative*
`SourceFaithfulIs.InformationFeasible` predicate — the same object every other
AssemblyP1 counterexample module uses — rather than a module-local stand-in. -/

open SourceFaithfulIs

/-- The true circular genome `AAATT` in the shared source-faithful representation. -/
abbrev truthGenome : SourceFaithfulIs.Genome Base where
  len := 5
  len_pos := by norm_num
  sym := truth

/-- **The actual `I_s` hypothesis for this realization**: coverage, every triple
repeat all-bridged, and every interleaved pair of repeats bridged, quantified over
all repeat lengths and all selected starts, discharged by finite `decide`.  No
repeat is enumerated by hand. -/
theorem truth_information_feasible :
    SourceFaithfulIs.InformationFeasible truthGenome 3 realizedStarts := by
  decide

/-! ## The literal §6.1 product-of-binomial-marginals objective -/

/-- One §6.1 binomial marginal for molecule class `c`, with fixed external
`N = 5`, total reads `n = 4`, observed count `x c`, candidate count `d c`. -/
def marginal (x d : Fin 8 → Nat) (c : Fin 8) : ℚ :=
  (Nat.choose 4 (x c) : ℚ) * ((d c : ℚ) / 5) ^ (x c) *
    (1 - (d c : ℚ) / 5) ^ (4 - x c)

/-- The literal §6.1 product of binomial marginals over the molecule-class space
(zero-count factors retained). -/
def lik (x d : Fin 8 → Nat) : ℚ :=
  ∏ c : Fin 8, marginal x d c

/-- A class with zero observed count and zero candidate multiplicity contributes
the factor `1` to the literal product. -/
lemma marginal_eq_one_of_zero (x d : Fin 8 → Nat) (c : Fin 8)
    (hx : x c = 0) (hd : d c = 0) : marginal x d c = 1 := by
  simp [marginal, hx, hd]

lemma lik_eq_supp_prod (x d : Fin 8 → Nat)
    (h : ∀ c : Fin 8, c ∉ suppClasses → x c = 0 ∧ d c = 0) :
    lik x d = ∏ c ∈ suppClasses, marginal x d c := by
  unfold lik
  exact (Finset.prod_subset (s₁ := suppClasses) (s₂ := Finset.univ)
    (by intro c _; exact Finset.mem_univ c)
    (by intro c _ hc; exact marginal_eq_one_of_zero x d c (h c hc).1 (h c hc).2)).symm

/-- Expansion of a product over the three-element `suppClasses` set. -/
lemma supp_prod_eq (f : Fin 8 → ℚ) :
    ∏ c ∈ suppClasses, f c = f 0 * (f 1 * f 4) := by
  unfold suppClasses
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]

theorem lik_truth :
    lik obs dS = marginal obs dS 0 * (marginal obs dS 1 * marginal obs dS 4) := by
  rw [lik_eq_supp_prod obs dS (fun c hc => ⟨obs_off c hc, dS_off c hc⟩), supp_prod_eq]

theorem lik_star :
    lik obs dStar = marginal obs dStar 0 * (marginal obs dStar 1 * marginal obs dStar 4) := by
  rw [lik_eq_supp_prod obs dStar (fun c hc => ⟨obs_off c hc, star_off c hc⟩), supp_prod_eq]

theorem lik_truth_pos : 0 < lik obs dS := by
  rw [lik_truth]
  norm_num [marginal, obs_0, obs_1, obs_4, dS_0, dS_1, dS_4, Nat.choose]

/-- The non-spellable flow strictly beats the truth under the literal §6.1
objective: ratio `256/81`. -/
theorem lik_star_over_truth : lik obs dStar / lik obs dS = (256 : ℚ) / 81 := by
  rw [lik_truth, lik_star]
  norm_num [marginal, obs_0, obs_1, obs_4, dS_0, dS_1, dS_4, star_0, star_1, star_4,
    Nat.choose]

/-- The non-spellable flow strictly beats the bridged truth. -/
theorem star_better : lik obs dS < lik obs dStar := by
  have h := lik_star_over_truth
  have hpos := lik_truth_pos
  rw [div_eq_iff (ne_of_gt hpos)] at h
  rw [h]
  nlinarith

/-! ### Coordinatewise behaviour of the separable objective

The §6.1 objective is separable, so its maximizer over the domain `1 ≤ d ≤ N` is
the coordinatewise maximizer.  Each coordinate is checked on the finite range
`0, …, 5`, which is the whole §6.1 domain once `d ≤ N = 5` is imposed. -/

lemma marg_AAA_le (d : Fin 8 → Nat) (hd : d 0 ≤ 5) :
    marginal obs d 0 ≤ marginal obs dStar 0 := by
  rw [marginal, marginal, obs_0, star_0]
  interval_cases d 0 <;> norm_num [Nat.choose]

lemma marg_AAT_le (d : Fin 8 → Nat) (hd : d 1 ≤ 5) :
    marginal obs d 1 ≤ marginal obs dStar 1 := by
  rw [marginal, marginal, obs_1, star_1]
  interval_cases d 1 <;> norm_num [Nat.choose]

lemma marg_TAA_le (d : Fin 8 → Nat) (hd : d 4 ≤ 5) :
    marginal obs d 4 ≤ marginal obs dStar 4 := by
  rw [marginal, marginal, obs_4, star_4]
  interval_cases d 4 <;> norm_num [Nat.choose]

lemma marg_AAA_eq (d : Fin 8 → Nat) (hd : d 0 ≤ 5) :
    marginal obs d 0 = marginal obs dStar 0 → (d 0 = 2 ∨ d 0 = 3) := by
  rw [marginal, marginal, obs_0, star_0]
  interval_cases d 0 <;> norm_num [Nat.choose]

lemma marg_AAT_eq (d : Fin 8 → Nat) (hd : d 1 ≤ 5) :
    marginal obs d 1 = marginal obs dStar 1 → d 1 = 1 := by
  rw [marginal, marginal, obs_1, star_1]
  interval_cases d 1 <;> norm_num [Nat.choose]

lemma marg_TAA_eq (d : Fin 8 → Nat) (hd : d 4 ≤ 5) :
    marginal obs d 4 = marginal obs dStar 4 → d 4 = 1 := by
  rw [marginal, marginal, obs_4, star_4]
  interval_cases d 4 <;> norm_num [Nat.choose]

/-- Each §6.1 marginal is nonnegative on the domain `0 ≤ d ≤ 5`. -/
theorem marginal_nonneg (d : Fin 8 → Nat) (hd : ∀ c : Fin 8, d c ≤ 5) (c : Fin 8) :
    0 ≤ marginal obs d c := by
  have hb := hd c
  rw [marginal]
  have h2 : (0 : ℚ) ≤ 1 - (d c : ℚ) / 5 := by interval_cases d c <;> norm_num
  positivity

/-- Each `d*` marginal on the support is positive. -/
theorem marginal_pos_star (c : Fin 8) (hc : c ∈ suppClasses) :
    0 < marginal obs dStar c := by
  rw [suppClasses, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl
  · rw [marginal, obs_0, star_0]; norm_num [Nat.choose]
  · rw [marginal, obs_1, star_1]; norm_num [Nat.choose]
  · rw [marginal, obs_4, star_4]; norm_num [Nat.choose]

/-- **The flow optimum is the unconstrained maximizer of the separable §6.1
objective over the domain `1 ≤ d ≤ N`, restricted to throughput vectors that
vanish off the observed support (as every §6.2 flow's throughput vector does).
Every such vector is at most `L(obs, d*)`; the companion script checks the whole
`0 ≤ d ≤ 5` box and finds the same maximizer set.** -/
theorem lik_le_star (d : Fin 8 → Nat) (hd : ∀ c : Fin 8, d c ≤ 5)
    (hd0 : ∀ c : Fin 8, c ∉ suppClasses → d c = 0) :
    lik obs d ≤ lik obs dStar := by
  rw [lik_eq_supp_prod obs d (fun c hc => ⟨obs_off c hc, hd0 c hc⟩), lik_star, supp_prod_eq]
  have h0 := marg_AAA_le d (hd 0)
  have h1 := marg_AAT_le d (hd 1)
  have h4 := marg_TAA_le d (hd 4)
  have p0 := marginal_pos_star 0 (by decide)
  have p1 := marginal_pos_star 1 (by decide)
  have p4 := marginal_pos_star 4 (by decide)
  have n0 := marginal_nonneg d hd 0
  have n1 := marginal_nonneg d hd 1
  have n4 := marginal_nonneg d hd 4
  gcongr

/-- **The complete *integral* maximizer set inside the §6.1 domain `1 ≤ d ≤ N` is
exactly `{d*, d*₃}`: attaining the bound forces `d 1 = d 4 = 1` and `d 0 ∈ {2, 3}`.**

This is the argmax over the *original integer genomics/count domain* (level (i) of
the three-level distinction).  It does **not** extend to the half-integral biflow
relaxation of MB09 §5.1 (level (ii)) or to a continuously-extended likelihood on
relaxed flows (level (iii)); see `half_integral_strictly_better` below. -/
theorem star_argmax (d : Fin 8 → Nat) (hd : ∀ c : Fin 8, d c ≤ 5)
    (hd0 : ∀ c : Fin 8, c ∉ suppClasses → d c = 0) :
    lik obs d = lik obs dStar → (d 0 = 2 ∨ d 0 = 3) ∧ d 1 = 1 ∧ d 4 = 1 := by
  intro heq
  have hoff : ∀ c : Fin 8, c ∉ suppClasses → obs c = 0 ∧ d c = 0 :=
    fun c hc => ⟨obs_off c hc, hd0 c hc⟩
  rw [lik_eq_supp_prod obs d hoff, lik_star, supp_prod_eq] at heq
  have h0 := marg_AAA_le d (hd 0)
  have h1 := marg_AAT_le d (hd 1)
  have h4 := marg_TAA_le d (hd 4)
  have p0 := marginal_pos_star 0 (by decide)
  have p1 := marginal_pos_star 1 (by decide)
  have p4 := marginal_pos_star 4 (by decide)
  have n0 := marginal_nonneg d hd 0
  have n1 := marginal_nonneg d hd 1
  have n4 := marginal_nonneg d hd 4
  have hpos : 0 < marginal obs dStar 0 * (marginal obs dStar 1 * marginal obs dStar 4) :=
    mul_pos p0 (mul_pos p1 p4)
  -- either the tail product on the `d` side vanishes (impossible, since the two
  -- sides agree and the `d*` side is strictly positive) or it is strictly positive.
  by_cases hz : marginal obs d 1 * marginal obs d 4 = 0
  · exfalso
    rw [hz, mul_zero] at heq
    linarith [heq, hpos]
  have htail : 0 < marginal obs d 1 * marginal obs d 4 := by
    have hne : marginal obs d 1 * marginal obs d 4 ≠ 0 := hz
    exact lt_of_le_of_ne (mul_nonneg n1 n4) (fun h => hz (Eq.symm h))
  have hD4 : 0 < marginal obs d 4 := by
    by_contra hcon
    have h0' : marginal obs d 4 = 0 := le_antisymm (not_lt.mp hcon) n4
    have hzeros : marginal obs d 1 * marginal obs d 4 = 0 := by rw [h0', mul_zero]
    exact hz hzeros
  have htail_le : marginal obs d 1 * marginal obs d 4
      ≤ marginal obs dStar 1 * marginal obs dStar 4 := by gcongr
  refine ⟨?_, ?_, ?_⟩
  · rcases le_iff_eq_or_lt.mp h0 with h | h
    · exact marg_AAA_eq d (hd 0) h
    · exfalso
      have hprod : marginal obs d 0 * (marginal obs d 1 * marginal obs d 4)
          < marginal obs dStar 0 * (marginal obs dStar 1 * marginal obs dStar 4) := by
        calc marginal obs d 0 * (marginal obs d 1 * marginal obs d 4)
            < marginal obs dStar 0 * (marginal obs d 1 * marginal obs d 4) :=
                mul_lt_mul_of_pos_right h htail
          _ ≤ marginal obs dStar 0 * (marginal obs dStar 1 * marginal obs dStar 4) :=
                mul_le_mul_of_nonneg_left htail_le (le_of_lt p0)
      linarith [heq, hprod]
  · rcases le_iff_eq_or_lt.mp h1 with h | h
    · exact marg_AAT_eq d (hd 1) h
    · exfalso
      have hst : marginal obs d 1 * marginal obs d 4
          < marginal obs dStar 1 * marginal obs dStar 4 :=
        lt_of_lt_of_le (mul_lt_mul_of_pos_right h hD4)
          (mul_le_mul_of_nonneg_left h4 (le_of_lt p1))
      have hprod : marginal obs d 0 * (marginal obs d 1 * marginal obs d 4)
          < marginal obs dStar 0 * (marginal obs dStar 1 * marginal obs dStar 4) := by
        calc marginal obs d 0 * (marginal obs d 1 * marginal obs d 4)
            ≤ marginal obs dStar 0 * (marginal obs d 1 * marginal obs d 4) :=
                mul_le_mul_of_nonneg_right h0 (mul_nonneg n1 n4)
          _ < marginal obs dStar 0 * (marginal obs dStar 1 * marginal obs dStar 4) :=
                mul_lt_mul_of_pos_left hst p0
      linarith [heq, hprod]
  · rcases le_iff_eq_or_lt.mp h4 with h | h
    · exact marg_TAA_eq d (hd 4) h
    · exfalso
      have hst : marginal obs d 1 * marginal obs d 4
          < marginal obs dStar 1 * marginal obs dStar 4 :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_right h1 n4)
          (mul_lt_mul_of_pos_left h p1)
      have hprod : marginal obs d 0 * (marginal obs d 1 * marginal obs d 4)
          < marginal obs dStar 0 * (marginal obs dStar 1 * marginal obs dStar 4) := by
        calc marginal obs d 0 * (marginal obs d 1 * marginal obs d 4)
            ≤ marginal obs dStar 0 * (marginal obs d 1 * marginal obs d 4) :=
                mul_le_mul_of_nonneg_right h0 (mul_nonneg n1 n4)
          _ < marginal obs dStar 0 * (marginal obs dStar 1 * marginal obs dStar 4) :=
                mul_lt_mul_of_pos_left hst p0
      linarith [heq, hprod]

/-- **Half-integral relaxation boundary.** The §6.1 AAA marginal at the
half-integral point `d = 5/2` is strictly greater than at the integral maximizers
`d = 2` and `d = 3`: the ratio is `625/576 > 1`.  This shows that `star_argmax`
above is an *integral* argmax only; the half-integral biflow relaxation of
MB09 §5.1 (level (ii)) or a continuously-extended likelihood (level (iii)) has a
strictly higher value.  The three levels — (i) original integer genomics/count
domain, (ii) algorithmic half-integral biflow approximation, (iii) optional
continuously-extended likelihood on relaxed flows — must not be conflated. -/
theorem half_integral_strictly_better :
    marginal obs dStar 0 < (6 : ℚ) * ((5 : ℚ) / 2 / 5) ^ 2 * (1 - (5 : ℚ) / 2 / 5) ^ 2 := by
  rw [marginal, obs_0, star_0]
  norm_num [Nat.choose]

/-- The exact ratio of the half-integral AAA marginal to the integral one. -/
theorem half_integral_ratio :
    (6 : ℚ) * ((5 : ℚ) / 2 / 5) ^ 2 * (1 - (5 : ℚ) / 2 / 5) ^ 2 / marginal obs dStar 0
      = (625 : ℚ) / 576 := by
  rw [marginal, obs_0, star_0]
  norm_num [Nat.choose]

/-! ## The literal §6.2 bidirected overlap graph and flow layer

Everything below replaces the molecule-spectrum level by the actual §6.2 object:
the explicit bidirected read-overlap graph on the observed read *molecules*, its
transitive edge reduction, the vertex and edge lower bounds, the §3.4
signed-incidence balance (checked both at molecule-class level, as the shared
`Feasible62` predicate states it, and at strand/port level) and the
supersource/supersink clause. -/

open AssemblyP1.Section62Flow

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

/-- The molecule-class representative of a strand (MB09 §4.1). -/
def rep3 (w : Strand3) : Strand3 := if code3 w ≤ code3 (rc3 w) then w else rc3 w

/-- The molecule-class code of a strand: the `Fin 8` label of its
reverse-complement pair. -/
def repCode (w : Strand3) : Fin 8 :=
  if h : min (code3 w) (code3 (rc3 w)) < 8 then ⟨min (code3 w) (code3 (rc3 w)), h⟩ else 0

/-- The bidirected overlap edge of overlap length `l` between two strands. -/
def ov (l : Nat) (x y : Strand3) : BdEdge Base Strand3 := bdEdge rep3 x y l

/-- The three observed read DNA molecules, the vertices of the §6.2 graph. -/
def readVerts : List Strand3 :=
  [m3 .A .A .A, m3 .A .A .T, m3 .T .A .A]

/-- The read length `L = 3`. -/
def readLen : Nat := 3

/-- The §6.2 overlap threshold of this instance, `o_min = 1`. -/
def oMin : Nat := 1

/-- The explicit bidirected overlap graph of MB09 §6.2 on the observed read
molecules at `o_min = 1`: all proper overlaps of length `1` and `2`. -/
def graph1 : List (BdEdge Base Strand3) :=
  overlapEdges Base Strand3 toList3 rep3 rc3 readLen oMin readVerts

theorem graph1_length : graph1.length = 28 := by decide

/-- The transitively reduced graph (Myers 2005 reading) of `graph1`: the twelve
edges that survive.  The six removed edges are the length-`1` overlaps that are
spelled by two longer (length-`2`) proper overlaps. -/
def reducedList : List (BdEdge Base Strand3) :=
  [ ov 1 (m3 .A .A .T) (m3 .T .A .A),
    ov 1 (m3 .T .T .A) (m3 .A .T .T),
    ov 2 (m3 .A .A .A) (m3 .A .A .A),
    ov 2 (m3 .A .A .A) (m3 .A .A .T),
    ov 2 (m3 .A .A .T) (m3 .A .T .T),
    ov 2 (m3 .T .A .A) (m3 .A .A .A),
    ov 2 (m3 .T .A .A) (m3 .A .A .T),
    ov 2 (m3 .T .T .T) (m3 .T .T .T),
    ov 2 (m3 .T .T .T) (m3 .T .T .A),
    ov 2 (m3 .A .T .T) (m3 .T .T .T),
    ov 2 (m3 .A .T .T) (m3 .T .T .A),
    ov 2 (m3 .T .T .A) (m3 .T .A .A) ]

/-- `reducedList` is exactly the Myers transitive edge reduction of `graph1`. -/
theorem reducedList_eq :
    transitivelyReducedLonger Base Strand3 toList3 rc3 readLen readVerts graph1
      = reducedList := by
  decide

/-- Under the literal MB09 §6.2 reading, "remove any overlap that is spelled by
two shorter overlaps", the reduction is vacuous at `L = 3`: no proper overlap of
length `l` is spelled by two strictly shorter ones, because the composition law
`l = l₁ + l₂ − L` with `l₁, l₂ < l` forces `L + 2 ≤ l ≤ L − 1`.  So the graph is
the full `graph1` under that reading. -/
theorem graph_reduction_vacuous_literal :
    transitivelyReduced Base Strand3 toList3 rc3 readLen readVerts graph1 = graph1 := by
  decide

/-- Every reduced edge is a genuine overlap edge of the §6.2 graph. -/
theorem reducedList_subset : ∀ e ∈ reducedList, e ∈ graph1 := by
  decide

/-! ### Port (strand-level) balance

MB09 §3.3 gives every molecule two strands; an overlap edge departs from one
strand and arrives at one strand.  The §3.4 balance read at that level asks for
the departing and arriving flow to agree at every strand.  This is *stronger*
than the class-level signed-incidence balance of `Feasible62` (which is the sum
of the two port balances with one sign flipped); the certificates below check
both, so the witnesses are feasible under either reading of §3.4. -/

/-- Flow on the edges that depart from the strand `s`. -/
def portOut (f : BdFlow Base Strand3) (edges : List (BdEdge Base Strand3))
    (s : Strand3) : ℕ :=
  edges.foldr (fun e acc => if e.sx = s then f e + acc else acc) 0

/-- Flow on the edges that arrive at the strand `s`. -/
def portIn (f : BdFlow Base Strand3) (edges : List (BdEdge Base Strand3))
    (s : Strand3) : ℕ :=
  edges.foldr (fun e acc => if e.sy = s then f e + acc else acc) 0

/-- MB09 §3.4 balance at strand (port) level: the departing and arriving flow
agree at every strand of every observed molecule. -/
def PortBalanced (f : BdFlow Base Strand3) (edges : List (BdEdge Base Strand3))
    (verts : List Strand3) : Bool :=
  (strandsOf rc3 verts).all
    (fun s => decide (portOut f edges s = portIn f edges s))

/-- A numeric key identifying an overlap edge by its overlap length and the
binary codes of its two strands.  The length is part of the key because at
`o_min = 1` two edges may join the same pair of strands with different overlap
lengths (`AAA.p → AAT.p` has both a length-`1` and a length-`2` overlap). -/
def ekey (e : BdEdge Base Strand3) : Nat :=
  64 * e.len + 8 * code3 e.sx + code3 e.sy

/-- The key of the edge of overlap length `l` between the strands `x` and `y`. -/
def keyOf (l : Nat) (x y : Strand3) : Nat :=
  64 * l + 8 * code3 x + code3 y

/-- No supersource and no supersink is used: all candidates below are circuits. -/
def noTerm : SuperTerminals Strand3 := noTerminals Strand3

/-- The truth-induced flow: the cyclic window walk of `AAATT`, which visits the
strand sequence `AAA, AAT, ATT, TTA, TAA`. -/
def truthFlow : BdFlow Base Strand3 := fun e =>
  if ekey e = keyOf 2 (m3 .A .A .A) (m3 .A .A .T) then 1 else
  if ekey e = keyOf 2 (m3 .A .A .T) (m3 .A .T .T) then 1 else
  if ekey e = keyOf 2 (m3 .A .T .T) (m3 .T .T .A) then 1 else
  if ekey e = keyOf 2 (m3 .T .T .A) (m3 .T .A .A) then 1 else
  if ekey e = keyOf 2 (m3 .T .A .A) (m3 .A .A .A) then 1 else
  0

/-- The non-spellable flow `d* = (AAA:2, AAT:1, TAA:1)`: a single bidirected
circuit through `AAA.p → AAA.p`, `AAA.p → AAT.p`, `AAT.p → TAA.p` (overlap
length `1`) and `TAA.p → AAA.p`. -/
def starFlow21 : BdFlow Base Strand3 := fun e =>
  if ekey e = keyOf 2 (m3 .A .A .A) (m3 .A .A .A) then 1 else
  if ekey e = keyOf 2 (m3 .A .A .A) (m3 .A .A .T) then 1 else
  if ekey e = keyOf 1 (m3 .A .A .T) (m3 .T .A .A) then 1 else
  if ekey e = keyOf 2 (m3 .T .A .A) (m3 .A .A .A) then 1 else
  0

/-- The non-spellable flow `d*₃ = (AAA:3, AAT:1, TAA:1)`: the circuit above plus
one extra traversal of the `AAA.p → AAA.p` self-overlap. -/
def starFlow31 : BdFlow Base Strand3 := fun e =>
  if ekey e = keyOf 2 (m3 .A .A .A) (m3 .A .A .A) then 2 else
  if ekey e = keyOf 2 (m3 .A .A .A) (m3 .A .A .T) then 1 else
  if ekey e = keyOf 1 (m3 .A .A .T) (m3 .T .A .A) then 1 else
  if ekey e = keyOf 2 (m3 .T .A .A) (m3 .A .A .A) then 1 else
  0

/-- The truth spectrum, relabelled by molecule class. -/
def dS' (w : Strand3) : Nat := dS (repCode w)

/-- The throughput vector of `starFlow21`, relabelled by molecule class. -/
def dStar' (w : Strand3) : Nat := dStar (repCode w)

/-- The throughput vector of `starFlow31`, relabelled by molecule class. -/
def dStar3' (w : Strand3) : Nat := dStar3 (repCode w)

/-! ### §6.2 feasibility, clause by clause -/

theorem truth_edge_lower_bounds :
    ∀ e ∈ graph1, (0 : ℕ) ≤ truthFlow e := by decide

theorem truth_vertex_lower_bounds :
    ∀ v ∈ readVerts, (1 : ℕ) ≤ throughput Base Strand3 rep3 truthFlow graph1 v := by
  decide

theorem truth_balance_zero :
    ∀ v ∈ readVerts,
      balance Base Strand3 rep3 truthFlow noTerm graph1 v = 0 := by
  decide

theorem truth_throughput_is_spectrum :
    ∀ v ∈ readVerts,
      throughput Base Strand3 rep3 truthFlow graph1 v = dS' v := by
  decide

/-- The truth `AAATT` is a §6.2 admissible flow on the full `o_min = 1` graph. -/
theorem truth_feasible62 :
    Feasible62 Base Strand3 rep3 readVerts graph1 truthFlow noTerm dS' :=
  ⟨⟨truth_edge_lower_bounds, truth_vertex_lower_bounds, truth_balance_zero,
    truth_throughput_is_spectrum⟩, fun _ => ⟨rfl, rfl⟩⟩

theorem star21_edge_lower_bounds :
    ∀ e ∈ graph1, (0 : ℕ) ≤ starFlow21 e := by decide

theorem star21_vertex_lower_bounds :
    ∀ v ∈ readVerts, (1 : ℕ) ≤ throughput Base Strand3 rep3 starFlow21 graph1 v := by
  decide

theorem star21_balance_zero :
    ∀ v ∈ readVerts,
      balance Base Strand3 rep3 starFlow21 noTerm graph1 v = 0 := by
  decide

theorem star21_throughput_is_spectrum :
    ∀ v ∈ readVerts,
      throughput Base Strand3 rep3 starFlow21 graph1 v = dStar' v := by
  decide

/-- **The non-spellable flow `d*` is a §6.2 admissible flow** on the full
`o_min = 1` graph (and, by `star21_feasible62_reduced`, on its Myers reduction). -/
theorem star21_feasible62 :
    Feasible62 Base Strand3 rep3 readVerts graph1 starFlow21 noTerm dStar' :=
  ⟨⟨star21_edge_lower_bounds, star21_vertex_lower_bounds, star21_balance_zero,
    star21_throughput_is_spectrum⟩, fun _ => ⟨rfl, rfl⟩⟩

theorem star21_reduced_lower_bounds :
    ∀ e ∈ reducedList, (0 : ℕ) ≤ starFlow21 e := by decide

theorem star21_reduced_vertex_lb :
    ∀ v ∈ readVerts,
      (1 : ℕ) ≤ throughput Base Strand3 rep3 starFlow21 reducedList v := by
  decide

theorem star21_reduced_balance :
    ∀ v ∈ readVerts,
      balance Base Strand3 rep3 starFlow21 noTerm reducedList v = 0 := by
  decide

theorem star21_reduced_throughput :
    ∀ v ∈ readVerts,
      throughput Base Strand3 rep3 starFlow21 reducedList v = dStar' v := by
  decide

/-- `d*` is also admissible on the Myers reduction, the smallest graph either
reading produces. -/
theorem star21_feasible62_reduced :
    Feasible62 Base Strand3 rep3 readVerts reducedList starFlow21 noTerm dStar' :=
  ⟨⟨star21_reduced_lower_bounds, star21_reduced_vertex_lb, star21_reduced_balance,
    star21_reduced_throughput⟩, fun _ => ⟨rfl, rfl⟩⟩

theorem star31_edge_lower_bounds :
    ∀ e ∈ graph1, (0 : ℕ) ≤ starFlow31 e := by decide

theorem star31_vertex_lower_bounds :
    ∀ v ∈ readVerts, (1 : ℕ) ≤ throughput Base Strand3 rep3 starFlow31 graph1 v := by
  decide

theorem star31_balance_zero :
    ∀ v ∈ readVerts,
      balance Base Strand3 rep3 starFlow31 noTerm graph1 v = 0 := by
  decide

theorem star31_throughput_is_spectrum :
    ∀ v ∈ readVerts,
      throughput Base Strand3 rep3 starFlow31 graph1 v = dStar3' v := by
  decide

/-- The other optimal flow `d*₃` is admissible too. -/
theorem star31_feasible62 :
    Feasible62 Base Strand3 rep3 readVerts graph1 starFlow31 noTerm dStar3' :=
  ⟨⟨star31_edge_lower_bounds, star31_vertex_lower_bounds, star31_balance_zero,
    star31_throughput_is_spectrum⟩, fun _ => ⟨rfl, rfl⟩⟩

/-- The flows are balanced at strand (port) level as well, so they are feasible
under the stricter reading of MB09 §3.4 too. -/
theorem star21_port_balanced : PortBalanced starFlow21 graph1 readVerts = true := by
  decide

theorem star31_port_balanced : PortBalanced starFlow31 graph1 readVerts = true := by
  decide

theorem truth_port_balanced : PortBalanced truthFlow graph1 readVerts = true := by
  decide

/-- The strand window of `AAATT` at position `i`. -/
def wall3 (i : Fin 5) : Strand3 :=
  [cyc5 truth i.val, cyc5 truth (i.val + 1), cyc5 truth (i.val + 2)]

/-- Every step of the truth's window walk is an overlap of length `L − 1 = 2` and
is an edge of the `o_min = 1` graph — which is what a spelled molecule does; the
non-spellable flows do not (`star21_uses_short_overlap`). -/
theorem truth_steps_are_maximal :
    ∀ i : Fin 5,
      (ov 2 (wall3 i) (wall3 ⟨(i.val + 1) % 5, Nat.mod_lt _ (by norm_num)⟩)).len = 2 ∧
        (ov 2 (wall3 i) (wall3 ⟨(i.val + 1) % 5, Nat.mod_lt _ (by norm_num)⟩)) ∈ graph1 := by
  decide

/-- The `d*` circuit carries positive flow on an overlap of length `1 < L − 1`,
which no window walk of a circular molecule can use. -/
theorem star21_uses_short_overlap :
    ∃ e, e ∈ graph1 ∧ e.len = 1 ∧ 0 < starFlow21 e := by
  refine ⟨ov 1 (m3 .A .A .T) (m3 .T .A .A), ?_, rfl, by decide⟩
  decide

/-! ## No circular molecule has the throughputs `d*`

The key fact is that a spectrum's total mass is the molecule's length: each window
position contributes to exactly one molecule class.  A molecule with the
throughputs `d*` therefore has length `4`, and the `2⁴` molecules of length `4`
are exhaustively checked.  This is a complete proof, not a bounded search. -/

/-- Cyclic successor on a nonempty circle. -/
def nxtG {G : ℕ} (hG : 0 < G) (r : Fin G) : Fin G :=
  ⟨(r.val + 1) % G, Nat.mod_lt (r.val + 1) hG⟩

/-- Number of window positions of the circular molecule `u` whose molecule class
is `c`. -/
def spectrumOf {G : ℕ} (hG : 0 < G) (u : Fin G → Base) (c : Fin 8) : Nat :=
  (Finset.univ.filter
    (fun r : Fin G => cls ![u r, u (nxtG hG r), u (nxtG hG (nxtG hG r))] = c)).card

/-- Each window position contributes to exactly one molecule class, so the total
spectrum mass is the length of the molecule. -/
theorem sum_spectrum {G : ℕ} (hG : 0 < G) (u : Fin G → Base) :
    ∑ c : Fin 8, spectrumOf hG u c = G := by
  have h2 : ∑ c : Fin 8, spectrumOf hG u c = ∑ c : Fin 8, ∑ r : Fin G,
      (if cls ![u r, u (nxtG hG r), u (nxtG hG (nxtG hG r))] = c then (1 : ℕ) else 0) := by
    apply Finset.sum_congr rfl
    intro c _
    exact (Finset.sum_boole (s := (Finset.univ : Finset (Fin G)))
      (p := fun r : Fin G => cls ![u r, u (nxtG hG r), u (nxtG hG (nxtG hG r))] = c)).symm
  have h1 : ∀ r : Fin G, ∑ c : Fin 8,
      (if cls ![u r, u (nxtG hG r), u (nxtG hG (nxtG hG r))] = c then (1 : ℕ) else 0) = 1 := by
    intro r
    have hf : ((Finset.univ : Finset (Fin 8)).filter
        (fun c => cls ![u r, u (nxtG hG r), u (nxtG hG (nxtG hG r))] = c))
        = {cls ![u r, u (nxtG hG r), u (nxtG hG (nxtG hG r))]} := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact eq_comm
    have hs : (∑ c : Fin 8, (if cls ![u r, u (nxtG hG r), u (nxtG hG (nxtG hG r))] = c
        then (1 : ℕ) else 0))
        = ((Finset.univ : Finset (Fin 8)).filter
            (fun c => cls ![u r, u (nxtG hG r), u (nxtG hG (nxtG hG r))] = c)).card := by
      rw [Finset.sum_boole]
      rfl
    rw [hs, hf, Finset.card_singleton]
  rw [h2, Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun r _ => h1 r)]
  simp

theorem sum_dStar : ∑ c : Fin 8, dStar c = 4 := by decide

/-- **No circular molecule of any length has the throughputs `d*`.** -/
theorem no_sequence_has_star_spectrum (G : ℕ) (hG : 0 < G) (u : Fin G → Base) :
    ¬ (∀ c : Fin 8, spectrumOf hG u c = dStar c) := by
  intro h
  have hG4 : G = 4 := by
    have hs := sum_spectrum hG u
    have : ∑ c : Fin 8, spectrumOf hG u c = ∑ c : Fin 8, dStar c :=
      Finset.sum_congr rfl (fun c _ => h c)
    have := sum_dStar
    omega
  subst hG4
  have exhaustive : ∀ v : Fin 4 → Base,
      ¬ (∀ c : Fin 8, spectrumOf (by norm_num) v c = dStar c) := by
    decide
  exact exhaustive u h

/-! ## A spelled candidate is a general feasible flow -/

/-- **The spelled sub-case is contained in the general flow feasible set.** A
§6.2 spelled candidate certifies, in its last conjunct, a `Feasible62` instance on
the *general* §6.2 feasibility predicate — the one that also admits flows that
spell no genome.  So the already kernel-checked spelled witnesses of
`AssemblyP1/Section62BridgingCounterexample.lean` and
`AssemblyP1/SameLengthSection62Counterexample.lean` are, without any change,
counterexamples to dominance over the *whole* §6.2 flow domain: the competing
candidate is an admissible flow, so the truth is not a maximizer there. -/
theorem spelled_subset_general {A : Type} {W : Type} [DecidableEq A] [DecidableEq W]
    {n : Nat} (toList : W → List A) (rep rc : W → W) (readLen oMin : Nat)
    (verts : List W) (sp : Spelling A W n) (f : BdFlow A W)
    (t : SuperTerminals W) (d : W → ℕ) :
    SpelledFeasible62 A W toList rep rc readLen oMin verts sp f t d →
      Feasible62 A W rep verts (overlapEdges A W toList rep rc readLen oMin verts) f t d :=
  fun h => h.2.2.2.2

/-! ## The spelled witnesses are feasible in the general flow optimizer

Claim (A) of issue #214, packaged as single kernel-checked objects: each
already-accepted spelled witness is, without any change, a counterexample to
dominance over the *whole* §6.2 flow feasible set.  Both witness modules state
feasibility through `SpelledFeasible62`, whose last conjunct is a `Feasible62`
instance over the *general* predicate — the same predicate under which the
non-spellable `starFlow21`/`starFlow31` are certified above, and the projection
recorded by `spelled_subset_general`.  Their strict likelihood inequalities
therefore already refute "the truth-induced flow maximizes the §6.1 objective
over the §6.2 feasible set"; no additional witness is needed for that
refutation.  All module-local names are fully qualified because the two witness
modules define `readVerts`, `graphList`, `dS'`, `dD'` of their own. -/

/-- The `AAATT → AAAATT` witness (`o_min = 2`, ratio `9/8`): the truth and the
competitor are both admissible flows for the *general* §6.2 feasibility
predicate, and the competitor strictly beats the truth. -/
theorem bridging_spelled_witnesses_general :
    Feasible62 AssemblyP1.Section62BridgingCounterexample.Base
        AssemblyP1.Section62BridgingCounterexample.Strand3
        AssemblyP1.Section62BridgingCounterexample.rep3
        AssemblyP1.Section62BridgingCounterexample.readVerts
        AssemblyP1.Section62BridgingCounterexample.graphList
        AssemblyP1.Section62BridgingCounterexample.truthCircuitFlow
        AssemblyP1.Section62BridgingCounterexample.noTerm
        AssemblyP1.Section62BridgingCounterexample.dS' ∧
      Feasible62 AssemblyP1.Section62BridgingCounterexample.Base
        AssemblyP1.Section62BridgingCounterexample.Strand3
        AssemblyP1.Section62BridgingCounterexample.rep3
        AssemblyP1.Section62BridgingCounterexample.readVerts
        AssemblyP1.Section62BridgingCounterexample.graphList
        AssemblyP1.Section62BridgingCounterexample.competitorCircuitFlow
        AssemblyP1.Section62BridgingCounterexample.noTerm
        AssemblyP1.Section62BridgingCounterexample.dD' ∧
      AssemblyP1.Section62BridgingCounterexample.lik
        AssemblyP1.Section62BridgingCounterexample.obs
        AssemblyP1.Section62BridgingCounterexample.dS
        < AssemblyP1.Section62BridgingCounterexample.lik
          AssemblyP1.Section62BridgingCounterexample.obs
          AssemblyP1.Section62BridgingCounterexample.dD :=
  ⟨AssemblyP1.Section62BridgingCounterexample.truth_feasible62,
    AssemblyP1.Section62BridgingCounterexample.competitor_feasible62,
    AssemblyP1.Section62BridgingCounterexample.competitor_strictly_better⟩

/-- The same-length `AAATAT → AAAAAT` witness (`o_min = 2`, ratio `5`): same
packaging. -/
theorem samelength_spelled_witnesses_general :
    Feasible62 AssemblyP1.SameLengthSection62Counterexample.Base
        AssemblyP1.SameLengthSection62Counterexample.Strand3
        AssemblyP1.SameLengthSection62Counterexample.rep3
        AssemblyP1.SameLengthSection62Counterexample.readVerts
        AssemblyP1.SameLengthSection62Counterexample.graphList
        AssemblyP1.SameLengthSection62Counterexample.truthCircuitFlow
        AssemblyP1.SameLengthSection62Counterexample.noTerm
        AssemblyP1.SameLengthSection62Counterexample.dS' ∧
      Feasible62 AssemblyP1.SameLengthSection62Counterexample.Base
        AssemblyP1.SameLengthSection62Counterexample.Strand3
        AssemblyP1.SameLengthSection62Counterexample.rep3
        AssemblyP1.SameLengthSection62Counterexample.readVerts
        AssemblyP1.SameLengthSection62Counterexample.graphList
        AssemblyP1.SameLengthSection62Counterexample.competitorCircuitFlow
        AssemblyP1.SameLengthSection62Counterexample.noTerm
        AssemblyP1.SameLengthSection62Counterexample.dD' ∧
      AssemblyP1.SameLengthSection62Counterexample.lik
        AssemblyP1.SameLengthSection62Counterexample.obs
        AssemblyP1.SameLengthSection62Counterexample.dS
        < AssemblyP1.SameLengthSection62Counterexample.lik
          AssemblyP1.SameLengthSection62Counterexample.obs
          AssemblyP1.SameLengthSection62Counterexample.dD :=
  ⟨AssemblyP1.SameLengthSection62Counterexample.truth_feasible62,
    AssemblyP1.SameLengthSection62Counterexample.competitor_feasible62,
    AssemblyP1.SameLengthSection62Counterexample.competitor_strictly_better⟩

/-! ## Main theorem -/

/-- The other optimal flow attains the same optimum, so the complete maximizer set
of the §6.1 objective over the §6.2 feasible flows is `{d*, d*₃}`. -/
theorem lik_star3_eq_star : lik obs dStar3 = lik obs dStar := by
  rw [lik_eq_supp_prod obs dStar3 (fun c hc => ⟨obs_off c hc, star3_off c hc⟩),
    lik_eq_supp_prod obs dStar (fun c hc => ⟨obs_off c hc, star_off c hc⟩), supp_prod_eq,
    supp_prod_eq]
  norm_num [marginal, obs_0, obs_1, obs_4, dS_0, dS_1, dS_4, star_0, star_1, star_4,
    star3_0, star3_1, star3_4, Nat.choose]

/-- **The general (non-spelled) §6.2 flow domain, stated as one finite
certificate.** Under the literal Medvedev–Brudno §6.2 object:

1. the bridging hypothesis `I_s` holds at full strength for the truth `AAATT`
   with the realized placements `{0, 1, 4}` (start `0` sampled twice, so the
   `n = 4` reads have multiplicities `x = (AAA:2, AAT:1, TAA:1)`);
2. the truth is an admissible §6.2 flow with the throughputs `d_S`;
3. two other admissible §6.2 flows have throughputs `d*` and `d*₃`, which are
   *not* the spectrum of any circular molecule of any length;
4. both strictly beat the truth under the literal §6.1 objective
   (ratio `256/81`), they attain that objective's maximum over its whole domain
   `1 ≤ d ≤ N`, and they are the complete maximizer set inside it;
5. so the §6.2 feasible set contains no "maximum-likelihood sequence" at all for
   this instance — the maximizer is a flow that spells no genome.

The sequence-side comparison of the companion note §4 — every spelled candidate
is strictly worse than the flow optimum — is a bounded certificate checked by
`scripts/verify_se62_nonspelled_flow_domain.py`, not a kernel-checked theorem.

This is the countermodel for issue #214's question: a flow optimum over the
literal §6.2 feasible set cannot be called an ML *sequence* without an additional
flow-to-sequence rule, and the source supplies none. -/
theorem nonspelled_se62_flow_domain_countermodel :
    SourceFaithfulIs.InformationFeasible truthGenome 3 realizedStarts ∧
      Feasible62 Base Strand3 rep3 readVerts graph1 truthFlow noTerm dS' ∧
      (Feasible62 Base Strand3 rep3 readVerts graph1 starFlow21 noTerm dStar' ∧
        Feasible62 Base Strand3 rep3 readVerts graph1 starFlow31 noTerm dStar3') ∧
      (lik obs dS < lik obs dStar ∧ lik obs dStar3 = lik obs dStar) ∧
      (∀ (G : ℕ) (hG : 0 < G) (u : Fin G → Base),
        ¬ (∀ c : Fin 8, spectrumOf hG u c = dStar c)) ∧
      (∀ d : Fin 8 → Nat, (∀ c : Fin 8, d c ≤ 5) →
        (∀ c : Fin 8, c ∉ suppClasses → d c = 0) → lik obs d ≤ lik obs dStar) ∧
      (∀ d : Fin 8 → Nat, (∀ c : Fin 8, d c ≤ 5) →
        (∀ c : Fin 8, c ∉ suppClasses → d c = 0) →
        lik obs d = lik obs dStar → (d 0 = 2 ∨ d 0 = 3) ∧ d 1 = 1 ∧ d 4 = 1) :=
  ⟨truth_information_feasible, truth_feasible62, ⟨star21_feasible62, star31_feasible62⟩,
    ⟨star_better, lik_star3_eq_star⟩, no_sequence_has_star_spectrum, lik_le_star,
    star_argmax⟩

end AssemblyP1.Section62NonSpelledFlow
