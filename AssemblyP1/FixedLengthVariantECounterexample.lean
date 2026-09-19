import Mathlib

namespace AssemblyP1.FixedLengthVariantECounterexample

inductive DNA where
  | A | C | G | T
  deriving DecidableEq, BEq, Repr, Inhabited

abbrev Genome := List DNA

private def base (g : Genome) (i : Nat) : DNA :=
  g[i % g.length]!

private def dinucleotideCount (g : Genome) (x y : DNA) : Nat :=
  (List.range g.length).countP fun i => base g i == x && base g (i + 1) == y

/--
Fixed-length exact multinomial likelihood for the observed multiset
`{AA:5, CA:1, GG:1}`.

All candidates have the same length G as the truth. For fixed-length
comparison the multinomial coefficient and G^{-N} factor cancel, so the
ordering objective is `∏_i d(i)^{x_i}`. We use the full formula for
clarity.
 -/
def sampleLikelihood (g : Genome) : ℚ :=
  let N := (7 : ℚ)
  let G := (g.length : ℚ)
  let coeff := (7 * 6 * 5 * 4 * 3 * 2 * 1 : ℚ) /
    ((5 * 4 * 3 * 2 * 1 : ℚ) * (1 : ℚ) * (1 : ℚ))
  coeff *
    ((dinucleotideCount g .A .A : ℚ) / G) ^ 5 *
    ((dinucleotideCount g .C .A : ℚ) / G) ^ 1 *
    ((dinucleotideCount g .G .G : ℚ) / G) ^ 1

/--
Simplified ordering objective: `∏_i d(i)^{x_i}`. This equals the full
likelihood up to the observation-only multinomial coefficient and G^{-N},
both of which are constant across fixed-length candidates.
-/
def orderingObjective (g : Genome) : ℚ :=
  ((dinucleotideCount g .A .A : ℚ)) ^ 5 *
    ((dinucleotideCount g .C .A : ℚ)) ^ 1 *
    ((dinucleotideCount g .G .G : ℚ)) ^ 1

/--
The true circular genome in the fixed-length counterexample.
Repeat-free for length-2 windows: all 6 dinucleotides are distinct.
 -/
def truth : Genome := [.A, .A, .C, .A, .G, .G]

/--
A competing circular genome of the same length.
De Bruijn-balanced: A→A(2), A→G(1), G→G(1), G→C(1), C→A(1).
 -/
def competitor : Genome := [.A, .A, .A, .G, .G, .C]

/-! ## Repeat-freeness of the truth -/

/-- All 6 length-2 circular windows of AACAGG are distinct. -/
private def allWindowsDistinct : Prop :=
  let windows := List.range 6 |>.map fun i => (base truth i, base truth (i + 1))
  windows.Nodup

theorem truth_repeat_free : allWindowsDistinct := by
  native_decide

/-! ## Coverage -/

/--
Latent start positions in the true genome. Reads at these starts with
length 2 cover all 6 positions.
-/
private def starts : List Nat := [0, 1, 2, 3, 4, 5]

/--
Every true position is covered by at least one realized length-two read.
 -/
private def covered : Prop :=
  (List.range truth.length).all (fun i =>
      starts.any (fun s =>
        (List.range 2).any (fun d => i == (s + d) % truth.length))) = true

theorem truth_covered : covered := by
  native_decide

/-! ## Bridging (vacuous for repeat-free genomes) -/

/--
For AACAGG, distinct circular starts disagree in their first symbol at
many positions; more importantly, no length-2 substring repeats, so
the source triple-repeat and interleaved-repeat bridging obligations are
vacuously satisfied.
 -/
private def noRepeatAtLength2 : Prop :=
  let mers := List.range 6 |>.map fun i => (base truth i, base truth (i + 1))
  mers.Nodup

theorem truth_no_repeat : noRepeatAtLength2 := by
  native_decide

/-! ## Competitor validity -/

/-- AAAGGC has de Bruijn balance: out(A)=3=in(A), out(G)=2=in(G), out(C)=1=in(C). -/
private def deBruijnBalanced (g : Genome) : Prop :=
  let mers := List.range g.length |>.map fun i => (base g i, base g (i + 1))
  let outDeg c := mers.countP fun (a, _) => a == c
  let inDeg c := mers.countP fun (_, b) => b == c
  outDeg .A == inDeg .A ∧ outDeg .C == inDeg .C ∧
  outDeg .G == inDeg .G ∧ outDeg .T == inDeg .T

theorem competitor_balanced : deBruijnBalanced competitor := by
  native_decide

/-- All observed types have positive occurrence count in the competitor. -/
private def allObservedPositive (g : Genome) : Prop :=
  dinucleotideCount g .A .A > 0 ∧
  dinucleotideCount g .C .A > 0 ∧
  dinucleotideCount g .G .G > 0

theorem competitor_observed_positive : allObservedPositive competitor := by
  native_decide

/-! ## Likelihood comparison -/

theorem truth_AA_count : dinucleotideCount truth .A .A = 1 := by native_decide
theorem truth_CA_count : dinucleotideCount truth .C .A = 1 := by native_decide
theorem truth_GG_count : dinucleotideCount truth .G .G = 1 := by native_decide

theorem competitor_AA_count : dinucleotideCount competitor .A .A = 2 := by native_decide
theorem competitor_CA_count : dinucleotideCount competitor .C .A = 1 := by native_decide
theorem competitor_GG_count : dinucleotideCount competitor .G .G = 1 := by native_decide

theorem truth_ordering : orderingObjective truth = 1 := by
  unfold orderingObjective
  rw [truth_AA_count, truth_CA_count, truth_GG_count]
  norm_num

theorem competitor_ordering : orderingObjective competitor = 32 := by
  unfold orderingObjective
  rw [competitor_AA_count, competitor_CA_count, competitor_GG_count]
  norm_num

theorem competitor_beats_truth_ordering : orderingObjective truth < orderingObjective competitor := by
  rw [truth_ordering, competitor_ordering]
  norm_num

/-- The full likelihood ratio including multinomial coefficient and denominator. -/
theorem likelihood_ratio : sampleLikelihood competitor / sampleLikelihood truth = 32 := by
  unfold sampleLikelihood orderingObjective at *
  rw [truth_AA_count, truth_CA_count, truth_GG_count,
      competitor_AA_count, competitor_CA_count, competitor_GG_count]
  norm_num [truth, competitor]

/-! ## The counterexample theorem -/

/--
The information-feasibility hypothesis for the truth: coverage holds and
bridging conditions are vacuously satisfied (repeat-free genome).
 -/
def informationFeasible : Prop := covered ∧ noRepeatAtLength2

theorem truth_information_feasible : informationFeasible :=
  ⟨truth_covered, truth_no_repeat⟩

/--
Maximum-likelihood predicate for fixed-length exact Variant E: the truth
is an ML maximizer among all length-G circular genomes.
 -/
def IsMaximumLikelihood (g : Genome) : Prop :=
  ∀ candidate : Genome, candidate.length = g.length →
    orderingObjective candidate ≤ orderingObjective g

theorem truth_not_maximum_likelihood : ¬ IsMaximumLikelihood truth := by
  intro h
  have hcomp := h competitor (by native_decide)
  rw [truth_ordering, competitor_ordering] at hcomp
  norm_num at hcomp

/--
Kernel-checked finite counterexample to fixed-length exact Variant E:
the realized reads satisfy coverage and the bridging obligations are
vacuous (truth is repeat-free), yet the truth is not an exact multinomial
maximum-likelihood candidate among genomes of the same length.

Truth: AACAGG (length 6, repeat-free, vacuous bridging).
Sample: {AA:5, CA:1, GG:1} (N=7), coverage satisfied.
Competitor: AAAGGC (length 6, de Bruijn-balanced, all observed types positive).
Likelihood ratio: 32 (competitor wins).

This theorem does not claim anything about unrestricted-length exact ML,
Variant A (binomial approximation), Variant F (flow feasible set), or
which interpretation Shomorony et al. intended in the published open
question.
 -/
theorem fixed_length_exact_variant_e_counterexample :
    informationFeasible ∧ ¬ IsMaximumLikelihood truth :=
  ⟨truth_information_feasible, truth_not_maximum_likelihood⟩

end AssemblyP1.FixedLengthVariantECounterexample
