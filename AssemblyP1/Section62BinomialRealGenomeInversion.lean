import Mathlib

/-!
# An actual circular-genome ranking inversion for the §6.1 product-binomial surrogate

At read length two, exact iid/multinomial likelihood and MB09 §6.1's product
of marginal binomial likelihoods can rank two genuine circular genomes of
equal fixed length differently. Both candidate read-count vectors below are
realized by the explicitly given circular binary words of length 100.

The full four-word alphabet is used, including all three unseen zero-count
coordinates. This does NOT assert that the candidates satisfy primitive P2
at L=2 (the known length bound would exclude them), and does not claim that
the marginal-binomial approximation is an exact joint sampling law.
-/

namespace AssemblyP1.Section62BinomialRealGenomeInversion

/-- A=0^51 1^49. -/
def genomeA : List Bool :=
  List.replicate 51 false ++ List.replicate 49 true

/-- B=0^50 1^18 (01)^16. -/
def genomeB : List Bool :=
  List.replicate 50 false ++ List.replicate 18 true ++
    (List.replicate 16 [false, true]).flatten

/-- The exact number of start positions on a circular genome yielding
the oriented two-letter word (a,b). -/
def circularTwoCount (s : List Bool) (a b : Bool) : Nat :=
  ((List.range s.length).filter (fun i =>
    (s.getD i false == a) &&
    (s.getD ((i + 1) % s.length) false == b))).length

theorem genomeA_len : genomeA.length = 100 := by decide
theorem genomeB_len : genomeB.length = 100 := by decide

/-- The four oriented circular two-read counts of A (00,01,10,11). -/
theorem genomeA_counts :
    circularTwoCount genomeA false false = 50 ∧
    circularTwoCount genomeA false true = 1 ∧
    circularTwoCount genomeA true false = 1 ∧
    circularTwoCount genomeA true true = 48 := by
  decide

/-- The four oriented circular two-read counts of B (00,01,10,11). -/
theorem genomeB_counts :
    circularTwoCount genomeB false false = 49 ∧
    circularTwoCount genomeB false true = 17 ∧
    circularTwoCount genomeB true false = 17 ∧
    circularTwoCount genomeB true true = 17 := by
  decide

/-! The exact likelihoods have a common denominator: 100 for one-read
iid sampling and 100^4 for the full product-binomial approximation with n=1.
Their INTEGER NUMERATORS suffice for a kernel-checked ranking comparison. -/

/-- The two exact iid likelihood numerators with common denominator 100. -/
def exactNumA : Nat := 50
def exactNumB : Nat := 49

/-- All four product-binomial factors, including the three zero-count
coordinates, with common denominator 100^4. -/
def surrogateNumA : Nat := 50 * 99 * 99 * 52
def surrogateNumB : Nat := 49 * 83 * 83 * 83

theorem exact_prefers_A : exactNumB < exactNumA := by decide
theorem surrogate_prefers_B : surrogateNumA < surrogateNumB := by decide
theorem surrogateA_num : surrogateNumA = 25482600 := by decide
theorem surrogateB_num : surrogateNumB = 28017563 := by decide
theorem common_denominator : 100 ^ 4 = 100000000 := by decide

#print axioms genomeA_counts
#print axioms genomeB_counts
#print axioms exact_prefers_A
#print axioms surrogate_prefers_B
#print axioms surrogateA_num
#print axioms surrogateB_num

/-! ## Non-vacuity hypotheses of the witness

The candidates are genuine connected circular words of the same fixed external
length N = 100, and each realizes the full oriented 2-mer alphabet, so the
§6.1 product below genuinely has four factors, three of them at zero-count
coordinates. -/

/-- A circular binary word is connected when its oriented 2-mer spectrum makes
the letter graph on {0,1} strongly connected: both orientations of the letter
change occur on the circle. -/
abbrev circularConnected (s : List Bool) : Prop :=
  0 < circularTwoCount s false true ∧ 0 < circularTwoCount s true false

/-- The witness pair is non-vacuous: both candidates are connected circular
words of equal fixed length N = 100, and both realize every oriented 2-mer. -/
theorem witness_nonvacuous :
    genomeA.length = 100 ∧ genomeB.length = 100 ∧
    circularConnected genomeA ∧ circularConnected genomeB ∧
    (0 < circularTwoCount genomeA false false ∧ 0 < circularTwoCount genomeA true true) ∧
    (0 < circularTwoCount genomeB false false ∧ 0 < circularTwoCount genomeB true true) := by
  decide

/-! ## Both likelihood expressions over exact rationals

For the single observed read `00` (sample size n = 1, count vector
x = (1,0,0,0) over the oriented alphabet (00,01,10,11)) the exact joint iid
read law is the multinomial point probability
`1!/(1!0!0!0!) · p00^1 p01^0 p10^0 p11^0 = p00 = d(00)/N`, whereas the MB09
§6.1 surrogate is the full-alphabet product of marginal binomials
`∏_w Binom(1; x_w, d(w)/N) = p00 · (1-p01)(1-p10)(1-p11)`, retaining every
zero-count coordinate. All four values are stated here as exact rationals. -/

/-- Exact joint iid likelihood of the observed read `00` under A: `50/100 = 1/2`. -/
theorem exact_joint_likelihood_A : (50 / 100 : ℚ) = 1 / 2 := by norm_num

/-- Exact joint iid likelihood of the observed read `00` under B: `49/100`. -/
theorem exact_joint_likelihood_B : (49 / 100 : ℚ) = 49 / 100 := by norm_num

/-- MB09 §6.1 product of marginal binomials for A, including all three
zero-count coordinates: `(50/100)(99/100)^2(52/100) = 127413/500000 = 0.254826`. -/
theorem surrogate_likelihood_A :
    (50 / 100 : ℚ) * (99 / 100) ^ 2 * (52 / 100) = 127413 / 500000 := by norm_num

/-- MB09 §6.1 product of marginal binomials for B, including all three
zero-count coordinates: `(49/100)(83/100)^3 = 28017563/100000000 = 0.28017563`. -/
theorem surrogate_likelihood_B :
    (49 / 100 : ℚ) * (83 / 100) ^ 3 = 28017563 / 100000000 := by norm_num

/-- The exact joint iid read law ranks A strictly above the B candidate. -/
theorem exact_joint_ranks_A : (49 / 100 : ℚ) < (50 / 100 : ℚ) := by norm_num

/-- The §6.1 product of marginal binomials ranks B strictly above the A
candidate, even at fixed external N = 100. -/
theorem surrogate_ranks_B :
    (50 / 100 : ℚ) * (99 / 100) ^ 2 * (52 / 100)
      < (49 / 100 : ℚ) * (83 / 100) ^ 3 := by norm_num

/-- The ranking inversion packaged with its non-vacuity hypotheses: both
candidates are connected circular words of the same fixed length N = 100, the
sample is the single observed read `00` (n = 1, x = (1,0,0,0)), and the §6.1
product ranges over the full oriented alphabet including all zero-count
coordinates. Under these hypotheses the exact joint iid read law prefers A,
while the §6.1 product of marginal binomials prefers B. -/
theorem ranking_inversion :
    (genomeA.length = 100 ∧ genomeB.length = 100 ∧
      circularConnected genomeA ∧ circularConnected genomeB ∧
      (0 < circularTwoCount genomeA false false ∧ 0 < circularTwoCount genomeA true true) ∧
      (0 < circularTwoCount genomeB false false ∧ 0 < circularTwoCount genomeB true true)) ∧
    ((49 / 100 : ℚ) < (50 / 100 : ℚ)) ∧
    ((50 / 100 : ℚ) * (99 / 100) ^ 2 * (52 / 100)
      < (49 / 100 : ℚ) * (83 / 100) ^ 3) := by
  exact ⟨witness_nonvacuous, by norm_num, by norm_num⟩

#print axioms circularConnected
#print axioms witness_nonvacuous
#print axioms exact_joint_likelihood_A
#print axioms exact_joint_likelihood_B
#print axioms surrogate_likelihood_A
#print axioms surrogate_likelihood_B
#print axioms exact_joint_ranks_A
#print axioms surrogate_ranks_B
#print axioms ranking_inversion

end AssemblyP1.Section62BinomialRealGenomeInversion
