import Std

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

end AssemblyP1.Section62BinomialRealGenomeInversion
