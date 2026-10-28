import AssemblyP1.ExactReadLikelihood
import AssemblyP1.FixedLengthExactCounterexample
import AssemblyP1.FixedLengthBinomialCounterexample
import AssemblyP1.Issue209EAudit
import AssemblyP1.OrientedRigidity
import AssemblyP1.OrientedVariableLengthSe62

/-!
# Existing exact and binomial witnesses as adapters to the common read law

The old witness code is preserved verbatim. These bridge lemmas ensure its
observable read types, position counts, and objectives are exactly those of
the shared SourceFaithfulIs circular window model.
-/

namespace AssemblyP1.ExactReadLikelihoodAdapters

namespace Exact
open AssemblyP1.FixedLengthExactCounterexample
open AssemblyP1.ExactReadLikelihood

instance : Fintype Base where
  elems := {Base.A, Base.B, Base.C, Base.G}
  complete := by intro x; cases x <;> simp

abbrev embed (g : Genome) : SourceFaithfulIs.Genome Base where
  len := 5
  len_pos := by decide
  sym := g

def observed : Fin 3 → (Fin 3 → Base) :=
  ![readAAA, readAAB, readBAA]

theorem window_shared (g : Genome) (r : Fin 5) :
    window g r = (embed g).window 3 r := by rfl

theorem occ_shared (g : Genome) (w : Fin 3 → Base) :
    occ g w = readCount (embed g) 3 w := by rfl

theorem factor_six : multinomialFactor 3 3 observed = 6 := by
  have hf : ∀ w : Fin 3 → Base, Nat.factorial (ExactReadLikelihood.observedCount observed w) = 1 := by
    intro w
    by_cases hA : readAAA = w
    · subst w
      decide
    by_cases hB : readAAB = w
    · subst w
      decide
    by_cases hC : readBAA = w
    · subst w
      decide
    have hu : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
    simp [ExactReadLikelihood.observedCount, observed, hu, hA, hB, hC]
  simp [multinomialFactor, hf]
  norm_num

theorem likelihood_shared (g : Genome) :
    likelihood g = exactMultinomialLikelihood (embed g) 3 3 observed := by
  simp only [exactMultinomialLikelihood, factor_six]
  simp [iidLikelihood, Fin.prod_univ_succ, readMass, ← occ_shared,
    observed, likelihood]
  ring
end Exact

namespace Binomial
open AssemblyP1.FixedLengthBinomialCounterexample
open AssemblyP1.ExactReadLikelihood

abbrev embed (g : Genome) : SourceFaithfulIs.Genome Base where
  len := 5
  len_pos := by decide
  sym := g

def observed : Fin 3 → (Fin 3 → Base) :=
  ![readAAA, readAAC, readCAA]

theorem window_shared (g : Genome) (r : Fin 5) :
    window g r = (embed g).window 3 r := by rfl

theorem occ_shared (g : Genome) (w : Fin 3 → Base) :
    occ g w = readCount (embed g) 3 w := by rfl

theorem observedCount_shared (w : Fin 3 → Base) :
    obsCount w = ExactReadLikelihood.observedCount observed w := by
  by_cases hA : w = readAAA
  · subst w; decide
  by_cases hB : w = readAAC
  · subst w; decide
  by_cases hC : w = readCAA
  · subst w; decide
  have hu : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  simp [obsCount, ExactReadLikelihood.observedCount, observed, hu, hA, hB, hC,
    Finset.filter_insert, Finset.filter_singleton, eq_comm]

theorem marginal_shared (g : Genome) (w : Fin 3 → Base) :
    marginal g w = binomialMarginal (embed g) 3 3 5 observed w := by
  simp [marginal, binomialMarginal, ← observedCount_shared, ← occ_shared]

theorem likelihood_shared (g : Genome) :
    likelihood g = productBinomialLikelihood (embed g) 3 3 5 observed := by
  simp [likelihood, productBinomialLikelihood, ← marginal_shared]
end Binomial


namespace Issue209
open AssemblyP1.Issue209EAudit

def observed : Fin 3 → (Fin 3 → Base) :=
  ![readAAA, readAAB, readBAA]

theorem winCount_shared (g : SourceFaithfulIs.Genome Base)
    (L : ℕ) (w : Fin L → Base) :
    winCount g L w = ExactReadLikelihood.readCount g L w := by rfl

theorem obs_shared (w : Fin 3 → Base) :
    obs w = ExactReadLikelihood.observedCount observed w := by
  by_cases hA : w = readAAA
  · subst w; decide
  by_cases hB : w = readAAB
  · subst w; decide
  by_cases hC : w = readBAA
  · subst w; decide
  have hu : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  simp [obs, ExactReadLikelihood.observedCount, observed, hu, hA, hB, hC,
    Finset.filter_insert, Finset.filter_singleton, eq_comm]

theorem marginal_shared (g : SourceFaithfulIs.Genome Base)
    (N : ℕ) (w : Fin 3 → Base) :
    binomialMarginal (winCount g 3 w) N 3 (obs w) =
      ExactReadLikelihood.binomialMarginal g 3 3 N observed w := by
  simp [binomialMarginal, ExactReadLikelihood.binomialMarginal,
    ← obs_shared, ← winCount_shared]

theorem likelihood_shared (g : SourceFaithfulIs.Genome Base) (N : ℕ) :
    likelihood g N = ExactReadLikelihood.productBinomialLikelihood g 3 3 N observed := by
  simp [likelihood, ExactReadLikelihood.productBinomialLikelihood,
    ← marginal_shared]
end Issue209

namespace Rigidity
open AssemblyP1.OrientedRigidity

variable {α : Type} [DecidableEq α] [Fintype α]
  {G L : ℕ} (hG : 0 < G) (S : Fin G → α)

abbrev embed : SourceFaithfulIs.Genome α :=
  { len := G, len_pos := hG, sym := S }

theorem window_shared (r : Fin G) :
    window (L := L) hG S r = (embed hG S).window L r := by rfl

theorem spec_shared (w : Fin L → α) :
    specCount (L := L) hG S w =
      ExactReadLikelihood.readCount (embed hG S) L w := by rfl
end Rigidity

namespace OrientedVariable
open AssemblyP1.OrientedVariableLengthSe62

variable {n : ℕ} [NeZero n] (g : Fin n → Base)

abbrev embed : SourceFaithfulIs.Genome Base :=
  { len := n, len_pos := NeZero.pos n, sym := g }

theorem window_shared (r : Fin n) :
    window g r = (embed g).window 3 r := by
  funext d
  fin_cases d <;> rfl
end OrientedVariable

end AssemblyP1.ExactReadLikelihoodAdapters
