import AssemblyP1.Model

/-!
# Equivalence and tie robustness of strict-improvement witnesses

This file kernel-checks the logical core of the candidate-genome-equivalence /
tie-semantics audit.  It isolates three facts about the abstract `AssemblyModel`
that make the repository's *strict-improvement* counterexamples immune to the
choice of genome equivalence (cyclic shift, reverse complement, dihedral, ...)
and to whether the published conclusion is read as "the truth is a maximizer"
or "the truth is the unique maximizer up to equivalence":

* `IsMaximumLikelihood` never mentions `genomeEquiv`, so a strictly better
  candidate refutes the maximizer schema verbatim;
* `IsUniqueMaximumLikelihoodUpToEquiv` is the conjunction of the maximizer
  schema and a tie clause, so the same strict improvement also refutes it — and,
  more strongly, refutes the tie clause for *every* relation `R`, not just the
  model's own equivalence;
* conversely, the uniqueness clause is monotone in the equivalence relation, so
  a uniqueness refutation that rests on a *tie* is relative to the equivalence
  chosen, unlike a strict-improvement refutation.

This is deliberately a pure-logic file: it adds no model infrastructure.  It
does not show that any particular witness satisfies the hypotheses; that is the
job of the per-witness Lean modules and the companion audit script.
-/

namespace AssemblyP1

namespace EquivalenceTieRobustness

variable {M : AssemblyModel}

/-- Strict improvement refutes the maximizer schema, independently of the
genome equivalence relation (which the schema does not mention). -/
theorem strict_improvement_refutes_maximizer
    (truth candidate : M.Genome) (reads : M.Reads)
    (h : M.likelihood truth reads < M.likelihood candidate reads) :
    ¬ M.IsMaximumLikelihood truth reads := by
  intro hmax
  exact not_le_of_gt h (hmax candidate)

/-- The uniqueness schema is exactly the maximizer schema conjoined with a tie
clause; `genomeEquiv` enters only through the tie clause. -/
theorem unique_iff_maximizer_and_ties
    (truth : M.Genome) (reads : M.Reads) :
    M.IsUniqueMaximumLikelihoodUpToEquiv truth reads ↔
      (M.IsMaximumLikelihood truth reads ∧
        ∀ candidate : M.Genome,
          M.likelihood candidate reads = M.likelihood truth reads →
            M.genomeEquiv.r candidate truth) :=
  Iff.rfl

/-- Strict improvement refutes the uniqueness schema for *every* relation `R`
used to identify tied genomes.  In particular no coarsening or refinement of the
genome equivalence (e.g. adding reverse-complement identification to cyclic
shift) can rescue a strict-improvement witness. -/
theorem strict_improvement_refutes_unique_any_equiv
    (R : M.Genome → M.Genome → Prop)
    (truth candidate : M.Genome) (reads : M.Reads)
    (h : M.likelihood truth reads < M.likelihood candidate reads) :
    ¬ (M.IsMaximumLikelihood truth reads ∧
        ∀ c : M.Genome,
          M.likelihood c reads = M.likelihood truth reads → R c truth) := by
  rintro ⟨hmax, _⟩
  exact strict_improvement_refutes_maximizer truth candidate reads h hmax

/-- Uniqueness up to equivalence is monotone in the equivalence relation: a
finer relation implies the schema for every coarser one.  Equivalently, a
uniqueness *refutation* that relies on a tie between merely non-`R`-equivalent
genomes can be destroyed by coarsening `R`.  This is the precise sense in which
strict-improvement witnesses are more robust than tie-only witnesses. -/
theorem unique_up_to_mono
    {R₁ R₂ : M.Genome → M.Genome → Prop}
    (hsub : ∀ a b : M.Genome, R₁ a b → R₂ a b)
    (truth : M.Genome) (reads : M.Reads)
    (h : M.IsMaximumLikelihood truth reads ∧
        ∀ c : M.Genome,
          M.likelihood c reads = M.likelihood truth reads → R₁ c truth) :
    M.IsMaximumLikelihood truth reads ∧
      ∀ c : M.Genome,
        M.likelihood c reads = M.likelihood truth reads → R₂ c truth :=
  ⟨h.1, fun c hc => hsub c truth (h.2 c hc)⟩

end EquivalenceTieRobustness

end AssemblyP1
