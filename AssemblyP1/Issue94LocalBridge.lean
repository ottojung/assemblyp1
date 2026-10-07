import AssemblyP1.BBTEulerian

/-!
# Issue 94: the local bridge from Eulerian-cycle uniqueness to
# complete-spectrum uniqueness

For fixed `K`, `L`, `S` with `2 ≤ L`, a **local** uniqueness hypothesis —
every Eulerian cycle of the `(L-1)`-mer multigraph of the truth has the
truth's own vertex cycle — proves `BBTCompleteSpectrumUniqueness hK L S`.

This is the first branch of `BBTEulerian.bbtCompleteSpec_of_obstruction`
in isolation: the equal-spectrum matching gives a pull-back presentation
(`BBTChords.exists_matching`), the pull-back is an Eulerian cycle
(`BBTEulerian.pullback_isEulerianCycle`), the local hypothesis applies
to it, and a rotational vertex cycle makes the candidate a rotation of
the truth (`BBTEulerian.rotEquiv_of_vertexCycleEq`, with
`BBTSequenceGraph.pullback_window` for the window hypothesis).  The
second branch of the obstruction dichotomy — the long obstruction,
discharged by `Ukkonen` — is not needed: the local hypothesis replaces
the whole dichotomy, so the `Ukkonen` hypothesis of
`BBTCompleteSpectrumUniqueness` is carried but unused.
-/

namespace AssemblyP1.Issue94LocalBridge

open AssemblyP1
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.OrientedRigidity
open AssemblyP1.PopulationReduction

variable {α : Type} [DecidableEq α]

/-- **The local bridge of issue 94.**  For fixed `K`, `L`, `S` with
`2 ≤ L`, if every Eulerian cycle of the `(L-1)`-mer multigraph of the
truth has the truth's own vertex cycle, then the complete `L`-spectrum
determines the truth up to cyclic rotation: every candidate with the same
complete `L`-spectrum is a rotation of the truth.  This is the first
branch of `BBTEulerian.bbtCompleteSpec_of_obstruction` with the
obstruction dichotomy replaced by the local hypothesis. -/
theorem bbtCompleteSpec_of_eulerianLocal {L : ℕ} (hL : 2 ≤ L) {K : ℕ} (hK : 0 < K)
    (S : Fin K → α)
    (hLocal : ∀ σ : Fin K ≃ Fin K, EulerianCycle hK L S σ →
      VertexCycleEq hK L S σ (Equiv.refl (α := Fin K))) :
    BBTCompleteSpectrumUniqueness hK L S := by
  intro E _hUkk hspec
  obtain ⟨σ, hm⟩ := exists_matching hK S E hspec
  have hEul : EulerianCycle hK L S (pullback hK L S E hm.1) :=
    pullback_isEulerianCycle hK L S hm
  exact rotEquiv_of_vertexCycleEq hK L S (pullback hK L S E hm.1) hL
    (hLocal (pullback hK L S E hm.1) hEul)
    (fun s => (pullback_window hK L S E hm s).symm)

end AssemblyP1.Issue94LocalBridge
