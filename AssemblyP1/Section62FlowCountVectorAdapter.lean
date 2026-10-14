import AssemblyP1.Section62BidirectedFlow

/-!
# The §6.2 flow-to-count-vector adapter (#261)

This module supplies the *adapter* between the literal MB09 §6.2
bidirected-flow feasibility object (`AssemblyP1.Section62BidirectedFlow`,
`Feasible62`/`Admissible`) and the abstract count-vector likelihood criteria of
`AssemblyP1.Section62BinomialCriterion` and
`AssemblyP1.GeneralBidirectedFlowML`.

The scope note `docs/issue261-general-bidirected-flow-ml.md` records the adapter
as one of the remaining OPEN axes of #261: the count-vector criterion is proved
for an abstract class of throughput vectors, but nothing connects a *flow* to its
*throughput vector*.  This module makes the connection that is available in the
present model precise:

* **The likelihood factors through the throughput.**  Any score that is a
  function of the throughput vector is invariant under replacing a flow by
  another flow with the same throughput.  Therefore ML maximality over a feasible
  *flow* set is equivalent to ML maximality over its *throughput image*, which is
  the exact sense in which the count-vector criteria apply to the §6.2 flow
  domain.

* **Candidate-set inclusion transfers negative witnesses, not positive ones.**
  This is the transfer principle the issue statement requires: a full-overlap
  *failure* lifts to a larger arbitrary-`oMin` candidate set once inclusion of the
  smaller candidate set in the larger one is proved, while a positive maximality
  statement only restricts downward.

## What is *not* claimed here

The remaining obligation — a structural characterization of the *throughput
image* of the §6.2 feasible set (the incidence/Graver problem), and the
construction of a §6.2 feasible flow from a spelled circuit with
`d = Spelling.visits` — is **not** proved here.  The finite obstruction of
`AssemblyP1.Section62NonSpelledFlow` (`no_sequence_has_star_spectrum`) shows that
the throughput image strictly contains the spelled throughputs, so no
spelling-based characterization can be complete.  This module does not decide the
Myers/MB09 source-fidelity question.
-/

namespace AssemblyP1.Section62FlowCountVectorAdapter

open AssemblyP1.Section62Flow

/-! ## ML maximality as a property of a candidate set -/

/-- A candidate `A` is a maximizer of `score` over the candidate set `S` when no
candidate `B ∈ S` has strictly larger score.  Ties are admitted, so this is
"truth is *a* maximizer", not uniqueness. -/
def Maximal {σ : Type*} (S : Set σ) (score : σ → ℚ) (A : σ) : Prop :=
  ∀ B ∈ S, score B ≤ score A

/-- **Positive statements restrict.**  If the truth is maximal over a large class,
it is maximal over any sub-class. -/
theorem maximal_of_subset {σ : Type*} {S₁ S₂ : Set σ} (h : S₁ ⊆ S₂) {score : σ → ℚ}
    {A : σ} (hmax : Maximal S₂ score A) : Maximal S₁ score A :=
  fun B hB => hmax B (h hB)

/-- **Negative witnesses transfer under candidate-set inclusion.**  If the truth
is not maximal over a sub-class and that sub-class is contained in a larger class,
it is not maximal over the larger class.  This is the formal content of "full-overlap
failures transfer only when candidate-set inclusion is proved". -/
theorem not_maximal_of_subset {σ : Type*} {S₁ S₂ : Set σ} (h : S₁ ⊆ S₂) {score : σ → ℚ}
    {A : σ} (hfail : ¬ Maximal S₁ score A) : ¬ Maximal S₂ score A :=
  fun hmax => hfail (maximal_of_subset h hmax)

/-! ## The throughput map -/

/-- The throughput vector of a §6.2 flow `f` on the graph `edges`: the function
mapping each molecule class `v` to the flow through vertex `v`.  This is the map
whose image the count-vector criteria score. -/
def throughputVec {A W : Type} [DecidableEq W] (rep : W → W) (f : BdFlow A W)
    (edges : List (BdEdge A W)) : W → ℕ :=
  fun v => throughput A W rep f edges v

/-- A score that is a function of the throughput vector is invariant under
replacing a flow by another flow with the same throughput.  This is the first
half of the flow-to-count-vector adapter. -/
theorem throughputVec_congr {A W : Type} [DecidableEq W] {rep : W → W} {f g : BdFlow A W}
    {edges : List (BdEdge A W)}
    (h : throughputVec rep f edges = throughputVec rep g edges) (score : (W → ℕ) → ℚ) :
    score (throughputVec rep f edges) = score (throughputVec rep g edges) := by
  rw [h]

/-- **Flow-to-count-vector reduction.**  For a feasible flow set `F` and a truth
flow `f₀`, ML maximality of the truth *throughput* `Θ f₀` over the throughput
image `Θ(F)` is equivalent to ML maximality of `f₀` over `F`.  Consequently any
count-vector criterion for the image applies verbatim to the flow domain;
characterizing the image is the remaining open sub-claim. -/
theorem maximal_image_iff {A W : Type} [DecidableEq W] (rep : W → W)
    (edges : List (BdEdge A W)) (F : Set (BdFlow A W)) (score : (W → ℕ) → ℚ)
    (f₀ : BdFlow A W) :
    Maximal (Set.image (fun f => throughputVec rep f edges) F) score
        (throughputVec rep f₀ edges) ↔
      Maximal F (fun f => score (throughputVec rep f edges)) f₀ := by
  constructor
  · intro h f hf
    exact h (throughputVec rep f edges) ⟨f, hf, rfl⟩
  · intro h B hB
    obtain ⟨f, hf, rfl⟩ := hB
    exact h f hf

end AssemblyP1.Section62FlowCountVectorAdapter
