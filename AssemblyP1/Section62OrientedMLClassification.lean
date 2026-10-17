import AssemblyP1.Section62OrientedStrandFlow

/-!
# Epistemic scope
This theorem family refers ONLY to scores and feasible flows defined by
the tagged ordered-edge experiment of Section62OrientedStrandFlow. It
does NOT classify genuine physical MB09 §6.2 flows: the inherited
ordered-departure throughput is not invariant under representing a
bidirected edge by its reverse-complement. Physical edge-orbit
normalization and positive-half-incidence visit counts remain OPEN.
The image maximality theorem is a formal image-pullback equivalence,
not a structural characterization of the attainable image.
-/

/-!
# ML maximality classification in the corrected general bidirected-flow domain (#261)

This module classifies maximum-likelihood maximality for the **corrected**
oriented-strand §6.2 domain of `AssemblyP1.Section62OrientedStrandFlow`.  It
**reuses** (does not redefine) the flow-to-count-vector adapter of
`AssemblyP1.Section62FlowCountVectorAdapter` and the spelled-sub-class transfer
of `AssemblyP1.Section62SpelledFlowMaximality`, and the objective separation of
`AssemblyP1.Section62FlowGenomeSeparation` (#269).

## The well-defined class

* **Candidate domain**: the corrected §6.2 zero-terminal feasible flows
  `orientedFeasibleFlowSet`, i.e. `Feasible62` on the tagged graph `oEdges` with
  vertex lower bound `1`, edge lower bound `0`, infinite edge upper bounds,
  signed-incidence balance `0`, and zero supersource/supersink usage.
* **Truth**: admitted (any element of the domain).
* **Likelihood / read model**: any score that is a function of the corrected
  throughput vector `orientedThroughput`.  This covers the MB09 §6.1
  fixed-external-`N` separable product-binomial evaluated on the throughput
  vector, the count-vector criteria of `AssemblyP1.Section62BinomialCriterion`,
  and the fixed-`n` extreme-sample criterion of
  `AssemblyP1.Section62FiniteNExtremeSamples`.  The exact oriented genome
  likelihood is **not** such a score (#269 separation).
* **Length universe**: all spelled lengths `n ≥ 1`; the flow domain itself is
  unconstrained in length (the throughput vector records molecule counts).

## The classification

1. `oriented_maximal_iff_image` — **exact reduction**: for any throughput-factoring
   score, the truth flow is a maximizer over `orientedFeasibleFlowSet` iff its
   throughput is a maximizer over the corrected feasible throughput image.  This
   is the precise sense in which the merged count-vector criteria apply to the
   corrected §6.2 flow domain.
2. `oriented_spelled_visits_mem_image` / `oriented_spelled_maximal_of_flow_maximal`
   — the spelled sub-class inclusion and the **necessary** direction.
3. `oriented_maximal_iff_spelled_maximal_of_image_eq` — **necessary-and-sufficient
   under image equality**: flow-level maximality is equivalent to the spelled
   sub-class test exactly when the corrected feasible throughput image equals the
   spelled visit set.  That identity is the remaining incidence/Graver obligation
   and stays OPEN in general.
4. `oriented_flow_not_maximal_of_spelled_witness` — the negative transfer, valid
   because the spelled sub-class is contained in the corrected image.

## What is *not* claimed

* No structural characterization of the corrected throughput image (OPEN).
* No transfer of the transitive-reduction axis (OPEN).
* No identification of the §6.1 product-binomial surrogate with the exact iid
   likelihood (that is #269's separation).
* No `sorry` / `admit` / `axiom` / `native_decide`.
-/

namespace AssemblyP1.Section62OrientedMLClassification

open AssemblyP1.Section62Flow
open AssemblyP1.Section62FlowCountVectorAdapter
open AssemblyP1.Section62SpelledFlowMaximality
open AssemblyP1.Section62SpelledFlowAdapter
open AssemblyP1.Section62OrientedStrandFlow

variable {A W : Type} [DecidableEq W]

/-- The corrected §6.2 zero-terminal feasible-flow set on the tagged graph. -/
def orientedFeasibleFlowSet [DecidableEq A] (toListW : W → List A) (rcW : W → W)
    (readLen oMin : Nat) (verts : List W) : Set (BdFlow A (OStrand W)) :=
  feasibleFlowSet (A := A) oRep (oVerts verts) (oEdges toListW rcW readLen oMin verts)

/-- The corrected §6.2 throughput map: the molecule-class count vector of a flow
on the tagged graph. -/
def orientedThroughput [DecidableEq A] (toListW : W → List A) (rcW : W → W)
    (readLen oMin : Nat) (verts : List W) : (BdFlow A (OStrand W)) → (OStrand W → ℕ) :=
  fun f => throughputVec oRep f (oEdges toListW rcW readLen oMin verts)

/-- **Exact ML-maximality reduction in the corrected domain.**  For any score
that factors through the corrected throughput vector, the truth flow is a
maximizer over the corrected zero-terminal feasible set iff its throughput is a
maximizer over the corrected feasible throughput image. -/
theorem oriented_maximal_iff_image [DecidableEq A] (toListW : W → List A) (rcW : W → W)
    (readLen oMin : Nat) (verts : List W) (score : (OStrand W → ℕ) → ℚ)
    (f₀ : BdFlow A (OStrand W)) :
    Maximal (Set.image (orientedThroughput toListW rcW readLen oMin verts)
        (orientedFeasibleFlowSet toListW rcW readLen oMin verts))
        score (orientedThroughput toListW rcW readLen oMin verts f₀)
      ↔ Maximal (orientedFeasibleFlowSet toListW rcW readLen oMin verts)
        (fun f => score (orientedThroughput toListW rcW readLen oMin verts f)) f₀ := by
  change Maximal
      (Set.image (fun f => throughputVec oRep f (oEdges toListW rcW readLen oMin verts))
        (feasibleFlowSet (A := A) oRep (oVerts verts) (oEdges toListW rcW readLen oMin verts)))
      score (throughputVec oRep f₀ (oEdges toListW rcW readLen oMin verts))
    ↔ Maximal
      (feasibleFlowSet (A := A) oRep (oVerts verts) (oEdges toListW rcW readLen oMin verts))
      (fun f => score (throughputVec oRep f (oEdges toListW rcW readLen oMin verts))) f₀
  exact maximal_image_iff oRep (oEdges toListW rcW readLen oMin verts)
    (feasibleFlowSet (A := A) oRep (oVerts verts) (oEdges toListW rcW readLen oMin verts)) score f₀

/-- **Spelled sub-class inclusion in the corrected domain.**  The visit vector of
a spelled circuit on the tagged graph lies in the corrected feasible throughput
image.  Reuse of `visits_mem_throughput_image`. -/
theorem oriented_spelled_visits_mem_image [DecidableEq A] (toListW : W → List A)
    (rcW : W → W) (readLen oMin : Nat) (verts : List W) {n : Nat}
    (sp : Spelling A (OStrand W) n)
    (hNodup : (oEdges toListW rcW readLen oMin verts).Nodup)
    (hSteps : ∀ i : Fin n,
      sp.step oRep readLen i ∈ oEdges toListW rcW readLen oMin verts)
    (hCircuit : BidirectedCircuit oRep readLen sp)
    (hVisit : ∀ v ∈ oVerts verts, 1 ≤ sp.visits oRep v) :
    sp.visits oRep ∈ Set.image (orientedThroughput toListW rcW readLen oMin verts)
      (orientedFeasibleFlowSet toListW rcW readLen oMin verts) := by
  change sp.visits oRep ∈ Set.image
      (fun f => throughputVec oRep f (oEdges toListW rcW readLen oMin verts))
      (feasibleFlowSet (A := A) oRep (oVerts verts) (oEdges toListW rcW readLen oMin verts))
  exact visits_mem_throughput_image (A := A) oRep sp (oVerts verts)
    (oEdges toListW rcW readLen oMin verts) hNodup hSteps hCircuit hVisit

/-- **Necessary direction in the corrected domain.**  If the truth flow is
maximal over the corrected feasible set, then its throughput is maximal over the
corrected spelled sub-class. -/
theorem oriented_spelled_maximal_of_flow_maximal [DecidableEq A] (toListW : W → List A)
    (rcW : W → W) (readLen oMin : Nat) (verts : List W) (score : (OStrand W → ℕ) → ℚ)
    (f₀ : BdFlow A (OStrand W))
    (hNodup : (oEdges toListW rcW readLen oMin verts).Nodup)
    (hmax : Maximal (orientedFeasibleFlowSet toListW rcW readLen oMin verts)
        (fun f => score (orientedThroughput toListW rcW readLen oMin verts f)) f₀) :
    Maximal (spelledVisitSet (A := A) oRep readLen (oVerts verts)
        (oEdges toListW rcW readLen oMin verts)) score
      (orientedThroughput toListW rcW readLen oMin verts f₀) := by
  change Maximal (spelledVisitSet (A := A) oRep readLen (oVerts verts)
        (oEdges toListW rcW readLen oMin verts)) score
      (throughputVec oRep f₀ (oEdges toListW rcW readLen oMin verts))
  exact spelled_maximal_of_flow_maximal oRep readLen (oVerts verts)
    (oEdges toListW rcW readLen oMin verts) hNodup score f₀ hmax

/-- **Negative transfer in the corrected domain.**  If a spelled candidate
strictly beats the truth throughput, the truth flow is not maximal over the
corrected feasible set. -/
theorem oriented_flow_not_maximal_of_spelled_witness [DecidableEq A] (toListW : W → List A)
    (rcW : W → W) (readLen oMin : Nat) (verts : List W) (score : (OStrand W → ℕ) → ℚ)
    (f₀ : BdFlow A (OStrand W))
    (hNodup : (oEdges toListW rcW readLen oMin verts).Nodup)
    (hwit : ∃ d ∈ spelledVisitSet (A := A) oRep readLen (oVerts verts)
        (oEdges toListW rcW readLen oMin verts),
      score (orientedThroughput toListW rcW readLen oMin verts f₀) < score d) :
    ¬ Maximal (orientedFeasibleFlowSet toListW rcW readLen oMin verts)
        (fun f => score (orientedThroughput toListW rcW readLen oMin verts f)) f₀ := by
  change ¬ Maximal
      (feasibleFlowSet (A := A) oRep (oVerts verts) (oEdges toListW rcW readLen oMin verts))
      (fun f => score (throughputVec oRep f (oEdges toListW rcW readLen oMin verts))) f₀
  exact flow_not_maximal_of_spelled_witness oRep readLen (oVerts verts)
    (oEdges toListW rcW readLen oMin verts) hNodup score f₀ hwit

/-- **Necessary-and-sufficient classification under image equality.**  The
corrected flow-level maximality is equivalent to the spelled sub-class test
exactly when the corrected feasible throughput image equals the spelled visit set
`spelledVisitSet`.  That image identity is the remaining incidence/Graver
obligation (OPEN in general); this theorem pins the classification to it. -/
theorem oriented_maximal_iff_spelled_maximal_of_image_eq [DecidableEq A]
    (toListW : W → List A) (rcW : W → W) (readLen oMin : Nat) (verts : List W)
    (score : (OStrand W → ℕ) → ℚ) (f₀ : BdFlow A (OStrand W))
    (hEq : Set.image (orientedThroughput toListW rcW readLen oMin verts)
        (orientedFeasibleFlowSet toListW rcW readLen oMin verts)
      = spelledVisitSet (A := A) oRep readLen (oVerts verts)
          (oEdges toListW rcW readLen oMin verts)) :
    Maximal (orientedFeasibleFlowSet toListW rcW readLen oMin verts)
        (fun f => score (orientedThroughput toListW rcW readLen oMin verts f)) f₀
      ↔ Maximal (spelledVisitSet (A := A) oRep readLen (oVerts verts)
          (oEdges toListW rcW readLen oMin verts)) score
          (orientedThroughput toListW rcW readLen oMin verts f₀) := by
  change Maximal
      (feasibleFlowSet (A := A) oRep (oVerts verts) (oEdges toListW rcW readLen oMin verts))
      (fun f => score (throughputVec oRep f (oEdges toListW rcW readLen oMin verts))) f₀
    ↔ Maximal (spelledVisitSet (A := A) oRep readLen (oVerts verts)
        (oEdges toListW rcW readLen oMin verts)) score
        (throughputVec oRep f₀ (oEdges toListW rcW readLen oMin verts))
  exact flow_maximal_iff_spelled_maximal_of_image_eq oRep readLen (oVerts verts)
    (oEdges toListW rcW readLen oMin verts) score f₀ hEq

end AssemblyP1.Section62OrientedMLClassification
