import AssemblyP1.Section62SpelledFlowAdapter
import AssemblyP1.Section62FlowCountVectorAdapter

/-!
# Spelled-circuit objective transfer for one well-defined class (#261)

## Candidate class (exactly one; no conflation)

* **Flow domain:** integral flows `BdFlow A W = BdEdge A W → ℕ` on a `Nodup`
  graph `edges` (no half-integral relaxation; `ℚ`-valued relaxations are a
  separate OPEN axis).
* **Candidates:** *spelled circuits* — a circular spelling `Spelling A W n`
  satisfying `BidirectedCircuit`, `StepsInGraph` (`∀ i, step i ∈ edges`), and
  the vertex lower bound `∀ v ∈ verts, 1 ≤ visits v`. The walk flow is
  `Spelling.flow` (edge-traversal multiplicities). This class does NOT include
  arbitrary feasible flows, and does NOT assert that every feasible flow is a
  spelled circuit or a circular genome (the `AAATT` obstruction of
  `Section62NonSpelledFlow` refutes the converse).
* **Truth:** admitted. All statements below are likelihood-independent
  identities; no claim is made that the truth is feasible or maximal.
* **Likelihood:** any score factoring through the molecule spectrum
  `score : (W → ℕ) → ℚ`. This covers both the exact iid score and the fixed-`N`
  product-binomial surrogate of `Section62BinomialCriterion` (both evaluate a
  count vector `d`), without identifying the two objectives with each other.
* **Length universe:** all `n ≥ 1` (`Spelling.hn`), arbitrary `readLen`, arbitrary
  observed vertex list `verts`.
* **RC quotient:** fixed by the caller-supplied representative map `rep`; visits
  and throughputs both count molecule classes via `rep`, and the identity below
  holds for every such `rep`.

## Linear-word vs cyclic-spell distinction

`throughput_eq_visits` (proved in `Section62SpelledFlowAdapter`) sums over the
**cyclic** walk: position `n-1` departs along `step (n-1)` toward position `0`,
so the wraparound departure is counted. A linear `spellChain` equality of
spelled words has no such closing step and proves nothing about this identity;
the `L = 5` witness of `Section62VisitTransport` shows linear word preservation
does not even preserve vertex visits across graphs. The identity below is
therefore stated only for compatible **cyclic** walks (`hSteps`), never for
linear chains.
-/

namespace AssemblyP1.Section62SpelledObjective261

open AssemblyP1.Section62Flow
open AssemblyP1.Section62FlowCountVectorAdapter
open AssemblyP1.Section62SpelledFlowAdapter

variable {A W : Type} [DecidableEq W]

/-- **Objective transfer (spectrum-factoring scores).** The spelled candidate's
spectrum objective equals the objective of its walk flow's throughput vector.
Holds for the exact iid score and the fixed-`N` binomial surrogate alike,
since both factor through `d`; it does not identify the two likelihoods. -/
theorem spelled_objective_eq_flow_objective {n readLen : Nat} (rep : W → W)
    (sp : Spelling A W n) (edges : List (BdEdge A W)) (hNodup : edges.Nodup)
    (hSteps : ∀ i : Fin n, sp.step rep readLen i ∈ edges)
    (score : (W → ℕ) → ℚ) :
    score (sp.visits rep) = score (throughputVec rep (sp.flow rep readLen) edges) := by
  congr 1
  funext v
  exact (throughput_eq_visits rep sp edges hNodup hSteps v).symm

/-- **Candidate-set inclusion (spelled circuits → feasible flows).** The walk
flow of a spelled circuit satisfying the circuit, step-inclusion, and vertex
lower-bound hypotheses is a zero-terminal feasible flow with spectrum
`Spelling.visits`. Integral domain only; half-integral flows are excluded. -/
theorem spelled_mem_feasible {n readLen : Nat} (rep : W → W) (sp : Spelling A W n)
    (verts : List W) (edges : List (BdEdge A W)) (hNodup : edges.Nodup)
    (hSteps : ∀ i : Fin n, sp.step rep readLen i ∈ edges)
    (hCircuit : BidirectedCircuit rep readLen sp)
    (hVisit : ∀ v ∈ verts, 1 ≤ sp.visits rep v) :
    sp.flow rep readLen ∈ feasibleFlowSet (A := A) rep verts edges ∧
      throughputVec rep (sp.flow rep readLen) edges = sp.visits rep := by
  constructor
  · show Feasible62 A W rep verts edges (sp.flow rep readLen) (noTerminals W)
      (throughputVec rep (sp.flow rep readLen) edges)
    rw [show throughputVec rep (sp.flow rep readLen) edges = sp.visits rep from
      funext (fun v => throughput_eq_visits rep sp edges hNodup hSteps v)]
    exact spelling_flow_feasible rep sp verts edges hNodup hSteps hCircuit hVisit
  · exact funext (fun v => throughput_eq_visits rep sp edges hNodup hSteps v)

/-- **Maximality reading (one direction only).** Maximality of a spelled
spectrum over the feasible throughput image implies maximality of its walk flow
over the feasible flow set for the pulled-back score; the converse across
classes (a flow-maximality failure refuting spelled maximality, or vice versa)
requires the proved inclusion above and is stated only in that direction. No
claim about unspelled flows, half-integral flows, or genomes that do not spell
one circular walk. -/
theorem spelled_maximal_transfer {n readLen : Nat} (rep : W → W)
    (sp : Spelling A W n) (verts : List W) (edges : List (BdEdge A W))
    (hNodup : edges.Nodup) (hSteps : ∀ i : Fin n, sp.step rep readLen i ∈ edges)
    (hCircuit : BidirectedCircuit rep readLen sp)
    (hVisit : ∀ v ∈ verts, 1 ≤ sp.visits rep v) (score : (W → ℕ) → ℚ)
    (hmax : Maximal
      (Set.image (fun f => throughputVec rep f edges)
        (feasibleFlowSet (A := A) rep verts edges))
      score (sp.visits rep)) :
    Maximal (feasibleFlowSet (A := A) rep verts edges)
      (fun f => score (throughputVec rep f edges)) (sp.flow rep readLen) := by
  have hmem : sp.flow rep readLen ∈ feasibleFlowSet (A := A) rep verts edges :=
    (spelled_mem_feasible rep sp verts edges hNodup hSteps hCircuit hVisit).1
  have heq : throughputVec rep (sp.flow rep readLen) edges = sp.visits rep :=
    (spelled_mem_feasible rep sp verts edges hNodup hSteps hCircuit hVisit).2
  rw [← heq] at hmax
  exact (maximal_image_iff (A := A) rep edges _ score (sp.flow rep readLen)).mp hmax

#print axioms spelled_objective_eq_flow_objective
#print axioms spelled_mem_feasible
#print axioms spelled_maximal_transfer

end AssemblyP1.Section62SpelledObjective261
