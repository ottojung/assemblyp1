import AssemblyP1.Section62SpelledFlowAdapter

/-!
# Spelled sub-class maximality transfer for the §6.2 flow domain (#261)

This module continues the #261 axis opened by
`AssemblyP1.Section62SpelledFlowAdapter` (`spelling_flow_feasible`,
`visits_mem_throughput_image`).  The previous module proved the *spelled
inclusion*: every spelled circuit's visit vector lies in the throughput image of
the zero-terminal §6.2 feasible-flow set.  Here we

1. pin the **length universe** of a spelled candidate: the visit vector of a
   circular spelling of `n` read positions has total mass exactly `n`
   (`sum_visits_eq_n`), and the walk flow's total throughput is the same `n`
   (`sum_throughput_eq_n`); and

2. turn the inclusion into the **maximality-transfer statements** the issue
   requires.  For any score that factors through the throughput vector:

   * `spelled_maximal_of_flow_maximal` — flow-level maximality **restricts** to
     the spelled sub-class;
   * `flow_not_maximal_of_spelled_witness` — a spelled candidate that strictly
     beats the truth **transfers upward** to the full feasible-flow set; and

3. prove **spelling preservation across transitive reduction**
   (`spelledVisitSet_mono_edges`,
   `spelled_witness_transfers_across_reduction`): the spelled class only shrinks
   under reduction, so a spelled failure on a reduced graph transfers to any
   edge-superset's feasible-flow set.

The spelled sub-class is the one for which the adapter applies, so this is the
available direction of the full §6.2 classification.

## What is *not* claimed (explicit OPEN subclaims)

* **Sufficiency is OPEN.**  `spelledVisitSet` is a *strict* subset of the
  throughput image: `AssemblyP1.Section62NonSpelledFlow.no_sequence_has_star_spectrum`
  exhibits a zero-terminal feasible throughput (`dStar`) that is not the spectrum
  of any genome, and `star_better` shows a non-spelled throughput can strictly
  beat a spelled truth under the literal §6.1 objective.  Therefore "no spelled
  candidate beats the truth" is a *necessary* but not a *sufficient* condition
  for flow-level maximality; whether the gap can produce a truth that is
  spelled-maximal but not flow-maximal is **not decided here**.
* **Image characterization is OPEN.**  No theorem characterizes the full
  throughput image (the incidence/Graver problem, cf. #263).
* **Source fidelity of the surrogate is OPEN.**  This module is
  likelihood-independent: it applies to any score factoring through the
  throughput vector, and does not identify the §6.1 product-binomial surrogate
  with the exact iid likelihood.
-/

namespace AssemblyP1.Section62SpelledFlowMaximality

open AssemblyP1.Section62Flow
open AssemblyP1.Section62FlowCountVectorAdapter
open AssemblyP1.Section62SpelledFlowAdapter

variable {A W : Type} [DecidableEq W]

/-! ## The length universe of a spelled candidate -/

/-- The image of a spelling's read positions under the molecule-class map: the
observed molecule classes the spelling visits. -/
def visitedClasses {n : Nat} (rep : W → W) (sp : Spelling A W n) : Finset W :=
  (List.finRange n).toFinset.image (fun i => rep (sp.strand i))

/-- **Length universe.**  The visit vector of a circular spelling of `n` read
positions has total mass exactly `n`: every read position lies in exactly one
molecule class, so the visits sum to the number of positions.  This is the
spelled analogue of "the candidate length equals its window count". -/
theorem sum_visits_eq_n {n : Nat} (rep : W → W) (sp : Spelling A W n) :
    ∑ v ∈ visitedClasses rep sp, sp.visits rep v = n := by
  have h := Finset.card_eq_sum_card_image (fun i : Fin n => rep (sp.strand i))
      ((List.finRange n).toFinset)
  rw [List.toFinset_card_of_nodup (List.nodup_finRange n), List.length_finRange] at h
  have hgoal : ∑ v ∈ visitedClasses rep sp, sp.visits rep v
      = ∑ b ∈ Finset.image (fun i => rep (sp.strand i)) (List.finRange n).toFinset,
          {a ∈ (List.finRange n).toFinset | rep (sp.strand a) = b}.card := by
    rw [visitedClasses]
    apply Finset.sum_congr rfl
    intro b _
    rw [Spelling.visits]
    rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ (List.nodup_finRange n))]
    rw [List.filter_toFinset]
  rw [hgoal]
  exact h.symm

/-- **Length universe, flow form.**  The walk flow of a spelled circuit has total
throughput exactly `n`, the number of read positions, on any graph containing its
steps.  This is the `d`-mass `N` consumed by the length-parameterized likelihood
criteria. -/
theorem sum_throughput_eq_n {n readLen : Nat} (rep : W → W) (sp : Spelling A W n)
    (edges : List (BdEdge A W)) (hNodup : edges.Nodup)
    (hSteps : ∀ i : Fin n, sp.step rep readLen i ∈ edges) :
    ∑ v ∈ visitedClasses rep sp, throughput A W rep (sp.flow rep readLen) edges v = n := by
  rw [Finset.sum_congr rfl (fun v _ =>
    throughput_eq_visits rep sp edges hNodup hSteps v)]
  exact sum_visits_eq_n rep sp

/-! ## The spelled visit set and its inclusion in the feasible throughput image -/

/-- The set of visit vectors of spelled circuits on the graph `edges`: the
spelled sub-class of §6.2 candidates, as a set of count vectors. -/
def spelledVisitSet (rep : W → W) (readLen : Nat) (verts : List W)
    (edges : List (BdEdge A W)) : Set (W → ℕ) :=
  { d | ∃ (n : Nat) (sp : Spelling A W n),
      (∀ i : Fin n, sp.step rep readLen i ∈ edges) ∧
      BidirectedCircuit rep readLen sp ∧
      (∀ v ∈ verts, 1 ≤ sp.visits rep v) ∧
      d = sp.visits rep }

/-- **Spelled sub-class inclusion.**  Every spelled visit vector is the
throughput vector of a member of the zero-terminal §6.2 feasible set, so the
spelled sub-class is contained in the feasible throughput image. -/
theorem spelledVisitSet_subset_image (rep : W → W) (readLen : Nat) (verts : List W)
    (edges : List (BdEdge A W)) (hNodup : edges.Nodup) :
    spelledVisitSet (A := A) rep readLen verts edges ⊆
      Set.image (fun f => throughputVec rep f edges)
        (feasibleFlowSet rep verts edges) := by
  rintro d ⟨n, sp, hSteps, hCircuit, hVisit, rfl⟩
  exact visits_mem_throughput_image rep sp verts edges hNodup hSteps hCircuit hVisit

/-! ## Maximality transfer between the spelled sub-class and the flow domain -/

/-- **Positive restriction.**  If the truth flow `f₀` is ML-maximal over the
zero-terminal §6.2 feasible-flow set (for a score factoring through the
throughput), then its throughput is maximal over the spelled sub-class. -/
theorem spelled_maximal_of_flow_maximal (rep : W → W) (readLen : Nat) (verts : List W)
    (edges : List (BdEdge A W)) (hNodup : edges.Nodup) (score : (W → ℕ) → ℚ)
    (f₀ : BdFlow A W)
    (hmax : Maximal (feasibleFlowSet rep verts edges)
        (fun f => score (throughputVec rep f edges)) f₀) :
    Maximal (spelledVisitSet (A := A) rep readLen verts edges) score
      (throughputVec rep f₀ edges) :=
  maximal_of_subset (spelledVisitSet_subset_image rep readLen verts edges hNodup)
    ((maximal_image_iff rep edges (feasibleFlowSet rep verts edges) score f₀).mpr hmax)

/-- **Negative transfer.**  If some spelled candidate strictly beats the truth
flow's throughput under `score`, then the truth flow is **not** ML-maximal over
the zero-terminal §6.2 feasible-flow set.  This is the transfer of a
spelled-sub-class failure to the full flow domain, valid precisely because the
spelled sub-class is contained in the feasible throughput image. -/
theorem flow_not_maximal_of_spelled_witness (rep : W → W) (readLen : Nat) (verts : List W)
    (edges : List (BdEdge A W)) (hNodup : edges.Nodup) (score : (W → ℕ) → ℚ)
    (f₀ : BdFlow A W)
    (hwit : ∃ d ∈ spelledVisitSet (A := A) rep readLen verts edges,
      score (throughputVec rep f₀ edges) < score d) :
    ¬ Maximal (feasibleFlowSet rep verts edges)
        (fun f => score (throughputVec rep f edges)) f₀ := by
  rintro hmax
  have himg : Maximal (Set.image (fun f => throughputVec rep f edges)
      (feasibleFlowSet rep verts edges)) score (throughputVec rep f₀ edges) :=
    (maximal_image_iff rep edges (feasibleFlowSet rep verts edges) score f₀).mpr hmax
  obtain ⟨d, hd, hlt⟩ := hwit
  exact not_lt.mpr (himg d (spelledVisitSet_subset_image rep readLen verts edges hNodup hd)) hlt

/-- **Negative transfer, spelled truth.**  If the truth is itself a spelled
circuit `sp₀` and some spelled candidate strictly beats its visit vector, then
the truth's walk flow is not maximal over the zero-terminal §6.2 feasible-flow
set. -/
theorem spelled_truth_flow_not_maximal_of_spelled_witness
    {n₀ : Nat} (rep : W → W) (readLen : Nat) (sp₀ : Spelling A W n₀) (verts : List W)
    (edges : List (BdEdge A W)) (hNodup : edges.Nodup)
    (hSteps₀ : ∀ i : Fin n₀, sp₀.step rep readLen i ∈ edges)
    (score : (W → ℕ) → ℚ)
    (hwit : ∃ d ∈ spelledVisitSet (A := A) rep readLen verts edges,
      score (sp₀.visits rep) < score d) :
    ¬ Maximal (feasibleFlowSet rep verts edges)
        (fun f => score (throughputVec rep f edges)) (sp₀.flow rep readLen) := by
  refine flow_not_maximal_of_spelled_witness rep readLen verts edges hNodup score
    (sp₀.flow rep readLen) ?_
  obtain ⟨d, hd, hlt⟩ := hwit
  refine ⟨d, hd, ?_⟩
  rwa [show throughputVec rep (sp₀.flow rep readLen) edges = sp₀.visits rep from
    funext (fun v => throughput_eq_visits rep sp₀ edges hNodup hSteps₀ v)]

/-- **Exact reduction of sufficiency to the image characterization.**  The
spelled sub-class test is *sufficient* for flow-level maximality exactly when the
spelled count vectors exhaust the feasible throughput image.  Since the spelled
sub-class is a strict sub-class in general (`no_sequence_has_star_spectrum`), this
identity is the precise extra hypothesis that sufficiency needs, and proving it is
the open incidence/Graver problem.  Formally: if
`Θ(feasibleFlowSet) = spelledVisitSet`, then ML maximality over the zero-terminal
§6.2 feasible-flow set is equivalent to maximality over the spelled sub-class. -/
theorem flow_maximal_iff_spelled_maximal_of_image_eq (rep : W → W) (readLen : Nat)
    (verts : List W) (edges : List (BdEdge A W)) (score : (W → ℕ) → ℚ) (f₀ : BdFlow A W)
    (hEq : Set.image (fun f => throughputVec rep f edges) (feasibleFlowSet rep verts edges)
      = spelledVisitSet (A := A) rep readLen verts edges) :
    Maximal (feasibleFlowSet rep verts edges)
        (fun f => score (throughputVec rep f edges)) f₀ ↔
      Maximal (spelledVisitSet (A := A) rep readLen verts edges) score
        (throughputVec rep f₀ edges) := by
  rw [← hEq]
  exact (maximal_image_iff rep edges (feasibleFlowSet rep verts edges) score f₀).symm

/-! ## Spelling preservation across transitive reduction -/

/-- **Spelled-class monotonicity in the edge set.**  A spelled circuit whose steps
all lie in `edges₁` is also a spelled circuit on any edge-superset `edges₂`.
In §6.2 terms: transitive reduction can only *shrink* the spelled candidate
class, never grow it — every circuit spelled on the reduced graph is preserved
on the unreduced graph.  The vertex-lower-bound clause is graph-independent
(it constrains only `sp.visits`), so it transfers unchanged. -/
theorem spelledVisitSet_mono_edges {edges₁ edges₂ : List (BdEdge A W)}
    (rep : W → W) (readLen : Nat) (verts : List W)
    (h : ∀ e ∈ edges₁, e ∈ edges₂) :
    spelledVisitSet (A := A) rep readLen verts edges₁ ⊆
      spelledVisitSet (A := A) rep readLen verts edges₂ := by
  rintro d ⟨n, sp, hSteps, hCircuit, hVisit, rfl⟩
  exact ⟨n, sp, fun i => h _ (hSteps i), hCircuit, hVisit, rfl⟩

/-- **Negative transfer across reduction.**  A spelled-sub-class failure found on
a transitively reduced graph `edges₁` transfers upward to the feasible-flow set
of any edge-superset `edges₂` (e.g. the unreduced overlap graph): the witness
is preserved by `spelledVisitSet_mono_edges` and then lifted by
`flow_not_maximal_of_spelled_witness`.  Candidate class: spelled circuits
(`spelledVisitSet`); truth: any feasible flow `f₀` on `edges₂`; likelihood: any
score factoring through the throughput vector (including the fixed-`N`
product-binomial surrogate); length universe: the spelling length `n`
(`sum_visits_eq_n`).  Inclusion is proved, so this is a licensed negative
transfer; no positive statement is claimed. -/
theorem spelled_witness_transfers_across_reduction {edges₁ edges₂ : List (BdEdge A W)}
    (rep : W → W) (readLen : Nat) (verts : List W)
    (hNodup₂ : edges₂.Nodup)
    (h : ∀ e ∈ edges₁, e ∈ edges₂) (score : (W → ℕ) → ℚ) (f₀ : BdFlow A W)
    (hwit : ∃ d ∈ spelledVisitSet (A := A) rep readLen verts edges₁,
      score (throughputVec rep f₀ edges₂) < score d) :
    ¬ Maximal (feasibleFlowSet rep verts edges₂)
        (fun f => score (throughputVec rep f edges₂)) f₀ := by
  refine flow_not_maximal_of_spelled_witness rep readLen verts edges₂ hNodup₂ score f₀ ?_
  obtain ⟨d, hd, hlt⟩ := hwit
  exact ⟨d, spelledVisitSet_mono_edges rep readLen verts h hd, hlt⟩

end AssemblyP1.Section62SpelledFlowMaximality
