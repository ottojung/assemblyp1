import AssemblyP1.Section62SpelledFlowMaximality

/-!
# Refutation of the spelled-throughput image identity `Θ(feasibleFlowSet) = spelledVisitSet` (#261)

The module `AssemblyP1.Section62SpelledFlowMaximality` reduces the *sufficiency*
of the spelled-circuit maximality test to the single open identity

```text
Θ(feasibleFlowSet) = spelledVisitSet,
```

where `Θ f = throughputVec rep f edges` is the §6.2 throughput map
(`flow_maximal_iff_spelled_maximal_of_image_eq`).  This module **refutes** that
identity in general, with a genuine, exact, kernel-checked counterexample: a
zero-terminal §6.2 feasible flow whose throughput vector is *not* the visit
vector of any spelled circuit.

## The obstruction

`Spelling.step` is always the *maximal* proper overlap of length `readLen − 1`:
two consecutive length-`readLen` windows of a circular molecule share exactly
`readLen − 1` symbols.  A §6.2 feasible flow, however, may be supported on
overlaps strictly shorter than `readLen − 1`.  When the overlap graph contains
*no* edge of the maximal length `readLen − 1`, no spelled circuit can use any
edge at all, so `spelledVisitSet` is empty — yet the graph may still carry a
balanced flow.  `spelledVisitSet_eq_empty_of_no_maxEdge` records the first half
in full generality; the concrete §6.2 instance below supplies the second half.

## The concrete instance (`o_min = 1`, `readLen = 3`)

Four DNA strands over the alphabet `{A,C,G,T}`, with the molecule classes
`{AAC, GTT}` and `{CCA, TGG}`:

```text
AAC   CCA   GTT = rc(AAC)   TGG = rc(CCA)
```

The complete §6.2 overlap graph at `o_min = 1` on the observed reads
`{AAC, CCA}` contains exactly four edges, all of overlap length `1`:

```text
AAC → CCA,   CCA → AAC,   GTT → TGG,   TGG → GTT.
```

There is **no** length-`2` (maximal) edge, because no two strands share a
`2`-symbol suffix/prefix.  The flow that puts one unit on `GTT → TGG` and one
unit on `TGG → GTT` is §6.2 feasible with zero terminals: it is balanced at both
observed classes (the signed incidences cancel) and has throughput `1` at each.
But `spelledVisitSet` is empty, so the identity fails.

The instance is `decide`-checked against the *literal* `overlapEdges`
construction of `AssemblyP1.Section62BidirectedFlow`, not against a proxy.

## Scope

* This refutes the identity as a general statement, hence the hypothesis `hEq` of
  `flow_maximal_iff_spelled_maximal_of_image_eq` is not universally satisfiable.
* It does **not** decide the identity when every edge is maximal
  (`e.len = readLen − 1`), where the spelled sub-class and the feasible set can
  still differ by connectivity/strand-consistency; that remains OPEN.
* It does not touch the count-vector criteria or the source-fidelity question.
-/

namespace AssemblyP1.Section62SpelledFlowImageRefutation

open AssemblyP1.Section62Flow
open AssemblyP1.Section62FlowCountVectorAdapter
open AssemblyP1.Section62SpelledFlowMaximality
open AssemblyP1.Section62SpelledFlowAdapter

variable {A W : Type} [DecidableEq W]

/-! ## General obstructions -/

/-- **No maximal edge arrives at a class ⇒ no spelled circuit visits it.**  Every
visited position `i` of a spelling is the *arrival* strand of the maximal edge
`sp.step (pred i)`, so if no edge of maximal length `readLen − 1` arrives at the
class `v`, no spelling can visit `v`.  This is a purely structural necessary
condition on `spelledVisitSet`, and it holds regardless of feasibility. -/
theorem visits_eq_zero_of_no_arriving_maxEdge
    (rep : W → W) (readLen : Nat) (v : W) (edges : List (BdEdge A W))
    (h : ∀ e ∈ edges, e.len = readLen - 1 → rep e.sy ≠ v) :
    ∀ {n : Nat} (sp : Spelling A W n), (∀ i : Fin n, sp.step rep readLen i ∈ edges) →
      sp.visits rep v = 0 := by
  intro n sp hSteps
  by_contra hne
  have hpos : 0 < ((List.finRange n).filter
      (fun i => decide (rep (sp.strand i) = v))).length := Nat.pos_of_ne_zero hne
  obtain ⟨i, hi⟩ := List.exists_mem_of_length_pos hpos
  rw [List.mem_filter] at hi
  obtain ⟨_, hiv⟩ := hi
  have hivi : rep (sp.strand i) = v := of_decide_eq_true hiv
  have hmem : sp.step rep readLen (pred sp i) ∈ edges := hSteps (pred sp i)
  have hlen : (sp.step rep readLen (pred sp i)).len = readLen - 1 := rfl
  have hsy : rep (sp.step rep readLen (pred sp i)).sy = v := by
    rw [show (sp.step rep readLen (pred sp i)).sy = sp.strand i from by
      simp only [Spelling.step, bdEdge]
      rw [next_pred]]
    exact hivi
  exact h _ hmem hlen hsy

/-- **A graph with no edge of the maximal overlap length `readLen − 1` has no
spelled circuit at all.**  Every `Spelling.step` is the maximal overlap
`readLen − 1`, so if no edge of `edges` has that length then no spelling's walk
can live on `edges` and `spelledVisitSet` is empty. -/
theorem spelledVisitSet_eq_empty_of_no_maxEdge
    (rep : W → W) (readLen : Nat) (verts : List W) (edges : List (BdEdge A W))
    (h : ∀ e ∈ edges, e.len ≠ readLen - 1) :
    spelledVisitSet (A := A) rep readLen verts edges = ∅ := by
  ext d
  constructor
  · rintro ⟨n, sp, hSteps, -, -, -⟩
    exact h (sp.step rep readLen ⟨0, sp.hn⟩) (hSteps ⟨0, sp.hn⟩) rfl
  · intro hd
    exact absurd hd (by simp)

/-! ## The concrete §6.2 instance -/

/-- The strand type of the counterexample: the four strands
`0 = AAC`, `1 = CCA`, `2 = GTT`, `3 = TGG` over the alphabet `{A,C,G,T}`. -/
abbrev W4 : Type := Fin 4

/-- The alphabet `{A,C,G,T}` of the instance. -/
abbrev A4 : Type := Fin 4

/-- The linearization of the four strands (`A = 0`, `C = 1`, `G = 2`, `T = 3`). -/
def toList4 : W4 → List A4 :=
  ![[0, 0, 1], [1, 1, 0], [2, 3, 3], [3, 2, 2]]

/-- Reverse complement on the four strands: `AAC ↔ GTT`, `CCA ↔ TGG`. -/
def rc4 : W4 → W4 := ![2, 3, 0, 1]

/-- Molecule-class representative: `AAC = rep(GTT)`, `CCA = rep(TGG)`. -/
def rep4 : W4 → W4 := ![0, 1, 0, 1]

/-- The observed read molecules: the two class representatives `AAC`, `CCA`. -/
def verts4 : List W4 := [0, 1]

/-- Read length `L = 3`. -/
def readLen4 : Nat := 3

/-- Overlap threshold `o_min = 1`. -/
def oMin4 : Nat := 1

/-- The complete §6.2 overlap graph at `o_min = 1` on the observed reads. -/
def edges4 : List (BdEdge A4 W4) :=
  overlapEdges A4 W4 toList4 rep4 rc4 readLen4 oMin4 verts4

/-- The counterexample flow: one unit on `GTT → TGG` and one on `TGG → GTT`. -/
def flow4 : BdFlow A4 W4 := fun e =>
  if e = bdEdge rep4 2 3 1 then 1 else if e = bdEdge rep4 3 2 1 then 1 else 0

/-! ### `decide`-checked facts about the instance -/

/-- The §6.2 graph has no maximal (length-`2`) edge. -/
theorem edges4_no_maxEdge : ∀ e ∈ edges4, e.len ≠ readLen4 - 1 := by
  decide

/-- The §6.2 graph is exactly the four length-`1` edges
`AAC → CCA`, `CCA → AAC`, `GTT → TGG`, `TGG → GTT`. -/
theorem edges4_eq :
    edges4 =
      [bdEdge rep4 0 1 1, bdEdge rep4 1 0 1, bdEdge rep4 2 3 1, bdEdge rep4 3 2 1] := by
  decide

/-- The counterexample flow is a zero-terminal §6.2 feasible flow. -/
theorem flow4_feasible : flow4 ∈ feasibleFlowSet rep4 verts4 edges4 := by
  change Feasible62 A4 W4 rep4 verts4 edges4 flow4 (noTerminals W4)
    (throughputVec rep4 flow4 edges4)
  unfold Feasible62 Admissible
  decide

/-- Its throughput at the observed class `AAC` is `1`. -/
theorem flow4_throughput_AAC : throughputVec rep4 flow4 edges4 0 = 1 := by
  decide

/-- Its throughput at the observed class `CCA` is `1`. -/
theorem flow4_throughput_CCA : throughputVec rep4 flow4 edges4 1 = 1 := by
  decide

/-! ## The refutation -/

/-- The feasible throughput image is nonempty: `flow4` supplies the vector with
`AAC ↦ 1`, `CCA ↦ 1`. -/
theorem image_nonempty :
    (Set.image (fun f => throughputVec rep4 f edges4)
      (feasibleFlowSet rep4 verts4 edges4)).Nonempty :=
  ⟨throughputVec rep4 flow4 edges4, flow4, flow4_feasible, rfl⟩

/-- **The spelled-circuit sufficiency test is not sufficient.**  The image of the
zero-terminal §6.2 feasible set under the throughput map strictly contains the
spelled visit set: `flow4`'s throughput is feasible but not spelled.  Hence the
identity `Θ(feasibleFlowSet) = spelledVisitSet` fails, and the hypothesis `hEq`
of `flow_maximal_iff_spelled_maximal_of_image_eq` is not universally satisfiable. -/
theorem image_ne_spelledVisitSet :
    Set.image (fun f => throughputVec rep4 f edges4) (feasibleFlowSet rep4 verts4 edges4)
      ≠ spelledVisitSet (A := A4) rep4 readLen4 verts4 edges4 := by
  rw [spelledVisitSet_eq_empty_of_no_maxEdge rep4 readLen4 verts4 edges4 edges4_no_maxEdge]
  intro h
  have hne := image_nonempty
  rw [h] at hne
  obtain ⟨x, hx⟩ := hne
  exact hx

/-- The witness, stated as a direct existential: a feasible throughput vector that
is not a spelled visit vector. -/
theorem exists_feasible_not_spelled :
    ∃ d ∈ Set.image (fun f => throughputVec rep4 f edges4) (feasibleFlowSet rep4 verts4 edges4),
      d ∉ spelledVisitSet (A := A4) rep4 readLen4 verts4 edges4 := by
  refine ⟨throughputVec rep4 flow4 edges4, ⟨flow4, flow4_feasible, rfl⟩, ?_⟩
  rw [spelledVisitSet_eq_empty_of_no_maxEdge rep4 readLen4 verts4 edges4 edges4_no_maxEdge]
  exact fun h => h

/-! ## A second instance with maximal edges present

The first instance has no maximal edge at all, so the "no maximal edge" obstruction
applies.  To show the failure is not merely an artefact of that, this second
instance *does* contain maximal edges (`AAA → AAA` and `TTT → TTT`, both of class
`AAA`), yet still has a feasible throughput outside the spelled set: no maximal
edge *arrives* at the class `ACA`, while the flow routes through `ACA` on a
length-`1` overlap. -/

/-- The second instance's strand type: `0 = AAA`, `1 = ACA`, `2 = TTT = rc(AAA)`,
`3 = TGT = rc(ACA)`. -/
def toList4b : W4 → List A4 :=
  ![[0, 0, 0], [0, 1, 0], [1, 1, 1], [1, 2, 1]]

/-- Reverse complement on the second instance: `AAA ↔ TTT`, `ACA ↔ TGT`. -/
def rc4b : W4 → W4 := ![2, 3, 0, 1]

/-- Molecule-class representative: `AAA = rep(TTT)`, `ACA = rep(TGT)`. -/
def rep4b : W4 → W4 := ![0, 1, 0, 1]

/-- The observed reads of the second instance. -/
def verts4b : List W4 := [0, 1]

/-- The complete §6.2 overlap graph of the second instance at `o_min = 1`. -/
def edges4b : List (BdEdge A4 W4) :=
  overlapEdges A4 W4 toList4b rep4b rc4b readLen4 oMin4 verts4b

/-- The flow: one unit on the length-`1` overlaps `AAA → ACA` and `ACA → AAA`. -/
def flow4b : BdFlow A4 W4 := fun e =>
  if e = bdEdge rep4b 0 1 1 then 1 else if e = bdEdge rep4b 1 0 1 then 1 else 0

/-- No maximal (length-`2`) edge of the graph arrives at the class `ACA = 1`. -/
theorem edges4b_no_arriving_ACA :
    ∀ e ∈ edges4b, e.len = readLen4 - 1 → rep4b e.sy ≠ 1 := by
  decide

/-- The second instance does contain maximal edges. -/
theorem edges4b_has_maxEdge : ∃ e ∈ edges4b, e.len = readLen4 - 1 := by
  decide

/-- The second flow is zero-terminal §6.2 feasible. -/
theorem flow4b_feasible : flow4b ∈ feasibleFlowSet rep4b verts4b edges4b := by
  change Feasible62 A4 W4 rep4b verts4b edges4b flow4b (noTerminals W4)
    (throughputVec rep4b flow4b edges4b)
  unfold Feasible62 Admissible
  decide

/-- Its throughput at the class `ACA` is `1`. -/
theorem flow4b_throughput_ACA : throughputVec rep4b flow4b edges4b 1 = 1 := by
  decide

/-- The second flow's throughput is not a spelled visit vector: no spelling can
visit `ACA` at all, by `visits_eq_zero_of_no_arriving_maxEdge`. -/
theorem flow4b_throughput_not_spelled :
    throughputVec rep4b flow4b edges4b ∉
      spelledVisitSet (A := A4) rep4b readLen4 verts4b edges4b := by
  rintro ⟨n, sp, hSteps, -, -, heq⟩
  have hzero := visits_eq_zero_of_no_arriving_maxEdge rep4b readLen4 1 edges4b
    edges4b_no_arriving_ACA sp hSteps
  have h1 : sp.visits rep4b 1 = 1 := by
    rw [← heq]; exact flow4b_throughput_ACA
  rw [hzero] at h1
  exact Nat.zero_ne_one h1

/-- **The identity fails even when the graph contains maximal edges.**  The
second instance's feasible throughput image is not the spelled visit set. -/
theorem image_ne_spelledVisitSet_of_maxEdge_instance :
    Set.image (fun f => throughputVec rep4b f edges4b) (feasibleFlowSet rep4b verts4b edges4b)
      ≠ spelledVisitSet (A := A4) rep4b readLen4 verts4b edges4b := by
  intro h
  have hmem : throughputVec rep4b flow4b edges4b ∈
      spelledVisitSet (A := A4) rep4b readLen4 verts4b edges4b := by
    rw [← h]
    exact ⟨flow4b, flow4b_feasible, rfl⟩
  exact flow4b_throughput_not_spelled hmem

end AssemblyP1.Section62SpelledFlowImageRefutation
