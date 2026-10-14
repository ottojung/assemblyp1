import AssemblyP1.Section62SpellingReductionCandidate
import AssemblyP1.Section62BridgingCounterexample

/-!
# Lifting full-overlap ML counterexamples to arbitrary overlap thresholds (#262)

This module is the independent parallel proof front for board issue #262, a child
of the AssemblyP1 #261 front.  It formalizes the two missing halves of the lift
that `AssemblyP1.Section62SpellingReductionCandidate` left open:

1. **`overlapEdges` membership monotonicity** when the overlap threshold is
   lowered while the read length and observed vertex list are fixed
   (`overlapEdges_mono`).  A full-overlap edge has `len = readLen - 1`, which is
   maximal among proper overlaps `< readLen`, so it stays in the graph for every
   `oMin' ≤ readLen - 1`; combined with the already kernel-checked
   `fullOverlap_survives`, the edge also stays in `transitivelyReducedSpelling`
   (`fullOverlap_step_survives`).

2. **The zero-extension flow lift** (`zeroExtend`, `feasible62_zeroExtend_of_decomp`).
   `BdFlow A W` is a *total* function `BdEdge A W → ℕ`, and `Admissible` only
   inspects `f` on its input edge list, so the old flow cannot be reused
   verbatim on a larger graph: it may be nonzero on newly introduced
   (shorter-overlap) edges.  We therefore define
   `zeroExtend oldEdges f := fun e => if e ∈ oldEdges then f e else 0` and prove
   that, whenever the new edge list is `pre ++ oldEdges` with `pre` disjoint from
   `oldEdges`, the lifted flow still satisfies the vertex throughput lower bound
   `1`, signed-incidence balance, the throughput-equals-spectrum (read-class
   count) clause, and the zero-terminal clause.  The conservation is proved by an
   exact fold–filter fusion, so it is multiplicity-correct: it does **not** need a
   `Nodup` hypothesis, because the decomposition keeps every occurrence of every
   old edge.

3. **Instantiation on the existing kernel-checked full-overlap witness.**  The
   `AAATT → AAAATT` bridging counterexample of
   `AssemblyP1.Section62BridgingCounterexample` uses `oMin = readLen - 1 = 2` and
   the literal transitive reduction.  We lift both its truth and competitor
   flows to `oMin = 1` by zero-extension onto the `28`-edge `oMin = 1` graph,
   kernel-check their `Feasible62` status and the survival of every walk step in
   `transitivelyReducedSpelling`, and retain the exact strict likelihood
   inequality `lik obs dS < lik obs dD`.

## What is *not* claimed

The lift is a **negative-witness transfer**: the two concrete witness circuits
remain feasible and the competitor still strictly beats the truth.  It is *not* a
transfer of uniqueness of the optimum, nor a transfer to the non-spelled flow
optimum of `AssemblyP1.Section62NonSpelledFlow` (whose optima use a length-`1`
overlap and hence are not full-overlap flows), nor a source-faithful Myers/MB09
algorithm correspondence.  Those remain separately open (see #284 and #261).

No `sorry`, `axiom`, `admit` or `native_decide` occurs below.
-/

namespace AssemblyP1.Section62FullOverlapLift

set_option maxHeartbeats 4000000

open AssemblyP1.Section62Flow
open AssemblyP1.Section62SpellingReductionCandidate

variable {A W : Type} [DecidableEq W]

/-! ## (i) Membership monotonicity of `overlapEdges` under lowering `oMin`

`overlapEdges` generates, for each overlap length `len` in
`(List.range readLen).filter (oMin ≤ ·)`, the same block of edges.  Lowering the
threshold only adds the blocks for `len < oMin`; it never changes the block for a
fixed `len`.  Hence every edge present at `oMin` is present at any `oMin' ≤ oMin`,
with the same multiplicity (the blocks are literally reused). -/

/-- **Membership monotonicity.**  Lowering the overlap threshold preserves
membership in the generated `overlapEdges` graph. -/
theorem overlapEdges_mono [DecidableEq A]
    (toList : W → List A) (rep rc : W → W) (readLen oMin oMin' : Nat) (verts : List W)
    (h : oMin' ≤ oMin) :
    ∀ e ∈ overlapEdges A W toList rep rc readLen oMin verts,
      e ∈ overlapEdges A W toList rep rc readLen oMin' verts := by
  intro e he
  unfold overlapEdges at he ⊢
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at he ⊢
  obtain ⟨len, ⟨hlen_range, hlen_ge⟩, he⟩ := he
  exact ⟨len, ⟨hlen_range, le_trans h hlen_ge⟩, he⟩

/-- **Full-overlap edges survive the spelling-preserving reduction at every
lowered threshold.**  Combining `overlapEdges_mono` with the kernel-checked
`fullOverlap_survives` of `Section62SpellingReductionCandidate`: a full-overlap
edge of the `oMin`-graph is in `transitivelyReducedSpelling` at any `oMin' ≤ oMin`. -/
theorem fullOverlap_step_survives [DecidableEq A]
    (toList : W → List A) (rep rc : W → W) (readLen oMin oMin' : Nat) (verts : List W)
    (h : oMin' ≤ oMin) (e : BdEdge A W) (hfull : e.len = readLen - 1)
    (hem : e ∈ overlapEdges A W toList rep rc readLen oMin verts) :
    e ∈ transitivelyReducedSpelling W toList rc readLen oMin' verts
          (overlapEdges A W toList rep rc readLen oMin' verts) :=
  fullOverlap_survives toList rc readLen oMin' verts
    (overlapEdges A W toList rep rc readLen oMin' verts) e hfull
    (overlapEdges_mono toList rep rc readLen oMin oMin' verts h e hem)

/-! ## (ii) The zero-extension flow lift

`BdFlow A W` is a total function, so a flow certified on `oldEdges` may take
arbitrary values on edges outside `oldEdges`.  We zero-extend it.  The
conservation lemmas below are multiplicity-correct because they work with an
*exact* list decomposition `newEdges = pre ++ oldEdges`, not a mere membership
inclusion. -/

/-- The flow `f` zero-extended off `oldEdges`: the value `f e` on `oldEdges` and
`0` on every other edge. -/
def zeroExtend (oldEdges : List (BdEdge A W)) (f : BdFlow A W) : BdFlow A W :=
  fun e => if e ∈ oldEdges then f e else 0

/-- **Fold helper.**  If `g` acts as the identity on every element of `l`, then
folding `g` over `l` returns the initial accumulator. -/
theorem foldr_eq_self_of {M : Type} (l : List (BdEdge A W)) (g : BdEdge A W → M → M)
    (a : M) (h : ∀ e ∈ l, ∀ acc, g e acc = acc) : l.foldr g a = a := by
  induction l with
  | nil => rfl
  | cons e es ih =>
      rw [List.foldr_cons, h e (by simp) _]
      exact ih (fun e he => h e (by simp [he]))

/-- **Fold helper.**  If `g` and `g'` agree pointwise on `l`, their folds agree. -/
theorem foldr_congr_on {M : Type} (l : List (BdEdge A W)) (g g' : BdEdge A W → M → M)
    (a : M) (h : ∀ e ∈ l, ∀ acc, g e acc = g' e acc) :
    l.foldr g a = l.foldr g' a := by
  induction l with
  | nil => rfl
  | cons e es ih =>
      rw [List.foldr_cons, List.foldr_cons, h e (by simp) _]
      rw [ih (fun e he => h e (by simp [he]))]

/-- **Fold fusion over a prefix.**  If `g` is the identity on `pre` and agrees
with `g'` on `old`, then folding `g` over `pre ++ old` equals folding `g'` over
`old`. -/
theorem foldr_pre_append_eq {M : Type} (pre old : List (BdEdge A W))
    (g g' : BdEdge A W → M → M) (a : M)
    (hpre : ∀ e ∈ pre, ∀ acc, g e acc = acc)
    (hold : ∀ e ∈ old, ∀ acc, g e acc = g' e acc) :
    (pre ++ old).foldr g a = old.foldr g' a := by
  rw [List.foldr_append]
  rw [foldr_eq_self_of pre g (old.foldr g a) hpre]
  exact foldr_congr_on old g g' a hold

/-- **Throughput conservation.**  The throughput of the zero-extension of `f`
over `pre ++ old` equals the throughput of `f` over `old`, when `pre` is disjoint
from `old`. -/
theorem throughput_pre_append (rep : W → W) (f : BdFlow A W)
    (pre old : List (BdEdge A W)) (v : W) (hdisj : ∀ e ∈ pre, e ∉ old) :
    throughput A W rep (zeroExtend old f) (pre ++ old) v = throughput A W rep f old v := by
  unfold throughput
  refine foldr_pre_append_eq pre old _ _ 0 ?_ ?_
  · intro e he acc
    have hne := hdisj e he
    by_cases hp : rep e.sx = v <;> simp [zeroExtend, hne, hp]
  · intro e he acc
    by_cases hp : rep e.sx = v <;> simp [zeroExtend, he, hp]

/-- **Signed-incidence balance conservation.**  The core balance of the
zero-extension of `f` over `pre ++ old` equals the core balance of `f` over
`old`, when `pre` is disjoint from `old`. -/
theorem balCore_pre_append (rep : W → W) (f : BdFlow A W)
    (pre old : List (BdEdge A W)) (v : W) (hdisj : ∀ e ∈ pre, e ∉ old) :
    balCore A W rep (zeroExtend old f) (pre ++ old) v = balCore A W rep f old v := by
  unfold balCore
  rw [List.filter_append, List.filter_append]
  congr 1
  · refine foldr_pre_append_eq (pre.filter (fun e => rep e.sx = v))
      (old.filter (fun e => rep e.sx = v)) _ _ 0 ?_ ?_
    · intro e he acc
      have hne := hdisj e (List.mem_of_mem_filter he)
      simp [zeroExtend, hne]
    · intro e he acc
      have hmem := List.mem_of_mem_filter he
      simp [zeroExtend, hmem]
  · refine foldr_pre_append_eq (pre.filter (fun e => rep e.sy = v))
      (old.filter (fun e => rep e.sy = v)) _ _ 0 ?_ ?_
    · intro e he acc
      have hne := hdisj e (List.mem_of_mem_filter he)
      simp [zeroExtend, hne]
    · intro e he acc
      have hmem := List.mem_of_mem_filter he
      simp [zeroExtend, hmem]

/-- **The zero-extension flow lift.**  If `f` is a §6.2 feasible flow on
`oldEdges` (vertex lower bound `1`, zero terminals, throughput vector `d`) and
the new edge list is `pre ++ oldEdges` with `pre` disjoint from `oldEdges`, then
`zeroExtend oldEdges f` is a §6.2 feasible flow on the new graph with the same
throughput vector `d` and the same zero terminals.  Every clause is preserved:
edge lower bounds (`0 ≤ ·`), vertex lower bound `1`, signed balance, and the
throughput-equals-spectrum clause. -/
theorem feasible62_zeroExtend_of_decomp (rep : W → W) (verts : List W)
    (pre oldEdges : List (BdEdge A W)) (f : BdFlow A W) (t : SuperTerminals W)
    (d : W → ℕ)
    (hfeas : Feasible62 A W rep verts oldEdges f t d)
    (hdisj : ∀ e ∈ pre, e ∉ oldEdges) :
    Feasible62 A W rep verts (pre ++ oldEdges) (zeroExtend oldEdges f) t d := by
  obtain ⟨⟨_hLB, hvLB, hbal, hthr⟩, hterm⟩ := hfeas
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hterm⟩
  · intro e _; exact Nat.zero_le _
  · intro v hv
    rw [throughput_pre_append rep f pre oldEdges v hdisj]
    exact hvLB v hv
  · intro v hv
    simp only [balance] at hbal ⊢
    rw [balCore_pre_append rep f pre oldEdges v hdisj]
    exact hbal v hv
  · intro v hv
    rw [throughput_pre_append rep f pre oldEdges v hdisj]
    exact hthr v hv

/-! ## (iii) Instantiation: the `AAATT → AAAATT` bridging witness at `oMin = 1`

The witness graph `graphList` of `Section62BridgingCounterexample` is the
`oMin = 2` graph.  The `oMin = 1` graph is `pre ++ graphList` where `pre` is the
block of length-`1` overlaps; this is a finite decidable equality.  The truth and
competitor flows are zero-extended onto the `oMin = 1` graph. -/

namespace Bridging

open AssemblyP1.Section62BridgingCounterexample

/-- The `oMin = 1` bidirected overlap graph on the three observed read molecules. -/
def oMin1Edges : List (BdEdge Base Strand3) :=
  overlapEdges Base Strand3 toList3 rep3 rc3 readLen 1 readVerts

/-- The new length-`1` overlap edges: the `oMin = 1` graph minus the old
`oMin = 2` graph. -/
def pre : List (BdEdge Base Strand3) :=
  oMin1Edges.filter (fun e => e ∉ graphList)

/-- The `oMin = 1` graph is the disjoint union of the new length-`1` block and the
old `oMin = 2` graph.  This is a finite computation. -/
theorem decomp : oMin1Edges = pre ++ graphList := by
  unfold pre oMin1Edges
  decide

/-- Every new edge is genuinely outside the old graph. -/
theorem pre_disjoint : ∀ e ∈ pre, e ∉ graphList := by
  intro e he
  unfold pre at he
  exact of_decide_eq_true (List.mem_filter.mp he).2

/-- The truth's circuit flow, zero-extended onto the `oMin = 1` graph, is §6.2
feasible with the truth's spectrum `dS'` and no terminals. -/
theorem truth_lifted_feasible62 :
    Feasible62 Base Strand3 rep3 readVerts oMin1Edges
      (zeroExtend graphList truthCircuitFlow) noTerm dS' := by
  rw [decomp]
  exact feasible62_zeroExtend_of_decomp rep3 readVerts pre graphList
    truthCircuitFlow noTerm dS' truth_feasible62 pre_disjoint

/-- The competitor's circuit flow, zero-extended onto the `oMin = 1` graph, is
§6.2 feasible with the competitor's spectrum `dD'` and no terminals. -/
theorem competitor_lifted_feasible62 :
    Feasible62 Base Strand3 rep3 readVerts oMin1Edges
      (zeroExtend graphList competitorCircuitFlow) noTerm dD' := by
  rw [decomp]
  exact feasible62_zeroExtend_of_decomp rep3 readVerts pre graphList
    competitorCircuitFlow noTerm dD' competitor_feasible62 pre_disjoint

/-- Every step of the truth's cyclic window walk survives the spelling-preserving
transitive reduction at `oMin = 1`, so the circuit lives on the reduced
arbitrary-overlap graph. -/
theorem truth_steps_survive_spelling :
    ∀ i : Fin 5,
      spellTruth.step rep3 readLen i ∈
        transitivelyReducedSpelling Strand3 toList3 rc3 readLen 1 readVerts oMin1Edges := by
  intro i
  have hmem : spellTruth.step rep3 readLen i ∈
      overlapEdges Base Strand3 toList3 rep3 rc3 readLen oMin readVerts := by
    have h := truth_steps_in_graph i
    rw [← graph_eq] at h
    exact h
  exact fullOverlap_step_survives toList3 rep3 rc3 readLen oMin 1 readVerts
    (by decide) _ rfl hmem

/-- Every step of the competitor's cyclic window walk survives the
spelling-preserving transitive reduction at `oMin = 1`. -/
theorem competitor_steps_survive_spelling :
    ∀ i : Fin 6,
      spellCompetitor.step rep3 readLen i ∈
        transitivelyReducedSpelling Strand3 toList3 rc3 readLen 1 readVerts oMin1Edges := by
  intro i
  have hmem : spellCompetitor.step rep3 readLen i ∈
      overlapEdges Base Strand3 toList3 rep3 rc3 readLen oMin readVerts := by
    have h := competitor_steps_in_graph i
    rw [← graph_eq] at h
    exact h
  exact fullOverlap_step_survives toList3 rep3 rc3 readLen oMin 1 readVerts
    (by decide) _ rfl hmem

/-- **The lifted strict-ML / bridging-sufficiency counterexample at the lowered
overlap threshold `oMin = 1 ≤ readLen - 1` (`readLen = 3`).**  Both the truth's
and the competitor's full-overlap flows are §6.2 feasible after zero-extension
onto the larger `oMin = 1` graph (so the candidate-set inclusion holds, not merely
an edge survival), every walk step survives the spelling-preserving reduction, and
the competitor still strictly beats the truth under the literal §6.1 objective.

This is one concrete witness instance (`readLen = 3`, `oMin : 2 → 1`); the
arbitrary-threshold content is carried by the general machinery
`overlapEdges_mono`, `fullOverlap_step_survives` and
`feasible62_zeroExtend_of_decomp` above, not by this instantiation. -/
theorem bridging_lifted_strict_counterexample :
    Feasible62 Base Strand3 rep3 readVerts oMin1Edges
        (zeroExtend graphList truthCircuitFlow) noTerm dS' ∧
      Feasible62 Base Strand3 rep3 readVerts oMin1Edges
        (zeroExtend graphList competitorCircuitFlow) noTerm dD' ∧
      (∀ i : Fin 5,
        spellTruth.step rep3 readLen i ∈
          transitivelyReducedSpelling Strand3 toList3 rc3 readLen 1 readVerts oMin1Edges) ∧
      (∀ i : Fin 6,
        spellCompetitor.step rep3 readLen i ∈
          transitivelyReducedSpelling Strand3 toList3 rc3 readLen 1 readVerts oMin1Edges) ∧
      lik obs dS < lik obs dD :=
  ⟨truth_lifted_feasible62, competitor_lifted_feasible62,
    truth_steps_survive_spelling, competitor_steps_survive_spelling,
    competitor_strictly_better⟩

end Bridging

#print axioms overlapEdges_mono
#print axioms fullOverlap_step_survives
#print axioms feasible62_zeroExtend_of_decomp
#print axioms AssemblyP1.Section62FullOverlapLift.Bridging.bridging_lifted_strict_counterexample

end AssemblyP1.Section62FullOverlapLift
