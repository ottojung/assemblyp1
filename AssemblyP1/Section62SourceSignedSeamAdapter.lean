import AssemblyP1.Section62GlobalSpellingPreservation
import AssemblyP1.Section62OverlapSuffix
import AssemblyP1.Section62PeriodicSeam

/-!
# A graph-level adapter from genuine signed overlap edges to the word-level seam

Membership in the actual complete bidirected overlap graph gives each step's
proper suffix/prefix overlap; signed path adjacency gives successive strand
equality. We use those facts to instantiate the generic word-level ValidPath.
This makes no claim that an arbitrary balanced integer flow is a spelled walk.
-/

namespace AssemblyP1.Section62SourceSignedSeamAdapter

open Section62Flow Section62SpellingReductionCandidate
open AssemblyP1.Section62GlobalSpellingPreservation
open AssemblyP1.Section62OverlapSuffix

variable {A W : Type} [DecidableEq A] [DecidableEq W]

def graphSteps (toList : W → List A) (edges : List (BdEdge A W)) :
    List (Nat × List A) :=
  edges.map (fun e => (e.len, toList e.sy))

/-- The actual edge graph's overlap membership and walk adjacency imply all
the elementary per-step hypotheses used by ValidPath. -/
theorem valid_graph_steps
    (toList : W → List A) (rep rc : W → W) (readLen oMin : Nat)
    (verts : List W)
    (hLen : ∀ s ∈ strandsOf rc verts, (toList s).length = readLen) :
    ∀ (edges : List (BdEdge A W)) (start : W),
      edges.IsChain Step →
      (∀ e ∈ edges, e ∈ overlapEdges A W toList rep rc readLen oMin verts) →
      (∀ e ∈ edges.head?, e.sx = start) →
      ValidPath readLen (toList start) (graphSteps toList edges) := by
  intro edges
  induction edges with
  | nil =>
      intro start hchain hmem hstart
      simp [graphSteps, ValidPath]
  | cons e rest ih =>
      intro start hchain hmem hstart
      have heStart : e.sx = start := hstart e (by simp)
      have hemem : e ∈ overlapEdges A W toList rep rc readLen oMin verts :=
        hmem e (by simp)
      have hinfo := overlapEdges_mem_iff hemem
      have hv : (toList e.sy).length = readLen :=
        hLen e.sy hinfo.2.2.2.1
      have hu : (toList e.sx).length = readLen :=
        hLen e.sx hinfo.2.2.1
      have hstartLen : (toList start).length = readLen := by
        simpa [heStart] using hu
      have hOverlap : (toList start).drop (readLen - e.len) =
          (toList e.sy).take e.len := by
        simpa [sufOf, preOf, heStart, hstartLen] using hinfo.2.2.2.2
      have hc := hchain
      rw [List.isChain_cons] at hc
      have hrest : ∀ x ∈ rest, x ∈ overlapEdges A W toList rep rc readLen oMin verts := by
        intro x hx
        exact hmem x (by simp [hx])
      have hrestStart : ∀ g ∈ rest.head?, g.sx = e.sy := by
        intro g hg
        exact (hc.1 g hg).symm
      change (toList e.sy).length = readLen ∧ e.len ≤ readLen ∧
        (toList start).drop (readLen-e.len) = (toList e.sy).take e.len ∧
        ValidPath readLen (toList e.sy) (graphSteps toList rest)
      exact ⟨hv, Nat.le_of_lt hinfo.2.1, hOverlap,
        ih e.sy hc.2 hrest hrestStart⟩

/-- The last target read of the projected steps is the last source edge's
arrival strand. This is purely structural and does not assume overlap legality. -/
theorem target_graphSteps_of_last
    (toList : W → List A) :
    ∀ (edges : List (BdEdge A W)) (start sy : W),
      (∃ e, edges.getLast? = some e ∧ e.sy = sy) →
      pathTarget (toList start) (graphSteps toList edges) = toList sy := by
  intro edges
  induction edges with
  | nil =>
      intro start sy hlast
      obtain ⟨e, he, _⟩ := hlast
      simp at he
  | cons e rest ih =>
      intro start sy hlast
      cases rest with
      | nil =>
          obtain ⟨last, hlast', hsy⟩ := hlast
          have he : e = last := by
            simpa using hlast'
          subst last
          simpa [graphSteps, pathTarget] using congrArg toList hsy
      | cons f tail =>
          obtain ⟨last, hlast', hsy⟩ := hlast
          have hlastRest : ∃ last,
              (f :: tail).getLast? = some last ∧ last.sy = sy := by
            refine ⟨last, ?_, hsy⟩
            simpa using hlast'
          simpa [graphSteps, pathTarget] using ih e.sy sy hlastRest

/-- Every genuine signed path in the source complete overlap graph satisfies
the elementary overlap-path conditions, with source endpoints preserved. -/
theorem signedPath_valid_graph_steps
    (toList : W → List A) (rep rc : W → W) (readLen oMin : Nat)
    (verts : List W)
    (hLen : ∀ s ∈ strandsOf rc verts, (toList s).length = readLen)
    (edges : List (BdEdge A W)) (start sy : W)
    (hsp : SignedPath start sy edges)
    (hmem : ∀ e ∈ edges,
      e ∈ overlapEdges A W toList rep rc readLen oMin verts) :
    ValidPath readLen (toList start) (graphSteps toList edges) ∧
      pathTarget (toList start) (graphSteps toList edges) = toList sy := by
  have hfirst : ∀ e ∈ edges.head?, e.sx = start := by
    intro e he
    obtain ⟨e₀, he₀, hs⟩ := hsp.1
    rw [he₀] at he
    have hEq : e = e₀ := by simpa using he.symm
    simpa [hEq] using hs
  refine ⟨valid_graph_steps toList rep rc readLen oMin verts hLen
    edges start hsp.2.2 hmem hfirst, ?_⟩
  exact target_graphSteps_of_last toList edges start sy hsp.2.1

/-- Projected steps append exactly the source spelling's edge tails. -/
theorem graphSteps_tails_eq_pathTail (toList : W → List A)
    (edges : List (BdEdge A W)) :
    (graphSteps toList edges).flatMap (fun p => p.2.drop p.1) =
      pathTail toList edges := by
  induction edges with
  | nil => rfl
  | cons e rest ih =>
      change (toList e.sy).drop e.len ++
          (graphSteps toList rest).flatMap (fun p => p.2.drop p.1) =
        (toList e.sy).drop e.len ++ pathTail toList rest
      exact congrArg (fun tail => (toList e.sy).drop e.len ++ tail) ih

/-- A CLOSED GENUINE SIGNED graph walk has the exact cyclic seam needed
to derive its aligned circular genome. No arbitrary flow is assumed spelled. -/
theorem signed_circuit_seam
    (toList : W → List A) (rep rc : W → W) (readLen oMin : Nat)
    (verts : List W)
    (hLen : ∀ s ∈ strandsOf rc verts, (toList s).length = readLen)
    (edges : List (BdEdge A W)) (start : W)
    (hstart : (toList start).length = readLen)
    (hsp : SignedPath start start edges)
    (hmem : ∀ e ∈ edges,
      e ∈ overlapEdges A W toList rep rc readLen oMin verts) :
    (toList start ++ pathTail toList edges).take readLen =
      (toList start ++ pathTail toList edges).drop (pathTail toList edges).length := by
  obtain ⟨hvalid, htarget⟩ :=
    signedPath_valid_graph_steps toList rep rc readLen oMin verts hLen
      edges start start hsp hmem
  have hseam :=
    closed_path_seam readLen (toList start) (graphSteps toList edges)
      hstart hvalid htarget
  simpa [graphSteps_tails_eq_pathTail] using hseam

/-- Each genuine closed overlap circuit contributes at least one symbol: graph
overlaps are proper, and a SignedPath contains a first edge. -/
theorem signed_circuit_tail_pos
    (toList : W → List A) (rep rc : W → W) (readLen oMin : Nat)
    (verts : List W)
    (hLen : ∀ s ∈ strandsOf rc verts, (toList s).length = readLen)
    (edges : List (BdEdge A W)) (start sy : W)
    (hsp : SignedPath start sy edges)
    (hmem : ∀ e ∈ edges,
      e ∈ overlapEdges A W toList rep rc readLen oMin verts) :
    0 < (pathTail toList edges).length := by
  obtain ⟨e₀, hh, _⟩ := hsp.1
  cases edges with
  | nil => simp at hh
  | cons e rest =>
      have he : e ∈ overlapEdges A W toList rep rc readLen oMin verts :=
        hmem e (by simp)
      have hinfo := overlapEdges_mem_iff he
      have htargetLen : (toList e.sy).length = readLen :=
        hLen e.sy hinfo.2.2.2.1
      have hproper : e.len < readLen := hinfo.2.1
      have htail : 0 < ((toList e.sy).drop e.len).length := by
        simp [htargetLen]
        omega
      rw [pathTail_cons, List.length_append]
      simp only [edgeTail] at *
      omega

/-- The graph-specific aligned circular spelling theorem. It follows from
a genuine CLOSED signed path and proper overlaps, and handles G < readLen. -/
theorem signed_circuit_aligned_periodicity
    (toList : W → List A) (rep rc : W → W) (readLen oMin : Nat)
    (verts : List W)
    (hLen : ∀ s ∈ strandsOf rc verts, (toList s).length = readLen)
    (edges : List (BdEdge A W)) (start : W) (default : A)
    (hstart : (toList start).length = readLen)
    (hsp : SignedPath start start edges)
    (hmem : ∀ e ∈ edges,
      e ∈ overlapEdges A W toList rep rc readLen oMin verts)
    (i : Nat)
    (hi : i < (toList start ++ pathTail toList edges).length) :
    (toList start ++ pathTail toList edges).getD i default =
      ((toList start ++ pathTail toList edges).take
        (pathTail toList edges).length).getD
        (i % (pathTail toList edges).length) default := by
  have hG := signed_circuit_tail_pos toList rep rc readLen oMin verts
    hLen edges start start hsp hmem
  have hseam := signed_circuit_seam toList rep rc readLen oMin verts
    hLen edges start hstart hsp hmem
  have hXlen :
      (toList start ++ pathTail toList edges).length =
        readLen + (pathTail toList edges).length := by
    simp [hstart]
  exact Section62PeriodicSeam.seam_periodic_prefix hG
    (toList start ++ pathTail toList edges) default hXlen hseam i hi

#print axioms target_graphSteps_of_last
#print axioms signedPath_valid_graph_steps
#print axioms graphSteps_tails_eq_pathTail
#print axioms signed_circuit_seam
#print axioms signed_circuit_tail_pos
#print axioms signed_circuit_aligned_periodicity

#print axioms valid_graph_steps

end AssemblyP1.Section62SourceSignedSeamAdapter
