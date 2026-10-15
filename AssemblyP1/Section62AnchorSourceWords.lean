import AssemblyP1.Section62CircularWindowAdapter
import AssemblyP1.Section62OverlapSuffix
import AssemblyP1.Section62AnchoredWindowBridge

/-!
Inductively identify the length-L word at each cumulative overlap-extension
anchor of a legally spelled path, without relying on a theorem about circular
genome windows. This is the missing middle link for Observation 7.
-/

namespace AssemblyP1.Section62AnchorSourceWords

open AssemblyP1.Section62CircularStarts
open AssemblyP1.Section62OverlapSuffix
open AssemblyP1.Section62SourceSignedSeamAdapter
open AssemblyP1.Section62GlobalSpellingPreservation
open AssemblyP1.Section62CircularWindowAdapter
open AssemblyP1.Section62AnchoredWindowBridge
open Section62Flow Section62SpellingReductionCandidate

/-- The read strand at the SOURCE of each edge of a path. -/
def sources {A : Type} (u : List A) : List (Nat × List A) → List (List A)
  | [] => []
  | (_, v) :: steps => u :: sources v steps

def extensionsOf (L : Nat) {A : Type}
    (steps : List (Nat × List A)) : List Nat :=
  steps.map (fun p => L - p.1)

def appendedTails {A : Type} (steps : List (Nat × List A)) : List A :=
  steps.flatMap (fun p => p.2.drop p.1)

/-- Shifting the initial genomic start shifts all anchors by the same amount. -/
theorem anchors_shift (s : Nat) (ds : List Nat) :
    anchors s ds = (anchors 0 ds).map (s + ·) := by
  induction ds generalizing s with
  | nil => simp [anchors]
  | cons d ds ih =>
      simp only [anchors, List.map_cons, Nat.add_zero]
      congr 1
      simp only [Nat.zero_add]
      rw [ih (s+d), ih d, List.map_map]
      apply List.map_congr_left
      intro x hx
      simp [Nat.add_assoc]

/-- Following a true suffix/prefix overlap and dropping its extension
length exposes the target read followed by exactly the remaining spelling. -/
theorem drop_overlap_step {A : Type} (u v tail : List A)
    (L ell : Nat) (hu : u.length = L) (hell : ell ≤ L)
    (hoverlap : u.drop (L - ell) = v.take ell) :
    (u ++ v.drop ell ++ tail).drop (L - ell) = v ++ tail := by
  rw [List.append_assoc]
  rw [List.drop_append_of_le_length (by omega : L - ell ≤ u.length)]
  rw [hoverlap, ← List.append_assoc, List.take_append_drop]

/-- A legal overlap path spells the source strand at every accumulated
extension anchor, in exactly the source-edge order. -/
theorem aligned_source_words {A : Type} (L : Nat) :
    ∀ (steps : List (Nat × List A)) (u : List A),
      u.length = L → ValidPath L u steps →
      (anchors 0 (extensionsOf L steps)).map
        (fun s => ((u ++ appendedTails steps).drop s).take L) =
      sources u steps := by
  intro steps
  induction steps with
  | nil =>
      intro u hu hvalid
      simp [anchors, extensionsOf, appendedTails, sources]
  | cons p rest ih =>
      rcases p with ⟨ell,v⟩
      intro u hu hvalid
      change v.length = L ∧ ell ≤ L ∧
        u.drop (L-ell) = v.take ell ∧ ValidPath L v rest at hvalid
      obtain ⟨hv, hell, hov, hrest⟩ := hvalid
      have hdrop := drop_overlap_step u v (appendedTails rest)
        L ell hu hell hov
      have hrestEq := ih v hv hrest
      simp only [extensionsOf, appendedTails, List.flatMap_cons,
        List.map_cons, anchors, sources]
      simp only [List.drop_zero, Nat.zero_add]
      change (u ++ (v.drop ell ++ appendedTails rest)).take L ::
        (anchors (L-ell) (extensionsOf L rest)).map
           (fun s => ((u ++ (v.drop ell ++ appendedTails rest)).drop s).take L)
            = u :: sources v rest
      have hfirst : (u ++ (v.drop ell ++ appendedTails rest)).take L = u := by
        simp [hu]
      rw [hfirst, List.cons.injEq]
      constructor
      · rfl
      · rw [anchors_shift]
        simp only [List.map_map]
        have hdrop' : (u ++ (v.drop ell ++ appendedTails rest)).drop (L-ell) =
            v ++ appendedTails rest := by
          simpa only [← List.append_assoc] using hdrop
        have hshift : ∀ s : Nat,
          ((u ++ (v.drop ell ++ appendedTails rest)).drop (L - ell + s)).take L =
          ((v ++ appendedTails rest).drop s).take L := by
          intro s
          rw [← List.drop_drop, hdrop']
        calc
          (anchors 0 (extensionsOf L rest)).map
             (fun x => ((u ++ (v.drop ell ++ appendedTails rest)).drop (L-ell+x)).take L)
            = (anchors 0 (extensionsOf L rest)).map
                (fun x => ((v ++ appendedTails rest).drop x).take L) := by
                  apply List.map_congr_left
                  intro x hx
                  exact hshift x
          _ = sources v rest := hrestEq


/-- The projected source-word list of a signed graph path is exactly the
list of departure strands of its actual overlap edges. -/
theorem graph_sources_eq_departures {A W : Type} [DecidableEq W]
    (toList : W → List A) :
    ∀ (walk : List (BdEdge A W)) (start : W),
      walk.IsChain Step →
      (∀ e ∈ walk.head?, e.sx = start) →
      sources (toList start) (graphSteps toList walk) =
        walk.map (fun e => toList e.sx) := by
  intro walk
  induction walk with
  | nil =>
      intro start hc hfirst
      rfl
  | cons e rest ih =>
      intro start hc hfirst
      have heStart : e.sx = start := hfirst e (by simp)
      have hc' := hc
      rw [List.isChain_cons] at hc'
      have hrestStart : ∀ g ∈ rest.head?, g.sx = e.sy := by
        intro g hg
        exact (hc'.1 g hg).symm
      change toList start :: sources (toList e.sy) (graphSteps toList rest) =
        toList e.sx :: rest.map (fun e => toList e.sx)
      rw [heStart]
      congr 1
      exact ih e.sy hc'.2 hrestStart

/-- Graph-specific linear version of the anchor-word identity: the read
starting at each accumulated extension is the source strand of its edge. -/
theorem signed_circuit_anchors_linear {A W : Type}
    [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rep rc : W → W) (L oMin : Nat)
    (verts : List W)
    (hLen : ∀ r ∈ strandsOf rc verts, (toList r).length = L)
    (walk : List (BdEdge A W)) (start : W)
    (hStart : (toList start).length = L)
    (hsp : SignedPath start start walk)
    (hmem : ∀ e ∈ walk, e ∈ overlapEdges A W toList rep rc L oMin verts) :
    (anchors 0 (extensions L walk)).map
      (fun s => ((toList start ++ pathTail toList walk).drop s).take L) =
        walk.map (fun e => toList e.sx) := by
  obtain ⟨hvalid, _⟩ :=
    signedPath_valid_graph_steps toList rep rc L oMin verts
      hLen walk start start hsp hmem
  have hraw := aligned_source_words L (graphSteps toList walk)
    (toList start) hStart hvalid
  have hsteps : extensionsOf L (graphSteps toList walk) = extensions L walk := by
    simp [extensionsOf, graphSteps, extensions, extension, List.map_map,
      Function.comp_def]
  have htails : appendedTails (graphSteps toList walk) =
      pathTail toList walk :=
    graphSteps_tails_eq_pathTail toList walk
  have hfirst : ∀ e ∈ walk.head?, e.sx = start := by
    intro e he
    obtain ⟨e₀, he₀, hs⟩ := hsp.1
    rw [he₀] at he
    have hEq : e = e₀ := by simpa using he.symm
    simpa [hEq] using hs
  have hsources :=
    graph_sources_eq_departures toList walk start hsp.2.2 hfirst
  simpa [hsteps, htails, hsources] using hraw


/-- Every anchor belongs to its own positive-extension range; no anchor
passes the total extension length (so every anchor is a circular position). -/
theorem anchors_lt_sum (ds : List Nat)
    (hpos : ∀ d ∈ ds, 0 < d) :
    ∀ s ∈ anchors 0 ds, s < ds.sum := by
  induction ds with
  | nil =>
      intro s hs
      simp [anchors] at hs
  | cons d ds ih =>
      intro s hs
      have hd : 0 < d := hpos d (by simp)
      have hrest : ∀ t ∈ ds, 0 < t := fun t ht => hpos t (by simp [ht])
      simp only [anchors] at hs
      rcases List.mem_cons.mp hs with rfl | hs
      · simp only [List.sum_cons]
        omega
      · rw [anchors_shift] at hs
        obtain ⟨t, ht, heq⟩ := List.mem_map.mp hs
        have hlt : t < ds.sum := ih hrest t ht
        simp only [List.sum_cons]
        omega

/-- Every genuine overlap-graph edge extends the spelling by at least one
symbol. Proper overlaps are a graph membership fact, not an extra assumption. -/
theorem graph_extensions_pos {A W : Type} [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rep rc : W → W) (L oMin : Nat)
    (verts : List W) (walk : List (BdEdge A W))
    (hmem : ∀ e ∈ walk, e ∈ overlapEdges A W toList rep rc L oMin verts) :
    ∀ d ∈ extensions L walk, 0 < d := by
  intro d hd
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  have heGraph := overlapEdges_mem_iff (hmem e he)
  change 0 < L - e.len
  omega

/-- The spelled tail length is exactly the sum of the proper overlap
extension lengths, not merely bounded by it. -/
theorem pathTail_len_eq_extensions_sum {A W : Type}
    [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rep rc : W → W) (L oMin : Nat)
    (verts : List W)
    (hLen : ∀ r ∈ strandsOf rc verts, (toList r).length = L) :
    ∀ (walk : List (BdEdge A W)),
      (∀ e ∈ walk, e ∈ overlapEdges A W toList rep rc L oMin verts) →
      (pathTail toList walk).length = (extensions L walk).sum := by
  intro walk
  induction walk with
  | nil =>
      intro hmem
      rfl
  | cons e rest ih =>
      intro hmem
      have heGraph := overlapEdges_mem_iff (hmem e (by simp))
      have hv : (toList e.sy).length = L :=
        hLen e.sy heGraph.2.2.2.1
      have hmemRest : ∀ e' ∈ rest,
          e' ∈ overlapEdges A W toList rep rc L oMin verts :=
        fun e' he' => hmem e' (by simp [he'])
      have hrest := ih hmemRest
      simp only [pathTail_cons, List.length_append, edgeTail,
        List.length_drop, extensions, List.map_cons, List.sum_cons, extension]
      rw [hv]
      simpa [extensions] using congrArg (fun n : Nat => L - e.len + n) hrest

/-- The previously abstract CircularSpelling.hAnchors clause follows
automatically from actual closed SignedPath legality and the source overlap
graph, for any genome length including G shorter than a read. -/
theorem signed_circuit_anchors_are_read_words {A W : Type}
    [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rep rc : W → W) (L oMin : Nat)
    (verts : List W) (default : A)
    (hLen : ∀ r ∈ strandsOf rc verts, (toList r).length = L)
    (walk : List (BdEdge A W)) (start : W)
    (hStart : (toList start).length = L)
    (hsp : SignedPath start start walk)
    (hmem : ∀ e ∈ walk, e ∈ overlapEdges A W toList rep rc L oMin verts) :
    (anchors 0 (extensions L walk)).map
       (window ((toList start ++ pathTail toList walk).take
         (pathTail toList walk).length) L) =
    walk.map (fun e => toList e.sx) := by
  have hpos := graph_extensions_pos toList rep rc L oMin verts walk hmem
  have hsum := pathTail_len_eq_extensions_sum toList rep rc L oMin verts hLen
    walk hmem
  have hLinear := signed_circuit_anchors_linear toList rep rc L oMin verts
    hLen walk start hStart hsp hmem
  calc
    (anchors 0 (extensions L walk)).map
        (window ((toList start ++ pathTail toList walk).take
          (pathTail toList walk).length) L) =
      (anchors 0 (extensions L walk)).map
        (fun s => ((toList start ++ pathTail toList walk).drop s).take L) := by
        apply List.map_congr_left
        intro s hs
        have hsBound : s < (extensions L walk).sum :=
          anchors_lt_sum (extensions L walk) hpos s hs
        have hsTail : s < (pathTail toList walk).length := by omega
        exact signed_circuit_window_eq_linear
          toList rep rc L oMin verts default hLen walk start
          hStart hsp hmem s hsTail
    _ = walk.map (fun e => toList e.sx) := hLinear

#print axioms anchors_lt_sum
#print axioms graph_extensions_pos
#print axioms pathTail_len_eq_extensions_sum
#print axioms signed_circuit_anchors_are_read_words

#print axioms graph_sources_eq_departures
#print axioms signed_circuit_anchors_linear

#print axioms anchors_shift
#print axioms drop_overlap_step
#print axioms aligned_source_words

end AssemblyP1.Section62AnchorSourceWords
