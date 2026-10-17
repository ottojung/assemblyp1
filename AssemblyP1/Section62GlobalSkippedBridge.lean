import AssemblyP1.Section62AnchorSourceWords
import AssemblyP1.Section62SkippedWindowFactor

/-!
The remaining geometric bridge for #284. A path of legal overlaps cannot
create an observed internal read at any global spelled-word offset if none
of its individual direct overlap edges does so locally. The later source
specialization must obtain that local fact from surviving reduced edges.
-/

namespace AssemblyP1.Section62GlobalSkippedBridge

open AssemblyP1.Section62CircularStarts
open AssemblyP1.Section62SkippedWindowFactor
open AssemblyP1.Section62AnchorSourceWords
open AssemblyP1.Section62OverlapSuffix
open AssemblyP1.Section62CircularWindowAdapter
open AssemblyP1.Section62AnchoredWindowBridge
open AssemblyP1.Section62SourceSignedSeamAdapter
open AssemblyP1.Section62GlobalSpellingPreservation
open Section62Flow Section62SpellingReductionCandidate

/-- Each internal offset of each direct edge spells no observed word. -/
def NoObservedSteps {A : Type} (L : Nat) (obs : List (List A))
    (u : List A) : List (Nat × List A) → Prop
  | [] => True
  | (ell,v)::rest =>
      (∀ t, 0 < t → t < L - ell → ∀ w ∈ obs,
         ((u ++ v.drop ell).drop t).take L ≠ w) ∧
      NoObservedSteps L obs v rest

/-- All interior starts of a list of extension blocks are at or after the
given initial start. -/
theorem interiors_ge_start (start : Nat) (ds : List Nat) (s : Nat)
    (hs : s ∈ interiors start ds) : start ≤ s := by
  induction ds generalizing start with
  | nil => simp [interiors] at hs
  | cons d ds ih =>
      change s ∈ List.Ico (start+1) (start+d) ++ interiors (start+d) ds at hs
      rcases List.mem_append.mp hs with hfirst | hrest
      · have hb : start+1 ≤ s ∧ s < start+d := by
          simpa using hfirst
        omega
      · have h := ih (start+d) hrest
        omega

/-- Adding an arbitrary suffix cannot alter a length-L window that fits
wholly inside the already-spelled prefix. -/
theorem window_unchanged_by_append {A : Type}
    (pref suffix : List A) (t L : Nat)
    (ht : t + L ≤ pref.length) :
    ((pref ++ suffix).drop t).take L = (pref.drop t).take L := by
  rw [List.drop_append_of_le_length (by omega : t ≤ pref.length)]
  apply List.take_append_of_le_length
  simp [List.length_drop]
  omega

/-- Global no-skips from local no-skips for any legal overlap path, with
arbitrary genomic coordinate origin. The path's word is not assumed circular. -/
theorem aligned_interiors_no_observed_aux {A : Type}
    (L : Nat) (obs : List (List A)) :
    ∀ (steps : List (Nat × List A)) (u : List A) (start : Nat),
      u.length = L →
      ValidPath L u steps →
      NoObservedSteps L obs u steps →
      ∀ s ∈ interiors start (extensionsOf L steps), ∀ w ∈ obs,
        ((u ++ appendedTails steps).drop (s-start)).take L ≠ w := by
  intro steps
  induction steps with
  | nil =>
      intro u start hu hv hn s hs w hw
      simp [interiors, extensionsOf] at hs
  | cons p rest ih =>
      rcases p with ⟨ell,v⟩
      intro u start hu hv hn s hs w hw
      change v.length = L ∧ ell ≤ L ∧
          u.drop (L-ell) = v.take ell ∧ ValidPath L v rest at hv
      obtain ⟨hvlen, hell, hov, hvrest⟩ := hv
      change (∀ t, 0<t → t<L-ell → ∀ w∈obs,
         ((u ++ v.drop ell).drop t).take L ≠ w) ∧
          NoObservedSteps L obs v rest at hn
      obtain ⟨hnLocal, hnRest⟩ := hn
      change s ∈ List.Ico (start+1) (start+(L-ell)) ++
          interiors (start+(L-ell)) (extensionsOf L rest) at hs
      rcases List.mem_append.mp hs with hfirst | hrest
      · have hb : start+1 ≤ s ∧ s < start+(L-ell) := by
          simpa using hfirst
        have ht : 0 < s-start ∧ s-start < L-ell := by omega
        have hlen : (u ++ v.drop ell).length = L + (L-ell) := by
          simp [hu, hvlen]
        have hwin : s-start+L ≤ (u ++ v.drop ell).length := by omega
        have heq := window_unchanged_by_append
          (u ++ v.drop ell) (appendedTails rest) (s-start) L hwin
        have hlocal := hnLocal (s-start) ht.1 ht.2 w hw
        change ((u ++ (v.drop ell ++ appendedTails rest)).drop (s-start)).take L ≠ w
        rw [← List.append_assoc, heq]
        exact hlocal
      · have hstart := interiors_ge_start
          (start+(L-ell)) (extensionsOf L rest) s hrest
        have hshift : s-start = (L-ell) + (s-(start+(L-ell))) := by omega
        have hdrop := drop_overlap_step u v (appendedTails rest)
          L ell hu hell hov
        have htail := ih v (start+(L-ell)) hvlen hvrest hnRest
          s hrest w hw
        change ((u ++ (v.drop ell ++ appendedTails rest)).drop (s-start)).take L ≠ w
        rw [← List.append_assoc, hshift, ← List.drop_drop, hdrop]
        exact htail

/-- The initial-start-zero specialization used by CircularSpelling. -/
theorem aligned_interiors_no_observed {A : Type}
    (L : Nat) (obs : List (List A))
    (steps : List (Nat × List A)) (u : List A)
    (hu : u.length = L)
    (hv : ValidPath L u steps)
    (hn : NoObservedSteps L obs u steps) :
    ∀ s ∈ interiors 0 (extensionsOf L steps), ∀ w ∈ obs,
       ((u ++ appendedTails steps).drop s).take L ≠ w := by
  simpa using aligned_interiors_no_observed_aux L obs steps u 0 hu hv hn


/-- The spelling-reduced source graph supplies the recursive no-observed-
internal-window property used by the generic linear spelling theorem. -/
theorem reduced_graph_no_observed_steps {A W : Type}
    [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rep rc : W → W)
    (L oMin : Nat) (verts : List W)
    (hLen : ∀ m ∈ strandsOf rc verts, (toList m).length = L) :
    ∀ (walk : List (BdEdge A W)) (start : W),
      walk.IsChain Step →
      (∀ e ∈ walk,
        e ∈ transitivelyReducedSpelling W toList rc L oMin verts
          (overlapEdges A W toList rep rc L oMin verts)) →
      (∀ e ∈ walk.head?, e.sx = start) →
      NoObservedSteps L ((strandsOf rc verts).map toList)
        (toList start) (graphSteps toList walk) := by
  intro walk
  induction walk with
  | nil =>
      intro start hc hmem hfirst
      trivial
  | cons e rest ih =>
      intro start hc hmem hfirst
      have hstart : e.sx = start := hfirst e (by simp)
      have heReduced := hmem e (by simp)
      have heGraph : e ∈ overlapEdges A W toList rep rc L oMin verts :=
        (List.mem_filter.mp heReduced).1
      have hinfo := overlapEdges_mem_iff heGraph
      have hsx : (toList e.sx).length = L := hLen e.sx hinfo.2.2.1
      have hsy : (toList e.sy).length = L := hLen e.sy hinfo.2.2.2.1
      have hlocal : ∀ t, 0<t → t<L-e.len →
          ∀ w ∈ (strandsOf rc verts).map toList,
            ((toList start ++ (toList e.sy).drop e.len).drop t).take L ≠ w := by
        intro t ht0 ht w hw
        obtain ⟨m,hm,hw⟩ := List.mem_map.mp hw
        have hno := surviving_edge_skips_no_observed_strand
          toList rc L oMin verts
          (overlapEdges A W toList rep rc L oMin verts)
          e hsx hsy hinfo.2.1 hinfo.1 hinfo.2.2.2.2
          heReduced t ht0 ht
        intro heq
        apply hno
        refine ⟨m, hm, ?_⟩
        rw [← hstart] at heq
        simpa [spellDirect] using (hw.trans heq.symm)
      have hc' := hc
      rw [List.isChain_cons] at hc'
      have hmemRest : ∀ e' ∈ rest,
          e' ∈ transitivelyReducedSpelling W toList rc L oMin verts
            (overlapEdges A W toList rep rc L oMin verts) :=
        fun e' he' => hmem e' (by simp [he'])
      have hrestStart : ∀ g ∈ rest.head?, g.sx = e.sy := by
        intro g hg
        exact (hc'.1 g hg).symm
      change (∀ t, 0<t → t<L-e.len →
          ∀ w ∈ (strandsOf rc verts).map toList,
          ((toList start ++ (toList e.sy).drop e.len).drop t).take L ≠ w) ∧
        NoObservedSteps L ((strandsOf rc verts).map toList)
          (toList e.sy) (graphSteps toList rest)
      exact ⟨hlocal, ih e.sy hc'.2 hmemRest hrestStart⟩


/-- No internal start can reach or exceed the end of the concatenated
extension blocks, even if some extension lengths are zero. -/
theorem interiors_lt_total (start : Nat) (ds : List Nat) (s : Nat)
    (hs : s ∈ interiors start ds) : s < start + ds.sum := by
  induction ds generalizing start with
  | nil => simp [interiors] at hs
  | cons d ds ih =>
      change s ∈ List.Ico (start+1) (start+d) ++ interiors (start+d) ds at hs
      rcases List.mem_append.mp hs with hfirst | hrest
      · have hb : start+1 ≤ s ∧ s < start+d := by
          simpa using hfirst
        simp only [List.sum_cons]
        omega
      · have h := ih (start+d) hrest
        simp only [List.sum_cons]
        omega

/-- The missing no-skipped-observed-window clause of CircularSpelling
is automatic for a genuine CLOSED signed walk whose every edge survives the
spelling-preserving overlap-graph reduction. It is NOT assumed as a premise. -/
theorem reduced_signed_circuit_no_skipped_windows {A W : Type}
    [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rep rc : W → W)
    (L oMin : Nat) (verts : List W) (default : A)
    (hLen : ∀ m ∈ strandsOf rc verts, (toList m).length = L)
    (walk : List (BdEdge A W)) (start : W)
    (hStart : (toList start).length = L)
    (hsp : SignedPath start start walk)
    (hsurv : ∀ e ∈ walk,
       e ∈ transitivelyReducedSpelling W toList rc L oMin verts
         (overlapEdges A W toList rep rc L oMin verts)) :
    ∀ m ∈ strandsOf rc verts,
      wordCount (toList m)
        ((interiors 0 (extensions L walk)).map
          (window ((toList start ++ pathTail toList walk).take
            (pathTail toList walk).length) L)) = 0 := by
  have hmem : ∀ e ∈ walk,
      e ∈ overlapEdges A W toList rep rc L oMin verts :=
    fun e he => (List.mem_filter.mp (hsurv e he)).1
  have hvalid := (signedPath_valid_graph_steps toList rep rc L oMin verts
    hLen walk start start hsp hmem).1
  have hfirst : ∀ e ∈ walk.head?, e.sx = start := by
    intro e he
    obtain ⟨e₀, he₀, hs⟩ := hsp.1
    rw [he₀] at he
    have hEq : e = e₀ := by simpa using he.symm
    simpa [hEq] using hs
  have hn := reduced_graph_no_observed_steps toList rep rc L oMin verts
    hLen walk start hsp.2.2 hsurv hfirst
  have hlinear := aligned_interiors_no_observed L
    ((strandsOf rc verts).map toList) (graphSteps toList walk)
    (toList start) hStart hvalid hn
  have hsteps : extensionsOf L (graphSteps toList walk) =
      extensions L walk := by
    simp [extensionsOf, graphSteps, extensions, extension, List.map_map,
      Function.comp_def]
  have htails : appendedTails (graphSteps toList walk) =
      pathTail toList walk :=
    graphSteps_tails_eq_pathTail toList walk
  have hsum := pathTail_len_eq_extensions_sum toList rep rc L oMin
    verts hLen walk hmem
  intro m hm
  apply interior_count_zero_of_pointwise toList
  intro s hs
  have hsBound : s < (extensions L walk).sum := by
    have h := interiors_lt_total 0 (extensions L walk) s hs
    omega
  have hsTail : s < (pathTail toList walk).length := by omega
  have hwin := signed_circuit_window_eq_linear
    toList rep rc L oMin verts default hLen walk start
    hStart hsp hmem s hsTail
  have hLin : ((toList start ++ pathTail toList walk).drop s).take L ≠
      toList m := by
    have hs' : s ∈ interiors 0 (extensionsOf L (graphSteps toList walk)) := by
      simpa [hsteps] using hs
    have hword : toList m ∈ (strandsOf rc verts).map toList :=
      List.mem_map.mpr ⟨m, hm, rfl⟩
    simpa [htails] using hlinear s hs' (toList m) hword
  rw [hwin]
  exact hLin


/-- Every CLOSED signed walk in the implemented spelling-reduced graph
constructs a concrete circular genome satisfying ALL THREE fields of the
CircularSpelling interface. No coherence or no-skips field is assumed. -/
theorem reduced_signed_circuit_circular_spelling {A W : Type}
    [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rep rc : W → W)
    (L oMin : Nat) (verts : List W) (default : A)
    (hLen : ∀ m ∈ strandsOf rc verts, (toList m).length = L)
    (walk : List (BdEdge A W)) (start : W)
    (hStart : (toList start).length = L)
    (hsp : SignedPath start start walk)
    (hsurv : ∀ e ∈ walk,
       e ∈ transitivelyReducedSpelling W toList rc L oMin verts
         (overlapEdges A W toList rep rc L oMin verts)) :
    CircularSpelling toList rc L oMin verts walk
      ((toList start ++ pathTail toList walk).take
        (pathTail toList walk).length) := by
  have hmem : ∀ e ∈ walk,
      e ∈ overlapEdges A W toList rep rc L oMin verts :=
    fun e he => (List.mem_filter.mp (hsurv e he)).1
  have hG : (pathTail toList walk).length ≤
      (toList start ++ pathTail toList walk).length := by simp
  have hLength :
      ((toList start ++ pathTail toList walk).take
        (pathTail toList walk).length).length =
        (extensions L walk).sum := by
    rw [List.length_take, Nat.min_eq_left hG]
    exact pathTail_len_eq_extensions_sum toList rep rc L oMin
      verts hLen walk hmem
  exact ⟨hLength,
    signed_circuit_anchors_are_read_words toList rep rc L oMin verts
      default hLen walk start hStart hsp hmem,
    reduced_signed_circuit_no_skipped_windows toList rep rc L oMin
      verts default hLen walk start hStart hsp hsurv⟩

/-- Source-faithful Observation 7 for the IMPLEMENTED spelling-preserving
reduction: every observed oriented read word occurs in the actual circular
genome exactly as many times as it is visited as an edge departure strand.
This counts ALL G circular starts, including repeated wraps when G<L. -/
theorem observation7_reduced_signed_circuit_range_count {A W : Type}
    [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rep rc : W → W)
    (L oMin : Nat) (verts : List W) (default : A)
    (hLen : ∀ m ∈ strandsOf rc verts, (toList m).length = L)
    (walk : List (BdEdge A W)) (start : W)
    (hStart : (toList start).length = L)
    (hsp : SignedPath start start walk)
    (hsurv : ∀ e ∈ walk,
       e ∈ transitivelyReducedSpelling W toList rc L oMin verts
         (overlapEdges A W toList rep rc L oMin verts))
    (m : W) (hm : m ∈ strandsOf rc verts) :
    let D := (toList start ++ pathTail toList walk).take
      (pathTail toList walk).length
    wordCount (toList m) ((List.range D.length).map (window D L)) =
      wordCount (toList m) (walk.map (fun e => toList e.sx)) := by
  have hmem : ∀ e ∈ walk,
      e ∈ overlapEdges A W toList rep rc L oMin verts :=
    fun e he => (List.mem_filter.mp (hsurv e he)).1
  have hpos := graph_extensions_pos toList rep rc L oMin verts walk hmem
  have hCS := reduced_signed_circuit_circular_spelling
    toList rep rc L oMin verts default hLen walk start hStart hsp hsurv
  exact observation7_range_count toList rc L oMin verts walk
    ((toList start ++ pathTail toList walk).take
      (pathTail toList walk).length) hCS hpos m hm

#print axioms reduced_signed_circuit_circular_spelling
#print axioms observation7_reduced_signed_circuit_range_count

#print axioms interiors_lt_total
#print axioms reduced_signed_circuit_no_skipped_windows

#print axioms reduced_graph_no_observed_steps

#print axioms interiors_ge_start
#print axioms window_unchanged_by_append
#print axioms aligned_interiors_no_observed_aux
#print axioms aligned_interiors_no_observed

end AssemblyP1.Section62GlobalSkippedBridge
