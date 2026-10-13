import Mathlib
import AssemblyP1.Section62SpellingReductionCandidate

/-!
# Global spelling reduction: path-tail algebra and well-founded expansion

This module proves the global per-edge spelling-preservation statement for the
candidate overlap reduction of `Section62SpellingReductionCandidate`: every
edge of the complete `overlapEdges` graph expands, by strong induction on the
extension weight `readLen − e.len`, into a signed path of *reduced*-graph
edges with the same endpoints and the same spelled tail.

The reading of transitive edge reduction used here is the longer-replacement
overlaps reading (SAGE 2014): a detour's two overlaps are strictly longer than
the removed edge's overlap, so the extension weight strictly decreases and the
recursion terminates.  The literal MB09 §6.2 "two shorter overlaps" reading is
numerically vacuous (see `Section62ReductionVacuityAudit`); exact MB09 source
fidelity and Observation 7 throughput equivalence remain separate and open.
Global walk-language preservation (concatenating the per-edge expansions along
a walk) is not proved here.
-/

namespace AssemblyP1.Section62GlobalSpellingPreservation

set_option maxHeartbeats 4000000

open Section62Flow Section62SpellingReductionCandidate

variable {A W : Type} [DecidableEq W]

/-- The newly spelled letters contributed by a given oriented overlap edge. -/
def edgeTail (toList : W → List A) (e : BdEdge A W) : List A :=
  (toList e.sy).drop e.len

/-- The extension spelled by a sequence of overlap edges. -/
def pathTail (toList : W → List A) (edges : List (BdEdge A W)) : List A :=
  edges.flatMap (edgeTail toList)

theorem pathTail_nil (toList : W → List A) :
    pathTail toList [] = [] := by
  rfl

theorem pathTail_cons (toList : W → List A)
    (e : BdEdge A W) (edges : List (BdEdge A W)) :
    pathTail toList (e :: edges) = edgeTail toList e ++ pathTail toList edges := by
  rfl

theorem pathTail_append (toList : W → List A)
    (left right : List (BdEdge A W)) :
    pathTail toList (left ++ right) =
      pathTail toList left ++ pathTail toList right := by
  induction left with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.cons_append, pathTail_cons, ih, List.append_assoc]

#print axioms pathTail_append

/-! ## The two-edge tail identity

Under the composition law `l₁ + l₂ = L + l` with genuine proper overlaps and a
common read length `L`, the direct edge's tail factors through the detour legs:
`C(direct) = C(leg₁) ++ C(leg₂)`.  This is the exact cancellation step that
makes the well-founded expansion preserve the spelled word. -/

theorem tail_detour_eq_tail_direct (toList : W → List A) (rep : W → W)
    (sx m sy : W) (L l1 l2 l : Nat)
    (hsx : (toList sx).length = L) (hm : (toList m).length = L)
    (hsy : (toList sy).length = L)
    (hl1 : l1 < L) (hl2 : l2 < L) (hl : l < L)
    (hov1 : sufOf (toList sx) l1 = preOf (toList m) l1)
    (hov2 : sufOf (toList m) l2 = preOf (toList sy) l2)
    (hcomp : l1 + l2 = L + l) :
    edgeTail toList (bdEdge rep sx m l1) ++ edgeTail toList (bdEdge rep m sy l2)
      = edgeTail toList (bdEdge rep sx sy l) := by
  have h := spellPath_eq_spellDirect hsx hm hsy hl1 hl2 hl hov1 hov2 hcomp
  unfold spellPath spellDirect at h
  rw [List.append_assoc] at h
  obtain ⟨-, h'⟩ := List.append_inj h rfl
  unfold edgeTail bdEdge
  exact h'

#print axioms tail_detour_eq_tail_direct

/-! ## Signed paths

A signed path is a list of edges whose first edge departs from `sx`, whose last
edge arrives at `sy`, and whose consecutive edges are adjacent: the arrival
strand of one edge is the departure strand of the next.  For `bdEdge`-
constructed edges (all graph edges), adjacent edges also have opposite
incidences at the common oriented strand (`bdEdge_step_signs_opposite`), which
is the MB09 §3.2 signed-walk condition. -/

/-- Two edges are adjacent when the arrival strand of the first is the departure
strand of the second. -/
def Step (f g : BdEdge A W) : Prop :=
  f.sy = g.sx

/-- A signed path from `sx` to `sy`. -/
def SignedPath (sx sy : W) (edges : List (BdEdge A W)) : Prop :=
  (∃ e₀, edges.head? = some e₀ ∧ e₀.sx = sx) ∧
  (∃ e₁, edges.getLast? = some e₁ ∧ e₁.sy = sy) ∧
  edges.IsChain Step

theorem sgnRep_neg_sgnTgt (s : W) (rep : W → W) :
    sgnRep s (rep s) = -sgnTgt s (rep s) := by
  unfold sgnRep sgnTgt
  split_ifs <;> omega

/-- For `bdEdge`-constructed edges (all graph edges), adjacent edges have
opposite incidences at the common oriented strand (MB09 §3.2). -/
theorem bdEdge_step_signs_opposite (rep : W → W) (sx m sy : W) (l1 l2 : Nat) :
    (@bdEdge A W _ rep sx m l1).sgnY = -(@bdEdge A W _ rep m sy l2).sgnX := by
  show sgnTgt m (rep m) = -sgnRep m (rep m)
  have h := sgnRep_neg_sgnTgt m rep
  omega

theorem signedPath_single {sx sy : W} {e : BdEdge A W} :
    SignedPath sx sy [e] ↔ e.sx = sx ∧ e.sy = sy := by
  constructor
  · intro h
    obtain ⟨e₀, hh0, hxs⟩ := h.1
    obtain ⟨e₁, hl1, hys⟩ := h.2.1
    have he₀ : e₀ = e := by simp at hh0; rw [hh0.symm]
    have he₁ : e₁ = e := by simp at hl1; rw [hl1.symm]
    exact ⟨by rw [he₀.symm]; exact hxs, by rw [he₁.symm]; exact hys⟩
  · intro h
    obtain ⟨hxs, hys⟩ := h
    exact ⟨⟨e, rfl, hxs⟩, ⟨e, rfl, hys⟩, List.isChain_singleton e⟩

theorem signedPath_concat {sx m sy : W}
    {p1 p2 : List (BdEdge A W)}
    (h1 : SignedPath sx m p1) (h2 : SignedPath m sy p2) :
    SignedPath sx sy (p1 ++ p2) := by
  obtain ⟨⟨e0, hh0, hxs⟩, ⟨e1, hl1, hys⟩, hc1⟩ := h1
  obtain ⟨⟨e0', hh0', hxs'⟩, ⟨e1', hl1', hys'⟩, hc2⟩ := h2
  have hp1ne : p1 ≠ [] := by intro hp; subst hp; simp at hh0
  have hp2ne : p2 ≠ [] := by intro hp; subst hp; simp at hh0'
  refine ⟨⟨e0, ?_, hxs⟩, ⟨e1', ?_, hys'⟩, ?_⟩
  · rw [List.head?_append_of_ne_nil _ hp1ne, hh0]
  · rw [List.getLast?_append_of_ne_nil _ hp2ne, hl1']
  · apply List.IsChain.append hc1 hc2
    intro x hx y hy
    have hx' : e1 = x := Option.some_inj.mp (hl1.symm.trans hx)
    have hy' : e0' = y := Option.some_inj.mp (hh0'.symm.trans hy)
    rw [hx'.symm, hy'.symm]
    exact (hys.trans hxs'.symm)

#print axioms signedPath_concat

/-! ## Well-founded expansion on the extension weight

For an edge `e` of the complete `overlapEdges` graph of uniform read length
`readLen`, the *extension weight* is `readLen − e.len`: the number of letters
the edge contributes beyond the first read.  A reducible edge's detour legs
have strictly *longer* overlaps (`replacement_overlaps_longer`), hence strictly
*smaller* extension weight; full-overlap edges are never reducible
(`fullOverlap_not_reducible`).  Strong induction on the extension weight
therefore terminates and expands every graph edge into a signed path of
*reduced*-graph edges with the same endpoints and the same tail. -/

/-- **Global per-edge spelling preservation.**  Every edge `e` of the complete
`overlapEdges` graph expands into a signed path `p` of edges of the
*transitively reduced* graph such that `p` has the same endpoints as `e` and
spells the same tail: `pathTail p = edgeTail e`. -/
theorem exists_surviving_signed_path [DecidableEq A]
    (toList : W → List A) (rep rc : W → W) (readLen oMin : Nat) (verts : List W)
    (hLen : ∀ s ∈ strandsOf rc verts, (toList s).length = readLen)
    (e : BdEdge A W) (he : e ∈ overlapEdges A W toList rep rc readLen oMin verts) :
    ∃ p : List (BdEdge A W),
      SignedPath e.sx e.sy p ∧
        (∀ g ∈ p, g ∈ transitivelyReducedSpelling W toList rc readLen oMin verts
          (overlapEdges A W toList rep rc readLen oMin verts)) ∧
        pathTail toList p = edgeTail toList e := by
  have key : ∀ k f, readLen - f.len = k →
      f ∈ overlapEdges A W toList rep rc readLen oMin verts →
      ∃ p, SignedPath f.sx f.sy p ∧
        (∀ g ∈ p, g ∈ transitivelyReducedSpelling W toList rc readLen oMin verts
          (overlapEdges A W toList rep rc readLen oMin verts)) ∧
        pathTail toList p = edgeTail toList f := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro f hkf hf
      have hmem := overlapEdges_mem_iff hf
      by_cases hred : isReducibleSpelling W toList rc readLen oMin verts f
      · unfold isReducibleSpelling isReducibleSpellingB at hred
        simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hred
        obtain ⟨m, hm, l1, hl1, l2, hl2, hconds⟩ := hred
        rcases hconds with ⟨⟨⟨⟨ho1, ho2⟩, hov1⟩, hov2⟩, hcomp⟩
        have hl1' : l1 < readLen := List.mem_range.mp hl1
        have hl2' : l2 < readLen := List.mem_range.mp hl2
        have hlong : f.len < l1 ∧ f.len < l2 :=
          replacement_overlaps_longer readLen f.len l1 l2 hl1' hl2' hcomp
        have hleg1 : bdEdge rep f.sx m l1 ∈ overlapEdges A W toList rep rc readLen oMin verts :=
          bdEdge_mem_overlapEdges hmem.2.2.1 hm ⟨ho1, hl1'⟩ hov1
        have hleg2 : bdEdge rep m f.sy l2 ∈ overlapEdges A W toList rep rc readLen oMin verts :=
          bdEdge_mem_overlapEdges hm hmem.2.2.2.1 ⟨ho2, hl2'⟩ hov2
        have hkey1 : readLen - l1 < k := by omega
        have hkey2 : readLen - l2 < k := by omega
        obtain ⟨p1, hp1, hsurv1, htail1⟩ := ih _ hkey1 (bdEdge rep f.sx m l1) rfl hleg1
        obtain ⟨p2, hp2, hsurv2, htail2⟩ := ih _ hkey2 (bdEdge rep m f.sy l2) rfl hleg2
        refine ⟨p1 ++ p2, signedPath_concat hp1 hp2, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.mp hg with hg | hg
          · exact hsurv1 g hg
          · exact hsurv2 g hg
        · rw [pathTail_append, htail1, htail2]
          exact tail_detour_eq_tail_direct toList rep f.sx m f.sy readLen l1 l2 f.len
            (hLen f.sx hmem.2.2.1) (hLen m hm) (hLen f.sy hmem.2.2.2.1)
            hl1' hl2' hmem.2.1 hov1 hov2 hcomp
      · refine ⟨[f], signedPath_single.mpr ⟨rfl, rfl⟩, ?_, ?_⟩
        · intro g hg
          rw [List.mem_singleton.mp hg]
          have hb : isReducibleSpellingB W toList rc readLen oMin verts f = false := by
            cases hb' : isReducibleSpellingB W toList rc readLen oMin verts f with
            | false => rfl
            | true =>
              have hred' : isReducibleSpelling W toList rc readLen oMin verts f := hb'
              exact absurd hred' hred
          unfold transitivelyReducedSpelling
          exact List.mem_filter.mpr ⟨hf, by simp [hb]⟩
        · simp [pathTail_cons, pathTail_nil]
  exact key _ e rfl he

#print axioms exists_surviving_signed_path

end AssemblyP1.Section62GlobalSpellingPreservation
