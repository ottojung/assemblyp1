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

Two global statements are proved here.  First, every graph edge expands into a
signed path of *transitively reduced* edges with the same endpoints, the same
spelled tail, and opposite incidences at every common oriented strand
(MB09 §3.2): `exists_surviving_signed_path_signed`.  Second, the per-edge
expansions concatenate along any signed walk of graph edges into a single
signed path of surviving edges spelling the same word:
`global_walk_signed_expansion`.  The actual MB09/Myers algorithm, its
equivalence to this candidate reduction, Observation 7 throughput equivalence,
and the two-flow ML lift remain open.
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
is the MB09 §3.2 signed-walk condition.  Every graph edge carries exactly the
incidences its endpoint molecule classes determine (`edge_signs_of_mem`), and
the adjacency sign opposition holds directly for graph edges
(`adjacent_edge_signs_opposite`). -/

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

/-- Every edge of the complete `overlapEdges` graph carries exactly the
incidences its endpoint molecule classes determine (MB09 §3.3): the departure
incidence `sgnRep e.sx (rep e.sx)` at the class of `e.sx` and the arrival
incidence `sgnTgt e.sy (rep e.sy)` at the class of `e.sy`. -/
theorem edge_signs_of_mem {A : Type} {W : Type} [DecidableEq A] [DecidableEq W]
    {toList : W → List A} {rep rc : W → W} {readLen oMin : Nat} {verts : List W}
    {e : BdEdge A W} (he : e ∈ overlapEdges A W toList rep rc readLen oMin verts) :
    e.sgnX = sgnRep e.sx (rep e.sx) ∧ e.sgnY = sgnTgt e.sy (rep e.sy) := by
  unfold overlapEdges at he
  rw [List.mem_flatMap] at he
  obtain ⟨l, hl, he⟩ := he
  rw [List.mem_flatMap] at he
  obtain ⟨sx, hsx, he⟩ := he
  rw [List.mem_flatMap] at he
  obtain ⟨sy, hsy, he⟩ := he
  split_ifs at he with hov
  · simp at he
    subst e
    exact ⟨rfl, rfl⟩
  · simp at he

/-- Two edges of the complete `overlapEdges` graph that are adjacent at a common
oriented strand have opposite incidences at that strand (MB09 §3.2): the arrival
incidence of the first edge is the negative of the departure incidence of the
second. -/
theorem adjacent_edge_signs_opposite {A : Type} {W : Type} [DecidableEq A] [DecidableEq W]
    {toList : W → List A} {rep rc : W → W} {readLen oMin : Nat} {verts : List W}
    {f g : BdEdge A W}
    (hf : f ∈ overlapEdges A W toList rep rc readLen oMin verts)
    (hg : g ∈ overlapEdges A W toList rep rc readLen oMin verts)
    (hadj : f.sy = g.sx) :
    f.sgnY = -g.sgnX := by
  have hfs := edge_signs_of_mem hf
  have hgs := edge_signs_of_mem hg
  have h := sgnRep_neg_sgnTgt g.sx rep
  rw [hfs.2, hgs.1, hadj]
  omega

/-- A chain of graph edges in the `Step` (adjacency) sense is automatically a
chain in the signed-incidence sense (MB09 §3.2): every two consecutive edges
of the chain are adjacent at a common oriented strand, so their incidences at
that strand are opposite. -/
theorem isChain_sign_incidence {A : Type} {W : Type} [DecidableEq A] [DecidableEq W]
    {toList : W → List A} {rep rc : W → W} {readLen oMin : Nat} {verts : List W}
    {p : List (BdEdge A W)}
    (hmem : ∀ e ∈ p, e ∈ overlapEdges A W toList rep rc readLen oMin verts)
    (hc : p.IsChain Step) :
    p.IsChain (fun f g => f.sgnY = -g.sgnX) :=
  hc.imp_of_mem_imp (fun f g hf hg hadj =>
    adjacent_edge_signs_opposite (hmem f hf) (hmem g hg) hadj)

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

/-- **Signed-incidence lift of the global expansion.**  Every edge `e` of the
complete `overlapEdges` graph expands into a signed path `p` of edges of the
*transitively reduced* graph such that `p` has the same endpoints as `e`,
consecutive edges of `p` have opposite incidences at every common oriented
strand (MB09 §3.2), and `p` spells the same tail: `pathTail p = edgeTail e`.
The reduction membership of every member of `p` implies its full-graph
membership, which feeds the signed-incidence chain. -/
theorem exists_surviving_signed_path_signed [DecidableEq A]
    (toList : W → List A) (rep rc : W → W) (readLen oMin : Nat) (verts : List W)
    (hLen : ∀ s ∈ strandsOf rc verts, (toList s).length = readLen)
    (e : BdEdge A W) (he : e ∈ overlapEdges A W toList rep rc readLen oMin verts) :
    ∃ p : List (BdEdge A W),
      SignedPath e.sx e.sy p ∧
        p.IsChain (fun f g => f.sgnY = -g.sgnX) ∧
        (∀ g ∈ p, g ∈ transitivelyReducedSpelling W toList rc readLen oMin verts
          (overlapEdges A W toList rep rc readLen oMin verts)) ∧
        pathTail toList p = edgeTail toList e := by
  obtain ⟨p, hp, hsurv, htail⟩ := exists_surviving_signed_path toList rep rc readLen oMin verts hLen e he
  refine ⟨p, hp, ?_, hsurv, htail⟩
  exact isChain_sign_incidence (fun g hg => (List.mem_filter.mp (hsurv g hg)).1) hp.2.2

#print axioms exists_surviving_signed_path_signed
#print axioms isChain_sign_incidence

/-! ## Global whole-walk spelling preservation

Given a signed walk (a `SignedPath`) all of whose edges belong to the complete
`overlapEdges` graph, the per-edge expansions of
`exists_surviving_signed_path_signed` concatenate, along the walk, into a single
signed path of *transitively reduced* edges spelling the same word
(`global_walk_signed_expansion`).  This is the global walk-language statement
of the candidate reduction under the longer-replacement-overlaps reading.
MB09/Myers source fidelity, Observation 7 throughput equivalence, and the
two-flow ML lift remain open. -/

/-- The last element recorded by `List.getLast?` is a member of the list. -/
theorem mem_of_mem_getLast? {α : Type} {l : List α} {x : α} (h : x ∈ l.getLast?) :
    x ∈ l := by
  obtain ⟨hne, hx⟩ := List.mem_getLast?_eq_getLast h
  rw [hx]
  exact List.getLast_mem hne

/-- **Global whole-walk spelling preservation.**  Given a signed walk `walk`
from `start` to `sy` all of whose edges are edges of the complete `overlapEdges`
graph, there is a signed path `p` of edges of the *transitively reduced* graph
such that

* `p` has the same endpoints as the walk: `SignedPath start sy p`;
* consecutive edges of `p` have opposite incidences at every common oriented
  strand (MB09 §3.2): `p.IsChain (fun f g => f.sgnY = -g.sgnX)`;
* every edge of `p` survives the spelling-preserving transitive reduction;
* `p` spells the same word as the walk:
  `toList start ++ pathTail toList p = toList start ++ pathTail toList walk`.

The proof concatenates, along the walk, the per-edge surviving expansions:
within each expansion the signed-incidence chain holds by
`isChain_sign_incidence`, and at each seam the last edge of one expansion and
the first edge of the next are adjacent graph edges, so
`adjacent_edge_signs_opposite` gives the seam incidence.  The word is
preserved by `pathTail_append` and the per-edge tail identity. -/
theorem global_walk_signed_expansion [DecidableEq A]
    (toList : W → List A) (rep rc : W → W) (readLen oMin : Nat) (verts : List W)
    (hLen : ∀ s ∈ strandsOf rc verts, (toList s).length = readLen) :
    ∀ {walk : List (BdEdge A W)} {start sy : W},
      SignedPath start sy walk →
      (∀ e ∈ walk, e ∈ overlapEdges A W toList rep rc readLen oMin verts) →
      ∃ p : List (BdEdge A W),
        SignedPath start sy p ∧
          p.IsChain (fun f g => f.sgnY = -g.sgnX) ∧
          (∀ g ∈ p, g ∈ transitivelyReducedSpelling W toList rc readLen oMin verts
            (overlapEdges A W toList rep rc readLen oMin verts)) ∧
          toList start ++ pathTail toList p = toList start ++ pathTail toList walk := by
  intro walk
  induction walk with
  | nil =>
      intro start sy hsp hmem
      exact absurd hsp.1 (by simp)
  | cons e rest ih =>
      intro start sy hsp hmem
      rcases rest with _ | ⟨g, rest'⟩
      · obtain ⟨hxs, hys⟩ := signedPath_single.mp hsp
        obtain ⟨p, hp, hchain, hsurv, htail⟩ :=
          exists_surviving_signed_path_signed toList rep rc readLen oMin verts hLen e
             (hmem e List.mem_cons_self)
        refine ⟨p, ?_, hchain, hsurv, ?_⟩
        · rw [← hxs, ← hys]; exact hp
        · rw [pathTail_cons, pathTail_nil, htail, List.append_nil]
      · have hchain : (e :: g :: rest').IsChain Step := hsp.2.2
        rw [List.isChain_cons] at hchain
        have hstep : Step e g := hchain.1 g (by simp)
        have hstep' : e.sy = g.sx := hstep
        have hrestchain : (g :: rest').IsChain Step := hchain.2
        obtain ⟨e₀, hh₀, hxs₀⟩ := hsp.1
        have hxs : e.sx = start := by
          have hh₀r : (e :: g :: rest').head? = some e := rfl
          have h₀ : e = e₀ := Option.some_inj.mp (hh₀r.symm.trans hh₀)
          rw [h₀]; exact hxs₀
        obtain ⟨e₁, hl₁, hys₁⟩ := hsp.2.1
        have hl₁' : (g :: rest').getLast? = some e₁ := by
          have hleq : (e :: g :: rest').getLast? = (g :: rest').getLast? := by simp
          rw [← hleq]; exact hl₁
        have hsp_rest : SignedPath g.sx sy (g :: rest') :=
          ⟨⟨g, rfl, rfl⟩, ⟨e₁, hl₁', hys₁⟩, hrestchain⟩
        have hmem_rest : ∀ e' ∈ g :: rest',
            e' ∈ overlapEdges A W toList rep rc readLen oMin verts := by
          intro e' he'
          exact hmem e' (List.mem_cons_of_mem e he')
        obtain ⟨p_rest, hp_rest, hchain_rest, hsurv_rest, htail_rest⟩ :=
          ih hsp_rest hmem_rest
        obtain ⟨p_e, hp_e, hchain_e, hsurv_e, htail_e⟩ :=
          exists_surviving_signed_path_signed toList rep rc readLen oMin verts hLen e
            (hmem e List.mem_cons_self)
        obtain ⟨e₁e, hl₁e, hys₁e⟩ := hp_e.2.1
        obtain ⟨e₀r, hh₀r, hxs₀r⟩ := hp_rest.1
        refine ⟨p_e ++ p_rest, ?_, ?_, ?_, ?_⟩
        · have hp_e' : SignedPath start e.sy p_e := by rw [← hxs]; exact hp_e
          have hp_rest' : SignedPath e.sy sy p_rest := by rw [hstep']; exact hp_rest
          exact signedPath_concat hp_e' hp_rest'
        · refine List.IsChain.append hchain_e hchain_rest ?_
          intro x hx y hy
          rw [hl₁e] at hx
          rw [hh₀r] at hy
          rw [(Option.some_inj.mp hx).symm, (Option.some_inj.mp hy).symm]
          have hmem₁ : e₁e ∈ overlapEdges A W toList rep rc readLen oMin verts :=
            (List.mem_filter.mp (hsurv_e e₁e (mem_of_mem_getLast? hl₁e))).1
          have hmem₀ : e₀r ∈ overlapEdges A W toList rep rc readLen oMin verts := by
            have hr : e₀r ∈ p_rest := by
              rw [List.eq_cons_of_mem_head? hh₀r]
              exact List.mem_cons_self
            exact (List.mem_filter.mp (hsurv_rest e₀r hr)).1
          have hadj : e₁e.sy = e₀r.sx := by
            rw [hys₁e, hstep', hxs₀r]
          exact adjacent_edge_signs_opposite hmem₁ hmem₀ hadj
        · intro g' hg'
          rcases List.mem_append.mp hg' with hg' | hg'
          · exact hsurv_e g' hg'
          · exact hsurv_rest g' hg'
        · have htail_rest' : pathTail toList p_rest = pathTail toList (g :: rest') :=
            List.append_right_injective (toList g.sx) htail_rest
          rw [pathTail_append, htail_e, htail_rest', pathTail_cons toList e (g :: rest')]

#print axioms global_walk_signed_expansion

end AssemblyP1.Section62GlobalSpellingPreservation
