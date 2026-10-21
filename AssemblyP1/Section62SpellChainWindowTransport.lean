import AssemblyP1.Section62SimultaneousReduction
import AssemblyP1.Section62VisitWindowBridge

/-!
# §6.2 sliding length-`L` window multiset of `spellChain` (#284)

The spelling-preserving §6.2 transitive reduction of
`AssemblyP1.Section62SimultaneousReduction` replaces an overlap edge by a chain
of edges that spells the same word (`spellChain toList e.sx es = spellDirect …`),
so the *full* length-`L` window multiset of the spelled word is invariant.  The
merged `AssemblyP1.Section62VisitTransport` and
`AssemblyP1.Section62VisitWindowBridge` prove the corresponding window-multiset
invariance and the physical-visit domination bound for a self-contained toy
walk-spelling `spellWalk` on bare lists of words.

This module closes the fidelity gap: it states the window object on the
repository's **actual** §6.2 spelling function `spellChain` of
`AssemblyP1.Section62SimultaneousReduction`, and proves that

1. `spellChain` of a chain of overlap edges equals `spellWalk` applied to the
   visited read words and the overlap lengths (`spellChain_eq_spellWalk`);
2. hence the length-`L` window multiset of `spellChain` is invariant under every
   spelling-preserving detour replacement
   (`reduction_preserves_language_windows`);
3. and, for a genuine chain of proper overlaps in the `overlapEdges` graph, the
   visited read-word multiset is a sub-multiset of that window multiset
   (`chain_visited_dominated` / `genuineChain_visited_dominated`), which is the
   explicit relation between the complete window multiset and the physical class
   counts, including the unobserved seam windows as the residual gap.

**What this licenses.**  A reduction-invariant *upper bound* on the physical
visit count of each read word by its window multiplicity, valid for every
genuine chain in the §6.2 overlap graph.  The window multiset is a function of
the spelled word, so the bound survives the spelling-preserving reduction while
the visit count itself does not.

**What this does not license.**  It does not license exact physical class
counts, exact §6.2 vertex throughput, or an ML-flow/likelihood equivalence: the
bound is strict (the unobserved seam window of
`Section62VisitWindowBridge.witness_bound_strict`), and the window box is not
sharpened to the exact physical image by any observed-window designation
(`Section62WindowBoxSharpness`).  The molecule-class quotient (`rep`,
reverse complements) additionally needs the separate Observation 7 / RC
arguments of `Section62ObservedMoleculeCount` and `Section62GlobalSkippedBridge`.

This module is purely additive: it does not redefine `isReducibleB`,
`transitivelyReduced`, `isReducibleSpellingB`, `transitivelyReducedSpelling`,
`SpelledFeasible62`, or `StepsSurviveReduction`, and it reproves no merged §6.2
theorem.  It adds new definitions and theorems only.
-/

namespace AssemblyP1.Section62SpellChainWindowTransport

open Section62Flow Section62SimultaneousReduction Section62SpellingReductionCandidate
open Section62VisitTransport Section62VisitWindowBridge

set_option linter.unusedSectionVars false

variable {A W : Type} [DecidableEq A] [DecidableEq W]

/-! ## The chain's visited strands and overlaps -/

/-- The strands visited by a chain `es` starting at `s`: the departure strand,
followed by the arrival strand of every edge. -/
def chainStrands (s : W) (es : List (BdEdge A W)) : List W :=
  s :: es.map (fun e => e.sy)

/-- The overlap lengths of a chain, in order. -/
def chainOvs (es : List (BdEdge A W)) : List Nat :=
  es.map (fun e => e.len)

/-! ## The bridge from `spellChain` to the walk spelling -/

/-- Unfolding `spellWalk` on a nonempty read list. -/
theorem spellWalk_cons_eq (v : List A) (rest : List (List A)) (ovs : List Nat) :
    spellWalk (v :: rest) ovs
      = v ++ cats (rest.zipWith (fun w o => w.drop o) ovs) := rfl

/-- Dropping `k` symbols from the spelling of a walk only affects the head read,
provided `k` does not exceed the head read's length. -/
theorem spellWalk_drop_head {v : List A} {rest : List (List A)} {ovs : List Nat}
    {k : Nat} (hk : k ≤ v.length) :
    (spellWalk (v :: rest) ovs).drop k
      = v.drop k ++ cats (rest.zipWith (fun w o => w.drop o) ovs) := by
  rw [spellWalk_cons_eq, List.drop_append_of_le_length hk]

/-- **Bridge: the real §6.2 `spellChain` equals the walk spelling.**  For a chain
whose every overlap is no longer than its arrival read, the word spelled by the
chain of overlap edges is exactly `spellWalk` applied to the visited read words
and the overlap lengths.  This is the statement that the §6.2 reduction module's
spelling function and the window-transport module's walk spelling are the same
object. -/
theorem spellChain_eq_spellWalk {toList : W → List A} {s : W} {es : List (BdEdge A W)}
    (h : ∀ e ∈ es, e.len ≤ (toList e.sy).length) :
    spellChain toList s es
      = spellWalk (toList s :: es.map (fun e => toList e.sy))
          (es.map (fun e => e.len)) := by
  induction es generalizing s with
  | nil => simp [spellChain, spellWalk, cats]
  | cons e es ih =>
      have hstep := ih (s := e.sy) (fun f hf => h f (by simp [hf]))
      rw [spellChain, hstep, spellWalk_drop_head (h e (by simp))]
      simp [spellWalk, cats, List.zipWith_cons_cons]

/-! ## Window-multiset invariance on `spellChain` -/

/-- The length-`L` window multiset is a function of the spelled word. -/
theorem spellChain_windows_congr {toList : W → List A} {L : Nat} {s : W}
    {es es' : List (BdEdge A W)}
    (h : spellChain toList s es = spellChain toList s es') :
    windows L (spellChain toList s es) = windows L (spellChain toList s es') := by
  rw [h]

/-- **The window multiset of `spellChain` is invariant under the spelling-
preserving expansion of an edge.**  When the chain `es` from `e.sx` spells exactly
the word the direct edge `e` spells, their length-`L` window multisets agree.  The
hypotheses are exactly those supplied by
`Section62SimultaneousReduction.reduction_preserves_language`. -/
theorem reduction_preserves_language_windows
    (toList : W → List A) (rep rc : W → W) (L oMin : Nat) (verts : List W)
    (_hLen : ∀ s ∈ strandsOf rc verts, (toList s).length = L)
    (e : BdEdge A W)
    (_hmem : e ∈ overlapEdges A W toList rep rc L oMin verts)
    (es : List (BdEdge A W))
    (_hchain : Chain e.sx es) (_hend : chainEnd e.sx es = e.sy)
    (hspell : spellChain toList e.sx es
        = spellDirect (toList e.sx) (toList e.sy) e.len) :
    windows L (spellChain toList e.sx es)
      = windows L (spellDirect (toList e.sx) (toList e.sy) e.len) := by
  rw [hspell]

/-! ## Genuine chains of proper overlaps -/

/-- A chain of edges of the `overlapEdges` graph, starting at an observed strand,
is a genuine walk of proper overlaps: each edge's overlap is proper and the
suffix/prefix compatibility of `overlapEdges` is exactly the genuine-overlap
hypothesis of `GenuineWalk`. -/
theorem genuineChain_of_overlapEdges {toList : W → List A} {rep rc : W → W}
    {L oMin : Nat} {verts : List W} {s : W} {es : List (BdEdge A W)}
    (hs : s ∈ strandsOf rc verts)
    (hchain : Chain s es)
    (hmem : ∀ e ∈ es, e ∈ overlapEdges A W toList rep rc L oMin verts)
    (hLen : ∀ w ∈ strandsOf rc verts, (toList w).length = L) :
    GenuineWalk L ((chainStrands s es).map toList) (chainOvs es) := by
  induction es generalizing s with
  | nil =>
      simp only [chainStrands, chainOvs, List.map_nil]
      exact GenuineWalk.single (toList s) (hLen s hs)
  | cons e es ih =>
      obtain ⟨hsx, hchain'⟩ := hchain
      have he := overlapEdges_mem_iff (hmem e (by simp))
      have ho : e.len < L := he.2.1
      have hov : (toList s).drop (L - e.len) = (toList e.sy).take e.len := by
        have h1 : (toList s).drop (L - e.len) = sufOf (toList s) e.len := by
          rw [sufOf, hLen s hs]
        rw [h1, ← hsx]
        simpa [preOf] using he.2.2.2.2
      have hsy : e.sy ∈ strandsOf rc verts := he.2.2.2.1
      have ihh := ih (s := e.sy) hsy hchain' (fun f hf => hmem f (by simp [hf]))
      simp only [chainStrands, chainOvs, List.map_cons]
      exact GenuineWalk.cons (hLen s hs) ho hov ihh

/-- Every visited strand of a chain of `overlapEdges` edges is itself a strand of
an observed molecule class. -/
theorem chainStrands_subset_strandsOf {toList : W → List A} {rep rc : W → W}
    {L oMin : Nat} {verts : List W} {s : W} {es : List (BdEdge A W)}
    (hs : s ∈ strandsOf rc verts)
    (hmem : ∀ e ∈ es, e ∈ overlapEdges A W toList rep rc L oMin verts) :
    ∀ w ∈ chainStrands s es, w ∈ strandsOf rc verts := by
  intro w hw
  simp only [chainStrands, List.mem_cons, List.mem_map] at hw
  rcases hw with rfl | ⟨f, hf, rfl⟩
  · exact hs
  · exact (overlapEdges_mem_iff (hmem f hf)).2.2.2.1

/-- **Window multiset dominates the physical visited reads of a real §6.2 chain.**
For a chain of genuine proper overlaps whose reads all have length `L`, the
visited read-word multiset is a sub-multiset of the length-`L` window multiset
of the spelled word `spellChain`.  Equivalently, for every read word `u`, the
number of chain positions whose read is `u` is at most the multiplicity of `u`
among the length-`L` windows of the spelled word.  This is the explicit relation
between the complete window multiset and the physical class counts; the residual
gap is exactly the unobserved seam windows. -/
theorem chain_visited_dominated {toList : W → List A} {L : Nat} {s : W}
    {es : List (BdEdge A W)}
    (_hLen : ∀ w ∈ chainStrands s es, (toList w).length = L)
    (hov : ∀ e ∈ es, e.len ≤ (toList e.sy).length)
    (hgenuine : GenuineWalk L ((chainStrands s es).map toList) (chainOvs es)) :
    Dominates ((chainStrands s es).map toList) (windows L (spellChain toList s es)) := by
  rw [spellChain_eq_spellWalk (s := s) (es := es) hov]
  simpa [chainStrands, chainOvs, List.map_cons, List.map_map, Function.comp_def]
    using genuineWalk_dominates hgenuine

/-- The combined real-model statement: a genuine chain in the `overlapEdges`
graph has its visited read words dominated by the length-`L` window multiset of
`spellChain`.  This is the §6.2-faithful form of
`Section62VisitWindowBridge.genuineWalk_dominates`. -/
theorem genuineChain_visited_dominated {toList : W → List A} {rep rc : W → W}
    {L oMin : Nat} {verts : List W} {s : W} {es : List (BdEdge A W)}
    (hs : s ∈ strandsOf rc verts)
    (hchain : Chain s es)
    (hmem : ∀ e ∈ es, e ∈ overlapEdges A W toList rep rc L oMin verts)
    (hLen : ∀ w ∈ strandsOf rc verts, (toList w).length = L) :
    Dominates ((chainStrands s es).map toList) (windows L (spellChain toList s es)) :=
  chain_visited_dominated
    (fun w hw => hLen w (chainStrands_subset_strandsOf hs hmem w hw))
    (fun e he => by
      have hlt : e.len < L := (overlapEdges_mem_iff (hmem e he)).2.1
      have hlen : (toList e.sy).length = L :=
        hLen e.sy (chainStrands_subset_strandsOf hs hmem e.sy
          (by right; exact List.mem_map.mpr ⟨e, he, rfl⟩))
      omega)
    (genuineChain_of_overlapEdges hs hchain hmem hLen)

/-! ## Axiom audit -/

#print axioms spellWalk_cons_eq
#print axioms spellWalk_drop_head
#print axioms spellChain_eq_spellWalk
#print axioms spellChain_windows_congr
#print axioms reduction_preserves_language_windows
#print axioms genuineChain_of_overlapEdges
#print axioms chainStrands_subset_strandsOf
#print axioms chain_visited_dominated
#print axioms genuineChain_visited_dominated

end AssemblyP1.Section62SpellChainWindowTransport
