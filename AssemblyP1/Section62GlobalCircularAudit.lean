import AssemblyP1.Section62SkippedWindowFactor
import AssemblyP1.Section62GlobalSpellingPreservation

/-!
# Global walk-level spelling and no-skipped-observed-window theorem (#284)

This module composes the two kernel-checked halves of the corrected §6.2 model
into a single **global** statement about arbitrary walks:

* `Section62GlobalSpellingPreservation.global_walk_signed_expansion` — every
  signed walk of `overlapEdges` edges expands, edge for edge, into a signed walk
  of *spelling-reduced* edges with the same endpoints, the same signed-incidence
  chain, and the same spelled tail.
* `Section62SkippedWindowFactor.surviving_edge_skips_no_observed_strand` — no
  surviving reduced edge has an *observed* internal length-`L` window.

`global_walk_reduced_skips_no_observed_window` below states that the surviving
expansion of any graph walk therefore has the same spelled word as the walk **and**
no edge of it skips an observed read strand.  Quantifying over an arbitrary
`SignedPath` makes this the global (whole-walk) version of the local no-skip
lemma; the RC/molecule-class lift is automatic because the intermediate is
quantified over `strandsOf rc verts`, which enumerates both strands of every
observed molecule class.

## What is *not* proved here

The **circular seam partition identity** — that the complete length-`L` window
counts `C_D(c)` of the spelled circular genome split into the visited-read counts
`V(c)` plus the skipped internal-window counts, giving

    C_D(c) = V(c) + Σ_j Σ_{u=1}^{e_j − 1} [ class(window(D, s_j + u)) = c ],

and hence (for observed class sets `S`) that `C_D(c) = V(c)` for all `c ∈ S`
iff no skipped internal window is observed — is the remaining formal obligation.
The graph-side hypothesis of that identity is exactly the no-skip conclusion
proved here; the cyclic-start interval partition itself is documented with its
exact formula in `docs/section62-global-circular-and-unseen-factor-284.md` and is
**not** silently assumed.  Likewise the `4^k` (oriented k-mer) versus
reverse-complement-class indexing question of §6.1 is left open there.
-/

namespace AssemblyP1.Section62GlobalCircularAudit

open Section62Flow Section62SpellingReductionCandidate
open AssemblyP1.Section62GlobalSpellingPreservation
open AssemblyP1.Section62SkippedWindowFactor

set_option maxHeartbeats 4000000

/-- **Global walk expansion with no observed skipped window.**  For any signed
walk `walk` from `start` to `sy` whose edges are all edges of the complete
`overlapEdges` graph, there is a signed walk `p` of edges of the
*spelling-reduced* graph such that

* `p` has the same endpoints as `walk`;
* `p` spells the same word as `walk` (`toList start ++ pathTail p` is unchanged);
* no edge `g` of `p` has an *observed* internal length-`readLen` window: for every
  internal offset `0 < t < readLen − g.len`, the internal window
  `(spellDirect (toList g.sx) (toList g.sy) g.len).drop t |>.take readLen` is not
  the linearization of any observed strand in `strandsOf rc verts`.

This is the corrected, global replacement for the old vacuous
`StepsSurviveReduction` conjunct. -/
theorem global_walk_reduced_skips_no_observed_window
    {A W : Type} [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rep rc : W → W) (readLen oMin : Nat) (verts : List W)
    (hLen : ∀ s ∈ strandsOf rc verts, (toList s).length = readLen)
    {walk : List (BdEdge A W)} {start sy : W}
    (hsp : SignedPath start sy walk)
    (hmem : ∀ e ∈ walk, e ∈ overlapEdges A W toList rep rc readLen oMin verts) :
    ∃ p : List (BdEdge A W),
      SignedPath start sy p ∧
        (∀ g ∈ p, g ∈ transitivelyReducedSpelling W toList rc readLen oMin verts
          (overlapEdges A W toList rep rc readLen oMin verts)) ∧
        toList start ++ pathTail toList p = toList start ++ pathTail toList walk ∧
        (∀ g ∈ p, ∀ t, 0 < t → t < readLen - g.len →
          ¬ ∃ m ∈ strandsOf rc verts,
            toList m =
              ((spellDirect (toList g.sx) (toList g.sy) g.len).drop t).take readLen) := by
  obtain ⟨p, hp, _hchain, hsurv, htail⟩ :=
    global_walk_signed_expansion toList rep rc readLen oMin verts hLen hsp hmem
  refine ⟨p, hp, hsurv, htail, ?_⟩
  intro g hg t ht0 ht
  have hmemg : g ∈ overlapEdges A W toList rep rc readLen oMin verts :=
    (List.mem_filter.mp (hsurv g hg)).1
  have hinfo := overlapEdges_mem_iff hmemg
  exact surviving_edge_skips_no_observed_strand toList rc readLen oMin verts
    (overlapEdges A W toList rep rc readLen oMin verts) g
    (hLen g.sx hinfo.2.2.1) (hLen g.sy hinfo.2.2.2.1)
    hinfo.2.1 hinfo.1 hinfo.2.2.2.2 (hsurv g hg) t ht0 ht

#print axioms global_walk_reduced_skips_no_observed_window

/-- **Closed (circular) specialization.**  If the walk is closed (`start = sy`),
so is its surviving expansion, and the spelled circular word is preserved with no
observed skipped internal window. -/
theorem global_closed_walk_reduced_skips_no_observed_window
    {A W : Type} [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rep rc : W → W) (readLen oMin : Nat) (verts : List W)
    (hLen : ∀ s ∈ strandsOf rc verts, (toList s).length = readLen)
    {walk : List (BdEdge A W)} {start : W}
    (hsp : SignedPath start start walk)
    (hmem : ∀ e ∈ walk, e ∈ overlapEdges A W toList rep rc readLen oMin verts) :
    ∃ p : List (BdEdge A W),
      SignedPath start start p ∧
        (∀ g ∈ p, g ∈ transitivelyReducedSpelling W toList rc readLen oMin verts
          (overlapEdges A W toList rep rc readLen oMin verts)) ∧
        toList start ++ pathTail toList p = toList start ++ pathTail toList walk ∧
        (∀ g ∈ p, ∀ t, 0 < t → t < readLen - g.len →
          ¬ ∃ m ∈ strandsOf rc verts,
            toList m =
              ((spellDirect (toList g.sx) (toList g.sy) g.len).drop t).take readLen) :=
  global_walk_reduced_skips_no_observed_window toList rep rc readLen oMin verts hLen hsp hmem

#print axioms global_closed_walk_reduced_skips_no_observed_window

end AssemblyP1.Section62GlobalCircularAudit
