import AssemblyP1.Section62SpellingReductionCandidate

/-!
# Idealized Myers two-hop transitivity, with no noisy-overlap heuristics

Myers 2005 §2 describes a transitive edge f→h as one for which a two-hop
f→g→h path spells exactly the same sequence. For equal-length error-free reads
the repository's spelling-preserving reduction uses the overlap-length law
l1+l2=L+l. Here we prove that this algebraic test is NECESSARY AND SUFFICIENT
for the literal idealized same-spelling two-hop relation, not merely sufficient.

This does not identify the complete practical Myers 2005 algorithm: FUZZ=10,
noisy approximate overlaps, contained reads, orientation and parallel-edge
details require separate treatment.
-/

namespace AssemblyP1.Section62MyersIdealTransitivity

open Section62Flow Section62SpellingReductionCandidate

/-- Semantic idealized transitivity: a legal two-edge detour through an
observed strand spells exactly the same sequence as the direct edge. -/
def TwoHopSameSpelling {A W : Type} [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rc : W → W) (L oMin : Nat)
    (verts : List W) (e : BdEdge A W) : Prop :=
  ∃ m ∈ strandsOf rc verts, ∃ l1 l2 : Nat,
    oMin ≤ l1 ∧ l1 < L ∧ oMin ≤ l2 ∧ l2 < L ∧
    sufOf (toList e.sx) l1 = preOf (toList m) l1 ∧
    sufOf (toList m) l2 = preOf (toList e.sy) l2 ∧
    spellPath (toList e.sx) (toList m) (toList e.sy) l1 l2 =
      spellDirect (toList e.sx) (toList e.sy) e.len

/-- The source-model exact two-hop spelling criterion is EQUIVALENT to the
implemented overlap-length Diophantine test for proper equal-length reads.
The reverse direction follows from comparing spelled lengths, not from an
unjustified heuristic or an assumed converse of the spelling lemma. -/
theorem reducible_iff_ideal_two_hop {A W : Type}
    [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rc : W → W) (L oMin : Nat)
    (verts : List W) (e : BdEdge A W)
    (hsx : (toList e.sx).length = L)
    (hsy : (toList e.sy).length = L)
    (hLen : ∀ m ∈ strandsOf rc verts, (toList m).length = L)
    (hproper : e.len < L) :
    isReducibleSpelling W toList rc L oMin verts e ↔
      TwoHopSameSpelling toList rc L oMin verts e := by
  constructor
  · intro h
    unfold isReducibleSpelling isReducibleSpellingB at h
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨m, hm, l1, hl1, l2, hl2, hconds⟩ := h
    rcases hconds with ⟨⟨⟨⟨ho1, ho2⟩, hov1⟩, hov2⟩, hcomp⟩
    have hl1' : l1 < L := List.mem_range.mp hl1
    have hl2' : l2 < L := List.mem_range.mp hl2
    have hspell := spellPath_eq_spellDirect hsx (hLen m hm) hsy
      hl1' hl2' hproper hov1 hov2 hcomp
    exact ⟨m, hm, l1, l2, ho1, hl1', ho2, hl2', hov1, hov2, hspell⟩
  · rintro ⟨m, hm, l1, l2, ho1, hl1, ho2, hl2, hov1, hov2, hspell⟩
    have hlenPath := spellPath_length hsx (hLen m hm) hsy
      (Nat.le_of_lt hl1) (Nat.le_of_lt hl2)
    have hlenDirect := spellDirect_length hsx hsy (Nat.le_of_lt hproper)
    have hlenEq := congrArg List.length hspell
    rw [hlenPath, hlenDirect] at hlenEq
    have hcomp : l1 + l2 = L + e.len := by omega
    unfold isReducibleSpelling isReducibleSpellingB
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨m, hm, l1, List.mem_range.mpr hl1,
      l2, List.mem_range.mpr hl2,
      ⟨⟨⟨⟨ho1, ho2⟩, hov1⟩, hov2⟩, hcomp⟩⟩


/-- Direct graph-level formulation: under the exact equal-length model, an
edge survives the implemented reduction iff it was an original edge and
NO legal observed two-hop detour spells the same word. This is the idealized
source semantics; it does not claim equivalence to noisy FUZZ heuristics. -/
theorem reduced_mem_iff_no_ideal_detour {A W : Type}
    [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rc : W → W) (L oMin : Nat)
    (verts : List W) (edges : List (BdEdge A W)) (e : BdEdge A W)
    (hsx : (toList e.sx).length = L)
    (hsy : (toList e.sy).length = L)
    (hLen : ∀ m ∈ strandsOf rc verts, (toList m).length = L)
    (hproper : e.len < L) :
    e ∈ transitivelyReducedSpelling W toList rc L oMin verts edges ↔
      e ∈ edges ∧ ¬ TwoHopSameSpelling toList rc L oMin verts e := by
  have hiff := reducible_iff_ideal_two_hop toList rc L oMin verts
    e hsx hsy hLen hproper
  unfold transitivelyReducedSpelling
  rw [List.mem_filter]
  constructor
  · rintro ⟨hem, hbool⟩
    refine ⟨hem, ?_⟩
    intro hsem
    have hred : isReducibleSpelling W toList rc L oMin verts e :=
      hiff.mpr hsem
    change isReducibleSpellingB W toList rc L oMin verts e = true at hred
    simp [hred] at hbool
  · rintro ⟨hem, hnot⟩
    refine ⟨hem, ?_⟩
    cases hb : isReducibleSpellingB W toList rc L oMin verts e with
    | false => rfl
    | true =>
        have hred : isReducibleSpelling W toList rc L oMin verts e := hb
        exact False.elim (hnot (hiff.mp hred))

#print axioms reduced_mem_iff_no_ideal_detour

#print axioms reducible_iff_ideal_two_hop

/-! ## Exact regression witness at the ideal-semantics level

The candidate regression (`Section62SpellingReductionCandidate`) removes the
direct `1`-overlap `0 → 2` over reads `[0,1,2]`, `[1,2,3]`, `[2,3,4]` of common
length `3`, keeping both `2`-overlap legs.  The following kernel-checked
identity is the exact numeric content of Myers 2005 §2 at the idealized level
for that instance: the two-hop path `0 → 1 → 2` spells literally the same
sequence (`[0,1,2,3,4]`) as the direct edge.  By `reducible_iff_ideal_two_hop`,
this is the semantic half of the predicate/semantic agreement on the
regression; the predicate half is `regression_edge_is_reducible` in the
candidate module.

Scope: idealized equal-length error-free spelling only.  This says nothing
about practical Myers heuristics (FUZZ tolerance, noisy approximate overlaps,
contained reads, orientation/parallel-edge handling), which remain open. -/

/-- The regression detour spells exactly the word Myers 2005 §2 requires:
the `2,2`-overlap path over `[0,1,2] → [1,2,3] → [2,3,4]` spells `[0,1,2,3,4]`,
the same word as the direct `1`-overlap `[0,1,2] → [2,3,4]`. -/
theorem myers_ideal_regression_witness :
    spellPath ([0, 1, 2] : List Nat) [1, 2, 3] [2, 3, 4] 2 2 =
      spellDirect [0, 1, 2] [2, 3, 4] 1 := by
  decide

#print axioms myers_ideal_regression_witness

end AssemblyP1.Section62MyersIdealTransitivity
