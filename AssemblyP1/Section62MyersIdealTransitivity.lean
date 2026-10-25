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

/-- Arithmetic core of requirement (3): when the overlap-length identity
`l1 + l2 = L + e` holds alongside properness (`l1, l2 < L`, `e < L`),
both replacement overlaps are forced to be strictly longer than the
direct edge overlap. Pure `Nat` fact, proved by `omega`. -/
theorem overlapLens_gt_direct_of_comp {l1 l2 L e : Nat}
    (h1 : l1 < L) (h2 : l2 < L) (he : e < L)
    (hcomp : l1 + l2 = L + e) : e < l1 ∧ e < l2 := by
  omega

/-- Lifted form: any idealized two-hop same-spelling witness for a proper
overlap edge uses replacement overlaps strictly longer than the direct
edge. The spelling identity forces the length identity
`l1 + l2 = L + e.len` (by comparing spelled lengths, as in
`reducible_iff_ideal_two_hop`), and the arithmetic core then forces
`e.len < l1` and `e.len < l2`. -/
theorem twoHop_overlaps_gt_direct {A W : Type}
    [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rc : W → W) (L oMin : Nat)
    (verts : List W) (e : BdEdge A W)
    (hsx : (toList e.sx).length = L)
    (hsy : (toList e.sy).length = L)
    (hLen : ∀ m ∈ strandsOf rc verts, (toList m).length = L)
    (hproper : e.len < L)
    (h : TwoHopSameSpelling toList rc L oMin verts e) :
    ∃ m ∈ strandsOf rc verts, ∃ l1 l2 : Nat,
      oMin ≤ l1 ∧ l1 < L ∧ oMin ≤ l2 ∧ l2 < L ∧
      e.len < l1 ∧ e.len < l2 ∧
      sufOf (toList e.sx) l1 = preOf (toList m) l1 ∧
      sufOf (toList m) l2 = preOf (toList e.sy) l2 ∧
      spellPath (toList e.sx) (toList m) (toList e.sy) l1 l2 =
        spellDirect (toList e.sx) (toList e.sy) e.len := by
  obtain ⟨m, hm, l1, l2, ho1, hl1, ho2, hl2, hov1, hov2, hspell⟩ := h
  have hlenPath := spellPath_length hsx (hLen m hm) hsy
    (Nat.le_of_lt hl1) (Nat.le_of_lt hl2)
  have hlenDirect := spellDirect_length hsx hsy (Nat.le_of_lt hproper)
  have hlenEq := congrArg List.length hspell
  rw [hlenPath, hlenDirect] at hlenEq
  have hcomp : l1 + l2 = L + e.len := by omega
  have hgt := overlapLens_gt_direct_of_comp hl1 hl2 hproper hcomp
  exact ⟨m, hm, l1, l2, ho1, hl1, ho2, hl2, hgt.1, hgt.2, hov1, hov2, hspell⟩

#print axioms twoHop_overlaps_gt_direct

#print axioms overlapLens_gt_direct_of_comp

#print axioms reduced_mem_iff_no_ideal_detour

#print axioms reducible_iff_ideal_two_hop

end AssemblyP1.Section62MyersIdealTransitivity
