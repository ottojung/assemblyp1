import AssemblyP1.Section62MyersIdealTransitivity

/-!
# Simultaneous spelling-preserving transitive reduction (#284)

`Section62SpellingReductionCandidate.isReducibleSpellingB` removes an overlap
edge when a **single** two-hop detour through an observed molecule spells the
same word.  `Section62MyersIdealTransitivity.reduced_mem_iff_no_ideal_detour`
proves that this one-step criterion is exactly the idealized Myers (2005) same-
spelling relation.

The remaining source-fidelity question for a *transitive* reduction is whether
removing **all** reducible edges at once preserves the language of spelled
molecules: the detour legs of a removed edge may themselves be reducible, so a
one-step replacement need not survive the full reduction.  This module closes
that gap for the equal-length error-free model.

The key fact is the well-founded measure supplied by
`Section62SpellingReductionCandidate.replacement_overlaps_longer`: a
spelling-preserving detour replaces an edge of overlap length `e.len` by legs
whose overlap lengths `l₁, l₂` are **strictly larger** than `e.len`.  Equivalently
the *extension length* `L - overlap` strictly decreases.  Since extension lengths
are natural numbers, repeatedly expanding reducible legs terminates, and every
expansion preserves the spelled word.  Hence every direct edge admits a finite
expansion into a chain of **irreducible** edges that spells exactly the same word
(`exists_irreducible_expansion`, `reduction_preserves_language`).

This is a genuine global language-preservation statement, not the one-step local
statement: it is independent of which detour is chosen and never assumes a leg
survives.  It does **not** claim equivalence to the practical Myers 2005 algorithm
(FUZZ=10, noisy overlaps, contained reads) — that remains a separate front.
-/

namespace AssemblyP1.Section62SimultaneousReduction

open Section62Flow Section62SpellingReductionCandidate

set_option maxHeartbeats 8000000

set_option linter.unusedSectionVars false

variable {A W : Type} [DecidableEq A] [DecidableEq W]

/-! ## The well-founded measure -/

/-- The **extension length** of an overlap edge: the number of bases it appends
beyond its departure read, `L - e.len`.  A spelling-preserving detour strictly
decreases this measure on both legs (`Section62SpellingReductionCandidate.
replacement_overlaps_longer`), which is what makes simultaneous reduction
terminate. -/
def Ext (L : Nat) (e : BdEdge A W) : Nat := L - e.len

/-! ## Chains of overlap edges and their spelled word -/

/-- The strand reached after following the chain `es` from strand `s`: the
arrival strand of the last edge, or `s` itself for the empty chain. -/
def chainEnd (s : W) : List (BdEdge A W) → W
  | [] => s
  | e :: es => chainEnd e.sy es

/-- `Chain s es` holds when the edges of `es` form a genuine bidirected walk
starting at strand `s`: the first edge departs from `s`, and each subsequent edge
departs from the arrival strand of the previous one. -/
def Chain (s : W) : List (BdEdge A W) → Prop
  | [] => True
  | e :: es => e.sx = s ∧ Chain e.sy es

/-- The word spelled by following the chain `es` from strand `s`: start with the
full read `toList s`, then append the part of each successive read beyond its
overlap with the previous one. -/
def spellChain (toList : W → List A) (s : W) : List (BdEdge A W) → List A
  | [] => toList s
  | e :: es => toList s ++ (spellChain toList e.sy es).drop e.len

/-! ## Structural lemmas about chains -/

/-- Splitting a chain at any point: the concatenation of two chains is a chain
from the start iff each part is a chain and the second starts where the first
ends. -/
theorem chain_append (s : W) (es1 es2 : List (BdEdge A W)) :
    Chain s (es1 ++ es2) ↔ Chain s es1 ∧ Chain (chainEnd s es1) es2 := by
  induction es1 generalizing s with
  | nil => simp [Chain, chainEnd]
  | cons e es ih =>
      simp only [List.cons_append, Chain, chainEnd]
      rw [ih e.sy]
      tauto

/-- The end strand of a concatenation is the end strand of the second chain
starting at the end strand of the first. -/
theorem chainEnd_append (s : W) (es1 es2 : List (BdEdge A W)) :
    chainEnd s (es1 ++ es2) = chainEnd (chainEnd s es1) es2 := by
  induction es1 generalizing s with
  | nil => simp [chainEnd]
  | cons e es ih =>
      simp only [List.cons_append, chainEnd]
      exact ih e.sy

/-! ## Structural lemmas about the spelled word -/

/-- A spelled chain always begins with the departure read: the spelled word is
`toList s` followed by a suffix. -/
theorem spellChain_self (toList : W → List A) (s : W) (es : List (BdEdge A W)) :
    spellChain toList s es =
      toList s ++ (spellChain toList s es).drop (toList s).length := by
  induction es generalizing s with
  | nil => simp [spellChain]
  | cons e es _ =>
      simp only [spellChain]
      rw [List.drop_append_of_le_length (l₁ := toList s)
        (l₂ := (spellChain toList e.sy es).drop e.len) (i := (toList s).length)
        (le_refl _)]
      simp

/-- The spelled word is at least as long as its departure read. -/
theorem length_le_spellChain (toList : W → List A) (s : W) (es : List (BdEdge A W)) :
    (toList s).length ≤ (spellChain toList s es).length := by
  have h := spellChain_self toList s es
  rw [h, List.length_append]
  omega

/-- **Concatenation of spelled chains.**  If every read along `es1` has length
`L` and every overlap of `es1` is proper (`≤ L`), then the word spelled by
`es1 ++ es2` is the word spelled by `es1` followed by the part of the word
spelled by `es2` beyond the shared `L`-symbol arrival read. -/
theorem spellChain_append (toList : W → List A) (L : Nat) (s : W)
    (es1 es2 : List (BdEdge A W))
    (hs : (toList s).length = L)
    (hLsy : ∀ e ∈ es1, (toList e.sy).length = L)
    (hlen : ∀ e ∈ es1, e.len ≤ L) :
    spellChain toList s (es1 ++ es2) =
      spellChain toList s es1 ++ (spellChain toList (chainEnd s es1) es2).drop L := by
  induction es1 generalizing s with
  | nil =>
      simp only [List.nil_append, chainEnd, spellChain]
      rw [spellChain_self toList s es2, hs]
      rw [List.drop_append_of_le_length (l₁ := toList s)
        (l₂ := List.drop L (spellChain toList s es2)) (i := L) (le_of_eq hs.symm)]
      rw [show (toList s).drop L = [] from by rw [← hs, List.drop_length], List.nil_append]
  | cons e es ih =>
      have hle : e.len ≤ (spellChain toList e.sy es).length := by
        have h1 : e.len ≤ L := hlen e (by simp)
        have h2 : L ≤ (spellChain toList e.sy es).length := by
          rw [← hLsy e (by simp)]
          exact length_le_spellChain toList e.sy es
        omega
      simp only [List.cons_append, chainEnd, spellChain]
      rw [ih e.sy (hLsy e (by simp)) (fun f hf => hLsy f (by simp [hf]))
        (fun f hf => hlen f (by simp [hf]))]
      rw [List.drop_append_of_le_length
        (l₁ := spellChain toList e.sy es)
        (l₂ := (spellChain toList (chainEnd e.sy es) es2).drop L) (i := e.len) hle]
      rw [List.append_assoc]

/-! ## Extraction of a detour witness from the reduction predicate -/

/-- The reduction predicate supplies an observed intermediate strand and two
proper overlap lengths satisfying the composition law. -/
theorem exists_detour_of_reducible {toList : W → List A} {rc : W → W} {L oMin : Nat}
    {verts : List W} {e : BdEdge A W}
    (h : isReducibleSpelling W toList rc L oMin verts e) :
    ∃ m ∈ strandsOf rc verts, ∃ l1 l2,
      oMin ≤ l1 ∧ oMin ≤ l2 ∧ l1 < L ∧ l2 < L ∧
        sufOf (toList e.sx) l1 = preOf (toList m) l1 ∧
        sufOf (toList m) l2 = preOf (toList e.sy) l2 ∧
        l1 + l2 = L + e.len := by
  unfold isReducibleSpelling isReducibleSpellingB at h
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨m, hm, l1, hl1, l2, hl2, hconds⟩ := h
  rcases hconds with ⟨⟨⟨⟨ho1, ho2⟩, hov1⟩, hov2⟩, hcomp⟩
  exact ⟨m, hm, l1, l2, ho1, ho2, List.mem_range.mp hl1, List.mem_range.mp hl2,
    hov1, hov2, hcomp⟩

/-! ## The main well-founded expansion theorem -/

/-- **Every proper edge has a finite expansion into irreducible edges spelling
the same word.**  For an edge `e` of the complete `overlapEdges` graph over
equal-length reads, there is a chain `es` that starts at `e.sx`, ends at `e.sy`,
all of whose edges are graph edges and are *not* spelling-preservingly reducible,
and whose spelled word is exactly the word spelled by `e`.

The proof is well-founded recursion on the extension length `Ext L e`: each
reduction step strictly decreases it (`replacement_overlaps_longer`), so the
recursion terminates; each step preserves the spelled word
(`spellPath_eq_spellDirect` and `spellChain_append`). -/
theorem exists_irreducible_expansion
    (toList : W → List A) (rep rc : W → W) (L oMin : Nat) (verts : List W)
    (hLen : ∀ s ∈ strandsOf rc verts, (toList s).length = L)
    (e : BdEdge A W)
    (hsx : e.sx ∈ strandsOf rc verts) (hsy : e.sy ∈ strandsOf rc verts)
    (hmem : e ∈ overlapEdges A W toList rep rc L oMin verts)
    (hproper : e.len < L) :
    ∃ es : List (BdEdge A W),
      Chain e.sx es ∧ chainEnd e.sx es = e.sy ∧
        (∀ f ∈ es, f ∈ overlapEdges A W toList rep rc L oMin verts) ∧
        (∀ f ∈ es, ¬ isReducibleSpelling W toList rc L oMin verts f) ∧
        spellChain toList e.sx es = spellDirect (toList e.sx) (toList e.sy) e.len := by
  have key : ∀ n, ∀ e : BdEdge A W, Ext L e = n →
      e.sx ∈ strandsOf rc verts → e.sy ∈ strandsOf rc verts →
      e ∈ overlapEdges A W toList rep rc L oMin verts → e.len < L →
      ∃ es : List (BdEdge A W),
        Chain e.sx es ∧ chainEnd e.sx es = e.sy ∧
          (∀ f ∈ es, f ∈ overlapEdges A W toList rep rc L oMin verts) ∧
          (∀ f ∈ es, ¬ isReducibleSpelling W toList rc L oMin verts f) ∧
          spellChain toList e.sx es = spellDirect (toList e.sx) (toList e.sy) e.len := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro e he hsx hsy hmem hproper
        by_cases hred : isReducibleSpelling W toList rc L oMin verts e
        · obtain ⟨m, hm, l1, l2, _ho1, _ho2, hl1, hl2, hov1, hov2, hcomp⟩ :=
            exists_detour_of_reducible hred
          have hlong := replacement_overlaps_longer L e.len l1 l2 hl1 hl2 hcomp
          -- The two detour legs.
          set leg1 : BdEdge A W := bdEdge rep e.sx m l1 with hleg1
          set leg2 : BdEdge A W := bdEdge rep m e.sy l2 with hleg2
          have hleg1sx : leg1.sx = e.sx := by rw [hleg1]; rfl
          have hleg1sy : leg1.sy = m := by rw [hleg1]; rfl
          have hleg2sx : leg2.sx = m := by rw [hleg2]; rfl
          have hleg2sy : leg2.sy = e.sy := by rw [hleg2]; rfl
          have hleg1len : leg1.len = l1 := by rw [hleg1]; rfl
          have hleg2len : leg2.len = l2 := by rw [hleg2]; rfl
          have hleg1mem : leg1 ∈ overlapEdges A W toList rep rc L oMin verts :=
            bdEdge_mem_overlapEdges hsx hm ⟨_ho1, hl1⟩ hov1
          have hleg2mem : leg2 ∈ overlapEdges A W toList rep rc L oMin verts :=
            bdEdge_mem_overlapEdges hm hsy ⟨_ho2, hl2⟩ hov2
          have hlt1 : Ext L leg1 < n := by
            rw [← he]
            simp only [Ext, hleg1len]
            omega
          have hlt2 : Ext L leg2 < n := by
            rw [← he]
            simp only [Ext, hleg2len]
            omega
          obtain ⟨es1, hchain1, hend1, hmem1, hirr1, hspell1⟩ :=
            ih (Ext L leg1) hlt1 leg1 rfl hsx hm hleg1mem (by rw [hleg1len]; exact hl1)
          obtain ⟨es2, hchain2, hend2, hmem2, hirr2, hspell2⟩ :=
            ih (Ext L leg2) hlt2 leg2 rfl hm hsy hleg2mem (by rw [hleg2len]; exact hl2)
          -- Reassemble.
          have hchain1' : Chain e.sx es1 := by rw [← hleg1sx]; exact hchain1
          have hend1' : chainEnd e.sx es1 = m := by rw [← hleg1sx]; exact hend1
          have hchain2' : Chain m es2 := by rw [← hleg2sx]; exact hchain2
          refine ⟨es1 ++ es2, ?_, ?_, ?_, ?_, ?_⟩
          · -- Chain
            rw [chain_append]
            exact ⟨hchain1', by rw [hend1']; exact hchain2'⟩
          · -- chainEnd
            rw [chainEnd_append, hend1']
            rw [← hleg2sx, ← hleg2sy]
            exact hend2
          · -- membership
            intro f hf
            rw [List.mem_append] at hf
            exact hf.elim (hmem1 f) (hmem2 f)
          · -- irreducible
            intro f hf
            rw [List.mem_append] at hf
            exact hf.elim (hirr1 f) (hirr2 f)
          · -- spelled word
            have hsxLen : (toList e.sx).length = L := hLen e.sx hsx
            have hmLen : (toList m).length = L := hLen m hm
            have hsyLen : (toList e.sy).length = L := hLen e.sy hsy
            have hLsy1 : ∀ f ∈ es1, (toList f.sy).length = L := by
              intro f hf
              have := overlapEdges_mem_iff (hmem1 f hf)
              exact hLen f.sy this.2.2.2.1
            have hlen1 : ∀ f ∈ es1, f.len ≤ L := by
              intro f hf
              have := overlapEdges_mem_iff (hmem1 f hf)
              omega
            have hs1 : spellChain toList e.sx es1 = spellDirect (toList e.sx) (toList m) l1 := by
              rw [← hleg1sx, ← hleg1sy, ← hleg1len]
              exact hspell1
            have hs2 : spellChain toList m es2 = spellDirect (toList m) (toList e.sy) l2 := by
              rw [← hleg2sx, ← hleg2sy, ← hleg2len]
              exact hspell2
            rw [spellChain_append toList L e.sx es1 es2 hsxLen hLsy1 hlen1]
            rw [hend1', hs1, hs2]
            have hdirect := spellPath_eq_spellDirect (L := L) (l1 := l1) (l2 := l2)
              (l := e.len) (sx := toList e.sx) (m := toList m) (sy := toList e.sy)
              hsxLen hmLen hsyLen hl1 hl2 hproper hov1 hov2 hcomp
            rw [← hdirect]
            simp only [spellPath, spellDirect]
            rw [List.drop_append_of_le_length (h := le_of_eq hmLen.symm)]
            rw [show (toList m).drop L = [] from by rw [← hmLen, List.drop_length],
              List.nil_append, List.append_assoc]
        · -- irreducible: the edge itself is the chain
          refine ⟨[e], ?_, ?_, ?_, ?_, ?_⟩
          · exact ⟨rfl, trivial⟩
          · rfl
          · intro f hf
            rw [List.mem_singleton] at hf
            rwa [hf]
          · intro f hf
            rw [List.mem_singleton] at hf
            rwa [hf]
          · simp only [spellChain, spellDirect]
  exact key (Ext L e) e rfl hsx hsy hmem hproper

/-- **Language preservation of the simultaneous spelling-preserving transitive
reduction.**  Every edge of the complete `overlapEdges` graph over equal-length
reads has a finite expansion into a chain of edges that all lie in the
*transitively reduced* graph `transitivelyReducedSpelling` and that spells the
same word as the original edge.  This is the global, simultaneous statement: it
does not assume any particular detour leg survives, because reducible legs are
themselves recursively expanded until irreducible. -/
theorem reduction_preserves_language
    (toList : W → List A) (rep rc : W → W) (L oMin : Nat) (verts : List W)
    (hLen : ∀ s ∈ strandsOf rc verts, (toList s).length = L)
    (e : BdEdge A W)
    (hmem : e ∈ overlapEdges A W toList rep rc L oMin verts) :
    ∃ es : List (BdEdge A W),
      Chain e.sx es ∧ chainEnd e.sx es = e.sy ∧
        (∀ f ∈ es, f ∈ transitivelyReducedSpelling W toList rc L oMin verts
          (overlapEdges A W toList rep rc L oMin verts)) ∧
        spellChain toList e.sx es = spellDirect (toList e.sx) (toList e.sy) e.len := by
  have hb := overlapEdges_mem_iff hmem
  obtain ⟨es, hchain, hend, hmemEs, hirrEs, hspell⟩ :=
    exists_irreducible_expansion toList rep rc L oMin verts hLen e hb.2.2.1 hb.2.2.2.1
      hmem hb.2.1
  refine ⟨es, hchain, hend, ?_, hspell⟩
  intro f hf
  have hfmem := hmemEs f hf
  have hfirr := hirrEs f hf
  unfold transitivelyReducedSpelling
  rw [List.mem_filter]
  refine ⟨hfmem, ?_⟩
  unfold isReducibleSpelling at hfirr
  cases hb' : isReducibleSpellingB W toList rc L oMin verts f with
  | false => rfl
  | true => exact absurd hb' hfirr

/-! ## Finite positive regression: a genuinely two-level cascade

The existing `Section62SpellingReductionCandidate` regression removes a `1`-overlap
through two maximal `2`-overlaps, which are themselves irreducible.  To exercise
the *simultaneous* content of this module we need a detour leg that is itself
reducible, so that a one-step replacement would **not** survive the full
reduction.

Four length-`5` observed reads over `{0,…,4}`:

* `sx = 01234`, `m₁ = 23412`, `m₂ = 12341`, `sy = 41200`.

Then `sx → sy` (overlap `1`) is reducible through `m₁` (`3 + 3 = 5 + 1`), and its
first leg `sx → m₁` (overlap `3`) is itself reducible through `m₂`
(`4 + 4 = 5 + 3`).  The fully expanded chain `sx → m₂ → m₁ → sy` uses the two
maximal `4`-overlaps and the surviving `3`-overlap `m₁ → sy`, all irreducible,
and spells exactly the direct `1`-overlap's word.  This is a concrete instance of
`exists_irreducible_expansion` in which the naive one-step detour legs do **not**
survive. -/

private def cascadeWord : Fin 4 → List Nat
  | 0 => [0, 1, 2, 3, 4] -- sx
  | 1 => [2, 3, 4, 1, 2] -- m₁
  | 2 => [1, 2, 3, 4, 1] -- m₂
  | _ => [4, 1, 2, 0, 0] -- sy

private def cascadeVerts : List (Fin 4) := [0, 1, 2, 3]
private def cascadeRc : Fin 4 → Fin 4 := id
private def cascadeRep : Fin 4 → Fin 4 := id

private def cascadeGraph : List (BdEdge Nat (Fin 4)) :=
  overlapEdges Nat (Fin 4) cascadeWord cascadeRep cascadeRc 5 1 cascadeVerts

/-- The direct `1`-overlap `sx → sy`. -/
private def cascadeDirect : BdEdge Nat (Fin 4) := bdEdge cascadeRep 0 3 1
/-- The one-step detour's first leg `sx → m₁` (`3`-overlap), itself reducible. -/
private def cascadeLeg : BdEdge Nat (Fin 4) := bdEdge cascadeRep 0 1 3
/-- The one-step detour's second leg `m₁ → sy` (`3`-overlap), irreducible. -/
private def cascadeLeg2 : BdEdge Nat (Fin 4) := bdEdge cascadeRep 1 3 3
/-- First edge of the fully expanded chain, `sx → m₂` (`4`-overlap). -/
private def cascadeF1 : BdEdge Nat (Fin 4) := bdEdge cascadeRep 0 2 4
/-- Second edge of the fully expanded chain, `m₂ → m₁` (`4`-overlap). -/
private def cascadeF2 : BdEdge Nat (Fin 4) := bdEdge cascadeRep 2 1 4

theorem cascade_direct_in_graph : cascadeDirect ∈ cascadeGraph := by decide
theorem cascade_leg_in_graph : cascadeLeg ∈ cascadeGraph := by decide
theorem cascade_leg2_in_graph : cascadeLeg2 ∈ cascadeGraph := by decide
theorem cascade_f1_in_graph : cascadeF1 ∈ cascadeGraph := by decide
theorem cascade_f2_in_graph : cascadeF2 ∈ cascadeGraph := by decide

/-- The direct edge is reducible. -/
theorem cascade_direct_reducible :
    isReducibleSpellingB (Fin 4) cascadeWord cascadeRc 5 1 cascadeVerts
      cascadeDirect = true := by
  decide

/-- **The first detour leg is itself reducible**: a one-step replacement would
not survive the full reduction, so this genuinely needs the simultaneous
expansion. -/
theorem cascade_leg_reducible :
    isReducibleSpellingB (Fin 4) cascadeWord cascadeRc 5 1 cascadeVerts
      cascadeLeg = true := by
  decide

/-- The two maximal-`4` overlaps of the expanded chain are irreducible. -/
theorem cascade_f1_irreducible :
    isReducibleSpellingB (Fin 4) cascadeWord cascadeRc 5 1 cascadeVerts
      cascadeF1 = false := by
  decide
theorem cascade_f2_irreducible :
    isReducibleSpellingB (Fin 4) cascadeWord cascadeRc 5 1 cascadeVerts
      cascadeF2 = false := by
  decide

/-- The surviving `3`-overlap `m₁ → sy` is irreducible: there is no observed read
giving the required `4 + 4` detour. -/
theorem cascade_leg2_irreducible :
    isReducibleSpellingB (Fin 4) cascadeWord cascadeRc 5 1 cascadeVerts
      cascadeLeg2 = false := by
  decide

/-- The fully expanded chain `sx → m₂ → m₁ → sy` is a genuine chain from the
direct edge's departure to its arrival. -/
theorem cascade_chain :
    Chain cascadeDirect.sx [cascadeF1, cascadeF2, cascadeLeg2] ∧
      chainEnd cascadeDirect.sx [cascadeF1, cascadeF2, cascadeLeg2] = cascadeDirect.sy := by
  constructor
  · exact ⟨rfl, rfl, rfl, trivial⟩
  · rfl

/-- The fully expanded chain spells exactly the direct `1`-overlap's word, so the
two-level cascade is spelling-preserving. -/
theorem cascade_spell :
    spellChain cascadeWord cascadeDirect.sx [cascadeF1, cascadeF2, cascadeLeg2] =
      spellDirect (cascadeWord cascadeDirect.sx) (cascadeWord cascadeDirect.sy)
        cascadeDirect.len := by
  decide

#print axioms exists_detour_of_reducible
#print axioms exists_irreducible_expansion
#print axioms reduction_preserves_language
#print axioms cascade_spell

end AssemblyP1.Section62SimultaneousReduction
