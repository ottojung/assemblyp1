import AssemblyP1.Section62BidirectedFlow
import Mathlib.Tactic

/-!
# Diagnostic: the literal shorter-overlap reduction predicate is vacuous

The current `Section62Flow.isReducibleB` uses lengths `l₁ < e.len` and
`l₂ < e.len` to spell a direct overlap of length `e.len`.
For proper read overlaps, the composition equation is arithmetically
incompatible with these inequalities. This audit deliberately proves the
impossibility rather than quietly replacing the existing source model.
-/

namespace AssemblyP1.Section62Flow

theorem shorter_overlaps_cannot_compose
    (readLen directLen l₁ l₂ : ℕ)
    (hProper : directLen < readLen)
    (h₁ : l₁ < directLen) (h₂ : l₂ < directLen) :
    l₁ + l₂ - readLen ≠ directLen := by
  omega

theorem current_reducible_false_of_proper
    {A W : Type} [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rc : W → W)
    (readLen : ℕ) (verts : List W) (e : BdEdge A W)
    (hProper : e.len < readLen) :
    isReducibleB A W toList rc readLen verts e = false := by
  classical
  by_contra hnot
  have htrue : isReducibleB A W toList rc readLen verts e = true := by
    cases hb : isReducibleB A W toList rc readLen verts e <;> simp_all
  unfold isReducibleB at htrue
  simp only [List.any_eq_true] at htrue
  obtain ⟨v, hv, m, hm, l₁, hl₁, l₂, hl₂, h⟩ := htrue
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  omega


/-- The current literal predicate cannot remove any proper-overlap graph edge. -/
theorem transitivelyReduced_eq_self_of_proper
    {A W : Type} [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rc : W → W)
    (readLen : ℕ) (verts : List W) (edges : List (BdEdge A W))
    (hProper : ∀ e ∈ edges, e.len < readLen) :
    transitivelyReduced A W toList rc readLen verts edges = edges := by
  unfold transitivelyReduced
  apply List.filter_eq_self.mpr
  intro e he
  simp [current_reducible_false_of_proper toList rc readLen verts e (hProper e he)]

#print axioms shorter_overlaps_cannot_compose
#print axioms current_reducible_false_of_proper
#print axioms transitivelyReduced_eq_self_of_proper

end AssemblyP1.Section62Flow
