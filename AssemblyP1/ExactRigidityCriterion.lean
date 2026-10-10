import Mathlib

/-!
# Exact circulation rigidity criterion (issue #257)

This file formalizes the necessary-and-sufficient checkable condition for
uniqueness of positive length-`G` circulations on the oriented `L`-mer support
graph, Theorem 1 of `docs/source-notes/issue-257-rigid-read-graphs.md`.

> Let `A : E → ℤ` be a positive balanced circulation of total `G` on a finite
> directed support graph. Then `A` is rigid (the unique positive balanced
> circulation of total `G` on the support) **iff** there is no `δ : E → ℤ`
> that is nonzero on the support with `M δ = 0` (balanced), `∑ δ = 0`
> (zero-sum), and `δ ≥ 1 - A` on every edge.

## Support-domain statement (blocking-review repair, 2026-10-10)

The hypotheses `Pos`, `BalancedZ`, and `ZeroSum` inspect only the support
`edges : Finset E`. Concluding global equality `B = A` over all of `E` would
therefore overstate the content: a `B` agreeing with `A` on `edges` but
differing off-support satisfies every hypothesis, so `Rigid` as previously
stated was false for every `A` whenever `edges ≠ Finset.univ`. Following the
review, equality and the nonzero-`δ` side condition are **restricted to the
support domain** (equivalently: one may subtype the edge functions, or assume
`edges = Finset.univ`, to recover the global statement). This is the
"bounded nonzero-kernel-delta iff on that domain" of the review.

## What is proved in Lean

* `nonrigid_iff_exists_delta`: the exact iff above, with both directions
  constructive. The forward direction extracts `δ = B - A` from an alternative
  circulation `B` (nonzero on the support because `B ≠ A` there); the backward
  direction builds `B = A + δ` from a witness `δ` (which then differs from `A`
  on the support).

## Relation to `OrientedRigidity.lean`

That file proves the *sufficiency* theorem (vertex throughput `≤ 2` ⇒ rigid).
This file supplies the missing *exact* criterion: rigidity is equivalent to the
absence of a support-nonzero zero-sum circulation inside the box
`∏_e [1 - A(e), ∞)`. No throughput cap, strong connectivity, or repeat bound is
assumed here; the criterion is purely the integer-feasibility statement of
Theorem 1.
-/

namespace AssemblyP1.ExactRigidityCriterion

open Finset
open BigOperators

section ExactCriterion

variable {V E : Type} [DecidableEq V] [DecidableEq E]
variable (tail head : E → V) (nodes : Finset V) (edges : Finset E)

/-- Out-edges of `v` within the support. -/
private def outF (v : V) : Finset E := edges.filter (fun e => tail e = v)

/-- In-edges of `v` within the support. -/
private def inF (v : V) : Finset E := edges.filter (fun e => head e = v)

/-- Balance at every node over `ℤ`: an integer circulation. -/
def BalancedZ (f : E → ℤ) : Prop :=
  ∀ v ∈ nodes, ∑ e ∈ outF tail edges v, f e = ∑ e ∈ inF head edges v, f e

/-- Zero total sum over `ℤ`. -/
def ZeroSum (f : E → ℤ) : Prop :=
  ∑ e ∈ edges, f e = 0

/-- Positivity over `ℤ`: every edge carries at least `1`. -/
def Pos (f : E → ℤ) : Prop :=
  ∀ e ∈ edges, (1 : ℤ) ≤ f e

/-- The truth circulation `A` (coerced to `ℤ`) is rigid: it is the only
positive balanced integer circulation of total `G` **on the support** `edges`.
Equality is asserted on `edges` only — off-support values are unconstrained by
the hypotheses, so global equality `B = A` would overstate the content unless
`edges = Finset.univ`. -/
def Rigid (A : E → ℤ) (G : ℕ) : Prop :=
  ∀ B : E → ℤ, Pos edges B → BalancedZ tail head nodes edges B →
    (∑ e ∈ edges, B e = G) → ∀ e ∈ edges, B e = A e

omit [DecidableEq E] in
/-- **Theorem 1 (exact rigidity criterion, issue #257).** `A` is rigid **iff**
there is **no** `δ : E → ℤ` that is nonzero on the support with `M δ = 0`,
`∑ δ = 0`, and `δ ≥ 1 - A` on every edge. Equivalently: no integral zero-sum
circulation nonzero on the support fits inside the box `∏_e [1 - A(e), ∞)`.

All statements are on the support domain `edges : Finset E`; when
`edges = Finset.univ` (or after restricting `A`, `B`, `δ` to the support
subtype) this specializes to the global statement. -/
theorem nonrigid_iff_exists_delta
    (A : E → ℤ) (G : ℕ)
    (hAbal : BalancedZ tail head nodes edges A)
    (hAtot : ∑ e ∈ edges, A e = G) :
    (¬ Rigid tail head nodes edges A G) ↔
      ∃ δ : E → ℤ, (∃ e ∈ edges, δ e ≠ 0) ∧ BalancedZ tail head nodes edges δ ∧
        ZeroSum edges δ ∧ ∀ e ∈ edges, (1 - A e) ≤ δ e := by
  constructor
  · -- (⟹) An alternative circulation `B` yields the witness `δ = B - A`.
    intro hnr
    have hB : ∃ B : E → ℤ, Pos edges B ∧ BalancedZ tail head nodes edges B ∧
        (∑ e ∈ edges, B e = G) ∧ ∃ e ∈ edges, B e ≠ A e := by
      by_contra hcon
      apply hnr
      unfold Rigid
      intro B hBpos hBbal hBtot
      by_contra hBne
      refine hcon ⟨B, hBpos, hBbal, hBtot, ?_⟩
      by_contra hcon'
      apply hBne
      intro e he
      by_contra h'
      exact hcon' ⟨e, he, h'⟩
    obtain ⟨B, hBpos, hBbal, hBtot, ⟨e₀, he₀, hBne⟩⟩ := hB
    refine ⟨fun e => B e - A e, ⟨e₀, he₀, ?_⟩, ?_, ?_, ?_⟩
    · -- `δ` nonzero on the support
      show B e₀ - A e₀ ≠ 0
      omega
    · -- `M δ = 0`
      intro v hv
      have h1 := hBbal v hv
      have h2 := hAbal v hv
      show ∑ e ∈ outF tail edges v, (B e - A e)
          = ∑ e ∈ inF head edges v, (B e - A e)
      simp only [Finset.sum_sub_distrib]
      omega
    · -- `∑ δ = 0`
      have h1 := hBtot
      have h2 := hAtot
      show ∑ e ∈ edges, (B e - A e) = 0
      simp only [Finset.sum_sub_distrib]
      omega
    · -- `δ ≥ 1 - A`
      intro e he
      show (1 - A e) ≤ B e - A e
      have hB := hBpos e he
      omega
  · -- (⟸) A witness `δ` yields the alternative circulation `B = A + δ`.
    rintro ⟨δ, ⟨e₀, he₀, hδne⟩, hδbal, hδsum, hδbox⟩
    unfold Rigid
    push Not
    refine ⟨fun e => A e + δ e, ?_, ?_, ?_, ⟨e₀, he₀, ?_⟩⟩
    · -- `B ≥ 1`
      intro e he
      show (1:ℤ) ≤ A e + δ e
      have hδ := hδbox e he
      omega
    · -- `M B = 0`
      intro v hv
      have h1 := hδbal v hv
      have h2 := hAbal v hv
      show ∑ e ∈ outF tail edges v, (A e + δ e)
          = ∑ e ∈ inF head edges v, (A e + δ e)
      simp only [Finset.sum_add_distrib]
      omega
    · -- `∑ B = G`
      have h1 : ∑ e ∈ edges, δ e = 0 := hδsum
      have h2 := hAtot
      show ∑ e ∈ edges, (A e + δ e) = G
      simp only [Finset.sum_add_distrib]
      omega
    · -- `B ≠ A` on the support
      show A e₀ + δ e₀ ≠ A e₀
      omega

end ExactCriterion

end AssemblyP1.ExactRigidityCriterion
