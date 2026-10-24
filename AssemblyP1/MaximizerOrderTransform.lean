import Mathlib

/-!
# Strictly monotone transformations preserve maximizers

For a function `f : α → β` on any domain `s`, a strictly monotone
`g : β → γ` preserves and reflects both `IsMaxOn` and `IsMinOn` witnesses
for `f` after composing `g ∘ f`; a strictly antitone `g` swaps them.
No finiteness, nonemptiness, continuity, or existence of extrema is assumed.
The intermediate type must be linearly ordered (required by Mathlib's
`StrictMono.le_iff_le` in this revision); the antitone pair additionally
needs `LinearOrder` on the target type since each direction contraposes on
one side.  Mathlib's `StrictAnti.le_iff_ge` is not used: its internal
`LinearOrder.toPartialOrder.toPreorder` instance path does not cohere with
the ambient typeclass search, so the antitone proofs contrapose directly
via `not_le` and trichotomy.

Finite-ML scope: for a fixed observed sample `x`, the exact-multinomial
likelihood and any strictly monotone reparameterization of it (for example
a log-likelihood on the positive-support cell) share the same maximizer set
over any candidate set.  This lemma is structure-independent (oriented or
reverse-complement molecule types, same or variable length, spelled genomes
or §6.2 flows) and settles no truth-maximality claim by itself.
-/

namespace AssemblyP1.MaximizerOrderTransform

/-- A strictly monotone transformation preserves and reflects being a
maximizer on an arbitrary domain. -/
theorem isMaxOn_comp_iff {α β γ : Type*} [LinearOrder β] [Preorder γ]
    (g : β → γ) (hg : StrictMono g)
    (f : α → β) (s : Set α) (a : α) :
    IsMaxOn (g ∘ f) s a ↔ IsMaxOn f s a := by
  simp only [IsMaxOn, IsMaxFilter, Filter.eventually_principal,
    Function.comp_apply]
  constructor
  · intro h x hx
    exact (hg.le_iff_le).1 (h x hx)
  · intro h x hx
    exact (hg.le_iff_le).2 (h x hx)

/-- A strictly monotone transformation preserves and reflects being a
minimizer on an arbitrary domain. -/
theorem isMinOn_comp_iff {α β γ : Type*} [LinearOrder β] [Preorder γ]
    (g : β → γ) (hg : StrictMono g)
    (f : α → β) (s : Set α) (a : α) :
    IsMinOn (g ∘ f) s a ↔ IsMinOn f s a := by
  simp only [IsMinOn, IsMinFilter, Filter.eventually_principal,
    Function.comp_apply]
  constructor
  · intro h x hx
    exact (hg.le_iff_le).1 (h x hx)
  · intro h x hx
    exact (hg.le_iff_le).2 (h x hx)

/-- A strictly antitone transformation reverses maximizers into minimizers.
This is the form used when a log-likelihood is negated to obtain a loss. -/
theorem isMinOn_comp_iff_of_strictAnti {α β γ : Type*} [LinearOrder β]
    [LinearOrder γ] (g : β → γ) (hg : StrictAnti g)
    (f : α → β) (s : Set α) (a : α) :
    IsMinOn (g ∘ f) s a ↔ IsMaxOn f s a := by
  simp only [IsMinOn, IsMinFilter, IsMaxOn, IsMaxFilter,
    Filter.eventually_principal, Function.comp_apply]
  constructor
  · intro h x hx
    by_contra hcon
    rw [not_le] at hcon
    exact absurd (hg hcon) (not_lt_of_ge (h x hx))
  · intro h x hx
    by_contra hcon
    rw [not_le] at hcon
    rcases lt_trichotomy (f x) (f a) with hlt | heq | hgt
    · exact absurd (hg hlt) (lt_asymm hcon)
    · rw [heq] at hcon
      exact absurd hcon (lt_irrefl _)
    · exact absurd (lt_of_le_of_lt (h x hx) hgt) (lt_irrefl _)

/-- A strictly antitone transformation reverses minimizers into maximizers. -/
theorem isMaxOn_comp_iff_of_strictAnti {α β γ : Type*} [LinearOrder β]
    [LinearOrder γ] (g : β → γ) (hg : StrictAnti g)
    (f : α → β) (s : Set α) (a : α) :
    IsMaxOn (g ∘ f) s a ↔ IsMinOn f s a := by
  simp only [IsMaxOn, IsMaxFilter, IsMinOn, IsMinFilter,
    Filter.eventually_principal, Function.comp_apply]
  constructor
  · intro h x hx
    by_contra hcon
    rw [not_le] at hcon
    exact absurd (hg hcon) (not_lt_of_ge (h x hx))
  · intro h x hx
    by_contra hcon
    rw [not_le] at hcon
    rcases lt_trichotomy (f x) (f a) with hlt | heq | hgt
    · exact absurd (lt_of_le_of_lt (h x hx) hlt) (lt_irrefl _)
    · rw [heq] at hcon
      exact absurd hcon (lt_irrefl _)
    · exact absurd (hg hgt) (lt_asymm hcon)

end AssemblyP1.MaximizerOrderTransform
