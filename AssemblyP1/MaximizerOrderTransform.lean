import Mathlib

/-!
# Strictly monotone transformations preserve maximizers

For a function `f : α → β` on any domain `s`, an order embedding of the
codomain preserves its complete set of maximizers and minimizers.  In
particular, a strictly monotone `g : β → γ` preserves both `IsMaxOn` and
`IsMinOn` witnesses for `f` after composing `g ∘ f`.  No finiteness,
nonemptiness, continuity, or existence of extrema is assumed.  The converse
also holds when `g` is strictly monotone, so the sets of maximizers/minimizers
are equivalent pointwise.
-/

namespace AssemblyP1.MaximizerOrderTransform

variable {α β γ : Type*} [Preorder β] [Preorder γ]

/-- A strictly monotone transformation preserves and reflects being a
maximizer on an arbitrary domain. -/
theorem isMaxOn_comp_iff (g : β → γ) (hg : StrictMono g)
    (f : α → β) (s : Set α) (a : α) :
    IsMaxOn (g ∘ f) s a ↔ IsMaxOn f s a := by
  simp only [IsMaxOn, Function.comp_apply]
  constructor
  · intro h x hx
    exact (hg.le_iff_le).1 (h x hx)
  · intro h x hx
    exact (hg.le_iff_le).2 (h x hx)

/-- A strictly monotone transformation preserves and reflects being a
minimizer on an arbitrary domain. -/
theorem isMinOn_comp_iff (g : β → γ) (hg : StrictMono g)
    (f : α → β) (s : Set α) (a : α) :
    IsMinOn (g ∘ f) s a ↔ IsMinOn f s a := by
  simp only [IsMinOn, Function.comp_apply]
  constructor
  · intro h x hx
    exact (hg.le_iff_le).1 (h x hx)
  · intro h x hx
    exact (hg.le_iff_le).2 (h x hx)

/-- A strictly antitone transformation reverses maximizers into minimizers.
This is the form used when a log-likelihood is negated to obtain a loss. -/
theorem isMinOn_comp_iff_of_strictAnti (g : β → γ) (hg : StrictAnti g)
    (f : α → β) (s : Set α) (a : α) :
    IsMinOn (g ∘ f) s a ↔ IsMaxOn f s a := by
  simp only [IsMinOn, IsMaxOn, Function.comp_apply]
  constructor
  · intro h x hx
    exact (hg.le_iff_ge).1 (h x hx)
  · intro h x hx
    exact (hg.le_iff_ge).2 (h x hx)

/-- A strictly antitone transformation reverses minimizers into maximizers. -/
theorem isMaxOn_comp_iff_of_strictAnti (g : β → γ) (hg : StrictAnti g)
    (f : α → β) (s : Set α) (a : α) :
    IsMaxOn (g ∘ f) s a ↔ IsMinOn f s a := by
  simp only [IsMaxOn, IsMinOn, Function.comp_apply]
  constructor
  · intro h x hx
    exact (hg.le_iff_ge).1 (h x hx)
  · intro h x hx
    exact (hg.le_iff_ge).2 (h x hx)

end AssemblyP1.MaximizerOrderTransform
