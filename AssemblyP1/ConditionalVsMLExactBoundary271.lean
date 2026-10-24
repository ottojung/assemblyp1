import AssemblyP1.ConditionalBayesEImpliesB271

/-!
# Exact-pmf bridge between conditional Bayes and ordinary ML (#271)

This small interface theorem connects the issue's two guarantees without
identifying their boundaries: conditional posterior certainty implies ordinary
ML truth-maximality when the supplied event is ML-sound.  Conversely, with the
event equal to the ML-maximizer predicate, conditional certainty is equivalent
to a *unique* ML maximizer.  All statements are over the same exact likelihood
table and positive finite prior; no MB09 surrogate is involved.

This is an abstract finite-model result, not a source-faithful genome witness.
-/

namespace AssemblyP1.ConditionalVsMLExactBoundary271

open AssemblyP1.ConditionalBayesEImpliesB271

theorem ml_sound_side_information_transfers_truth_maximality
    {Θ X : Type*} [Fintype Θ] [DecidableEq Θ]
    {π : Θ → ℚ} {p : Θ → X → ℚ} {E : Θ → X → Prop} [DecidableRel E]
    {x : X} {g : Θ}
    (hSound : MLSound p E)
    (hCertain : PosteriorE π p E x g = 1) :
    MLMax p g x :=
  condCertain_imp_MLMax_of_MLsound hSound hCertain

theorem maximizer_certificate_boundary_is_unique_ml
    {Θ X : Type*} [Fintype Θ] [DecidableEq Θ]
    {π : Θ → ℚ} {p : Θ → X → ℚ}
    (hπ : ∀ h, 0 ≤ π h) (hp : ∀ h x, 0 ≤ p h x) {x : X}
    (hpos : ∀ h, 0 < Joint π p h x) :
    CondCertain π p (EML p) x ↔
      ∃ g, MLMax p g x ∧ ∀ h, MLMax p h x → h = g :=
  condCertain_EML_iff_unique hπ hp hpos

end AssemblyP1.ConditionalVsMLExactBoundary271
