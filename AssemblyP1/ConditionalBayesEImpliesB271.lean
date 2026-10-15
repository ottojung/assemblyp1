import AssemblyP1.ConditionalVsOrdinaryMLSeparation
import AssemblyP1.ConditionalVsMLGenomeAdapter271
import Mathlib

/-!
# When does conditional recovery imply ordinary ML recovery? (issue #271, goal 5)

**Status: abstract finite-model theorem, Lean kernel-checked. This is NOT a
source-faithful genome witness.**

Issue #271 goal 5 asks precisely which assumption refinements establish the
implication `E → B` — that certain conditional-Bayes recovery under the side
information `E` yields ordinary R-only maximum-likelihood recovery — and which
merely refute it. The merged `AssemblyP1/ConditionalVsOrdinaryMLSeparation`
module exhibits the *unrestricted* separation `A ∧ ¬B` on a two-candidate toy.
This module isolates a sufficient refinement that repairs the implication, for an
**arbitrary finite candidate type** `Θ` and observation type `X` over any
linear ordered field.

The refinement is *ML-soundness* of the side information:

> `E` is ML-sound when `E h x` can only hold for a candidate `h` that is already
> an ordinary maximum-likelihood maximizer at `x`:
> `∀ h x, E h x → MLMax p h x`.

* `condCertain_imp_MLMax_of_MLsound` — **the refinement that establishes
  `E → B`.** If `E` is ML-sound, then conditional certainty on `g` implies
  `g` is an ordinary ML maximizer. The proof only needs the one fact that
  posterior certainty forces `E g x` (`condCertain_imp_E`), which holds with no
  positivity hypotheses.
* `not_MLsound_of_witness` — **the refutation.** If at some `(g, x)` the side
  information holds (`E g x`) while `g` is not an ML maximizer, then `E` is not
  ML-sound. The merged toy's `sideInfo` is exactly such a witness
  (`toy_sideInfo_not_MLsound`): it is the *failure* of ML-soundness that lets
  conditional recovery be certain while ordinary ML strictly prefers a wrong
  candidate.
* `condCertain_EML_iff_unique` — **the boundary case `E = MLMax`.** When the side
  information is *defined* to be the maximizer certificate `EML p h x := MLMax p
  h x`, conditional certainty on `g` is equivalent to `g` being the unique
  ordinary ML maximizer (under positive prior and positive likelihood). So
  choosing `E` to be the maximizer predicate makes `A` and `B` coincide, while
  the toy's truth-dependent `E` deliberately does not.

This is the exact sense in which "knowing the truth satisfies `F`" as supplied
side information is **not** the same as running ordinary ML over `F`-qualified
candidates: ML-soundness of the supplied `E` is *sufficient* for the implication
`E → B`, and the implication can fail when `E` is not ML-sound (as the toy's and
the genome adapter's unsound `E` show). Necessity of ML-soundness is not claimed.

No `sorry`/`admit`/`axiom`/`native_decide`; the axiom audit is in
`AxiomAudit271.lean`.
-/

set_option linter.unusedSectionVars false

namespace AssemblyP1.ConditionalBayesEImpliesB271

open AssemblyP1.ConditionalVsOrdinaryMLSeparation

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {Θ X : Type*} [Fintype Θ] [DecidableEq Θ]

/-- Ordinary maximum-likelihood maximizer predicate (ties allowed): `h` scores
at least as high as every candidate at the fixed observation `x`. The prior and
the side information do not enter. -/
def MLMax (p : Θ → X → 𝕜) (h : Θ) (x : X) : Prop :=
  ∀ h' : Θ, p h' x ≤ p h x

omit [Fintype Θ] [DecidableEq Θ] in
/-- Joint mass `π h · p_h(x)`. -/
def Joint (π : Θ → 𝕜) (p : Θ → X → 𝕜) (h : Θ) (x : X) : 𝕜 :=
  π h * p h x

omit [DecidableEq Θ] in
/-- Joint mass with the side-information indicator made explicit:
`π h · p_h(x) · 1_{E(h, x)}`. -/
def JointE (π : Θ → 𝕜) (p : Θ → X → 𝕜) (E : Θ → X → Prop) [DecidableRel E]
    (h : Θ) (x : X) : 𝕜 :=
  if E h x then Joint π p h x else 0

omit [DecidableEq Θ] in
/-- Predictive mass under the side information `E`: `∑_h π h · p_h(x) · 1_{E(h,x)}`. -/
def PredictiveE (π : Θ → 𝕜) (p : Θ → X → 𝕜) (E : Θ → X → Prop) [DecidableRel E]
    (x : X) : 𝕜 :=
  ∑ h, JointE π p E h x

omit [DecidableEq Θ] in
/-- Posterior under the side information `E`: `P(θ = h | R = x, E)`. -/
def PosteriorE (π : Θ → 𝕜) (p : Θ → X → 𝕜) (E : Θ → X → Prop) [DecidableRel E]
    (x : X) (h : Θ) : 𝕜 :=
  JointE π p E h x / PredictiveE π p E x

omit [DecidableEq Θ] in
/-- Conditional recovery is certain at `x` under `E` when some candidate's
conditional posterior is exactly `1`. -/
def CondCertain (π : Θ → 𝕜) (p : Θ → X → 𝕜) (E : Θ → X → Prop) [DecidableRel E]
    (x : X) : Prop :=
  ∃ g, PosteriorE π p E x g = 1

/-! ## The single fact the refinement needs: certainty forces `E` -/

omit [DecidableEq Θ] in
/-- **Posterior certainty forces the side information.** If the conditional
posterior on `g` is `1`, then `E g x` holds. No positivity or normalization
hypothesis is needed: `PosteriorE = 1` forces the predictive mass to be nonzero,
hence `JointE g x ≠ 0`, hence the indicator cannot be false. -/
theorem condCertain_imp_E {π : Θ → 𝕜} {p : Θ → X → 𝕜} {E : Θ → X → Prop}
    [DecidableRel E] {x : X} {g : Θ} (h1 : PosteriorE π p E x g = 1) :
    E g x := by
  have hden : PredictiveE π p E x ≠ 0 := by
    intro h0
    rw [PosteriorE, h0, div_zero] at h1
    exact zero_ne_one h1
  have heq : JointE π p E g x = PredictiveE π p E x := by
    have := (div_eq_iff hden).mp h1
    simpa using this
  have hne : JointE π p E g x ≠ 0 := by
    rw [heq]; exact hden
  by_contra hEx
  exact hne (by unfold JointE; exact ite_eq_right hEx)

/-! ## The refinement that establishes `E → B` -/

omit [Fintype Θ] [DecidableEq Θ] in
/-- **ML-soundness.** The side information `E` never holds for a candidate that
is not already an ordinary maximum-likelihood maximizer. This is the exact
assumption refinement under which conditional recovery implies ordinary ML
recovery. -/
def MLSound (p : Θ → X → 𝕜) (E : Θ → X → Prop) : Prop :=
  ∀ h x, E h x → MLMax p h x

omit [DecidableEq Θ] in
/-- **`E → B`, established.** If the side information is ML-sound, then
conditional certainty on `g` at `x` implies `g` is an ordinary ML maximizer at
`x`: the side information cannot manufacture recovery of a candidate that the
ordinary likelihood rejects. -/
theorem condCertain_imp_MLMax_of_MLsound {π : Θ → 𝕜} {p : Θ → X → 𝕜}
    {E : Θ → X → Prop} [DecidableRel E] {x : X} {g : Θ}
    (hE : MLSound p E) (h1 : PosteriorE π p E x g = 1) : MLMax p g x :=
  hE g x (condCertain_imp_E h1)

omit [DecidableEq Θ] in
/-- The packaged form: ML-soundness upgrades conditional certainty into ordinary
ML recovery, with no prior or likelihood-positivity side conditions. -/
theorem condCertain_imp_MLMax_exists_of_MLsound {π : Θ → 𝕜} {p : Θ → X → 𝕜}
    {E : Θ → X → Prop} [DecidableRel E] {x : X}
    (hE : MLSound p E) (h : CondCertain π p E x) : ∃ g, MLMax p g x := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, condCertain_imp_MLMax_of_MLsound hE hg⟩

omit [Fintype Θ] [DecidableEq Θ] in
/-- **`E → B`, refuted for an unsound `E`.** If `E` holds at `(g, x)` while `g`
is not an ordinary ML maximizer, then `E` is not ML-sound. This is the exact
obstruction the merged toy exploits: its truth-dependent `E` holds on the truth
at a read where the truth is not a maximizer. -/
theorem not_MLsound_of_witness {p : Θ → X → 𝕜} {E : Θ → X → Prop}
    {g : Θ} {x : X} (hE : E g x) (hnot : ¬ MLMax p g x) : ¬ MLSound p E :=
  fun hs => hnot (hs g x hE)

/-! ## The fibre characterization of conditional certainty

For the boundary case `E = MLMax` we need the full support-collapse form: a
posterior of `1` forces every *other* candidate's conditional joint mass to
vanish. This generalizes `ConditionalVsOrdinaryMLSeparation.condPosterior_one_imp`
from the two-candidate toy to an arbitrary finite candidate type. -/

omit [DecidableEq Θ] in
/-- Conditional joint masses are nonnegative under a nonnegative prior and
nonnegative likelihood. -/
theorem jointE_nonneg {π : Θ → 𝕜} {p : Θ → X → 𝕜} {E : Θ → X → Prop}
    [DecidableRel E] (hπ : ∀ h, 0 ≤ π h) (hp : ∀ h x, 0 ≤ p h x) (h : Θ) (x : X) :
    0 ≤ JointE π p E h x := by
  unfold JointE Joint
  split
  · exact mul_nonneg (hπ h) (hp h x)
  · exact le_refl 0

omit [DecidableEq Θ] in
theorem predictiveE_nonneg {π : Θ → 𝕜} {p : Θ → X → 𝕜} {E : Θ → X → Prop}
    [DecidableRel E] (hπ : ∀ h, 0 ≤ π h) (hp : ∀ h x, 0 ≤ p h x) (x : X) :
    0 ≤ PredictiveE π p E x :=
  Finset.sum_nonneg (fun h _ => jointE_nonneg hπ hp h x)

/-- **Support-collapse boundary (general finite candidate type).** A conditional
posterior of `1` on `g` at `x` holds exactly when `g` has positive joint mass,
satisfies `E`, and every other candidate's conditional joint mass vanishes. -/
theorem posteriorE_eq_one_imp {π : Θ → 𝕜} {p : Θ → X → 𝕜} {E : Θ → X → Prop}
    [DecidableRel E] (hπ : ∀ h, 0 ≤ π h) (hp : ∀ h x, 0 ≤ p h x)
    {x : X} {g : Θ} (h1 : PosteriorE π p E x g = 1) :
    0 < Joint π p g x ∧ E g x ∧ ∀ h, h ≠ g → JointE π p E h x = 0 := by
  have hden : PredictiveE π p E x ≠ 0 := by
    intro h0
    rw [PosteriorE, h0, div_zero] at h1
    exact zero_ne_one h1
  have heq : JointE π p E g x = PredictiveE π p E x := by
    have := (div_eq_iff hden).mp h1
    simpa using this
  have hje_pos : 0 < JointE π p E g x := by
    rw [heq]
    exact lt_of_le_of_ne (predictiveE_nonneg hπ hp x) (Ne.symm hden)
  have hE : E g x := condCertain_imp_E h1
  have hjpos : 0 < Joint π p g x := by
    have : JointE π p E g x = Joint π p g x := by
      unfold JointE; exact ite_eq_left hE
    rwa [this] at hje_pos
  refine ⟨hjpos, hE, ?_⟩
  have hsum : ∑ h', JointE π p E h' x = JointE π p E g x := by
    simpa only [PredictiveE] using heq.symm
  have herase : ∑ h' ∈ Finset.univ.erase g, JointE π p E h' x = 0 := by
    have hdecomp := Finset.sum_erase_add (s := Finset.univ)
      (f := fun h' => JointE π p E h' x) (Finset.mem_univ g)
    rw [hsum] at hdecomp
    linarith
  intro h hne
  exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => jointE_nonneg hπ hp i x)).mp herase h
    (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ h⟩)

/-- The converse: if `g` has positive joint mass, satisfies `E`, and every other
candidate's conditional joint mass vanishes, its conditional posterior is `1`. -/
theorem posteriorE_of_fibre {π : Θ → 𝕜} {p : Θ → X → 𝕜} {E : Θ → X → Prop}
    [DecidableRel E] {x : X} {g : Θ} (hE : E g x) (hjpos : 0 < Joint π p g x)
    (hoff : ∀ h, h ≠ g → JointE π p E h x = 0) :
    PosteriorE π p E x g = 1 := by
  have hcj : JointE π p E g x = Joint π p g x := by
    unfold JointE; exact ite_eq_left hE
  have hden : PredictiveE π p E x = Joint π p g x := by
    unfold PredictiveE
    rw [Finset.sum_eq_single g]
    · exact hcj
    · intro h _ hne; exact hoff h hne
    · intro hg; exact absurd (Finset.mem_univ g) hg
  rw [PosteriorE, hden, hcj, div_self (ne_of_gt hjpos)]

/-- **The general (A)-boundary.** Conditional recovery is certain at `x` under
`E` iff the posterior support fibre is a singleton in the support-collapse
sense: some `g` has positive joint mass, satisfies `E`, and every other
candidate's conditional joint mass vanishes. -/
theorem condCertain_iff {π : Θ → 𝕜} {p : Θ → X → 𝕜} {E : Θ → X → Prop}
    [DecidableRel E] (hπ : ∀ h, 0 ≤ π h) (hp : ∀ h x, 0 ≤ p h x) {x : X} :
    CondCertain π p E x ↔
      ∃ g, 0 < Joint π p g x ∧ E g x ∧ ∀ h, h ≠ g → JointE π p E h x = 0 := by
  constructor
  · rintro ⟨g, h1⟩
    exact ⟨g, posteriorE_eq_one_imp hπ hp h1⟩
  · rintro ⟨g, hjpos, hE, hoff⟩
    exact ⟨g, posteriorE_of_fibre hE hjpos hoff⟩

/-! ## The boundary case `E = MLMax`: `A` and `B` coincide -/

omit [DecidableEq Θ] in
/-- The side information that *is* the maximizer certificate. -/
def EML (p : Θ → X → 𝕜) (h : Θ) (x : X) : Prop := MLMax p h x

omit [DecidableEq Θ] in
instance (p : Θ → X → 𝕜) : DecidableRel (EML p) := fun h x =>
  inferInstanceAs (Decidable (∀ h' : Θ, p h' x ≤ p h x))

omit [DecidableEq Θ] in
/-- `EML` is trivially ML-sound. -/
theorem mlSound_EML (p : Θ → X → 𝕜) : MLSound p (EML p) := fun _ _ h => h

/-- **`E = MLMax` collapses `A` and `B`.** Under a positive prior and positive
likelihood, conditional certainty under the maximizer-certificate side
information is equivalent to `g` being the *unique* ordinary ML maximizer. So
the refinement "supply `E` = `MLMax`" turns the incomparable guarantees into the
same statement, while the toy's truth-dependent `E` is not `EML` and does not
collapse them. -/
theorem condCertain_EML_iff_unique {π : Θ → 𝕜} {p : Θ → X → 𝕜}
    (hπ : ∀ h, 0 ≤ π h) (hp : ∀ h x, 0 ≤ p h x) {x : X}
    (hpos : ∀ h, 0 < Joint π p h x) :
    CondCertain π p (EML p) x ↔
      ∃ g, MLMax p g x ∧ ∀ h, MLMax p h x → h = g := by
  constructor
  · rintro ⟨g, h1⟩
    obtain ⟨_, hE, hoff⟩ := posteriorE_eq_one_imp hπ hp h1
    refine ⟨g, hE, ?_⟩
    intro h hh
    by_contra hne
    have hje : JointE π p (EML p) h x = 0 := hoff h hne
    have hh' : EML p h x := hh
    have : JointE π p (EML p) h x = Joint π p h x := by
      unfold JointE; exact ite_eq_left hh'
    rw [this] at hje
    exact absurd hje (ne_of_gt (hpos h))
  · rintro ⟨g, hg, huniq⟩
    refine ⟨g, posteriorE_of_fibre (hE := hg) (hpos g) ?_⟩
    intro h hne
    have hnot : ¬ EML p h x := fun hh => hne (huniq h hh)
    unfold JointE; exact ite_eq_right hnot

/-! ## Connection to the merged toy: its `E` is exactly *not* ML-sound -/

instance : Fintype Hypothesis where
  elems := {Hypothesis.A, Hypothesis.B}
  complete := by intro h; cases h <;> simp

/-- The merged toy's side information `sideInfo`, transported to the general
interface, is not ML-sound: at `r = 0` it holds under the truth `A`, which is not
an ordinary ML maximizer there (`lik A r0 = 1/4 < 3/4 = lik B r0`). This is the
precise reason the toy achieves `A ∧ ¬B`: the refinement of
`condCertain_imp_MLMax_of_MLsound` is violated. -/
theorem toy_sideInfo_not_MLsound :
    ¬ MLSound (fun (h : Hypothesis) (r : Obs) => lik h r) sideInfo := by
  refine not_MLsound_of_witness (p := fun (h : Hypothesis) (r : Obs) => lik h r)
    (E := sideInfo) (g := Hypothesis.A) (x := Obs.r0) ?_ ?_
  · simp [sideInfo]
  · intro hmax
    exact absurd (hmax Hypothesis.B) (by norm_num [lik])

/-! ## Connection to the source-faithful genome adapter: its `E` is not ML-sound -/

/-- The genome-level latent-start information-feasibility predicate `E` of the
merged #271 adapter (`AssemblyP1.ConditionalVsMLGenomeAdapter271`) is **not**
ML-sound: at read `00` it holds on the truth orbit `1` (`E_one_00`), which is not
an ordinary ML maximizer there (`sep_truth_not_ml`, `1/4 < 1/2`). This is the
source-faithful instantiation of the obstruction of
`not_MLsound_of_witness`: the conditional-recovery witness is separated from
ordinary ML precisely because its candidate-specific feasibility event is not a
maximizer certificate. -/
theorem genome_E_not_MLsound :
    ¬ MLSound (fun i r => AssemblyP1.ConditionalVsMLGenomeAdapter271.p i r)
      AssemblyP1.ConditionalVsMLGenomeAdapter271.E :=
  not_MLsound_of_witness
    (p := fun i r => AssemblyP1.ConditionalVsMLGenomeAdapter271.p i r)
    (E := AssemblyP1.ConditionalVsMLGenomeAdapter271.E)
    (g := 1) (x := AssemblyP1.ConditionalVsMLGenomeAdapter271.r2 0 0)
    AssemblyP1.ConditionalVsMLGenomeAdapter271.E_one_00
    AssemblyP1.ConditionalVsMLGenomeAdapter271.sep_truth_not_ml

end AssemblyP1.ConditionalBayesEImpliesB271
