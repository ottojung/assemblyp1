import Mathlib
import AssemblyP1.FiniteBayesDecision
import AssemblyP1.IidMapMonotonicity

/-!
# AssemblyP1 finite circular-read orbit adapter (Antonina #269)

This module connects the merged abstract finite-Bayes/MAP decision theorem
(`AssemblyP1.FiniteBayesDecision`, PR #174) and its exact iid `n → n+1`
monotonicity bridge (`AssemblyP1.IidMapMonotonicity`, PR #193) to the concrete
AssemblyP1 circular read model.  It does **not** reprove the merged generic
finite-sum lemmas; it instantiates them.

## The read model

Fix a finite read alphabet `α`, a positive circular genome length `G`, and a
read length `L`.  A circular genome is a word `S : ZMod G → α` (`ZMod G` is
canonically `Fin G`; we use the additive-group structure so that rotation is a
genuine group action).  The oriented length-`L` window placed at a uniformly
sampled genomic start `s : ZMod G` is `window S s : Fin L → α`, and its exact
read pmf is the normalized window multiplicity

    readPmf S w = multiplicity_S(w) / |G|,   multiplicity_S(w) = #{s | window S s = w}.

This is the "uniformly sampled genomic starts" read model, not the MB09
fixed-`N` product-binomial pseudo-likelihood and not the §6.2 feasible-flow
optimization.  `readPmf_sum_one` kernel-checks the normalization
`∑_w readPmf S w = 1` from `∑_w multiplicity_S(w) = G` (every start contributes
exactly one window).

## Rotation is a genuine group action; reverse complement is separate

`rotWord S j` rotates the circle by `j`; `readPmf_rotWord` proves the oriented
read pmf is rotation invariant, so it descends to the rotation-orbit type
`Quotient (rotSetoid α G)` via `orbitReadPmf`.  The general principle is
`quotient_likelihood_well_defined_iff`: a likelihood descends to a genome
quotient **iff** it is constant on equivalence classes.  Rotation invariance
holds for the oriented one-strand read model.  Reverse-complement equivalence is
a *different* action, and an oriented one-strand read distribution need not be
RC-invariant; this file therefore quotients by rotation only and does not claim
an RC quotient.

## Priors on orbits vs priors on spellings

A prior may be placed on *orbit classes* rather than on raw spellings.  The
pushforward of the uniform prior on raw spellings is proportional to orbit size:
`spellingPushforwardPrior o = orbitSize(o) / |spellings|`
(`spellingPushforward_eq_uniform_iff_constant_orbitSize`).  It equals the uniform
orbit prior **iff all orbits have equal size**, so the two must not be
interchanged when orbits differ (RC-symmetric or nonprimitive circular genomes
have smaller orbits).  With the uniform orbit prior the MAP policy is exactly a
maximum-likelihood policy (`uniform_orbit_prior_ML`).

## What is and is not claimed

* `orbit_map_success_monotone` is **prior-averaged** zero-one success under the
  exact iid read model, nondecreasing in the number of reads `n`, for every `n`
  including `0`, for an arbitrary prior on orbit classes.  It is not a
  per-true-genome claim; `PerTruthDrop.perTruth_true_drops` is a kernel-checked
  counterexample of per-truth success *drop*.
* `CoverageConditional.conditionalSuccess_univ_eq` records that conditioning on a
  coverage event rescales the objective by the predictive mass `P(C)`; the
  conditional experiment is a different quantity from the unconditional Bayes
  average, and truth-dependent conditioning is Antonina #266, not this module.
* `ExactVsSurrogate.exact_ne_productBinomial` records that the exact iid
  likelihood of the observed read multiset is `∏_w p_w^{c_w}`, while the
  fixed-`N` product-binomial surrogate multiplies an extra
  `(1 - p_w)^{N - c_w}` factor per class; the two are not silently identified.
* The only external input is the finite circular read model itself; every
  statement below is kernel-checked with no `sorry`/`admit`/new axiom.
-/

namespace AssemblyP1.GenomeOrbitAdapter

open Finset BigOperators

/-- Rotate a circular word by `j`. -/
def rotWord {α : Type*} {G : ℕ} (S : ZMod G → α) (j : ZMod G) : ZMod G → α :=
  fun i => S (i + j)

@[simp] theorem rotWord_zero {α : Type*} {G : ℕ} (S : ZMod G → α) :
    rotWord S 0 = S := by
  funext i
  simp [rotWord]

theorem rotWord_add {α : Type*} {G : ℕ} (S : ZMod G → α) (j k : ZMod G) :
    rotWord (rotWord S j) k = rotWord S (j + k) := by
  funext i
  simp only [rotWord]
  congr 1
  abel

theorem rotWord_neg {α : Type*} {G : ℕ} (S : ZMod G → α) (j : ZMod G) :
    rotWord (rotWord S j) (-j) = S := by
  funext i
  simp only [rotWord]
  congr 1
  abel

/-- Rotation equivalence on circular words: `T` is a rotation of `S`. -/
def rotSetoid (α : Type*) [Fintype α] [DecidableEq α] (G : ℕ) [NeZero G] :
    Setoid (ZMod G → α) where
  r S T := ∃ j : ZMod G, T = rotWord S j
  iseqv :=
    ⟨fun S => ⟨0, (rotWord_zero S).symm⟩,
     fun h => by
       obtain ⟨j, rfl⟩ := h
       exact ⟨-j, (rotWord_neg _ j).symm⟩,
     fun hST hTU => by
       obtain ⟨j, rfl⟩ := hST
       obtain ⟨k, rfl⟩ := hTU
       exact ⟨j + k, rotWord_add _ j k⟩⟩

instance instDecidableRelRotSetoid (α : Type*) [Fintype α] [DecidableEq α]
    (G : ℕ) [NeZero G] : DecidableRel (rotSetoid α G).r :=
  fun S T => inferInstanceAs (Decidable (∃ j : ZMod G, T = rotWord S j))

/-- Decidable equality on the rotation-orbit type (noncomputable, used only to
state and prove the decision-theoretic theorems). -/
noncomputable instance instDecidableEqQuotientRotSetoid (α : Type*) [Fintype α]
    [DecidableEq α] (G : ℕ) [NeZero G] :
    DecidableEq (Quotient (rotSetoid α G)) :=
  Classical.decEq _

/-- Nonemptiness of the rotation-orbit type. -/
instance instNonemptyQuotientRotSetoid (α : Type*) [Fintype α] [DecidableEq α]
    (G : ℕ) [NeZero G] [Nonempty α] :
    Nonempty (Quotient (rotSetoid α G)) :=
  ⟨Quotient.mk _ (fun _ : ZMod G => Classical.choice (inferInstance : Nonempty α))⟩

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## 1. The concrete finite circular read model -/

section ReadModel

variable {G L : ℕ} [NeZero G]

/-- Oriented length-`L` circular window at start `s`. -/
def window (S : ZMod G → α) (s : ZMod G) : Fin L → α :=
  fun d => S (s + (d.val : ZMod G))

/-- Window multiplicity: how many starts spell the read type `w`. -/
def mult (S : ZMod G → α) (w : Fin L → α) : ℕ :=
  (Finset.univ.filter (fun s : ZMod G => window S s = w)).card

/-- Exact read pmf `p_S(w) = multiplicity_S(w) / |G|`. -/
noncomputable def readPmf (S : ZMod G → α) (w : Fin L → α) : ℝ :=
  (mult S w : ℝ) / (G : ℝ)

omit [Fintype α] in
/-- Multiplicity as an indicator sum. -/
theorem mult_eq_sum (S : ZMod G → α) (w : Fin L → α) :
    mult S w = ∑ s : ZMod G, if window S s = w then 1 else 0 := by
  simp only [mult]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- The window multiplicities total to the genome length `G`: every one of the
`G` starts contributes exactly one window. -/
theorem sum_mult (S : ZMod G → α) : ∑ w : Fin L → α, mult S w = G := by
  calc ∑ w : Fin L → α, mult S w
      = ∑ w : Fin L → α, ∑ s : ZMod G, if window S s = w then 1 else 0 :=
          Finset.sum_congr rfl (fun w _ => mult_eq_sum S w)
    _ = ∑ s : ZMod G, ∑ w : Fin L → α, if window S s = w then 1 else 0 :=
          Finset.sum_comm
    _ = ∑ _s : ZMod G, (1 : ℕ) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.sum_ite_eq]
          simp
    _ = G := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_one]

/-- **Normalization.** The exact circular read pmf is a probability mass
function: `∑_w readPmf S w = 1`. -/
theorem readPmf_sum_one (S : ZMod G → α) :
    ∑ w : Fin L → α, readPmf S w = 1 := by
  have hG : (G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne G)
  have hsum : ∑ w : Fin L → α, (mult S w : ℝ) = (G : ℝ) := by
    rw [← Nat.cast_sum, sum_mult]
  unfold readPmf
  rw [← Finset.sum_div, hsum, div_self hG]

end ReadModel

/-! ## 2. Rotation invariance and the rotation-orbit quotient -/

section Rotation

variable {G L : ℕ} [NeZero G]

omit [Fintype α] [DecidableEq α] [NeZero G] in
/-- Windows commute with rotation. -/
theorem window_rotWord (S : ZMod G → α) (j : ZMod G) (s : ZMod G) :
    window (α := α) (L := L) (rotWord S j) s =
      window (α := α) (L := L) S (s + j) := by
  funext d
  simp only [window, rotWord]
  congr 1
  abel

omit [Fintype α] in
/-- The window multiplicity is rotation invariant. -/
theorem mult_rotWord (S : ZMod G → α) (j : ZMod G) (w : Fin L → α) :
    mult (rotWord S j) w = mult S w := by
  rw [mult_eq_sum (rotWord S j) w, mult_eq_sum S w]
  trans ∑ s : ZMod G, if window S (s + j) = w then 1 else 0
  · apply Finset.sum_congr rfl
    intro s _
    rw [window_rotWord]
  · exact Equiv.sum_comp (Equiv.addRight j)
      (fun t => if window S t = w then 1 else 0)

omit [Fintype α] in
/-- The exact read pmf is rotation invariant, hence well defined on rotation
orbits. -/
theorem readPmf_rotWord (S : ZMod G → α) (j : ZMod G) (w : Fin L → α) :
    readPmf (rotWord S j) w = readPmf S w := by
  unfold readPmf
  rw [mult_rotWord]

/-- The exact read pmf descended to rotation-orbit classes. -/
noncomputable def orbitReadPmf (G L : ℕ) [NeZero G] :
    Quotient (rotSetoid α G) → (Fin L → α) → ℝ :=
  Quotient.lift (fun S => readPmf (G := G) (L := L) S) (by
    intro S T h
    obtain ⟨j, rfl⟩ := h
    funext w
    exact (readPmf_rotWord S j w).symm)

/-- The descended orbit read pmf is normalized. -/
theorem orbitReadPmf_sum_one (G L : ℕ) [NeZero G]
    (o : Quotient (rotSetoid α G)) :
    ∑ w : Fin L → α, orbitReadPmf (α := α) G L o w = 1 := by
  refine Quotient.inductionOn o (fun S => ?_)
  change (∑ w : Fin L → α, readPmf (G := G) (L := L) S w) = 1
  exact readPmf_sum_one S

end Rotation

/-! ## 3. A likelihood descends to a genome quotient iff it is invariant -/

section OrbitAction

variable {β R : Type*}

/-- A read likelihood descends to the quotient by a genome equivalence exactly
when it is constant on equivalence classes.  For rotation this is discharged by
`readPmf_rotWord`; for reverse complement it is a genuine extra hypothesis that
an oriented one-strand read distribution need not satisfy. -/
theorem quotient_likelihood_well_defined_iff
    (ρ : Setoid β) (L : β → R → ℝ) :
    (∃ L' : Quotient ρ → R → ℝ,
        ∀ g r, L' (Quotient.mk ρ g) r = L g r) ↔
      (∀ g h, g ≈ h → L g = L h) := by
  constructor
  · rintro ⟨L', hL'⟩ g h hgh
    funext r
    rw [← hL' g r, ← hL' h r, Quotient.sound hgh]
  · intro hinv
    exact ⟨Quotient.lift L hinv, fun g _ => rfl⟩

end OrbitAction

/-! ## 4. Prior-averaged MAP success is monotone in the number of reads -/

section Monotonicity

variable {G L : ℕ} [NeZero G]

/-- **Exact assembly n → n+1 MAP success monotonicity.**  For the concrete
finite circular-read orbit model, the constructed MAP policy's prior-averaged
zero-one success does not decrease when one more read is observed, for every
`n` including `0` and for an arbitrary prior on orbit classes.  Interpreting the
formula probabilistically requires a nonnegative normalized prior; the algebraic
inequality uses only the per-candidate read-pmf normalization. -/
theorem orbit_map_success_monotone [Nonempty α]
    (π : Quotient (rotSetoid α G) → ℝ) (n : ℕ) :
    IidMapMonotonicity.mapSuccess π (orbitReadPmf (α := α) G L) n ≤
      IidMapMonotonicity.mapSuccessSucc π (orbitReadPmf (α := α) G L) n :=
  IidMapMonotonicity.iid_map_success_monotone π (orbitReadPmf (α := α) G L) n
    (fun o => orbitReadPmf_sum_one (α := α) G L o)

end Monotonicity

/-! ## 5. Priors on orbit classes, and why spellings are the wrong carrier -/

section Orbits

variable {G : ℕ} [NeZero G]

/-- Uniform prior on rotation-orbit classes. -/
noncomputable def uniformOrbitPrior :
    Quotient (rotSetoid α G) → ℝ :=
  fun _ => 1 / (Fintype.card (Quotient (rotSetoid α G)) : ℝ)

/-- Number of raw spellings in an orbit class. -/
noncomputable def orbitSize (o : Quotient (rotSetoid α G)) : ℕ :=
  (Finset.univ.filter
    (fun S : ZMod G → α => Quotient.mk (rotSetoid α G) S = o)).card

/-- The pushforward of the uniform prior on raw spellings onto orbit classes. -/
noncomputable def spellingPushforwardPrior (o : Quotient (rotSetoid α G)) : ℝ :=
  (orbitSize o : ℝ) / (Fintype.card (ZMod G → α) : ℝ)

/-- Every orbit class has at least one spelling. -/
theorem orbitSize_pos (o : Quotient (rotSetoid α G)) :
    0 < orbitSize o := by
  classical
  refine Quotient.inductionOn o (fun S => ?_)
  unfold orbitSize
  rw [Finset.card_pos]
  exact ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

theorem uniformOrbitPrior_sum_one [Nonempty α] :
    ∑ o : Quotient (rotSetoid α G), uniformOrbitPrior (α := α) o = 1 := by
  classical
  have hcard : (Fintype.card (Quotient (rotSetoid α G)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold uniformOrbitPrior
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_one_div, div_self hcard]

/-- Orbit sizes total to the number of raw spellings. -/
theorem sum_orbitSize :
    ∑ o : Quotient (rotSetoid α G), orbitSize o =
      Fintype.card (ZMod G → α) := by
  classical
  have h : ∀ o : Quotient (rotSetoid α G), orbitSize o =
      ∑ S : ZMod G → α,
        if Quotient.mk (rotSetoid α G) S = o then 1 else 0 := by
    intro o
    unfold orbitSize
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  calc ∑ o : Quotient (rotSetoid α G), orbitSize o
      = ∑ o : Quotient (rotSetoid α G), ∑ S : ZMod G → α,
          if Quotient.mk (rotSetoid α G) S = o then 1 else 0 :=
          Finset.sum_congr rfl (fun o _ => h o)
    _ = ∑ S : ZMod G → α, ∑ o : Quotient (rotSetoid α G),
          if Quotient.mk (rotSetoid α G) S = o then 1 else 0 :=
          Finset.sum_comm
    _ = ∑ _S : ZMod G → α, (1 : ℕ) := by
          apply Finset.sum_congr rfl
          intro S _
          rw [Finset.sum_ite_eq]
          simp
    _ = Fintype.card (ZMod G → α) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]

/-- The uniform spelling prior, pushed forward to orbits, is a probability
distribution on orbits. -/
theorem spellingPushforwardPrior_sum_one [Nonempty α] :
    ∑ o : Quotient (rotSetoid α G), spellingPushforwardPrior (α := α) o = 1 := by
  classical
  have hcard : (Fintype.card (ZMod G → α) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum : ∑ o : Quotient (rotSetoid α G), (orbitSize o : ℝ) =
      (Fintype.card (ZMod G → α) : ℝ) := by
    rw [← Nat.cast_sum, sum_orbitSize]
  unfold spellingPushforwardPrior
  rw [← Finset.sum_div, hsum, div_self hcard]

/-- **Uniform spellings are uniform on orbits iff all orbits have equal size.**
This is the precise sense in which a prior must be placed on orbit classes
rather than raw spellings when orbit sizes differ. -/
theorem spellingPushforward_eq_uniform_iff_constant_orbitSize [Nonempty α] :
    (∀ o : Quotient (rotSetoid α G),
        spellingPushforwardPrior (α := α) o = uniformOrbitPrior (α := α) o) ↔
      (∀ o o' : Quotient (rotSetoid α G),
        orbitSize o = orbitSize o') := by
  classical
  have hW : (Fintype.card (ZMod G → α) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hΩ : (Fintype.card (Quotient (rotSetoid α G)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  constructor
  · intro h o o'
    have ho := h o
    have ho' := h o'
    unfold spellingPushforwardPrior uniformOrbitPrior at ho ho'
    have h1 : (orbitSize o : ℝ) / (Fintype.card (ZMod G → α) : ℝ) =
        (orbitSize o' : ℝ) / (Fintype.card (ZMod G → α) : ℝ) := by
      rw [ho, ho']
    rw [div_eq_div_iff hW hW] at h1
    have h2 : (orbitSize o : ℝ) = (orbitSize o' : ℝ) :=
      mul_right_cancel₀ hW h1
    exact_mod_cast h2
  · intro hconst o
    have hs : (orbitSize o : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (orbitSize_pos o))
    have hsum_nat : Fintype.card (ZMod G → α) =
        Fintype.card (Quotient (rotSetoid α G)) * orbitSize o := by
      rw [← sum_orbitSize]
      rw [Finset.sum_congr rfl (fun o' _ => hconst o' o), Finset.sum_const,
        Finset.card_univ, smul_eq_mul]
    have hsum : (Fintype.card (ZMod G → α) : ℝ) =
        (Fintype.card (Quotient (rotSetoid α G)) : ℝ) * (orbitSize o : ℝ) := by
      rw [hsum_nat]; push_cast; ring
    unfold spellingPushforwardPrior uniformOrbitPrior
    rw [hsum]
    rw [div_eq_div_iff (mul_ne_zero hΩ hs) hΩ]
    ring

end Orbits

/-! ## 6. Uniform orbit prior makes MAP a maximum-likelihood policy -/

section UniformML

variable {G L : ℕ} [NeZero G]

/-- Exact likelihood of the sample `x` under orbit class `o`. -/
noncomputable def likelihood (n : ℕ) (o : Quotient (rotSetoid α G))
    (x : Fin n → (Fin L → α)) : ℝ :=
  ∏ i : Fin n, orbitReadPmf (α := α) G L o (x i)

/-- **Uniform orbit prior ⟹ MAP is maximum likelihood.**  Under the uniform
prior on orbit classes, the constructed MAP policy's decision maximizes the
exact iid likelihood pointwise, so MAP = ML for this prior. -/
theorem uniform_orbit_prior_ML [Nonempty α]
    (n : ℕ) (x : Fin n → (Fin L → α)) (o : Quotient (rotSetoid α G)) :
    likelihood (α := α) n o x ≤
      likelihood (α := α) n
        (FiniteBayesDecision.chooseMAP
          (IidMapMonotonicity.iidJoint (uniformOrbitPrior (α := α))
            (orbitReadPmf (α := α) G L) n) x) x := by
  classical
  have hcard : 0 < (Fintype.card (Quotient (rotSetoid α G)) : ℝ) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr inferInstance)
  have hpos : 0 < uniformOrbitPrior (α := α) o := by
    unfold uniformOrbitPrior
    exact one_div_pos.mpr hcard
  have hmax := FiniteBayesDecision.chooseMAP_maximizes
    (IidMapMonotonicity.iidJoint (uniformOrbitPrior (α := α))
      (orbitReadPmf (α := α) G L) n) x o
  simp only [IidMapMonotonicity.iidJoint, likelihood] at hmax ⊢
  exact le_of_mul_le_mul_left hmax hpos

end UniformML

/-! ## 7. Per-truth success is *not* monotone (target C counterexample) -/

namespace PerTruthDrop

/-- Binary read alphabet `{A, C}`. -/
abbrev Read := Fin 2

/-- Two candidate pmfs: candidate `0` has `p(A) = 4/5`, candidate `1` has
`p(A) = 1/2`; both have `p(C)` the complement. -/
def readP (θ w : Read) : ℚ :=
  if θ = 0 then (if w = 0 then 4 / 5 else 1 / 5)
  else (if w = 0 then 1 / 2 else 1 / 2)

/-- One-read maximum-likelihood decision (no ties in this model). -/
def ml1 (w : Read) : Read :=
  if (1 / 2) * readP 0 w ≥ (1 / 2) * readP 1 w then 0 else 1

/-- Two-read maximum-likelihood decision (no ties in this model). -/
def ml2 (a b : Read) : Read :=
  if (1 / 2) * (readP 0 a * readP 0 b) ≥ (1 / 2) * (readP 1 a * readP 1 b)
    then 0 else 1

/-- Probability that the one-read ML policy returns the true candidate `θ`. -/
def perTruth1 (θ : Read) : ℚ :=
  ∑ w : Read, if ml1 w = θ then readP θ w else 0

/-- Probability that the two-read ML policy returns the true candidate `θ`. -/
def perTruth2 (θ : Read) : ℚ :=
  ∑ a : Read, ∑ b : Read,
    if ml2 a b = θ then readP θ a * readP θ b else 0

/-- One read: the true candidate is recovered with probability `4/5`. -/
theorem perTruth_true_one : perTruth1 0 = 4 / 5 := by
  unfold perTruth1
  simp only [Fin.sum_univ_two]
  norm_num [readP, ml1]

/-- Two reads: the true candidate is recovered with probability `16/25`. -/
theorem perTruth_true_two : perTruth2 0 = 16 / 25 := by
  unfold perTruth2
  simp only [Fin.sum_univ_two]
  norm_num [readP, ml2]

/-- **Per-truth success can drop.**  Observing one more read strictly decreases
the success probability for the fixed true candidate `0`, even though the
*prior-averaged* success is nondecreasing.  This is why
`orbit_map_success_monotone` must not be read as a per-truth claim. -/
theorem perTruth_true_drops : perTruth2 0 < perTruth1 0 := by
  rw [perTruth_true_two, perTruth_true_one]
  norm_num

end PerTruthDrop

/-! ## 8. Conditional-on-coverage vs unconditional Bayes success -/

namespace CoverageConditional

variable {Θ X : Type*} [Fintype Θ] [DecidableEq Θ] [Fintype X]

/-- Predictive mass of a finite observation event `C`. -/
noncomputable def predictiveMass (J : Θ → X → ℝ) (C : Finset X) : ℝ :=
  ∑ x ∈ C, ∑ θ : Θ, J θ x

/-- Conditional zero-one success of a policy, given the observation event `C`. -/
noncomputable def conditionalSuccess (J : Θ → X → ℝ) (C : Finset X) (d : X → Θ) : ℝ :=
  (∑ x ∈ C, J (d x) x) / predictiveMass J C

omit [DecidableEq Θ] [Fintype X] in
/-- Within the conditioning event `C`, the pointwise MAP policy still maximizes
conditional success. -/
theorem conditional_MAP_optimal [Nonempty Θ] (J : Θ → X → ℝ) (C : Finset X)
    (hC : 0 < predictiveMass J C) (d : X → Θ) :
    conditionalSuccess J C d ≤ conditionalSuccess J C (FiniteBayesDecision.chooseMAP J) := by
  have hnum : (∑ x ∈ C, J (d x) x) ≤
      ∑ x ∈ C, J (FiniteBayesDecision.chooseMAP J x) x :=
    Finset.sum_le_sum (fun x _ => FiniteBayesDecision.chooseMAP_maximizes J x (d x))
  exact div_le_div_of_nonneg_right hnum (le_of_lt hC)

/-- Conditioning on the whole space rescales unconditional success by the
predictive mass `P(C)`: the conditional experiment is a different quantity from
the unconditional Bayes average.  Truth-dependent conditioning is #266. -/
theorem conditionalSuccess_univ_eq [Nonempty Θ] (J : Θ → X → ℝ) (d : X → Θ) :
    conditionalSuccess J Finset.univ d =
      FiniteBayesDecision.success J d / predictiveMass J Finset.univ := by
  simp only [conditionalSuccess, FiniteBayesDecision.success_eq_observation_sum]

end CoverageConditional

/-! ## 9. Posterior/MAP equivalence for positive predictive mass -/

namespace PosteriorMAP

variable {Θ X : Type*} [Fintype Θ] [DecidableEq Θ] [Fintype X]

/-- Predictive mass of a sample `x`. -/
noncomputable def predictiveMass (J : Θ → X → ℝ) (x : X) : ℝ :=
  ∑ θ : Θ, J θ x

/-- Posterior mass of `θ` given `x`, defined only when the predictive mass is
nonzero; for zero predictive mass no conditioning is asserted. -/
noncomputable def posterior (J : Θ → X → ℝ) (x : X)
    (_h : predictiveMass J x ≠ 0) (θ : Θ) : ℝ :=
  J θ x / predictiveMass J x

omit [DecidableEq Θ] [Fintype X] in
/-- **Posterior/MAP equivalence.**  When the sample has positive predictive
mass, a candidate maximizes the posterior iff it maximizes the joint mass, so
the MAP policy is a posterior maximizer.  Zero-mass samples are excluded by the
`h : predictiveMass J x ≠ 0` argument of `posterior` (no division by zero). -/
theorem posterior_argmax_iff [Nonempty Θ] (J : Θ → X → ℝ) (x : X)
    (h : 0 < predictiveMass J x) (θ : Θ) :
    posterior J x (ne_of_gt h) θ ≤
        posterior J x (ne_of_gt h) (FiniteBayesDecision.chooseMAP J x) ↔
      J θ x ≤ J (FiniteBayesDecision.chooseMAP J x) x := by
  unfold posterior
  exact div_le_div_iff_of_pos_right h

end PosteriorMAP

/-! ## 10. Exact iid likelihood vs fixed-`N` product-binomial surrogate -/

namespace ExactVsSurrogate

/-- Exact likelihood of an observed read multiset with counts `c`, under the
ordered iid model: `∏_w p_w^{c_w}`. -/
def exactIidLikelihood {R : Type*} [Fintype R] (p : R → ℚ) (c : R → ℕ) : ℚ :=
  ∏ w : R, (p w) ^ (c w)

/-- A fixed-`N` product-binomial surrogate in the MB09 style: every read class
contributes an independent binomial factor with `N` trials. -/
def productBinomialSurrogate {R : Type*} [Fintype R]
    (N : ℕ) (p : R → ℚ) (c : R → ℕ) : ℚ :=
  ∏ w : R, (p w) ^ (c w) * (1 - p w) ^ (N - c w)

/-- The exact iid likelihood and the fixed-`N` product-binomial surrogate are
**not** the same objective: on a concrete two-class observation they differ. -/
theorem exact_ne_productBinomial :
    exactIidLikelihood (fun _ : Fin 2 => (1 / 2 : ℚ)) (fun _ : Fin 2 => 1) ≠
      productBinomialSurrogate 2 (fun _ : Fin 2 => (1 / 2 : ℚ)) (fun _ : Fin 2 => 1) := by
  unfold exactIidLikelihood productBinomialSurrogate
  simp only [Fin.prod_univ_two]
  norm_num

end ExactVsSurrogate

/-! ## Axiom audit -/

#print axioms sum_mult
#print axioms readPmf_sum_one
#print axioms readPmf_rotWord
#print axioms orbitReadPmf_sum_one
#print axioms quotient_likelihood_well_defined_iff
#print axioms orbit_map_success_monotone
#print axioms uniformOrbitPrior_sum_one
#print axioms orbitSize_pos
#print axioms sum_orbitSize
#print axioms spellingPushforwardPrior_sum_one
#print axioms spellingPushforward_eq_uniform_iff_constant_orbitSize
#print axioms uniform_orbit_prior_ML
#print axioms PerTruthDrop.perTruth_true_one
#print axioms PerTruthDrop.perTruth_true_two
#print axioms PerTruthDrop.perTruth_true_drops
#print axioms CoverageConditional.conditional_MAP_optimal
#print axioms CoverageConditional.conditionalSuccess_univ_eq
#print axioms PosteriorMAP.posterior_argmax_iff
#print axioms ExactVsSurrogate.exact_ne_productBinomial

end AssemblyP1.GenomeOrbitAdapter
