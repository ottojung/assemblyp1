import Mathlib
import AssemblyP1.FiniteBayesDecision
import AssemblyP1.IidMapMonotonicity
import AssemblyP1.GenomeOrbitAdapter

/-!
# Posterior/MAP equivalence, completed (Antonina #269, target D)

This module completes the posterior/MAP equivalence endpoint of Antonina #269
target D.  The merged `AssemblyP1.GenomeOrbitAdapter.PosteriorMAP.posterior_argmax_iff`
(`GenomeOrbitAdapter.lean`, section 9) states the equivalence only against the
constructive `chooseMAP` witness.  This module adds the genuinely missing pieces,
reusing the merged `posterior`/`predictiveMass` definitions (no re-definition,
no re-proof of the merged finite-sum lemmas of PR #174/#193):

* `posterior_sum_one` — the posterior is a normalized probability distribution:
  for positive predictive mass, `∑ θ, posterior J x h θ = 1`.
* `posterior_le_iff_joint_le` — the general two-candidate equivalence: for
  positive predictive mass, `J θ x ≤ J θ' x ↔ posterior θ ≤ posterior θ'`,
  so the posterior maximizers are exactly the joint (MAP) maximizers.
* `zeroMass_joint_zero` / `zeroMass_all_joint_max` — explicit zero-mass
  handling: for nonnegative `J`, zero predictive mass forces every joint mass
  to vanish, so every candidate is a joint maximizer on such samples (ties at
  zero) and the MAP tie choice is irrelevant; no conditioning is asserted on
  zero-mass samples (the merged `posterior` is only defined for nonzero mass).
* `iid_posterior_le_iff_joint_le` / `iid_map_posterior_max` — the equivalence
  instantiated to the exact iid read-model joint `IidMapMonotonicity.iidJoint`,
  so it applies to read samples `x : Fin n → R` directly.

Everything is exact over `ℝ`; no `sorry`/`admit`/`native_decide`/new axioms.
-/

namespace AssemblyP1.PosteriorMAPEquivalence

open Finset BigOperators

variable {Θ X : Type*} [Fintype Θ] [DecidableEq Θ] [Fintype X]

omit [DecidableEq Θ] [Fintype X] in
/-- **Posterior normalization.**  For positive predictive mass the posterior is
a probability distribution on `Θ`: `∑ θ, posterior J x h θ = 1`. -/
theorem posterior_sum_one (J : Θ → X → ℝ) (x : X)
    (h : 0 < GenomeOrbitAdapter.PosteriorMAP.predictiveMass J x) :
    ∑ θ : Θ, GenomeOrbitAdapter.PosteriorMAP.posterior J x (ne_of_gt h) θ = 1 := by
  unfold GenomeOrbitAdapter.PosteriorMAP.posterior
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt h)

omit [DecidableEq Θ] [Fintype X] in
/-- **General posterior/MAP equivalence.**  For positive predictive mass, the
posterior order on candidates is exactly the joint-mass order:
`J θ x ≤ J θ' x ↔ posterior θ ≤ posterior θ'`.  Hence the posterior
maximizers are precisely the joint (MAP) maximizers. -/
theorem posterior_le_iff_joint_le (J : Θ → X → ℝ) (x : X)
    (h : 0 < GenomeOrbitAdapter.PosteriorMAP.predictiveMass J x) (θ θ' : Θ) :
    J θ x ≤ J θ' x ↔
      GenomeOrbitAdapter.PosteriorMAP.posterior J x (ne_of_gt h) θ ≤
        GenomeOrbitAdapter.PosteriorMAP.posterior J x (ne_of_gt h) θ' := by
  unfold GenomeOrbitAdapter.PosteriorMAP.posterior
  exact (div_le_div_iff_of_pos_right h).symm

omit [DecidableEq Θ] [Fintype X] in
/-- **Zero-mass handling.**  For nonnegative `J`, zero predictive mass forces
every joint mass to vanish: `predictiveMass J x = 0 → ∀ θ, J θ x = 0`. -/
theorem zeroMass_joint_zero (J : Θ → X → ℝ) (x : X)
    (hnn : ∀ θ, 0 ≤ J θ x)
    (hz : GenomeOrbitAdapter.PosteriorMAP.predictiveMass J x = 0) (θ : Θ) :
    J θ x = 0 := by
  have hsum : (∑ θ : Θ, J θ x) = 0 := hz
  have hiff := Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (fun θ _ => hnn θ)
  rw [hsum] at hiff
  exact hiff.mp rfl θ (Finset.mem_univ θ)

omit [DecidableEq Θ] [Fintype X] in
/-- **Zero-mass samples are ties.**  On a zero-mass sample every candidate is a
joint maximizer (all joints are zero), so the MAP policy's tie choice is
irrelevant there. -/
theorem zeroMass_all_joint_max (J : Θ → X → ℝ) (x : X)
    (hnn : ∀ θ, 0 ≤ J θ x)
    (hz : GenomeOrbitAdapter.PosteriorMAP.predictiveMass J x = 0) (θ θ' : Θ) :
    J θ x ≤ J θ' x := by
  have h0 := zeroMass_joint_zero J x hnn hz θ
  have h0' := zeroMass_joint_zero J x hnn hz θ'
  rw [h0, h0']

/-! ## Instantiation to the iid read model -/

omit [DecidableEq Θ] in
/-- **Posterior/MAP equivalence for iid read samples.**  Instantiated to the
exact iid read-model joint `IidMapMonotonicity.iidJoint π p n`: for a read
sample `x : Fin n → R` with positive predictive mass, the posterior order on
candidates is exactly the joint (prior × likelihood) order. -/
theorem iid_posterior_le_iff_joint_le {R : Type*} [Fintype R] (π : Θ → ℝ) (p : Θ → R → ℝ)
    (n : ℕ) (x : Fin n → R)
    (h : 0 < GenomeOrbitAdapter.PosteriorMAP.predictiveMass (IidMapMonotonicity.iidJoint π p n) x)
    (θ θ' : Θ) :
    IidMapMonotonicity.iidJoint π p n θ x ≤ IidMapMonotonicity.iidJoint π p n θ' x ↔
      GenomeOrbitAdapter.PosteriorMAP.posterior (IidMapMonotonicity.iidJoint π p n) x (ne_of_gt h) θ ≤
        GenomeOrbitAdapter.PosteriorMAP.posterior (IidMapMonotonicity.iidJoint π p n) x (ne_of_gt h) θ' :=
  posterior_le_iff_joint_le _ _ h θ θ'

omit [DecidableEq Θ] in
/-- **The MAP policy is a posterior maximizer for iid read samples.**  For a
read sample `x : Fin n → R` with positive predictive mass, the constructed MAP
policy's posterior is at least every candidate's posterior. -/
theorem iid_map_posterior_max {R : Type*} [Fintype R] [Nonempty Θ] (π : Θ → ℝ) (p : Θ → R → ℝ)
    (n : ℕ) (x : Fin n → R)
    (h : 0 < GenomeOrbitAdapter.PosteriorMAP.predictiveMass (IidMapMonotonicity.iidJoint π p n) x)
    (θ : Θ) :
    GenomeOrbitAdapter.PosteriorMAP.posterior (IidMapMonotonicity.iidJoint π p n) x (ne_of_gt h) θ ≤
      GenomeOrbitAdapter.PosteriorMAP.posterior (IidMapMonotonicity.iidJoint π p n) x (ne_of_gt h)
        (FiniteBayesDecision.chooseMAP (IidMapMonotonicity.iidJoint π p n) x) := by
  have hmax := FiniteBayesDecision.chooseMAP_maximizes (IidMapMonotonicity.iidJoint π p n) x θ
  exact (posterior_le_iff_joint_le _ _ h θ
    (FiniteBayesDecision.chooseMAP (IidMapMonotonicity.iidJoint π p n) x)).mp hmax

end AssemblyP1.PosteriorMAPEquivalence

#print axioms AssemblyP1.PosteriorMAPEquivalence.posterior_sum_one
#print axioms AssemblyP1.PosteriorMAPEquivalence.posterior_le_iff_joint_le
#print axioms AssemblyP1.PosteriorMAPEquivalence.zeroMass_joint_zero
#print axioms AssemblyP1.PosteriorMAPEquivalence.zeroMass_all_joint_max
#print axioms AssemblyP1.PosteriorMAPEquivalence.iid_posterior_le_iff_joint_le
#print axioms AssemblyP1.PosteriorMAPEquivalence.iid_map_posterior_max
