import Mathlib
import AssemblyP1.FiniteBayesDecision
import AssemblyP1.IidMapMonotonicity
import AssemblyP1.GenomeOrbitAdapter

/-!
# A necessary-and-sufficient certificate for finite Bayes/MAP optimality (#269)

Antonina #269 target B asks for the finite Bayes/MAP optimality theorem: the MAP
policy `argmax_θ π θ · ∏_i p_θ(x_i)` maximizes prior-averaged zero-one success
against **every** policy, for every sample size `n` (including `n = 0`), with
finite sum/max reasoning and tie handling.  The merged
`AssemblyP1.FiniteBayesDecision` (PR #174) proves the **sufficient** half:
pointwise joint-mass maximization implies aggregate optimality, for arbitrary
real joint mass.

This module closes the **necessary** half and packages the result as an exact
*optimality certificate*: a deterministic policy attains the maximal
prior-averaged success **iff** it is pointwise MAP at every sample.  The proof
is a finite, sign-free argument: for every sample the deficit
`max_θ J θ x - J (d x) x` is nonnegative, and the deficits sum to zero exactly
when the policy is optimal.  Consequently the certificate holds for arbitrary
real joint mass — no positivity or normalization is needed for the algebraic
statement; those enter only when reading `J` probabilistically.

The module then delivers, all kernel-checked:

* `pointwiseMAP_iff_bayesOptimal` — the exact certificate.
* `pointwiseMAP_forces_strictMax` — at a sample with a strict maximizer every
  optimal policy is *forced* to return it (the "singleton" corner).
* `posterior_eq_one_iff_singleton_support` — the necessary-and-sufficient
  conditional-posterior-one theorem for the merged posterior
  `AssemblyP1.GenomeOrbitAdapter.PosteriorMAP.posterior`: for nonnegative joint
  mass and positive predictive probability, the posterior is `1` at `θ` exactly
  when every candidate of positive joint mass is `θ` (the supported
  truth-fibre is a singleton).
* `orbit_posterior_eq_one_iff_singleton_support` — the same theorem
  instantiated to the concrete finite family of genome **rotation-equivalence
  classes** with the exact circular read pmf `p_G(w) = mult_G(w)/|G|`.
* Two smallest finite witnesses pinning the directions that are *not* claimed:
  `TieWitness.both_optimal` (ties: two distinct policies are both optimal, so
  optimality does not force a unique answer) and
  `StrictLossWitness.strict_loss` (a non-pointwise policy strictly loses, so
  the certificate is not vacuous).
* `iid_certificate` / `orbit_certificate` — the certificate instantiated to the
  exact iid read model and to the orbit-class read model.

The prior-averaged scope is essential: the merged
`AssemblyP1.GenomeOrbitAdapter.PerTruthDrop.perTruth_true_drops` shows per-truth
success can strictly *drop* (`16/25 < 4/5`), which is consistent with the
certificate because the certificate concerns the prior-weighted average.  This
module reuses that endpoint rather than reproving it.

This is a finite Bayesian decision theorem for a fixed observation model; it is
**not** the MB09 fixed-`N` product-binomial pseudo-likelihood, not the §6.2
feasible-flow objective, and not a global "ML is best" claim.  It preserves a
clean separation from the event-conditional inference of #266
(`AssemblyP1.ConditionalIdentifiability`): nothing here conditions the prior or
the likelihood on a truth-dependent event.  The posterior-one boundary is the
#269-scoped form of the more general #272 endpoint
`AssemblyP1.FiniteBayesianSideInformation.readOnly_posterior_eq_one_iff`
(the `π ≡ 1`, `orbit = id`, `E ≡ True` specialization, restated for the merged
#269 point-candidate `GenomeOrbitAdapter.PosteriorMAP.posterior` and used to
instantiate the genome rotation-class model); it is not claimed to be a new
mathematical fact beyond that specialization.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

set_option linter.unusedSectionVars false

namespace AssemblyP1.BayesOptimalityCertificate

open Finset BigOperators

variable {Θ X : Type*} [Fintype Θ] [DecidableEq Θ] [Fintype X]

/-! ## 1. The optimality certificate -/

/-- A deterministic policy is **pointwise MAP** when it picks a joint-mass
maximizer at every observed sample. -/
def PointwiseMAP (J : Θ → X → ℝ) (d : X → Θ) : Prop :=
  ∀ x θ, J θ x ≤ J (d x) x

/-- A deterministic policy is **Bayes-optimal** when it attains the maximal
prior-averaged zero-one success, i.e. the success of the constructed MAP rule. -/
def BayesOptimal [Nonempty Θ] (J : Θ → X → ℝ) (d : X → Θ) : Prop :=
  FiniteBayesDecision.success J (FiniteBayesDecision.chooseMAP J) ≤
    FiniteBayesDecision.success J d

/-- **Sufficiency (merged endpoint, restated in certificate form).**  A pointwise
MAP policy is Bayes-optimal. -/
theorem pointwiseMAP_imp_bayesOptimal [Nonempty Θ] (J : Θ → X → ℝ) (d : X → Θ)
    (hd : PointwiseMAP J d) : BayesOptimal J d :=
  FiniteBayesDecision.pointwise_MAP_optimal J d (FiniteBayesDecision.chooseMAP J) hd

/-- **Necessity (new).**  Every Bayes-optimal policy is pointwise MAP.  For
arbitrary real joint mass the nonnegative deficits
`J (chooseMAP J x) x - J (d x) x` sum to zero, so each vanishes. -/
theorem bayesOptimal_imp_pointwiseMAP [Nonempty Θ] (J : Θ → X → ℝ) (d : X → Θ)
    (hd : BayesOptimal J d) : PointwiseMAP J d := by
  intro x θ
  have hle : FiniteBayesDecision.success J d ≤
      FiniteBayesDecision.success J (FiniteBayesDecision.chooseMAP J) :=
    FiniteBayesDecision.chooseMAP_optimal J d
  have heq : FiniteBayesDecision.success J d =
      FiniteBayesDecision.success J (FiniteBayesDecision.chooseMAP J) :=
    le_antisymm hle hd
  have hsum : (∑ y : X,
        (J (FiniteBayesDecision.chooseMAP J y) y - J (d y) y)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have h1 : (∑ y : X, J (FiniteBayesDecision.chooseMAP J y) y) =
        FiniteBayesDecision.success J (FiniteBayesDecision.chooseMAP J) :=
      (FiniteBayesDecision.success_eq_observation_sum J
        (FiniteBayesDecision.chooseMAP J)).symm
    have h2 : (∑ y : X, J (d y) y) = FiniteBayesDecision.success J d :=
      (FiniteBayesDecision.success_eq_observation_sum J d).symm
    rw [h1, h2, heq, sub_self]
  have hnn : ∀ y ∈ (Finset.univ : Finset X),
      0 ≤ J (FiniteBayesDecision.chooseMAP J y) y - J (d y) y := by
    intro y _
    have hmax := FiniteBayesDecision.chooseMAP_maximizes J y (d y)
    linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum x (Finset.mem_univ x)
  have hxd : J (d x) x = J (FiniteBayesDecision.chooseMAP J x) x := by linarith
  calc J θ x ≤ J (FiniteBayesDecision.chooseMAP J x) x :=
        FiniteBayesDecision.chooseMAP_maximizes J x θ
    _ = J (d x) x := hxd.symm

/-- **The optimality certificate.**  For every finite decision problem over the
reals, a deterministic policy is Bayes-optimal exactly when it is pointwise
MAP. -/
theorem pointwiseMAP_iff_bayesOptimal [Nonempty Θ] (J : Θ → X → ℝ) (d : X → Θ) :
    BayesOptimal J d ↔ PointwiseMAP J d :=
  ⟨bayesOptimal_imp_pointwiseMAP J d, pointwiseMAP_imp_bayesOptimal J d⟩

/-- **The certificate is not vacuous.**  A policy that is not pointwise MAP
strictly loses prior-averaged success. -/
theorem not_pointwiseMAP_imp_strict_loss [Nonempty Θ] (J : Θ → X → ℝ) (d : X → Θ)
    (hd : ¬ PointwiseMAP J d) :
    FiniteBayesDecision.success J d <
      FiniteBayesDecision.success J (FiniteBayesDecision.chooseMAP J) := by
  have hle : FiniteBayesDecision.success J d ≤
      FiniteBayesDecision.success J (FiniteBayesDecision.chooseMAP J) :=
    FiniteBayesDecision.chooseMAP_optimal J d
  refine lt_of_le_of_ne hle ?_
  intro heq
  exact hd ((pointwiseMAP_iff_bayesOptimal J d).mp (le_of_eq heq.symm))

/-! ## 2. Forced choice at a strict maximizer -/

/-- A candidate `θ` **strictly maximizes** at `x` when every other candidate has
strictly smaller joint mass there. -/
def StrictMax (J : Θ → X → ℝ) (x : X) (θ : Θ) : Prop :=
  ∀ θ', θ' ≠ θ → J θ' x < J θ x

/-- **Forcing.**  At a sample with a strict maximizer, every Bayes-optimal policy
is forced to return that maximizer (in particular the choice is unique). -/
theorem pointwiseMAP_forces_strictMax (J : Θ → X → ℝ) (d : X → Θ)
    (hd : PointwiseMAP J d) {x : X} {θ : Θ} (h : StrictMax J x θ) : d x = θ := by
  by_contra hne
  have hlt := h (d x) hne
  have hle := hd x θ
  linarith

/-- The strict maximizer is the unique maximizer: every maximizer equals it. -/
theorem strictMax_unique (J : Θ → X → ℝ) {x : X} {θ : Θ} (h : StrictMax J x θ) :
    ∀ θ', J θ x ≤ J θ' x → θ' = θ := by
  intro θ' hle
  by_contra hne
  have hlt := h θ' hne
  linarith

/-! ## 3. The conditional-posterior-one boundary (necessary and sufficient) -/

/-- **Conditional posterior is one iff the supported truth-fibre is a
singleton.**  For nonnegative joint mass and positive predictive probability, the
merged posterior `AssemblyP1.GenomeOrbitAdapter.PosteriorMAP.posterior` equals
`1` at `θ` exactly when every candidate of positive joint mass equals `θ`.  This
is the exact boundary at which posterior certainty and singleton support agree;
the positive-predictive-mass hypothesis is essential (zero-mass samples are
handled separately by `AssemblyP1.PosteriorMAPEquivalence.zeroMass_all_joint_max`). -/
theorem posterior_eq_one_iff_singleton_support (J : Θ → X → ℝ) (x : X) (θ : Θ)
    (hnn : ∀ θ', 0 ≤ J θ' x)
    (hpos : 0 < GenomeOrbitAdapter.PosteriorMAP.predictiveMass J x) :
    GenomeOrbitAdapter.PosteriorMAP.posterior J x (ne_of_gt hpos) θ = 1 ↔
      ∀ θ', 0 < J θ' x → θ' = θ := by
  unfold GenomeOrbitAdapter.PosteriorMAP.posterior
  rw [div_eq_one_iff_eq (ne_of_gt hpos)]
  constructor
  · intro h θ' hpos'
    unfold GenomeOrbitAdapter.PosteriorMAP.predictiveMass at h
    by_contra hne
    have hsplit : J θ x + (∑ θ'' ∈ (Finset.univ.erase θ), J θ'' x) =
        ∑ θ'' : Θ, J θ'' x :=
      Finset.add_sum_erase (Finset.univ : Finset Θ) (fun θ'' => J θ'' x)
        (Finset.mem_univ θ)
    have hrest : (∑ θ'' ∈ (Finset.univ.erase θ), J θ'' x) = 0 := by linarith
    have hmem : θ' ∈ (Finset.univ.erase θ : Finset Θ) :=
      Finset.mem_erase.mpr ⟨hne, Finset.mem_univ θ'⟩
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun θ'' _ => hnn θ'')).mp hrest θ' hmem
    linarith
  · intro h
    unfold GenomeOrbitAdapter.PosteriorMAP.predictiveMass
    have hzero : ∀ θ' ∈ (Finset.univ : Finset Θ), θ' ≠ θ → J θ' x = 0 := by
      intro θ' _ hne
      have hnot : ¬ 0 < J θ' x := fun hp => hne (h θ' hp)
      exact le_antisymm (not_lt.mp hnot) (hnn θ')
    exact (Finset.sum_eq_single θ hzero
      (fun hnot => absurd (Finset.mem_univ θ) hnot)).symm

/-- The converse form: the posterior at `θ` is *not* one exactly when some other
candidate also carries positive joint mass. -/
theorem posterior_ne_one_iff_not_singleton_support (J : Θ → X → ℝ) (x : X) (θ : Θ)
    (hnn : ∀ θ', 0 ≤ J θ' x)
    (hpos : 0 < GenomeOrbitAdapter.PosteriorMAP.predictiveMass J x) :
    GenomeOrbitAdapter.PosteriorMAP.posterior J x (ne_of_gt hpos) θ ≠ 1 ↔
      ∃ θ', θ' ≠ θ ∧ 0 < J θ' x := by
  rw [Ne, posterior_eq_one_iff_singleton_support J x θ hnn hpos]
  constructor
  · intro h
    by_contra hc
    apply h
    intro θ' hpos'
    by_contra hne
    exact hc ⟨θ', hne, hpos'⟩
  · rintro ⟨θ', hne, hpos'⟩ h1
    exact hne (h1 θ' hpos')

/-! ## 4. Smallest finite witnesses pinning the non-claimed directions -/

namespace TieWitness

/-- Two candidates, one sample, equal joint mass `1`. -/
def J : Fin 2 → Fin 1 → ℝ := fun _ _ => 1

/-- The constant-`0` policy is pointwise MAP. -/
theorem pointwise_zero : PointwiseMAP J (fun _ => 0) := by
  intro x θ
  simp [J]

/-- The constant-`1` policy is pointwise MAP as well. -/
theorem pointwise_one : PointwiseMAP J (fun _ => 1) := by
  intro x θ
  simp [J]

/-- **Ties.**  Two distinct policies are both Bayes-optimal, so optimality does
not force a unique answer. -/
theorem both_optimal :
    BayesOptimal J (fun _ => 0) ∧ BayesOptimal J (fun _ => 1) :=
  ⟨pointwiseMAP_imp_bayesOptimal J _ pointwise_zero,
    pointwiseMAP_imp_bayesOptimal J _ pointwise_one⟩

/-- The two optimal policies are genuinely different. -/
theorem policies_distinct :
    (fun _ : Fin 1 => (0 : Fin 2)) ≠ (fun _ : Fin 1 => (1 : Fin 2)) := by
  intro h
  have := congrFun h (0 : Fin 1)
  norm_num at this

end TieWitness

namespace StrictLossWitness

/-- `J θ x = 2` on the diagonal and `1` off it. -/
def J : Fin 2 → Fin 2 → ℝ := fun θ x => if θ = x then 2 else 1

/-- The constant-`1` policy is not pointwise MAP: at `x = 0` it returns `1`
(mass `1`) while `0` has mass `2`. -/
theorem not_pointwise : ¬ PointwiseMAP J (fun _ => 1) := by
  intro h
  have h0 := h 0 0
  simp [J] at h0

/-- **Strict loss.**  The constant-`1` policy strictly loses prior-averaged
success, so the certificate genuinely constrains every optimal policy. -/
theorem strict_loss :
    FiniteBayesDecision.success J (fun _ => 1) <
      FiniteBayesDecision.success J (FiniteBayesDecision.chooseMAP J) :=
  not_pointwiseMAP_imp_strict_loss J _ not_pointwise

end StrictLossWitness

/-! ## 5. Instantiation to the exact iid read model -/

/-- **The certificate for the exact iid read model.**  For the merged iid joint
`AssemblyP1.IidMapMonotonicity.iidJoint π p n`, a policy is Bayes-optimal exactly
when it is pointwise MAP, for every sample size `n` including `0`. -/
theorem iid_certificate {R : Type*} [Fintype R] [Nonempty Θ]
    (n : ℕ) (π : Θ → ℝ) (p : Θ → R → ℝ) (d : (Fin n → R) → Θ) :
    BayesOptimal (IidMapMonotonicity.iidJoint π p n) d ↔
      PointwiseMAP (IidMapMonotonicity.iidJoint π p n) d :=
  pointwiseMAP_iff_bayesOptimal _ d

/-! ## 6. Instantiation to the finite genome rotation-class read model -/

/-- **The certificate for the concrete AssemblyP1 circular oriented read model.**
Candidate hypotheses are genome **rotation-equivalence classes**
`Quotient (rotSetoid α G)`, the likelihood is the exact normalized window pmf
`p_G(w) = mult_G(w)/|G|`, and the observation is `n` independent reads.  A policy
on orbit classes is Bayes-optimal exactly when it is pointwise MAP. -/
theorem orbit_certificate {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {G L : ℕ} [NeZero G]
    (π : Quotient (GenomeOrbitAdapter.rotSetoid α G) → ℝ) (n : ℕ)
    (d : (Fin n → (Fin L → α)) → Quotient (GenomeOrbitAdapter.rotSetoid α G)) :
    BayesOptimal
        (IidMapMonotonicity.iidJoint π
          (GenomeOrbitAdapter.orbitReadPmf (α := α) G L) n) d ↔
      PointwiseMAP
        (IidMapMonotonicity.iidJoint π
          (GenomeOrbitAdapter.orbitReadPmf (α := α) G L) n) d :=
  pointwiseMAP_iff_bayesOptimal _ d

/-- **The conditional-posterior-one boundary for genome rotation classes.**  For
a read sample `x` with positive predictive mass and nonnegative joint mass, the
posterior on the orbit class `θ` is `1` exactly when every orbit class of
positive joint mass is `θ`.  This is the "singleton supported truth-fibre"
endpoint of target D instantiated to the finite family of genome
rotation-equivalence classes. -/
theorem orbit_posterior_eq_one_iff_singleton_support
    {α : Type*} [Fintype α] [DecidableEq α] {G L : ℕ} [NeZero G]
    (π : Quotient (GenomeOrbitAdapter.rotSetoid α G) → ℝ)
    (n : ℕ) (x : Fin n → (Fin L → α))
    (θ : Quotient (GenomeOrbitAdapter.rotSetoid α G))
    (hnn : ∀ o, 0 ≤ IidMapMonotonicity.iidJoint π
      (GenomeOrbitAdapter.orbitReadPmf (α := α) G L) n o x)
    (hpos : 0 < GenomeOrbitAdapter.PosteriorMAP.predictiveMass
      (IidMapMonotonicity.iidJoint π
        (GenomeOrbitAdapter.orbitReadPmf (α := α) G L) n) x) :
    GenomeOrbitAdapter.PosteriorMAP.posterior
        (IidMapMonotonicity.iidJoint π
          (GenomeOrbitAdapter.orbitReadPmf (α := α) G L) n) x
        (ne_of_gt hpos) θ = 1 ↔
      ∀ o, 0 < IidMapMonotonicity.iidJoint π
        (GenomeOrbitAdapter.orbitReadPmf (α := α) G L) n o x → o = θ :=
  posterior_eq_one_iff_singleton_support _ x θ hnn hpos

/-! ## 7. Axiom audit -/

#print axioms pointwiseMAP_imp_bayesOptimal
#print axioms bayesOptimal_imp_pointwiseMAP
#print axioms pointwiseMAP_iff_bayesOptimal
#print axioms not_pointwiseMAP_imp_strict_loss
#print axioms pointwiseMAP_forces_strictMax
#print axioms strictMax_unique
#print axioms posterior_eq_one_iff_singleton_support
#print axioms posterior_ne_one_iff_not_singleton_support
#print axioms iid_certificate
#print axioms orbit_certificate
#print axioms orbit_posterior_eq_one_iff_singleton_support
#print axioms TieWitness.both_optimal
#print axioms StrictLossWitness.strict_loss

end AssemblyP1.BayesOptimalityCertificate
