# A necessary-and-sufficient finite Bayes/MAP optimality certificate (#269)

Antonina #269 target B asks for a kernel-checked finite Bayes/MAP theorem: the
MAP policy `argmax_θ π θ · ∏_i p_θ(x_i)` maximizes prior-averaged zero-one
success against **every** policy, for every sample size `n` (including `n = 0`),
with finite sum/max reasoning and explicit tie handling.  Target D asks for the
correctly formulated posterior/MAP equivalence with positive predictive mass and
zero-mass cases handled.

The merged generic core is `AssemblyP1.FiniteBayesDecision` (PR #174): it proves
the **sufficient** half (pointwise joint-mass maximization implies aggregate
optimality) for arbitrary real joint mass, and the exact iid `n → n+1`
monotonicity bridge is `AssemblyP1.IidMapMonotonicity` (PR #193) with the
explicit Bayes value `V_{n+1} ≥ V_n` in `AssemblyP1.BayesValueMonotonicity`
(PR #231).  The orbit-class adapter is `AssemblyP1.GenomeOrbitAdapter` (PR #200)
and the positive-mass posterior equivalence is
`AssemblyP1.PosteriorMAPEquivalence` (PR #261).

This note records the **missing increment**: the *necessary* half of optimality,
packaged as an exact certificate, plus the conditional-posterior-one boundary
instantiated to genome rotation classes.  The Lean module is
`AssemblyP1/BayesOptimalityCertificate.lean`, its dedicated axiom audit is
`AssemblyP1/BayesOptimalityCertificateAudit.lean`, and the independent exact
rational verifier is
`scripts/verify_269_bayes_optimality_certificate.py`.

## The certificate (target B, necessary and sufficient)

All in namespace `AssemblyP1.BayesOptimalityCertificate`, over
`{Θ X : Type*} [Fintype Θ] [DecidableEq Θ] [Fintype X]` and `J : Θ → X → ℝ`.

- `PointwiseMAP J d := ∀ x θ, J θ x ≤ J (d x) x`.
- `BayesOptimal J d := success J (chooseMAP J) ≤ success J d` (the constructed
  MAP rule is the reference optimum; `chooseMAP`/`success` are the merged
  `AssemblyP1.FiniteBayesDecision` definitions, reused, not reproved).

| Declaration | Statement |
|---|---|
| `pointwiseMAP_imp_bayesOptimal` | pointwise MAP ⟹ Bayes-optimal (restates the merged sufficient half) |
| `bayesOptimal_imp_pointwiseMAP` | Bayes-optimal ⟹ pointwise MAP (**new**) |
| `pointwiseMAP_iff_bayesOptimal` | the exact certificate: `BayesOptimal J d ↔ PointwiseMAP J d` |
| `not_pointwiseMAP_imp_strict_loss` | a non-pointwise policy strictly loses (`success J d < success J (chooseMAP J)`) |

The new necessity proof is a finite, **sign-free** argument.  For every sample
`y` the deficit `J (chooseMAP J y) y - J (d y) y` is nonnegative by
`chooseMAP_maximizes`; if `d` is optimal the total deficit is zero, so by
`Finset.sum_eq_zero_iff_of_nonneg` every deficit vanishes and `d` is pointwise
MAP.  No positivity or normalization of `J` is needed for the algebraic
statement; those enter only when reading `J` probabilistically.  Ties are
handled by the constructive `chooseMAP` witness (a genuine maximizer is
selected); no uniqueness is claimed.

### Forced choice and uniqueness at a strict maximizer

- `StrictMax J x θ := ∀ θ', θ' ≠ θ → J θ' x < J θ x`.
- `pointwiseMAP_forces_strictMax` — every pointwise (hence every optimal) policy
  returns the strict maximizer at such a sample.
- `strictMax_unique` — a strict maximizer is the unique maximizer.

### Smallest witnesses pinning the directions *not* claimed

- `TieWitness.both_optimal` — two **distinct** policies (`const 0` and `const 1`
  on two equal-mass candidates) are both Bayes-optimal, so optimality does not
  force a unique answer; `TieWitness.policies_distinct` records that they
  differ.
- `StrictLossWitness.strict_loss` — on `J θ x = 2` on the diagonal and `1` off
  it, the constant-`1` policy is not pointwise and strictly loses, so the
  certificate is not vacuous.

## The conditional-posterior-one boundary (target D)

`posterior_eq_one_iff_singleton_support` states, for nonnegative joint mass and
**positive predictive mass**, that the merged posterior
`AssemblyP1.GenomeOrbitAdapter.PosteriorMAP.posterior` equals `1` at `θ` exactly
when every candidate of positive joint mass equals `θ` — i.e. the supported
truth-fibre is a **singleton**:

```
posterior J x _ θ = 1  ↔  ∀ θ', 0 < J θ' x → θ' = θ
```

`posterior_ne_one_iff_not_singleton_support` is the contrapositive form: the
posterior fails to be one exactly when some other candidate carries positive
joint mass.  The positive-predictive-mass hypothesis is essential; zero-mass
samples are handled separately by the merged
`AssemblyP1.PosteriorMAPEquivalence.zeroMass_all_joint_max` (every candidate is
a tie there, so the MAP tie choice is irrelevant).  This is a theorem about
conditioning on the observation alone — it is **not** the truth-dependent
event-conditional inference of #266.

This is also a specialization of the more general #272 endpoint
`AssemblyP1.FiniteBayesianSideInformation.readOnly_posterior_eq_one_iff`: taking
`π ≡ 1`, `orbit = id`, and the trivial promise `E ≡ True` there recovers exactly
the statement above (up to the object-level identity
`posteriorMass 1 J True id x θ = posterior J x _ θ`).  The contribution here is
therefore the #269-scoped statement for the merged point-candidate
`GenomeOrbitAdapter.PosteriorMAP.posterior` and its rotation-class instantiation
`orbit_posterior_eq_one_iff_singleton_support`, not a new mathematical fact
beyond that specialization; the genuinely new target-B content is the necessity
half `bayesOptimal_imp_pointwiseMAP`.

### Instantiation to the AssemblyP1 read model

Candidate hypotheses are the finite family of genome **rotation-equivalence
classes** `Quotient (rotSetoid α G)`, the likelihood is the exact normalized
circular window pmf `p_G(w) = mult_G(w)/|G|` (`orbitReadPmf`), and the
observation is `n` independent reads `Fin n → (Fin L → α)`:

- `orbit_certificate` — a policy on rotation classes is Bayes-optimal iff it is
  pointwise MAP for the exact iid orbit joint.
- `orbit_posterior_eq_one_iff_singleton_support` — the posterior on a rotation
  class is `1` iff every positive-mass rotation class is that class.
- `iid_certificate` — the same certificate for the exact iid joint
  `AssemblyP1.IidMapMonotonicity.iidJoint`.

## Prior-averaged scope: the PerTruthDrop corollary check

The certificate is about the **prior-averaged** success, which is essential.
The merged `AssemblyP1.GenomeOrbitAdapter.PerTruthDrop.perTruth_true_drops`
shows per-truth success can strictly *drop* (`16/25 < 4/5`) with one extra read.
This is consistent: the independent verifier recomputes the prior-averaged MAP
success for the same binary model as `V_1 = 13/20` and `V_2 = 139/200`, so the
average is strictly increasing while one per-truth term decreases.  No per-truth
monotonicity is claimed anywhere.

## What is external versus Lean

| Item | Status |
|---|---|
| finite MAP optimality (sufficient + necessary), certificate | **Lean kernel-checked**, this module |
| posterior-one boundary, rotation-class instantiation | **Lean kernel-checked**, this module |
| per-truth drop `4/5 → 16/25` | **Lean kernel-checked** (`GenomeOrbitAdapter.PerTruthDrop`, PR #200) |
| circularity, uniform start sampling, `p_G = mult_G/|G|` as likelihood | **external modeling inputs** (documented in `docs/assembly-map-orbit-adapter-269.md`) |
| reverse-complement / dihedral orbit quotient | **not claimed** (rotation classes only) |
| global "ML is best algorithm" | **not claimed**; only specified prior-average accuracy for a fixed observation model |

## Reproducible proof commands

```sh
lake build AssemblyP1.BayesOptimalityCertificate --wfail        # build, warnings as errors
lake build AssemblyP1.BayesOptimalityCertificateAudit --wfail  # audit module build
lake env leanchecker AssemblyP1.BayesOptimalityCertificate     # kernel replay
lake env leanchecker AssemblyP1.BayesOptimalityCertificateAudit
python3 scripts/verify_269_bayes_optimality_certificate.py     # independent exact rational check
python3 scripts/check-research-docs.py                         # docs integrity
```

Axiom audit: every audited theorem depends only on `propext`,
`Classical.choice`, `Quot.sound` (inline `#print axioms` in
`AssemblyP1/BayesOptimalityCertificate.lean`, replayed by
`AssemblyP1/BayesOptimalityCertificateAudit.lean`; the CI step `Audit axioms in
every theorem module` enforces the same allow-list over the whole `AssemblyP1`
tree).  No `sorry`, `admit`, new `axiom`, `native_decide`, `implemented_by`, or
`unsafe` in the module.
