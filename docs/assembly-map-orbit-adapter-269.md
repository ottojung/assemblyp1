# Assembly-specific MAP orbit adapter for circular oriented reads (#269)

Antonina #269 asks for a kernel-checked adapter from the merged finite Bayes/MAP
optimality theorem to the concrete AssemblyP1 read model: circular oriented
genomes with uniformly sampled genomic starts,

```text
p_G(w) = multiplicity_G(w) / |G|,
```

a finite family of genome **rotation-equivalence classes** (not raw rotations)
with correct priors on classes, and real/rational normalization.  This note
records that adapter (`AssemblyP1/GenomeOrbitAdapter.lean`, PR #200), its
dedicated axiom audit (`AssemblyP1/GenomeOrbitAdapterAudit.lean`), and the
independent exact rational verifier
`scripts/verify_269_genome_orbit_adapter.py`.

## The read model (external input)

Fix a finite read alphabet `α`, a positive circular genome length `G`, and a
read length `L`.  A circular genome is a word `S : ZMod G → α`; the oriented
length-`L` window at a uniformly sampled genomic start `s : ZMod G` is
`window S s : Fin L → α`.  The read pmf is the normalized window multiplicity
`readPmf S w = mult S w / G` with `mult S w = #{s | window S s = w}`.  The
modeling inputs — circularity, uniformity of start sampling, and the choice of
the read pmf as the likelihood — are external; every arithmetic and
decision-theoretic claim below is Lean-kernel-checked.

## Exact theorem names and statements

All in namespace `AssemblyP1.GenomeOrbitAdapter` unless noted.  Section
variables: `{α : Type*} [Fintype α] [DecidableEq α]`, `{G L : ℕ} [NeZero G]`.

Read model and normalization:

- `mult_eq_sum (S) (w) : mult S w = ∑ s : ZMod G, if window S s = w then 1 else 0`
- `sum_mult (S) : ∑ w : Fin L → α, mult S w = G` — every one of the `G` starts contributes exactly one window.
- `readPmf_sum_one (S) : ∑ w : Fin L → α, readPmf S w = 1` — the exact read pmf is a probability mass function.

Rotation invariance and the rotation-orbit quotient:

- `window_rotWord (S) (j) (s) : window (rotWord S j) s = window S (s + j)`
- `mult_rotWord (S) (j) (w) : mult (rotWord S j) w = mult S w`
- `readPmf_rotWord (S) (j) (w) : readPmf (rotWord S j) w = readPmf S w`
- `orbitReadPmf` — the descended pmf on `Quotient (rotSetoid α G)` (noncomputable lift).
- `orbitReadPmf_sum_one (G L) (o) : ∑ w, orbitReadPmf G L o w = 1` — normalization survives the quotient.
- `quotient_likelihood_well_defined_iff (ρ) (L) : (∃ L', ∀ g r, L' (Quotient.mk ρ g) r = L g r) ↔ (∀ g h, g ≈ h → L g = L h)` — a likelihood descends to a genome quotient **iff** it is constant on equivalence classes.  Rotation invariance holds for the oriented one-strand model; reverse-complement invariance is a genuine extra hypothesis, so no RC/dihedral quotient is claimed.

Prior-averaged monotonicity (target C endpoint, instantiated not reproved):

- `orbit_map_success_monotone [Nonempty α] (π) (n) : IidMapMonotonicity.mapSuccess π (orbitReadPmf G L) n ≤ IidMapMonotonicity.mapSuccessSucc π (orbitReadPmf G L) n` — for **every** `n` including `0` and an arbitrary prior `π` on orbit classes.

Priors on orbit classes versus raw spellings:

- `uniformOrbitPrior` (noncomputable), `uniformOrbitPrior_sum_one : ∑ o, uniformOrbitPrior o = 1`
- `orbitSize_pos (o) : 0 < orbitSize o`, `sum_orbitSize : ∑ o, orbitSize o = Fintype.card (ZMod G → α)`
- `spellingPushforwardPrior` (noncomputable), `spellingPushforwardPrior_sum_one : ∑ o, spellingPushforwardPrior o = 1`
- `spellingPushforward_eq_uniform_iff_constant_orbitSize : (∀ o, spellingPushforwardPrior o = uniformOrbitPrior o) ↔ (∀ o o', orbitSize o = orbitSize o')` — the uniform-spelling pushforward is proportional to orbit size; it equals the uniform orbit prior **iff all orbits have equal size**.

Uniform orbit prior makes MAP a maximum-likelihood policy:

- `uniform_orbit_prior_ML [Nonempty α] (n) (x) (o) : likelihood n o x ≤ likelihood n (FiniteBayesDecision.chooseMAP (IidMapMonotonicity.iidJoint (uniformOrbitPrior) (orbitReadPmf G L) n) x) x`

Per-truth success is **not** monotone (why the monotonicity is prior-averaged only):

- `PerTruthDrop.perTruth_true_one : perTruth1 0 = 4 / 5`
- `PerTruthDrop.perTruth_true_two : perTruth2 0 = 16 / 25`
- `PerTruthDrop.perTruth_true_drops : perTruth2 0 < perTruth1 0`

  Binary read alphabet, `p_true(A) = 4/5`, `p_comp(A) = 1/2`: one-read success `4/5`, two-read success `16/25`.

Separation from #266 (event-conditional inference):

- `CoverageConditional.conditional_MAP_optimal [Nonempty Θ] (J) (C) (hC) (d) : conditionalSuccess J C d ≤ conditionalSuccess J C (FiniteBayesDecision.chooseMAP J)`
- `CoverageConditional.conditionalSuccess_univ_eq [Nonempty Θ] (J) (d) : conditionalSuccess J Finset.univ d = FiniteBayesDecision.success J d / predictiveMass J Finset.univ` — conditioning on a coverage event rescales by the predictive mass `P(C)`; the conditional experiment is a different quantity from the unconditional Bayes average.  Truth-dependent conditioning is #266, not this module.

Posterior/MAP equivalence for positive predictive mass:

- `PosteriorMAP.posterior_argmax_iff [Nonempty Θ] (J) (x) (h : 0 < predictiveMass J x) (θ) : posterior J x _ θ ≤ posterior J x _ (FiniteBayesDecision.chooseMAP J x) ↔ J θ x ≤ J (FiniteBayesDecision.chooseMAP J x) x` — zero-mass samples are excluded by the `posterior` argument `h : predictiveMass J x ≠ 0`; no division by zero.

Separation from the MB09 fixed-`N` product-binomial pseudo-likelihood:

- `ExactVsSurrogate.exact_ne_productBinomial : exactIidLikelihood (fun _ : Fin 2 => 1/2) (fun _ : Fin 2 => 1) ≠ productBinomialSurrogate 2 (fun _ : Fin 2 => 1/2) (fun _ : Fin 2 => 1)` — the exact iid likelihood `∏_w p_w^{c_w}` omits the surrogate's extra `(1 - p_w)^{N - c_w}` factor per class.

Separation from the §6.2 feasible-flow objective:

- `AssemblyP1.Section62FlowGenomeSeparation.section62_flow_objective_ne_genome_likelihood` (PR #286) — no §6.2 feasible-flow objective equals the exact oriented genome likelihood; the RC pair `S0 = 00`, `S1 = 11` shares a §6.2 visit vector but has exact likelihoods `1` and `0` on the sample `(00)`.

## The adapter invokes the merged optimality theorems by name

The module does **not** redefine or reprove the generic finite-sum cores:

| Merged declaration | Instantiation in the adapter |
|---|---|
| `IidMapMonotonicity.iid_map_success_monotone` | `orbit_map_success_monotone` is literally `iid_map_success_monotone π (orbitReadPmf G L) n (fun o => orbitReadPmf_sum_one G L o)` |
| `FiniteBayesDecision.chooseMAP_maximizes` | `uniform_orbit_prior_ML` (via `le_of_mul_le_mul_left` with the positive uniform prior), `CoverageConditional.conditional_MAP_optimal`, `PosteriorMAP.posterior_argmax_iff` |
| `FiniteBayesDecision.success`, `success_eq_observation_sum` | `CoverageConditional.conditionalSuccess_univ_eq` |
| `IidMapMonotonicity.iidJoint`, `mapSuccess`, `mapSuccessSucc` | the exact iid joint `π o * ∏ i, p o (x i)` and the prior-averaged success sums |

So the concrete objective — maximize `π o * ∏ i : Fin n, orbitReadPmf G L o (x i)` over the finite orbit-class family — **is** the merged Bayes/MAP optimum objective, with `orbitReadPmf_sum_one` supplying the per-candidate pmf normalization hypothesis.

## Reproducible proof commands

```sh
lake build AssemblyP1.GenomeOrbitAdapter --wfail        # build, warnings as errors
lake build AssemblyP1.GenomeOrbitAdapterAudit --wfail  # audit module build
lake env leanchecker AssemblyP1.GenomeOrbitAdapter     # kernel replay
lake env leanchecker AssemblyP1.GenomeOrbitAdapterAudit
python3 scripts/verify_269_genome_orbit_adapter.py     # independent exact rational check
python3 scripts/check-research-docs.py                 # docs integrity
```

Axiom audit: every audited theorem above depends only on `propext`,
`Classical.choice`, `Quot.sound` (inline `#print axioms` in
`GenomeOrbitAdapter.lean`, replayed by `GenomeOrbitAdapterAudit.lean`; the CI
step `Audit axioms in every theorem module` enforces the same allow-list over
the whole `AssemblyP1` tree with `axiom-audit --allow propext,Classical.choice,Quot.sound`).
No `sorry`, `admit`, new `axiom`, `native_decide`, `implemented_by`, or
`unsafe` in the module.

## External versus Lean

External (modeling) inputs: the circular oriented read model itself, uniformity
of genomic-start sampling, and the choice of the read pmf as the likelihood.
Lean-kernel-checked: all normalization, rotation-invariance, quotient,
prior, monotonicity, separation, and counterexample statements listed above.

## Manuscript-ready proof sketch

**Normalization.** Each of the `G` genomic starts contributes exactly one
length-`L` window, so `∑_w mult_S(w) = G` (`sum_mult`, by `Finset.sum_comm`
and `Finset.sum_ite_eq`); dividing by `G` gives `∑_w readPmf S w = 1`
(`readPmf_sum_one`).

**Rotation invariance.** Rotating the genome by `j` reindexes the start set
(`window_rotWord`), and translation is a bijection of `ZMod G`
(`Equiv.sum_comp (Equiv.addRight j)`), so `mult` and hence `readPmf` are
rotation invariant (`mult_rotWord`, `readPmf_rotWord`).  By
`quotient_likelihood_well_defined_iff` the pmf descends to the finite
rotation-orbit type (`orbitReadPmf`) and stays normalized
(`orbitReadPmf_sum_one`).

**Prior-averaged monotonicity.** With `π` an arbitrary prior on orbit classes
and `orbitReadPmf` the per-candidate read pmf, the merged refinement theorem
`IidMapMonotonicity.iid_map_success_monotone` applies verbatim: the policy
that ignores read `n+1` witnesses `mapSuccess π p n ≤ mapSuccessSucc π p n`
for every `n`, including `n = 0`.  This is an average over the prior only:
`PerTruthDrop` kernel-checks that for the fixed true candidate the success
probability drops from `4/5` (one read) to `16/25` (two reads).

**MAP = ML under the uniform orbit prior.** `uniformOrbitPrior` is positive on
every class, so `FiniteBayesDecision.chooseMAP_maximizes` divides away:
the constructed MAP decision maximizes the exact iid likelihood pointwise
(`uniform_orbit_prior_ML`).  Under a uniform prior on raw *spellings* the
induced orbit prior is proportional to orbit size and equals the uniform orbit
prior iff all orbits have equal size
(`spellingPushforward_eq_uniform_iff_constant_orbitSize`) — the prior must be
placed on orbit classes, not spellings.

**Separations.** The exact iid likelihood `∏_w p_w^{c_w}` differs from the
MB09 fixed-`N` product-binomial surrogate on a concrete two-class observation
(`ExactVsSurrogate.exact_ne_productBinomial`), and no §6.2 feasible-flow
objective — all of which factor through the RC molecule-class throughput — can
equal the exact oriented likelihood (PR #286).  Conditioning on a coverage
event rescales the objective by the predictive mass
(`CoverageConditional.conditionalSuccess_univ_eq`); truth-dependent
conditioning is #266 and is not claimed here.
