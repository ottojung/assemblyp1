# Genome-level adapter: conditional Bayes vs ordinary finite ML in the exact AssemblyP1 read model (#271)

_Status: research comparison note. All Lean statements referenced below are
kernel-checked in `AssemblyP1/ConditionalVsMLGenomeAdapter271.lean` and audited in
`AxiomAudit271.lean` (only `propext`, `Classical.choice`, `Quot.sound`). This
note closes the single item that the merged #271 handoff left open — a
genome-level (A)-side adapter — while keeping the source-fidelity boundary
explicit: the promise `E` used here is an attributed **external** input, not the
source predicate `I_s`._

## 1. What is instantiated, exactly

The abstract separation of
`AssemblyP1/ConditionalVsOrdinaryMLSeparation.lean` (#271) and the general
orbit-class boundary `AssemblyP1.FiniteBayesianSideInformation.posteriorMass_eq_one_iff`
(#272) are instantiated on the concrete finite circular read model of
`AssemblyP1/GenomeOrbitAdapter.lean` (#269):

| axis | choice in this adapter |
| --- | --- |
| alphabet | `Sym = Fin 2` (binary) |
| genome length | `G = 4`; circular genome `ZMod 4 → Sym` |
| read length | `L = 2`; oriented read string `Read = Fin 2 → Sym` |
| candidate universe | three rotation-**orbit classes**: `0001`, `0011`, `0101` up to rotation (`rep`, `orbit`) |
| observation model | `p i w = orbitReadPmf (G:=4) (L:=2) (orbit i) w = #{starts spelling w in g} / 4`; normalized (`p_sum_one`) and nonnegative (`p_nonneg`) |
| observation representation | oriented one-strand windows; **no** reverse-complement quotient (per #269/#260) |
| prior | uniform `1/3` over the three orbit classes (`prior`), normalized (`prior_sum_one`); **not** over raw spellings |
| likelihood objective | exact single-read pmf (the iid product is its `n`-fold power); **not** the MB09 fixed-`N` product-binomial and **not** the §6.2 feasible-flow objective |
| side information | truth-dependent promise `E t g r` revealing the true genome's read-pmf support (`SupportEq`) |
| rotation | the genuine rotation action on `ZMod 4`; `readPmf` is rotation invariant (`readPmf_rotWord`), so it descends to orbits |

The three representatives are genuinely distinct orbit classes
(`orbit_zero_ne_one`, `orbit_zero_ne_two`, `orbit_one_ne_two`,
`orbit_injective`), proved through the rotation-invariant read pmf rather than
by quotient reasoning.

## 2. The two kernel-checked endpoints

### (A ∧ ¬B) — separation

Truth orbit `1` (`0011`), observed read string `00`.

* **(A) conditional recovery is certain.** With the externally supplied
  truth-dependent promise `E 1`,
  `posteriorMass prior p (E 1) orbit (r2 0 0) (orbit 1) = 1`
  (`sep_posteriorMass_one`), established by the general #272 theorem
  `posteriorMass_eq_one_iff`: under `E 1` the only candidate of positive prior
  and positive likelihood is the truth (`E_one_eq`). The same fact in the
  excluded-competitor form of #272 is `sep_posteriorMass_one_excluded`
  (`posteriorMass_eq_one_iff_excluded`): every candidate of positive prior and
  positive likelihood outside the true orbit is excluded by `E 1`.
* **(B) ordinary ML prefers the wrong orbit.** `p 1 (r2 0 0) = 1/4 < 1/2 =
  p 0 (r2 0 0)` (`sep_ml_strict`), so the truth orbit `1` is not an ML maximizer
  (`sep_truth_not_ml`); the wrong orbit `0` (`0001`) is.
* **the ordinary posterior is not certain.** The wrong orbit `0` retains
  positive prior and positive likelihood, so
  `posteriorMass prior p (fun _ _ => True) orbit (r2 0 0) (orbit 1) ≠ 1`
  (`sep_ordinary_not_certain`); its exact value is `1/3`
  (`postCandidate_sep`).

Packaged as `separation_genome`.

### (B ∧ ¬A) — converse

Truth orbit `2` (`0101`), observed read string `01`.

* **(B) ordinary ML uniquely selects the truth.** `p 2 (r2 0 1) = 1/2 > 1/4`
  beats both other orbits (`conv_ml_strict`), and `2` is the *unique* maximizer
  (`conv_ml_unique`).
* **(A) the ordinary posterior is not certain.** The wrong orbit `1` (`0011`)
  retains positive prior and positive likelihood, so
  `posteriorMass prior p (fun _ _ => True) orbit (r2 0 1) (orbit 2) ≠ 1`
  (`conv_ordinary_not_certain`); its exact value is `1/2`
  (`postCandidate_conv`).

Packaged as `converse_genome`.

Both endpoints use **one and the same** generative read model: the same `p`,
the same orbit universe, and the same prior. The only additional ingredient in
(A) is the side observation `E`.

## 3. The promise `E` is external, truth-dependent, and not observable from `R`

`E t g r = SupportEq t g` states that candidate `g` has the same read-pmf
**support** as the true genome `t`. It is a predicate on the concrete read
model; it ignores the read `r`, so it is certainly not inferred from `r`; and at
a fixed read it genuinely separates candidates, so it is **not data-only**:
`E_one_not_dataOnly` proves there is no `f : Read → Prop` with
`E 1 g r ↔ f r` for all `g, r`. This is the same boundary the abstract toy draws
with `sideInfo_not_dataOnly` (#271) and the data-only cancellation lemma
`condPosterior_dataOnly`.

Consequences, stated to avoid over-claiming:

* `E` must be **supplied**; it cannot be computed from the observed read alone.
* Conditioning the prior **and** the likelihood on `E` is what
  `posteriorMass`/`predictiveMass` do (`jointMass = π g · p_g(r) · 1_{E(g,r)}`);
  the indicator is not dropped.
* `E` is **not** the source predicate
  `SourceFaithfulIs.InformationFeasible`. It is an abstract, attributed side
  observation. No claim is made here that `E` is realised by coverage/bridging
  information or by the Not-So-Greedy theorem.
* "Knowing the truth satisfies `F`" as side information is **not** the same as
  running ordinary ML over `F`-qualified candidates (a restricted unconditional
  experiment), and **not** the same as a theorem for unrestricted likelihood.

## 4. Relation to the historical W1/W2 witnesses and the representation warnings

This adapter does **not** coerce W1/W2 into the conditional layer, and does not
manufacture a contradiction. The merged `W1W2SeparationCompatibility` verdict
stands: under the exact shared observable model of the same-length witnesses
(fixed realized read-type count vector; §6.1 product-of-binomial-marginals and
exact same-length multinomial objectives) the (B)-side failure is instantiated,
but the (A)-side is **not defined** there — no prior, no normalized observation
pmf, no side event. The present adapter supplies exactly those three missing
objects, on a *different* (but also exact) read model: the uniformly-sampled
oriented-window read pmf of `GenomeOrbitAdapter`. It is therefore a genuine
genome-level (A)-side witness, but it is **not** a source-faithful `I_s`
witness.

Representation warnings carried over unchanged:

* oriented read strings (`GenomeOrbitAdapter`/`SourceFaithfulIs.window`) versus
  the reverse-complement-collapsed molecule representation (#260) are different
  observables with different likelihoods and are not identified here;
* realized read **start positions** (`SourceFaithfulIs.R : Finset (Fin S.len)`,
  the latent placements used by `InformationFeasible`) are different from the
  observed read **strings** consumed by the likelihood; the adapter's `Obs` is
  the read string, and its `E` is a promise, not a latent placement set.

## 5. Connection to the merged classification lemmas (reuse, no forking)

* **(A)-boundary:** `posteriorMass_eq_one_iff` / `readOnly_posterior_eq_one_iff`
  (#272) are applied by name; the adapter re-proves no generic posterior lemma.
* **(B)-boundary:** `MLMax` is the read-model instance of the prior-free,
  `E`-free `ConditionalVsOrdinaryMLSeparation.isMLMaximizer`; the unique form is
  the read-model instance of the unique-maximizer boundary.
* **MAP vs ML:** the general posterior/joint-mass equivalence is #269
  `GenomeOrbitAdapter.PosteriorMAP.posterior_argmax_iff`, instantiated on the
  read-model joint by `map_ml_agree_uniform`: under the uniform orbit prior the
  posterior ordering coincides with the ordinary ML ordering. The prior
  therefore does not by itself produce the (A)-side collapse — the promise `E`
  is what does.
* The general ordinary-ML classification (#255/#258/#259/#261) is untouched.

## 6. Open items (labelled, not claimed)

1. **Source-faithful `E`.** Replacing the support-revealing promise by a
   concrete candidate-specific latent-start predicate — e.g. `∃ T` compatible
   with the observed read strings with `InformationFeasible g T`, per the #266
   correction — and proving the same collapse is **open**. This is the only
   step between the present adapter and a source-faithful genome witness.
2. **`E → B`.** No truth-dependent `E` implies ordinary ML recovery in general
   (`sep_truth_not_ml` refutes it on this model). A sufficient refinement would
   add an observation-side component `C(R)` that is itself sufficient for (B)
   on the fixed universe (candidates: the #255/#258 classifications); this is a
   conjecture, not proved here.
3. **Orbit-size vs spelling prior.** The general distinction is #269
   `spellingPushforward_eq_uniform_iff_constant_orbitSize`; the adapter uses an
   orbit-class prior and does not assert specific orbit sizes.

## 7. Manuscript-safe wording (for #265/#268, non-competing)

> The abstract conditional-Bayes / ordinary-ML separation instantiates on the
> exact finite circular read model: taking the candidate universe to be rotation
> orbits, the observation model to be the normalized oriented-window read pmf,
> the prior to be uniform over orbit classes, and the side information to be an
> externally supplied truth-dependent promise, there is a read at which the
> conditional posterior on the true orbit is one while ordinary maximum
> likelihood strictly prefers a wrong orbit; conversely, there is a read at
> which ordinary maximum likelihood uniquely selects the true orbit while the
> unconditional posterior is not certain. The promise is a genuine side
> observation (not a function of the read alone) and is explicitly external: it
> is not the source information-feasibility predicate, whose instantiation
> remains open. The historical same-length witnesses instantiate the
> ordinary-ML failure under their fixed count-vector objectives but do not carry
> the prior, normalized observation model, or promise that the conditional layer
> requires.
