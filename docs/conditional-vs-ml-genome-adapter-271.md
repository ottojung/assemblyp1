# Genome-level adapter: conditional Bayes vs ordinary finite ML in the exact AssemblyP1 read model (#271)

_Status: research comparison note. All Lean statements referenced below are
kernel-checked in `AssemblyP1/ConditionalVsMLGenomeAdapter271.lean` and audited in
`AxiomAudit271.lean` (only `propext`, `Classical.choice`, `Quot.sound`). This
revision closes the item that the previous merged #271 handoff left open: the
(A)-side premise is no longer an externally supplied, truth-dependent support
oracle, but a **candidate-specific latent-start information-feasibility
predicate** built from the exact source predicate
`SourceFaithfulIs.InformationFeasible` (the `I_s` of Shomorony et al. (2016),
Eq. (1))._

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
| side information | candidate-specific latent-start information feasibility `E i r := ∃ T, (∃ s ∈ T, window (genOf i) 2 s = r) ∧ InformationFeasible (genOf i) 2 T` |
| rotation | the genuine rotation action on `ZMod 4`; `readPmf` is rotation invariant (`readPmf_rotWord`), so it descends to orbits |

The three representatives are genuinely distinct orbit classes
(`orbit_zero_ne_one`, `orbit_zero_ne_two`, `orbit_one_ne_two`,
`orbit_injective`), proved through the rotation-invariant read pmf rather than
by quotient reasoning.

## 2. The two kernel-checked endpoints

### (A ∧ ¬B) — separation

Truth orbit `1` (`0011`), observed read string `00`.

* **(A) conditional recovery is certain.** Conditioning on the latent-start
  feasibility event `E`,
  `posteriorMass prior p E orbit (r2 0 0) (orbit 1) = 1`
  (`sep_posteriorMass_one`), established by the general #272 theorem
  `posteriorMass_eq_one_iff`: at read `00` the only candidate of positive prior
  and positive likelihood satisfying `E` is the truth orbit `1`. The same fact in
  the excluded-competitor form of #272 is `sep_posteriorMass_one_excluded`
  (`posteriorMass_eq_one_iff_excluded`): every candidate of positive prior and
  positive likelihood outside the true orbit is excluded by `E`.
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
(A) is the feasibility event `E`.

## 3. The predicate `E` is candidate-specific, model-internal, and not data-only

The A-side premise is the predicate

```
E i r := ∃ T : Finset (Fin 4),
    (∃ s ∈ T, (genOf i).window 2 s = r) ∧ InformationFeasible (genOf i) 2 T,
```

where `genOf i` is candidate `i`'s representative read as a source-faithful
circular genome (`toGenome`, `genOf`) and `InformationFeasible` is **exactly** the
repository's source predicate `SourceFaithfulIs.InformationFeasible`
(coverage + all-bridged triple repeats + bridged interleaved repeat pairs).

It is therefore:

* **candidate-specific and model-internal.** `E` is a function of the candidate
  `i` and the read `r` only; it is built from the read model and the source
  predicate. No truth-dependent support oracle is supplied. This is the
  `∃ T` compatible-with-the-observed-read, `InformationFeasible g T` predicate
  that the previous handoff listed as the open adapter.
* **not a function of the read alone.** At the *same* read `00` it holds for
  candidate `1` (`E_one_00`) and fails for candidate `0` (`E_zero_00`), so there
  is no `f : Read → Prop` with `E i r ↔ f r` (`E_not_dataOnly`). Hence it cannot
  be inferred from `R`.
* **the source hypothesis, not an extra input.** Conditioning on `E(G, R)` is
  conditioning on "the true genome admits an `I_s`-feasible placement explaining
  the observed read". This is the hypothesis of the source regime, made a
  predicate of the candidate and the read rather than an attributed oracle.

The finite content is kernel-checked:

* candidate `1` (`0011`) is feasible: `feasible_genOf_one` proves
  `InformationFeasible (genOf 1) 2 {0,2}` (the reads at starts `0` and `2` cover
  the circle; read length `2` leaves no triple repeat);
* candidate `0` (`0001`) is **infeasible at every placement**: it has the
  length-`1` triple repeat at starts `{0,1,2}`, and
  `informationFeasible_two_no_tripleRepeat` shows that with read length `2` no
  copy of length `≥ 1` can be bridged (`bridgesCopy_length` forces `e + 2 ≤ 2`),
  so no `I_s`-feasible placement exists (`E_zero_00`);
* candidate `2` (`0101`) never spells `00` (`no_window_two_00`), so it is
  infeasible for the observed read `00` (`E_two_00`).

Consequences, stated to avoid over-claiming:

* `E` must be **computed from the model**; it cannot be an arbitrary oracle.
* Conditioning the prior **and** the likelihood on `E` is what
  `posteriorMass`/`predictiveMass` do (`jointMass = π g · p_g(r) · 1_{E(g,r)}`);
  the indicator is not dropped.
* This is a **bounded finite witness**, not the general source-level theorem:
  `E` is defined through the chosen orbit representatives (`genOf i = toGenome (rep i)`)
  and is not shown to descend to rotation orbits; the observation is a single
  observed read string rather than the full sampled read set. See §6.
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
oriented-window read pmf of `GenomeOrbitAdapter`, with the side event now given by
the source predicate `InformationFeasible` rather than an oracle.

Representation warnings carried over unchanged:

* oriented read strings (`GenomeOrbitAdapter`/`SourceFaithfulIs.window`) versus
  the reverse-complement-collapsed molecule representation (#260) are different
  observables with different likelihoods and are not identified here;
* realized read **start positions** (`SourceFaithfulIs.R : Finset (Fin S.len)`,
  the latent placements used by `InformationFeasible`) are different from the
  observed read **strings** consumed by the likelihood; the adapter's `Obs` is
  the read string, and its `E` existentially quantifies over the latent placement
  set, requiring only that the observed read is realized at one of its starts.

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
  therefore does not by itself produce the (A)-side collapse — the feasibility
  event `E` is what does.
* The general ordinary-ML classification (#255/#258/#259/#261) is untouched.

## 6. Open items (labelled, not claimed)

1. **Rotation descent of `E` — CLOSED.** `E` is stated through the chosen
   representatives (`genOf i = toGenome (rep i)`). The source predicate
   `InformationFeasible` is rotation invariant
   (`SourceFaithfulIs.informationFeasible_rotGenome`), so `E` descends to the
   orbit classes as `p` does; the orbit-level separation is
   `ConditionalVsMLGenomeAdapter271.separation_orbit`. See
   [`information-feasible-rotation-271.md`](information-feasible-rotation-271.md).
2. **Full read-set observation.** The adapter observes a single read string and
   existentially quantifies the latent placement. The source observes the whole
   sampled read set and weights placements; the source-faithful weighted-placement
   event mass is formalized abstractly in
   `AssemblyP1/ConditionalIdentifiability.PlacementModel`
   (`placement_posterior_certain`). Connecting the present finite witness to that
   placement-level mass, with `HistoricalCovers.HistoricalInformationFeasibleLiteral`
   as the event, is **open**.
3. **`E → B`.** No candidate-specific feasibility event implies ordinary ML
   recovery in general (`sep_truth_not_ml` refutes it on this model). A
   sufficient refinement would add an observation-side component `C(R)` that is
   itself sufficient for (B) on the fixed universe (candidates: the #255/#258
   classifications); this is a conjecture, not proved here.
4. **Orbit-size vs spelling prior.** The general distinction is #269
   `spellingPushforward_eq_uniform_iff_constant_orbitSize`; the adapter uses an
   orbit-class prior and does not assert specific orbit sizes.

## 7. Manuscript-safe wording (for #265/#268, non-competing)

> The abstract conditional-Bayes / ordinary-ML separation instantiates on the
> exact finite circular read model: taking the candidate universe to be rotation
> orbits, the observation model to be the normalized oriented-window read pmf,
> the prior to be uniform over orbit classes, and the side information to be the
> candidate-specific latent-start information-feasibility predicate
> (`∃` placement `T` with `InformationFeasible g T` realizing the observed read),
> there is a read at which the conditional posterior on the true orbit is one
> while ordinary maximum likelihood strictly prefers a wrong orbit; conversely,
> there is a read at which ordinary maximum likelihood uniquely selects the true
> orbit while the unconditional posterior is not certain. The side predicate is
> built from the source information-feasibility predicate `I_s` itself — not from
> an externally supplied truth-dependent oracle — though it is instantiated on
> the chosen orbit representatives with a single observed read string, so it is a
> bounded finite witness rather than the general source-level theorem. The
> historical same-length witnesses instantiate the ordinary-ML failure under
> their fixed count-vector objectives but do not carry the prior, normalized
> observation model, or feasibility event that the conditional layer requires.
