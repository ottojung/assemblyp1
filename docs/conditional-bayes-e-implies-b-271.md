# When does conditional recovery imply ordinary ML recovery? (#271 goal 5)

_Status: abstract finite-model theorem, kernel-checked in
`AssemblyP1/ConditionalBayesEImpliesB271.lean` and audited in
`AxiomAudit271.lean` (only `propext`, `Classical.choice`, `Quot.sound`). This is
a research comparison note; it is **not** a source-faithful genome witness._

## 1. The question

Issue #271 compares two finite-recovery guarantees in one generative model:

* **(A)** conditional-Bayes recovery: given the observation `x` *and* side
  information `E`, the posterior is a point mass on the true candidate;
* **(B)** ordinary R-only maximum-likelihood recovery: the truth is a maximizer
  of the likelihood (and, separately, the *unique* maximizer).

The merged `AssemblyP1/ConditionalVsOrdinaryMLSeparation` module exhibits the
unrestricted separation `A ∧ ¬B` on a two-candidate toy (`Θ = {A, B}`,
`P_A(0) = 1/4`, `P_B(0) = 3/4`, truth-dependent `E`). Goal 5 asks which
assumption refinement on the side information repairs the implication `E → B`.

## 2. The refinement: ML-soundness

A sufficient refinement is **ML-soundness** of `E`:

```
MLSound p E  :=  ∀ h x, E h x → MLMax p h x,
MLMax  p h x :=  ∀ h', p h' x ≤ p h x.
```

`E` is ML-sound when it can only ever hold on a candidate that the ordinary
likelihood already admits as a maximizer.

* **`condCertain_imp_MLMax_of_MLsound`** — *the refinement that establishes
  `E → B`.* If `E` is ML-sound, then conditional certainty on `g` implies
  `MLMax p g x`. The only ingredient is `condCertain_imp_E`: a posterior of `1`
  forces `E g x` (no positivity or normalization hypothesis is needed, because
  `PosteriorE = 1` forces the predictive mass to be nonzero and hence
  `JointE g x ≠ 0`).
* **`not_MLsound_of_witness`** — *the refutation.* If `E g x` holds while `g`
  is not an ML maximizer, `E` is not ML-sound. The merged toy's `sideInfo` is
  such a witness (`toy_sideInfo_not_MLsound`), and so is the merged genome
  adapter's latent-start feasibility predicate (`genome_E_not_MLsound`). Their
  failure of ML-soundness is exactly why they achieve `A ∧ ¬B`.
* **`condCertain_EML_iff_unique`** — *the boundary case `E = MLMax`.* With
  `EML p h x := MLMax p h x`, and under positive prior and positive likelihood,
  conditional certainty is equivalent to `g` being the unique ordinary ML
  maximizer. Choosing `E` to be the maximizer certificate makes `A` and `B`
  coincide; the toy's truth-dependent `E` is not `EML`, which is why it does
  not.

The module also proves the general support-collapse characterization
`condCertain_iff` for an arbitrary finite candidate type `Θ`, generalizing
`ConditionalVsOrdinaryMLSeparation.condPosterior_one_imp` from two candidates.

## 3. What this says about "knowing the truth satisfies `F`"

Supplying "the truth satisfies `F`" as side information is **not** the same as
running ordinary ML over `F`-qualified candidates. ML-soundness of the supplied
`E` is *sufficient* for the implication `E → B` (the module does not claim
necessity). The implication can fail when `E` is not ML-sound: the toy's and the
genome adapter's `E` certify the truth even where the ordinary likelihood rejects
it. In other words, an arbitrary side-information promise can make the posterior
certain about a candidate the unconditional likelihood strictly disprefers, while
an ML-sound promise converts conditional certainty into ordinary ML recovery.

## 4. Relation to the source-faithful genome adapter

The merged genome adapter (`docs/conditional-vs-ml-genome-adapter-271.md`)
instantiates (A) with the candidate-specific latent-start information-feasibility
predicate `E i r := ∃ T, (∃ s ∈ T, window (genOf i) 2 s = r) ∧
InformationFeasible (genOf i) 2 T`. At read `00` that `E` holds on the truth
orbit `1` (`E_one_00`), which the adapter proves is not an ordinary ML maximizer
there (`sep_truth_not_ml`, `1/4 < 1/2`). Hence `genome_E_not_MLsound`: the
source-faithful adapter's `E` is not ML-sound, and the general refinement
`condCertain_imp_MLMax_of_MLsound` correctly does not apply to it. This is a
consistency check between the abstract goal-5 classification and the
source-faithful witness, not a new genome-level theorem.

## 5. Manuscript-safe wording (for #265/#268, non-competing)

> Conditional-Bayes certainty under externally supplied side information is
> guaranteed to imply ordinary maximum-likelihood recovery when that side
> information is *ML-sound*, i.e. it can only certify candidates that the
> ordinary likelihood already maximizes. If the side information can certify a
> candidate the ordinary likelihood rejects, the two guarantees can separate: the
> posterior can be a point mass on a candidate that is not a maximum-likelihood
> maximizer. In the source-faithful finite circular read model the
> candidate-specific latent-start information-feasibility predicate is not
> ML-sound, which is why the conditional posterior can be certain on the true
> orbit while ordinary maximum likelihood strictly prefers a wrong orbit.

## 6. Open items

* The refinement is stated for the abstract finite model. A source-faithful
  statement that a *specific* model-internal side predicate is ML-sound (hence
  yields `E → B`) is open; the two known source-faithful predicates are not.
* Maximizer vs unique maximizer: `condCertain_EML_iff_unique` treats the unique
  form under positivity; the tied-maximizer boundary is covered by the merged
  `ConditionalVsOrdinaryMLBoundary271`.
