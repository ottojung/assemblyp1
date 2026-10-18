# W1/W2 reverse-complement molecules versus oriented read strings (issue #271, goal 3)

_Status: research comparison note. The representation determination is
Lean kernel-checked in `AssemblyP1/W1W2RcOrientedRepresentation271.lean`
(audited in `AxiomAudit271.lean`; `leanchecker` clean). It reuses the merged
`AssemblyP1/W1W2SeparationCompatibility.lean` and does not fork the #255/#258/
#259/#261 classification._

## 1. The exact question

Issue #271 goal 3 asks whether the existing historical W1/W2
**reverse-complement-collapsed** cases instantiate the conditional-Bayes `E`
guarantee (A) versus ordinary R-only maximum-likelihood recovery (B) under ONE
*exactly shared observable data model* — same candidate universe, same prior,
same read representation, same likelihood objective — and to pay close attention
to the W1/W2 reverse-complement-collapsed likelihood versus the oriented
Not-So-Greedy read strings.

## 2. Determination: no, for two independent reasons

**Representation mismatch (kernel-checked here).** The historical W1/W2
witnesses reused by `W1W2SeparationCompatibility` — `AAATAT` vs `AAAAAT`
(`SameLengthSection62Counterexample`) and `ATATACAC` vs `ATACACAC`
(`PerOccurrenceSameLengthCounterexample`) — are **reverse-complement molecule**
witnesses, exactly as the paper classifies them (Theorem `thm:cex-historical-W1`
/ `thm:cex-historical-W2`; Remark `rem:historical-distinctions`(b)). Their
observable is the molecule-class count vector `obs : Fin 8 → Nat` (resp.
`Fin 64 → Nat`), obtained by collapsing oriented length-`3` windows through the
molecule class `cls`. That collapse is **not injective**: a read and its reverse
complement share a class, and so do distinct oriented reads (`ATA`/`TAT`). Hence
the molecule-class count is a *strict quotient* of the oriented read-string
observable (`SourceFaithfulIs.Genome.window`) on which the Not-So-Greedy /
Shomorony read model is built. Any likelihood that is a function of the
molecule-class count — the W1/W2 `lik` and `exactLik` — is therefore
reverse-complement **invariant**, while the oriented observable is not. The two
are different observable representations and cannot be substituted for one
another inside a single shared observable data model without either discarding
the oriented distinctions NSG uses or replacing the W1/W2 likelihood with a
different (RC-noninvariant) one.

**Missing conditional layer (reused).** The W1/W2 model carries no candidate
prior and no candidate-specific side event `E`, so the conditional posterior
`P(g | obs, E) ∝ π g · P(obs | g) · 1_{E(g,obs)}` of (A) is not defined there.
The merged `W1W2SeparationCompatibility` kernel-checks only the (B)-side failure
under the shared fixed count-vector objectives. This note does not fork it.

Consequently the existing W1/W2 reverse-complement-collapsed cases do **not**
instantiate the full (A)-versus-(B) separation under one shared model, and no
shared-model separation can be manufactured from them by silently identifying
their observable with the oriented NSG read-string observable.

## 3. Kernel-checked evidence

All in `AssemblyP1/W1W2RcOrientedRepresentation271.lean`:

* `rc_involutive` — the implemented reverse complement `rc` is an involution.
* `cls_rc` — the molecule class is reverse-complement invariant, `cls (rc w) = cls w`.
* `cls_not_injective` and `exists_rc_pair_same_class` — the collapse is
  non-injective; the distinct reads `ATA`, `TAT` share a class.
* `window2_ne_window3`, `window3_eq_rc_window2`, `window_cls_eq` — on the W1
  truth `AAATAT` the distinct oriented windows at starts `2` and `3` (`ATA`
  versus `TAT = rc ATA`) collapse to one molecule class.
* `molCount_map_rc` — the molecule-class count of a read list is unchanged when
  every read is replaced by its reverse complement.
* `obs_eq_molCount` — the W1 observed vector `obs` is exactly the molecule-class
  count of the oriented windows at the realized starts.
* `orientedReads_ne_rc`, `molCount_orientedReadsRc_eq`, `lik_rc_blind` — the
  oriented read list and its reverse-complement image are different oriented
  observations with the same molecule counts, and the W1 likelihood is unchanged.
* `rc_vs_oriented_verdict` — the packaged statement.

The axiom audit (`AxiomAudit271.lean`) reports only the Mathlib foundations
`propext`, `Classical.choice`, `Quot.sound`; there is no `sorry`/`admit`/`axiom`/
`native_decide`, and `lake env leanchecker AssemblyP1.W1W2RcOrientedRepresentation271`
is clean.

## 4. Why this is not a contradiction

No contradiction is manufactured between the Not-So-Greedy oriented guarantee and
the W1/W2 molecule likelihood failure. They are different observables — oriented
strings versus reverse-complement molecule classes — exactly as the paper's
Remark `rem:historical-distinctions`(b) and Proposition `prop:historical-source`
require. The W1/W2 (B)-side failure is a statement about the molecule observable
only, and must not be read as a statement about the oriented NSG model.

## 5. The feasibility-predicate axis also differs

The W1/W2 witnesses satisfy the historical matched-string predicate
`I_s^match` (`HistoricalInformationFeasible`; see
`SameLengthSection62Counterexample.historical_information_feasible`), whereas the
merged #271 genome adapter conditions on the placement-based latent-start
`SourceFaithfulIs.InformationFeasible`. The two predicates are incomparable
(paper Proposition `prop:historical-source`; kernel-checked instances in
`AssemblyP1/AcgtWitness211.lean` and `AssemblyP1/HistoricalCovers.lean`). So even
the `E`-side objects are not shared between the two models.

## 6. Relation to the merged #271 modules

* `ConditionalVsOrdinaryMLSeparation` / `ConditionalVsOrdinaryMLBoundary271` —
  the abstract (A)/(B) boundary and separations; unchanged.
* `ConditionalBayesEImpliesB271` — the `E → B` refinement (ML-soundness) and its
  refutation; unchanged. The W1/W2 molecule model supplies no `E`, so this
  framework is not instantiated there.
* `ConditionalVsMLGenomeAdapter271` — the oriented read-model adapter with a
  normalized per-candidate pmf, orbit prior, and candidate-specific latent-start
  `E`. It is a *separate* adapter on the oriented observable, not a
  reconciliation with the molecule W1/W2 model; keeping it open is allowed by
  the issue.
* `W1W2SeparationCompatibility` — the (B)-side reuse. Its representation warning
  is corrected to the molecule reading in this PR.

## 7. Manuscript-safe wording (for #265/#268, non-competing)

> The historical same-length witnesses `W_1` and `W_2` are reverse-complement
> molecule witnesses: their observable is the molecule-class count vector,
> obtained by collapsing oriented windows through the reverse-complement class.
> That collapse is not injective, so the molecule observable is a strict quotient
> of the oriented read-string observable on which the Not-So-Greedy model is
> built, and the witness likelihood is reverse-complement invariant. The
> witnesses therefore instantiate the ordinary-ML failure under their fixed
> count-vector objectives, but they do not instantiate the conditional-Bayes
> layer (no candidate prior, no candidate-specific side event) and they must not
> be identified with the oriented read-string model; a conditional-versus-ML
> separation on the oriented model is supplied separately by a dedicated adapter
> and is not a statement about the molecule witnesses.

## 8. Open items

* The genome-level oriented adapter remains a bounded finite witness
  (`ConditionalVsMLGenomeAdapter271`); a source-level reconciliation is open.
* Rotation descent of the adapter's `E`, and the full sampled-read-set
  observation, remain open as recorded in
  `docs/conditional-vs-ml-genome-adapter-271.md`.
