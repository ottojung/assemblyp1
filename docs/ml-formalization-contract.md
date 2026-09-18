# Maximum-likelihood formalization contract

_Status: modeling contract for issue #9, derived from the locked literature ground truth and the source-recovery packets #5 and #7. This document organizes the formalization; it does not resolve source ambiguities by fiat._

## Authority and dependency boundary

The authoritative literature ground truth is the locked `docs/literature-status.md` at commit `99c158c59aa374ea3898ec4658b6eec52fbad342`, as required by `$id-4318762045197832`.

The integrated source notes from PR #6 and PR #8 sharpen that ground truth:

- `docs/source-notes/medvedev-brudno-candidate-class.md` distinguishes the exact Medvedev–Brudno likelihood, its fixed-length approximation, and the Section 6.2 flow feasible set.
- `docs/source-notes/shomorony-ml-reference.md` records that the accepted Shomorony et al. (2016) text does not select among those levels and does not resolve the competitor-length or tie-semantics questions.

This contract remains subordinate to the locked literature ground truth; later source work must be reconciled proposition-by-proposition rather than treating summaries as authority.

## Epistemic classification

### Source facts fixed by the locked ground truth

The Shomorony et al. exposition uses a circular true sequence `s` of length `G`, error-free reads of common length `L`, and independent uniform sampling from the `G` circular start positions. The observed sequencing data must retain read multiplicity for likelihood calculations.

For a circular Medvedev–Brudno candidate genome `D`, let `N(D)` be its length, `d_i` the number of occurrences of read/k-molecule type `i`, and `x_i` its observed count among `n` reads. The exact global read-count likelihood is multinomial:

```text
L_exact(D | x) = n! / (∏ᵢ xᵢ!) · ∏ᵢ (dᵢ / N(D)) ^ xᵢ.
```

Medvedev–Brudno then introduce a separable/binomial approximation for tractable convex flow optimization. In that approximation the candidate-dependent `N(D)` is replaced by a fixed or externally estimated genome length. This approximation is not definitionally the exact multinomial objective.

Shomorony et al.'s 2016 sentence does not specify whether “the maximum-likelihood sequence” means the exact objective or the approximation, and it does not disambiguate “truth is a maximizer” from “every maximizer is the truth up to the intended genome equivalence.”

### Modeling organization justified by those facts

The Lean development should share source-stable primitives and keep source-ambiguous choices at the boundary. In particular, it should not encode the whole published question as one concrete `AssemblyModel` until doing so would cease to hide a source fork.

This organization is a repository modeling decision, not a claim that either paper presents its definitions in this software architecture.

## Shared formal substrate

The following concepts can be developed without selecting the unresolved ML variant:

1. **Circular genome/string representation.** It must support the true sequence and arbitrary circular candidates and expose intrinsic candidate length.
2. **Circular windows / read types.** A length-`L` read type is determined by a circular window in a candidate genome.
3. **Occurrence multiplicity.** `occurs(D, r)` counts candidate start positions whose length-`L` circular window equals read type `r`.
4. **Observed read multiplicity.** The observation records counts `x(r)` (or an equivalent multiset/list preserving repeated reads), not merely the set of distinct read strings.
5. **True sequencing realization.** Bridging predicates may need latent start positions in the true genome. These positions are not part of the likelihood estimator's observed count vector and must not leak into candidate scoring.
6. **Genome equivalence as a parameter until reconciled.** Cyclic shift is required by the Shomorony circular exposition; any additional identification such as reverse complement must not be silently added from a different source convention.

The likelihood layer should consume only the observable read multiplicities plus a candidate genome. Bridging may consume the richer true sequencing realization. Keeping those types distinct prevents the likelihood objective from receiving latent placement information.

## Likelihood variants that must remain distinct

### Variant E: exact multinomial objective

For a candidate `D`, the formal definition should use the candidate's intrinsic `N(D)` in every read-type probability `occurs(D,r) / N(D)` and the exact multinomial count likelihood.

For maximum-likelihood *ordering*, the observation-only multinomial coefficient can be factored out by a proved lemma. It must not simply be deleted from a definition advertised as the exact probability without documenting that distinction.

No fixed competitor length belongs in Variant E unless a separately named restriction is imposed. Such a restriction would define a subproblem, not follow automatically from the fact that the true Shomorony genome has known length `G`.

### Variant A: separable/binomial approximation

The approximation should be a separately named objective whose length parameter is external/fixed. It must not reuse the exact-likelihood name or theorem merely because the 2009 paper uses it to approximate the same statistical motivation.

Any theorem comparing Variant A to Variant E needs explicit hypotheses and proof. The formalization must not treat their maximizers as definitionally equal.

### Variant F: Section 6.2 flow optimization

The read-derived overlap-graph flow feasible set is an algorithmic search space with its own constraints. It is not, without a correspondence theorem, the candidate universe quantified over by Variant E.

If formalized, Variant F should therefore expose both:

- its feasible-flow predicate/search space; and
- the interpretation from a flow to an assembly object.

A result proved only over feasible flows must not be presented as quantification over every circular candidate genome.

## Conclusion variants that must remain distinct

For each likelihood/candidate-universe variant under investigation, retain at least these two propositions:

```text
truthIsML:
  ∀ candidate, likelihood candidate reads ≤ likelihood truth reads
```

and

```text
mlIsTruthUpToEquiv:
  truthIsML ∧
  ∀ candidate,
    likelihood candidate reads = likelihood truth reads → candidate ≈ truth
```

The existing abstract `AssemblyModel.IsMaximumLikelihood` and `AssemblyModel.IsUniqueMaximumLikelihoodUpToEquiv` already reflect this logical distinction. Until source evidence resolves the English singular “the maximum-likelihood sequence is the true sequence,” neither proposition may be deleted or silently designated as the sole published conjecture.

## Candidate-universe discipline

Every concrete theorem declaration derived from the open question must make its competitor universe recoverable from its type. Examples of materially different universes include:

- all nonempty circular candidates for which the read model is defined;
- candidates restricted to the true length `G`;
- candidates represented by a particular overlap graph or flow feasible set.

These are not interchangeable. If a restricted universe is useful for an intermediate theorem, its restriction belongs in the theorem name/type and its epistemic status is a restricted mathematical result, not a settlement of the source ambiguity.

## Constraints for subsequent Lean work

1. Do not replace `AssemblyModel.likelihood` by one concrete function and then reuse the generic open-problem theorem name as though the literature selected it.
2. Introduce source-stable primitives first, with elementary invariance/counting lemmas independently checkable against hand examples.
3. Give exact, approximate, and flow objectives separate declarations/namespaces or structures.
4. Keep candidate length explicit in types/definitions wherever it changes the objective.
5. Keep observed read multiplicity separate from latent true read placements.
6. Parameterize or separately name the genome-equivalence convention until the source reconciliation is strong enough to select one.
7. State maximizer-only and uniqueness-up-to-equivalence implications separately.
8. A theorem about a restricted candidate class, fixed length, approximate objective, or flow feasible set must say so in its declaration and documentation.
9. No source ambiguity may be converted into an `axiom`, hidden hypothesis, or undocumented definitional choice.
10. When a concrete variant becomes formalized, add hand-checkable examples and a prose correspondence note before treating it as a faithful transcription.

## What this contract does not decide

This document intentionally does not decide:

- which ML variant Shomorony et al. intended;
- whether competitors must have length `G`;
- whether the published conclusion is existence/maximality or uniqueness;
- whether reverse-complement equivalence belongs in the final theorem;
- which proof or counterexample strategy should be attempted.

Those are unresolved source/model or research questions. Preserving them as visible forks is part of correctness, not unfinished bookkeeping.
