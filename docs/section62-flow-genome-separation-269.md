# §6.2 feasible-flow objective vs the source-faithful genome likelihood (#269)

Antonina #269's goal is to kernel-check the finite Bayes/MAP optimum for the
AssemblyP1 circular read model and to keep that model *distinct* from the MB09
surrogates.  The `AssemblyP1/GenomeOrbitAdapter.lean` docstring already stated in
prose that the uniformly sampled genomic-start model is

> "not the MB09 fixed-`N` product-binomial pseudo-likelihood and not the §6.2
> feasible-flow optimization".

The exact-iid-versus-product-binomial half is kernel-checked by
`AssemblyP1.GenomeOrbitAdapter.ExactVsSurrogate.exact_ne_productBinomial`.  This
note records the module that turns the **§6.2 feasible-flow** half into a
kernel-checked separation theorem.

## Artifact

`AssemblyP1/Section62FlowGenomeSeparation.lean` (+ its `AxiomAudit` companion
`AssemblyP1/Section62FlowGenomeSeparationAudit.lean`), with the independent exact
rational verifier `scripts/verify_269_flow_genome_separation.py`.

It **reuses**, and does not redefine, the merged
`AssemblyP1/Section62FlowCountVectorAdapter`:

| Reused declaration | Role here |
|---|---|
| `throughputVec`, `throughputVec_congr` | the §6.2 objective can only depend on the throughput vector (`flow_objective_factors_throughput`) |
| `Maximal`, `maximal_image_iff` | §6.2 ML-maximality over the feasible-flow set is maximality over the throughput image (`flow_maximality_is_throughput_property`) |
| `Spelling.visits` (`AssemblyP1.Section62Flow`), `AssemblyP1.Section62SpelledFlowAdapter.throughput_eq_visits` | a spelled genome's §6.2 throughput is its molecule-class visit vector (`classCount_eq_visits`) |

## The separation

The §6.2 graph of MB09 §4.1 represents each read *molecule* once: the vertices are
reverse-complement **molecule classes**, so the §6.2 throughput is an
RC-invariant class count.  The source-faithful read model of
`AssemblyP1/GenomeOrbitAdapter.lean` is **oriented**: the read pmf
`p_S(w) = multiplicity_S(w) / |G|` is indexed by oriented length-`L` windows.

The witness is the reverse-complement pair of length-`2` circular binary genomes

```text
S0 = 00        (windows: 00, 00)
S1 = 11        (windows: 11, 11)
```

* `classCount_S0_eq_S1` — both induce the *same* §6.2 molecule-class visit
  vector, `{00,11} ↦ 2` (kernel-checked by `decide`);
* `likelihood_S0 : exactLikelihood 1 S0 x0 = 1` and
  `likelihood_S1 : exactLikelihood 1 S1 x0 = 0` for the one-read sample `(00)`;
* `likelihood_S0_ne_S1` — the exact oriented likelihoods differ.

Hence `exactLikelihood_not_factors_throughput`:

```text
¬ ∃ φ, ∀ S, exactLikelihood 1 S x0 = φ (classCount S),
```

i.e. **no function of the §6.2 throughput can equal the exact oriented
likelihood**.  Combined with `flow_objective_factors_throughput` /
`flow_maximality_is_throughput_property`, no §6.2 feasible-flow objective equals
the source-faithful genome likelihood
(`section62_flow_objective_ne_genome_likelihood`).

## Theorem names (all kernel-checked, no `sorry`/`admit`/new axiom/`native_decide`)

- `AssemblyP1.Section62FlowGenomeSeparation.flow_objective_factors_throughput`
- `AssemblyP1.Section62FlowGenomeSeparation.flow_maximality_is_throughput_property`
- `AssemblyP1.Section62FlowGenomeSeparation.classCount_eq_sum`
- `AssemblyP1.Section62FlowGenomeSeparation.classCount_eq_visits`
- `AssemblyP1.Section62FlowGenomeSeparation.likelihood_S0`
- `AssemblyP1.Section62FlowGenomeSeparation.likelihood_S1`
- `AssemblyP1.Section62FlowGenomeSeparation.likelihood_S0_ne_S1`
- `AssemblyP1.Section62FlowGenomeSeparation.exactLikelihood_not_factors_throughput`
- `AssemblyP1.Section62FlowGenomeSeparation.no_flow_objective_eq_likelihood`
- `AssemblyP1.Section62FlowGenomeSeparation.section62_flow_objective_ne_genome_likelihood`

`#print axioms` reports `[propext, Classical.choice, Quot.sound]` (the first two
reuses depend on no axioms at all).

## Reproduce

```sh
lake build AssemblyP1.Section62FlowGenomeSeparation --wfail
lake env leanchecker AssemblyP1.Section62FlowGenomeSeparation
python3 scripts/verify_269_flow_genome_separation.py
```

## What is *not* claimed

- Not the §6.1 product-binomial versus exact-iid distinction (that is
  `AssemblyP1.GenomeOrbitAdapter.ExactVsSurrogate.exact_ne_productBinomial`).
- Not the throughput-image / spelled-circuit classification of #261
  (`AssemblyP1.Section62SpelledFlowImageRefutation`), which is orthogonal.
- Not a claim that a genome and its reverse complement are
  information-theoretically indistinguishable by every experiment; only that the
  exact oriented uniform-start read model distinguishes them while the §6.2
  molecule-class throughput does not.
- No global "ML is best algorithm" claim; only the specified fixed observation
  model and prior-averaged accuracy.
