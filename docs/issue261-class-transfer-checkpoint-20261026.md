# Issue #261 class-transfer checkpoint (2026-10-26)

This checkpoint reconciles the existing #261 criteria by candidate class. It
does not claim a general maximality theorem for the source-faithful §6.2 model.

## Candidate-set transfer rules

Let `C` be a candidate class and `D ⊆ C` a subclass, with the same truth,
observation, score, and equivalence convention. If the truth maximizes over
`C`, it maximizes over `D`. Conversely, a strict defeating candidate in `D`
also defeats it in `C`. Neither implication permits transferring a positive
maximality result from `D` to `C`. For a score that factors through a map
`Θ : C → V`, maximality on `C` is equivalent to maximality on the image
`Θ(C)`; replacing that image by another set requires an independently proved
image equality or inclusion in the appropriate direction. These are the
already kernel-checked transfer lemmas in
`Section62FlowCountVectorAdapter` / `Section62SpelledFlowMaximality`, not new
source-model assertions.

## Scope reconciliation

| Candidates | Objective/length | Current conclusion | Transfer boundary |
|---|---|---|---|
| Full count vectors | Exact §6.1 multinomial, variable candidate `N` | Density iff in `varLengthCriterion`; under the added genome constraint `sum d=N`, proportional spectra result | Count-vector result only; does not identify the §6.2 feasible-flow image |
| Full count vectors | §6.1 product-binomial, fixed external `N` | q-factorization and fixed-support samplewise criteria, including fixed-`n` extreme iff, are kernel-checked | Requires all molecule coordinates, including unobserved classes; not directly a flow theorem |
| Integer feasible flows | Fixed-`N` product-binomial | ML reduces exactly to the throughput image; a finite non-spelled witness disproves general spelling-only sufficiency | Throughput image is not characterized; source-faithful reduction, terminals and probability bounds remain open |
| Half-integral flows | Fixed-`N` product-binomial | Exact `AAATT` witness has strict relaxation improvement | Finite flow-domain obstruction only; it does not imply a gap for spelled circuits or genomes |
| Half-integral feasible flows | Exact variable-length multinomial | Doubling preserves normalized throughput and exact score, so no half-integral strict improvement for this relaxation | Depends on homogeneous feasible clauses/objective; not transferrable to fixed-`N` binomial |
| Spelled circuits | Fixed-`N` binomial | Spelled flow inclusion and one strict same-length witness are available | Inclusion transfers a spelled counterexample upward, but spelled maximality does not certify all flows |
| Circular genomes, oriented reads | Exact iid uniform-start likelihood | `AAATT` vs `AAATA`: truth strictly beats this competitor (ratio 0) | Pair only; not a global maximum claim |
| Circular genomes, RC-molecule classes | Exact iid uniform-start likelihood | Same pair ties after quotient (ratio 1) | Pair only; this changes pairwise verdict and does not settle maximality |

The last two rows are documented and independently rational-checked in
`issue261-rc-orientation-class-20261026.md`. The associated finite witness has
`L=3`, `o_min=1`, truth admitted, `N=5`, and observed reads `AAA,AAA,AAT,ATT`.
It is not an arbitrary-flow witness. The fixed-external-`N` binomial statements
elsewhere in this repository must not be substituted for this exact iid
calculation.

## Explicit remaining open claims

1. Characterize the integer §6.2 throughput image under the source-faithful
   spelling-preserving transitive reduction and signed bidirected incidences.
2. Reconcile the complete genome molecule spectrum (including unobserved types)
   with observed-vertex flow throughput; specify the binomial candidate domain
   where every coordinate is at most external `N`.
3. Resolve orientation/RC semantics for the whole candidate set, not just the
   AAATT pair, and prove any orientation-quotient candidate-set relationship
   before transferring maximality claims.
4. Obtain a general necessary-and-sufficient criterion for each feasible-flow,
   spelled-circuit, and circular-genome class, or retain each as OPEN with
   source-faithful counterexamples/partial implications. Arbitrary-overlap
   sample realizability and the interaction of transitive reduction with ML
   remain unresolved.

The previous RC witness and its verifier were rerun for this checkpoint; see
the terminal handoff for validation. No Lean code was changed, so no claim here
is presented as a new kernel-checked result.
