# Realizable sample-uniform MB09 maximality: exact finite criterion (#259)

This note records the exact finite criterion for one specific observation
family. It does not classify that criterion by graph rigidity.

Fix alphabet `Σ`, read length `L`, universe `U=Σ^L`, circular candidate length
`G≥L`, and external normalization `N=G`. For each circular word `g`, let
`d_g(i)` count its circular `L`-windows equal to `i`, and let `C_G` be the set
of distinct spectra. The truth `A` belongs to `C_G`. Observations are restricted
to `X(A)={x∈C_G : x_i>0 for every i∈supp(A)}`; thus `n=∑x=G`. This does not
cover other sample sizes.

The MB09 §6.1 approximation is a product of binomial marginals, not the exact
joint multinomial. Removing candidate-independent factors gives

```
F_B(x)=∏_{i∈U} q_i(B)^x_i,
q_i(B)=B_i ∏_{j∈U,j≠i}(N-B_j).
```

All universe coordinates remain in the failure factors, including zero-count
coordinates; the probability boundaries follow `0^0=1`, `0^k=0` for `k>0`.
By the definition of `X(A)`, truth uniformly maximizes there iff for every
`B∈C_G` and every `x∈X(A)`, `F_B(x)≤F_A(x)`. If `q_i(B)=0` for any true-support
coordinate, its score is zero on all such observations. Otherwise the
competitor comparison is equivalently
`∑_{i∈supp(A)} x_i log(q_i(B)/q_i(A))≤0` for each such `x`.
This is an exact finite test, not a structural theorem.

## Structural question and scope matrix

The test does not establish that non-rigidity forces a realizable observation
that beats truth: the observation family is restricted to circular spectra of
length `G`, and competitor weights retain all universe failure factors.

| Dimension | Fixed by this criterion | Still open |
|---|---|---|
| Objective | MB09 §6.1 fixed-external-`N` product-binomial surrogate | Exact multinomial and §6.2 flows are distinct |
| Candidate length | Same circular length `G≥L`; `N=G` | Other normalization/length interpretations |
| Observation support | Complete truth support; competitors may add support | Simplification across support patterns |
| Sample size | `n=G`, and `x∈C_G` | Other `n`; general `G,L,Σ` structural result |
| Boundaries | Exact integer product, including zero and unit probabilities | — |
| Rigidity | No implication follows from this criterion | Necessity or a smallest exact counterexample for this realizable family |

This finite criterion and its scope are not closure of issue #259.
