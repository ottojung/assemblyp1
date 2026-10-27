# Issue #259 realizability frontier checkpoint

This checkpoint isolates what the general full-class theorem does and does not
imply for realizable circular spectra. The objective throughout is the MB09
§6.1 fixed-external-`N` product-binomial surrogate, not the exact multinomial
objective of #256 or the §6.2 bidirected-flow objective of #260/#261.

For a fixed finite read universe `E`, a candidate spectrum `B : E → ℕ` of
length `N` has effective weights

```
q_e(B) = B_e ∏_{j ≠ e}(N - B_j),   F_B(x) = ∏_e q_e(B)^(x_e).
```

All `j ∈ E`, including zero-count coordinates, occur in the first product;
`q_e=0` at boundary probabilities is interpreted by the usual natural-power
convention. The omitted binomial coefficients and `N^(-n|E|)` are candidate
independent. Candidate lengths are equal, and `N` is fixed externally.

## A rigorous obstruction, but not a complete answer

The already kernel-checked positive-vector lemma in
`ProductBinomialRigidityNecessity` says that for distinct positive vectors `A`
and `B` with the same total `N`, their effective weights cannot satisfy
`q_e(B) ≤ q_e(A)` for every `e`. Its proof uses the exact identity

```
Σ_e B_e log(q_e(B)/q_e(A))
 = Σ_e B_e log(B_e/A_e)
 + Σ_e (N-B_e) log((N-B_e)/(N-A_e)),
```

whose right side is a sum of nonnegative divergence terms. Therefore, whenever
`A,B` are distinct positive *realizable* same-support spectra, some effective
weight of `B` strictly exceeds that of `A`. This establishes a useful
intermediate step without transferring the exact-multinomial criterion.

It does **not** by itself provide a realizable observation `x` that favors `B`:
the coordinatewise excess need not dominate the negative log-ratio
contributions at other true-supported coordinates, and a realizable spectrum
must obey the balance constraints of the read graph. The covered-sample iff
can choose counts on the full ambient coordinate lattice; that construction
does not assert that those counts are a same-length circular spectrum. This is
the precise gap between the general-vector necessity theorem and the desired
realizable rigidity theorem.

## Check performed in this pass

Inspected the existing kernel-checked full-class theorem and the positive
effective-weight lemma, including their boundary conventions and ambient
coverage hypotheses. They prove: rigidity is necessary when the candidate
class is restricted to positive same-support circulations and observations
range over all covered count vectors; full-class maximality over arbitrary
count vectors has the separate `{0,1}`/single-support characterization. Neither
statement quantifies only over realizable circular observations. Thus neither
settles whether a non-rigid truth is beaten by a realizable complete-support
observation.

The smallest existing new-support example `(2,1,1,0)` versus `(1,1,1,1)` is
about failure of rigidity sufficiency when competitors can add support; it is
not a non-rigid truth counterexample and is not used as one here. No new
realizable counterexample or proof has been established in this checkpoint.
The outstanding productive route is to restrict the log-ratio comparison to
the integer circulation cone of observations and determine whether its
generators force a positive pairing for every nonzero same-support circulation
direction, or else exhibit the smallest pair where they do not.

## Scope

This note concerns only issue #259's realizable-observation question. It does
not alter the general bidirected-flow scope of #260/#261. It records a precise
obstruction to a tempting proof transfer, not a theorem that graph rigidity is
or is not necessary under realizable observations.
