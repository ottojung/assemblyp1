# Uniform primitive-P2 separation and an explicit exponential exact-ML error bound (issue #281)

**Research status:** kernel-checked Lean theorem with an axiom audit. This is
the quantitative strengthening of `AssemblyP1.PrimitiveP2FiniteClass`: where
that module proved only that some uniform Hellinger gap `rho_* < 1` exists, this
module exhibits an explicit gap and rate that depend only on the read length
`L` and the alphabet size `q`.

## The statement

**Lean:** `AssemblyP1/PrimitiveP2UniformSeparation.lean`, audited in
`AssemblyP1/PrimitiveP2UniformSeparationAudit.lean`.

Fix a finite alphabet `alpha` with `q = |alpha|` and read length `L >= 2`, and
set `B = 2 * q^(L-1)`. Let `S` be a primitive oriented circular genome
satisfying `P2` at read length `L`, with `G_S = |S|`.

1. `readLaw_separation` — if the oriented uniform-start read laws of two
   genomes `S`, `D` differ, then some length-`L` word `w` satisfies
   `1/(G_S G_D) <= |p_S(w) - p_D(w)|`. The read law is a count divided by the
   genome length, so the difference is `(c_w G_D - c'_w G_S)/(G_S G_D)` and a
   nonzero integer numerator has absolute value at least one.
2. `abs_sub_le_two_abs_sqrt_sub` — the coordinate inequality
   `|p - q| <= 2 |sqrt p - sqrt q|` for `p, q` in `[0,1]`.
3. `one_sub_hellinger_ge_of_gap` — combining the coordinate inequality with
   the Hellinger identity `1 - rho = (1/2) sum (sqrt p - sqrt q)^2` gives
   `1 - rho >= 1/(8 (G_S G_D)^2)`.
4. `hellinger_le_of_length_bound` — if additionally `G_S, G_D <= B`, then
   `rho(p_S, p_D) <= 1 - 1/(8 B^4)`.
5. `primitiveP2_exponential_error_bound` — the exact iid maximum-likelihood
   error probability over the complete primitive-P2 non-rotational class is at
   most `N_C * exp(-n/(8 B^4))`.
6. `primitiveP2_ML_confidence_explicit` — `n >= 8 B^4 log(N_C/delta)` suffices
   for error at most `delta`.
7. `readLawFamily_card_le` — `N_C <= sum_{g=1}^{B} q^g`.

## What is reused, not re-proved

The finite-iid Hellinger union bound `eventProb_pairwise`,
`eventProb_wrong_le_card` and `circular_wrong_le_card`, the length bound
`primitive_P2_len_le`, the candidate families `nonRotationalCandidates` /
`primitiveP2Candidates`, and the structural separation
`equal_laws_imply_rotation_of_primitiveP2` are all imported from the merged
modules `FiniteReadRecovery`, `FiniteReadRecoveryGenome`,
`FiniteReadRecoveryP2Complete` and `PrimitiveP2FiniteClass`. No likelihood
argument, no population uniqueness theorem and no existing definition is
reproved or changed here.

## Scope and honest limits

* Competitor class: primitive-P2 admissible, oriented, exact iid reads. Not
  universal maximum likelihood over all genomes, and not the MB09
  product-binomial approximation.
* The constants are deliberately loose: `B` is exponential in `L` and `N_C` is
  enormous. This is a kernel-checked positive rate, not a tractability or
  efficiency claim.
* This is a frequentist uniform-separation guarantee for the exact multinomial
  likelihood, distinct from the Bayes-optimality rationale.
* The bound concerns the eventual rate and does not contradict the
  non-monotonicity of finite-sample success (see
  `docs/issue281-nonmonotonicity-witness.md`).

## Reproducing the checks

```
lake build --wfail AssemblyP1.PrimitiveP2UniformSeparation AssemblyP1.PrimitiveP2UniformSeparationAudit
lake env leanchecker AssemblyP1.PrimitiveP2UniformSeparation
lake env leanchecker AssemblyP1.PrimitiveP2UniformSeparationAudit
```

Axiom audit (`#print axioms` in the audit module): every endpoint depends only
on `propext`, `Classical.choice` and `Quot.sound`. No `axiom`, `sorry` or
`admit` is introduced.

## Non-vacuity

`separation_gap_strict_at_L2` records `1 - 1/(8 * 4^4) < 1`, i.e. the gap is a
genuine strict separation at `L = 2` over a two-letter alphabet; the candidate
class is nonempty by the witness in
`AssemblyP1/PrimitiveP2FiniteClassAudit.lean` (`1100` at `L = 2`).

## Provenance

New here: the cross-multiplied integer-denominator separation, the coordinate
square-root inequality, the explicit uniform gap, the explicit exponential
bound and threshold, and the class-size bound. Everything else predates this
work.
