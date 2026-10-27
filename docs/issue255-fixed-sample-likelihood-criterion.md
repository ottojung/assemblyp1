# Fixed-sample ML criterion: likelihood-ratio form (#255)

This note isolates the exact mathematical test for axis (A), separately from
the harder task of simplifying that test using genome or graph structure.
It is a bounded lemma, not a classification of any candidate universe.

## Finite categorical experiment

Let `Ω` be a finite set of oriented read strings (or, in a separate model,
reverse-complement molecule classes). Let `p_S` and `p_D` be the normalized
read-type probability vectors induced by truth `S` and one admissible
competitor `D`. For a fixed nonnegative integer count vector `x`, with
`n = Σ_i x_i`, exact multinomial likelihood is

`L(p;x) = n! / ∏_i x_i! · ∏_i p_i^(x_i)`.

For each candidate separately, the finite-ML comparison is exactly

`S` weakly beats `D` at `x` iff `∏ p_S(i)^(x_i) ≥ ∏ p_D(i)^(x_i)`.

The common multinomial coefficient cancels. Equivalently, in extended-real
log form, `Σ_{i:x_i>0} x_i log p_S(i) ≥ Σ_{i:x_i>0} x_i log p_D(i)`, with
`log 0 = -∞`; define the empty product as `1` (so at `n=0` every candidate
ties). Truth is a maximizer iff this inequality holds for every admissible
`D`. This is necessary and sufficient for fixed `x`, without assuming truth
support coverage, equal candidate length, or a particular graph realization.

The log form must retain the support convention: a zero probability at any
observed type gives likelihood zero; if both sides are zero, they tie rather
than producing a finite log-ratio. On the common positive observed support,
the comparison can also be written as the empirical cross-entropy/KL
projection comparison, but the product inequality is the unconditional form.

## What this does and does not identify

This criterion is objective-level and candidate-wise. Its candidate family
may be spelled circular genomes or a specified flow set, but `p_D` must be
the probability vector actually assigned by that model. In particular, it
does not identify MB09 §6.2 flow throughput with a spelled-genome spectrum,
settle whether the historical literal read-string `I_s` equals project
placement `I_s`, or ensure that `S` belongs to the candidate family.

For the exact multinomial, oriented strings and RC molecule classes are
different choices of `Ω`; the displayed argument applies to either only
after the corresponding normalized probability vectors are fixed. It also
does not transfer to the fixed-external-`N` product-binomial objective:
there the candidate-specific factors `(N-d_i)^(n-x_i)` remain and do not
cancel as a multinomial coefficient. Nor does it turn fixed-`x` (A) into
sample-uniform (B): (B) universally quantifies this comparison over its
admissible count vectors, and the admissible set must be stated precisely.

## Proof sketch

Substitute the multinomial formula for both likelihoods. Since `x` and hence
`n! / ∏ x_i!` are fixed independently of the candidate, cancel this common
nonnegative factor; the residual comparison is exactly the product
inequality. The equivalence with logs follows from monotonicity of `log` on
positive values, with zero cases handled separately by `log 0 = -∞`. Taking
the conjunction over the candidate set is precisely the definition of truth
being a weak maximizer. No asymptotic or population argument is used.

This elementary criterion gives a reliable starting point for fixed-sample
research, but provides no structural shortcut for deciding all inequalities
over a nontrivial genome/flow class. In particular, it closes no open
classification cell in #255.
