# Counterexample to unrestricted-length exact multinomial ML

## Scope and epistemic status

This note records a finite counterexample to the repository's **unrestricted-length exact multinomial Variant E**. It does not settle the broader question posed by Shomorony et al., because that paper refers to the Medvedev–Brudno maximum-likelihood formulation without resolving the repository's source-documented fork between the literal exact objective and the later fixed-length approximation/flow formulation.

The arithmetic, candidate admissibility for the literal exact objective, and repeat/bridging hypotheses have been independently checked. The finite claim is mature enough for a small Phase-B formal verification. Nothing here claims a result for fixed-length exact ML, the separable approximation, or flow optimization.

## Instance

Take the true circular genome

`S = ACGT`

of length `G = 4`, read length `L = 2`, and three realized reads with latent starts `0, 0, 2`. The observed multiset is therefore

`R = {AC, AC, GT}`.

Take the competing circular sequence

`D = ACACGT`

of length 6.

## Coverage and repeat hypotheses

The read `AC` starting at 0 covers true positions 0 and 1, while `GT` starting at 2 covers positions 2 and 3. Hence the realized reads cover the entire true circular genome.

Bresler, Bresler & Tse (2013), in the discussion around Theorem 1, define a repeat as the same length-`ℓ` subsequence appearing at two distinct genome positions with the stated maximality conditions; triple repeats analogously use three positions, and interleaving is defined from two repeat pairs. A repeat copy is bridged when a read covers bases on both sides of it. Their MultiBridging sufficient conditions require all interleaved repeats to be bridged, all triple repeats to be all-bridged, and sequence coverage.

For `ACGT`, the four circular starts have pairwise distinct first symbols. Consequently no positive-length circular subsequence at two distinct starts can be equal: equality would already force equality of the first symbols. This also excludes full-cycle and longer circular windows, not only proper substrings. Thus `S` has no repeats at all under these definitions, hence no triple repeats and no pairs of interleaved repeats. The repeat-bridging conditions are vacuous, while coverage is satisfied as above.

Primary source: Guy Bresler, Ma'ayan Bresler, David Tse, *Optimal assembly for high throughput shotgun sequencing*, BMC Bioinformatics 14(Suppl 5):S18 (2013), DOI 10.1186/1471-2105-14-S5-S18, especially the repeat/interleaving/bridging definitions around Theorem 1 and the sufficient conditions in Theorem 6.

## Exact likelihood comparison

Medvedev & Brudno §6.1 define the exact global read-count probability for a circular candidate `C` using the candidate's own length `N(C)`. For observed read-type counts `x_i` and candidate occurrence counts `d_i`, the exact multinomial probability is

`n! / (∏ x_i!) * ∏ (d_i / N(C))^(x_i)`.

For the truth `S = ACGT`, the length-2 circular windows are

`AC, CG, GT, TA`.

Thus `d_AC = 1` and `d_GT = 1`. With `x_AC = 2`, `x_GT = 1`, the likelihood is

`3 * (1/4)^2 * (1/4) = 3/64`.

For `D = ACACGT`, the length-2 circular windows are

`AC, CA, AC, CG, GT, TA`.

Thus `d_AC = 2` and `d_GT = 1`, giving

`3 * (2/6)^2 * (1/6) = 1/18`.

The difference is

`1/18 - 3/64 = 5/576 > 0`.

Therefore `D` has strictly greater literal exact global read-count likelihood than the true sequence `S`.

Primary source: Konstantin Medvedev and Michael Brudno, *Maximum Likelihood Genome Assembly*, Journal of Computational Biology 16(8) (2009), §6.1, DOI 10.1089/cmb.2009.0047. The exact objective uses the candidate-dependent sequence length. In the subsequent approximation the denominator is replaced by the actual genome length, and the experiments assume known genome size; this distinction is essential here.

## What this refutes

The example refutes the statement that the truth must be an ML maximizer under **unrestricted-length exact Variant E**, even when the realized reads cover the truth and the relevant repeat-bridging conditions hold. Since the competitor is strictly better, the example refutes both the maximizer-only and uniqueness versions of that exact variant.

The mechanism is finite-sample frequency fitting. Bridging constrains reconstructibility of the realized reads in the truth, whereas the literal exact objective scores empirical read-type frequencies. Allowing candidate length to vary lets a competitor duplicate contexts for overrepresented observed read types and thereby improve likelihood.

## What this does not refute

The competitor has length 6 while the truth has length 4. It therefore does not refute a fixed-length candidate universe. It also does not refute the later Medvedev–Brudno approximation or its flow formulation. Most importantly, it does not by itself resolve which interpretation Shomorony et al. intended when asking whether bridging guarantees that the maximum-likelihood sequence is the true sequence.

The appropriate formalization target is the finite Variant-E statement above, with the broader source ambiguity kept explicit.