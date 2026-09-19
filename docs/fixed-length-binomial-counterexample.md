# Fixed-length binomial-approximation counterexample

_Status: independently reproduced finite mathematical certificate for the literal Medvedev–Brudno Section 6.1 product-of-binomial-marginals approximation. This note does not claim settlement of the source-ambiguous Shomorony open question._

Primary sources:

- Paul Medvedev and Michael Brudno, “Maximum Likelihood Genome Assembly,” *Journal of Computational Biology* 16(8), 2009, 1101–1116. DOI: <https://doi.org/10.1089/cmb.2009.0047>; open full text: <https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/>.
- Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, and David N. C. Tse, “Information-optimal genome assembly via sparse read-overlap graphs,” *Bioinformatics* 32(17), 2016, i494–i502. DOI: <https://doi.org/10.1093/bioinformatics/btw450>.

## Scope of the objective

Medvedev–Brudno Section 6.1 first gives the exact multinomial read-count likelihood. To obtain a separable objective, it then approximates that multinomial by the product of the individual binomial marginals. In this approximation the candidate-dependent `N(D)` is replaced by a fixed external genome length `N`; the paper states that genome size is assumed known for its experiments.

For observed read counts `x_i`, total number of reads `n`, candidate read-type multiplicities `d_i`, and fixed external length `N`, the literal marginal for type `i` is

`Binomial(n, x_i) (d_i/N)^(x_i) (1-d_i/N)^(n-x_i)`.

The approximate likelihood is the product of these marginals over the read-type space. In particular, types with `x_i = 0` retain their `(1-d_i/N)^n` factors. Dropping those factors defines a different objective.

## Concrete instance

Use DNA alphabet symbols `A,C` inside the ordinary four-letter DNA read-type space.

- true circular genome `S = AAACC`, length `N = 5`;
- read length `L = 3`;
- realized starts `0,1,4`;
- observed reads `AAA, AAC, CAA`, once each, so `n = 3`;
- same-length competitor `D = AAAAC`.

The circular 3-mer multiplicities are

- `S`: `{AAA:1, AAC:1, ACC:1, CCA:1, CAA:1}`;
- `D`: `{AAA:2, AAC:1, ACA:1, CAA:1}`.

All other DNA 3-mers have candidate multiplicity zero and hence contribute factor one when their observed count is also zero.

## Exact arithmetic

Taking the product of the literal binomial marginals gives

- `L_A(S) = 452984832 / 30517578125`;
- `L_A(D) = 7962624 / 244140625`;
- therefore `L_A(D) / L_A(S) = 1125 / 512 > 1`.

Thus truth is not a maximizer for this fixed-length literal Section 6.1 binomial-approximation objective: the explicit same-length competitor has strictly greater approximate likelihood.

The arithmetic was independently reproduced twice in issue #32, including a full-type-space calculation. The source reading was independently checked against the open Medvedev–Brudno text.

## Bridging hypothesis

This is the `AAABB / AAAAB` witness from issue #31 with `B` relabeled to `C`. The relabeling preserves the equality pattern on which repeats, coverage, and bridging depend. The source-faithful certificate established for #31 therefore transfers directly:

1. starts `0,1,4` cover all five positions;
2. the three `A` copies at starts `0,1,2` form the maximal length-1 triple repeat;
3. those copies are bridged respectively by reads starting at `4,0,1`, each extending one base on both sides on a circular lift;
4. there is no interleaved repeat pair requiring an additional bridge.

The hypothesis is therefore non-vacuous: the all-bridged triple-repeat clause is exercised.

## Exact boundaries of the result

This certificate is distinct from the fixed-length exact-multinomial result in `docs/fixed-length-exact-counterexample.md`. There the same equality-pattern witness has exact likelihood ratio `2`; here the zero-count binomial factors change the ratio to `1125/512`.

This note does **not** show that `D` is feasible for the Section 6.2 transitively reduced bidirected-overlap-graph flow problem. Section 6.2 has its own read-derived feasible set and may represent non-contiguous assemblies; `docs/source-notes/medvedev-brudno-candidate-class.md` records why it must not be silently identified with the Section 6.1 circular-candidate universe.

Most importantly, this does not by itself resolve which Medvedev–Brudno formulation Shomorony et al. intended by “the maximum-likelihood sequence.” The repository must keep that source ambiguity explicit rather than upgrading this scoped negative result into settlement of the published question.

## Remaining verification boundary

The finite arithmetic and source interpretation above are independently checked and durable. Issue #32 remains the coordination point for the smallest appropriate kernel check of this distinct approximate objective and for any further source-correspondence work needed before changing its epistemic status.