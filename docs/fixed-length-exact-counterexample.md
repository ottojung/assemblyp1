# Fixed-length exact-multinomial counterexample

## Scope and epistemic status

This note records a finite counterexample to the statement that the
source-faithful bridging hypothesis `R ∈ I_s` forces the true sequence to be an
exact maximum-likelihood assembly **when all candidate genomes are required to
have the true genome's length**.

The candidate universe is the set of circular genomes of length `G = 5`; the
objective is the exact Medvedev–Brudno read-count multinomial likelihood
evaluated at the observed read counts (the repository's *fixed-length exact
variant*). The certificate and arithmetic below are reproduced by the
kernel-checked Lean theorem
`AssemblyP1.FixedLengthExactCounterexample.fixed_length_exact_counterexample`
in `AssemblyP1/FixedLengthExactCounterexample.lean`.

This note does **not** settle the published Shomorony et al. open question. In
particular it says nothing about unrestricted-length exact ML (issue #24 /
PR #25), the separable/binomial approximation, or the Section 6.2 flow
feasible set. See `docs/ml-formalization-contract.md` for the variant
discipline.

## Instance

Take the true circular genome

`S = AAABB`

of length `G = 5`, read length `L = 3`, and the realized latent starts `0, 1, 4`.
The resulting observed read multiset is

`R = {AAA, AAB, BAA}`, each with multiplicity one.

Take the competing circular genome

`D = AAAAB`

of length `5`, i.e. the same length as the truth.

## Coverage

The length-`3` reads at starts `0, 1, 4` cover the circular positions as

- start `0`: positions `0, 1, 2`;
- start `1`: positions `1, 2, 3`;
- start `4`: positions `4, 0, 1`.

The union is all five positions, so `R` covers `S`. This is the kernel-checked
`Covers`/`truth_covered` certificate.

## Repeat and bridging certificate

Source semantics (see `docs/bridging-source-semantics.md` and the citations
therein): a repeat pair consists of two distinct starts whose length-`ℓ`
circular windows are equal and which are maximal on both sides (preceding
symbols differ and following symbols differ); a triple repeat uses three
starts with the analogous three-copy maximality condition (preceding symbols
not all equal, following symbols not all equal); a copy is bridged when some
read covers at least one base strictly on both sides of it; a triple repeat is
all-bridged when every selected copy is bridged; a pair of repeats is
interleaved when their four selected starts alternate in cyclic order, and is
bridged when at least one constituent copy is bridged.

Enumerating the length-`1` and length-`2` circular windows of `S = AAABB`
gives the complete list of maximal repeat pairs:

- length `1`: the `A` copies at `0, 2`, and the `B` copies at `3, 4`;
- length `2`: the `AA` copies at `0, 1`.

There are no maximal repeat pairs of length `3` or more (the length-`3` windows
`AAA, AAB, ABB, BBA, BAA` are pairwise distinct).

**Triple repeat.** The length-`1` `A` copies at starts `0, 1, 2` form a triple
repeat: the windows are equal, the preceding symbols are `B, A, A` (not all
equal), and the following symbols are `A, A, B` (not all equal). This is a
genuine maximal triple repeat, not a substring counted by total multiplicity.

**All-bridged.** A length-`3` read starting at `r` bridges a length-`1` copy at
`t` exactly when `t = r + 1 (mod 5)`, so the copy is strictly interior to the
read. The three `A` copies are bridged respectively by the reads at starts
`4`, `0`, `1`:

- copy `0` is bridged by the read at `4` (covering `4, 0, 1`);
- copy `1` is bridged by the read at `0` (covering `0, 1, 2`);
- copy `2` is bridged by the read at `1` (covering `1, 2, 3`).

`TripleRepeatAllBridged`/`truth_triple_repeat_all_bridged` kernel-checks this.
The all-bridged clause is therefore genuinely exercised rather than vacuous.

**Interleaved repeats.** Among the maximal repeat pairs listed above, no two
have four starts alternating in cyclic order: the `A` pair `{0,2}` and the `B`
pair `{3,4}` occupy the cyclic label pattern `A A B B`, and the `AA` pair
`{0,1}` shares a start with the `A` pair and again does not alternate with the
`B` pair. Hence `S` has no interleaved repeat pair, so `I_s` imposes no
additional bridging obligation here. This finite check is recorded here rather
than formalized in Lean so that no general repeat/interleaving infrastructure
is introduced.

In particular, the length-`2` `AA` repeat at `0, 1` is *not* bridged by
`R` (a length-`3` read cannot strictly extend beyond a length-`2` copy), but it
is also not interleaved with any other repeat, so the source `I_s` conditions
do not require it to be bridged. This is why the example is source-faithful
while the earlier exploratory `AACAGG`/`AAAGGC`, `G = 6, L = 2` candidate is
not: there the all-bridged triple-repeat clause genuinely fails.

The conjunction of coverage and the kernel-checked all-bridged triple repeat is
`SourceHypotheses` in the Lean module.

## Exact likelihood comparison

Medvedev & Brudno §6.1 define the exact global read-count probability for a
circular candidate `C` with candidate-intrinsic length `N(C)`: for observed
read-type counts `x_i` and candidate occurrence counts `d_i`,

`n! / (∏ x_i!) * ∏ (d_i / N(C))^(x_i)`.

For the observed types, the circular occurrence counts are:

| read type | occurrences in `S` | occurrences in `D` |
|-----------|--------------------|--------------------|
| `AAA`     | 1                  | 2                  |
| `AAB`     | 1                  | 1                  |
| `BAA`     | 1                  | 1                  |

The remaining observed-type count is zero, so their factors are `1`. With
`n = 3` and all `x_i = 1`, the multinomial coefficient is `3! = 6`, and both
candidates have length `5`, so

`L(S) = 6 * (1/5) * (1/5) * (1/5) = 6/125`

and

`L(D) = 6 * (2/5) * (1/5) * (1/5) = 12/125 = 2 * L(S)`.

The exact likelihood ratio is therefore `2`, so `D` is strictly more likely
than `S` even among candidates of the same length. Hence the truth is not a
fixed-length exact maximum-likelihood maximizer, which refutes both the
maximizer-only and uniqueness readings for this restricted variant. The Lean
theorems `likelihood_ratio` and `truth_not_maximum_likelihood` kernel-check
this with exact rational arithmetic.

Primary source: Konstantin Medvedev and Michael Brudno, *Maximum Likelihood
Genome Assembly*, Journal of Computational Biology 16(8) (2009), §6.1, DOI
10.1089/cmb.2009.0047.

## Parametric family

Repeating the start-`0` read `k` times gives the observed multiset
`{AAA^k, AAB, BAA}` and likelihood ratio `2^k`; for example, starts
`0, 0, 0, 1, 4` give ratio `8`. This family is recorded as exact arithmetic;
it is not part of the minimal kernel-checked theorem above.

## What this refutes and what it does not

It refutes the statement that `R ∈ I_s` makes the truth a fixed-length exact
ML maximizer, and exposes the mechanism: the exact objective scores empirical
read-type frequencies, so a same-length competitor can duplicate contexts for
an overrepresented observed type and improve likelihood while the bridging
hypothesis constrains only reconstructibility of the realized reads.

It does **not** refute unrestricted-length exact Variant E (already addressed
separately by issue #24 / PR #25) or the Medvedev–Brudno separable/binomial
approximation, and it does not resolve which interpretation Shomorony et al.
intended. For the Section 6.2 bidirected-flow feasible set, the sibling
`AAABB`/`AAAAB` instance (the same witness with `B` relabelled) **is**
flow-feasible under the loop-inclusive reading and beats the truth there too;
see `docs/flow-feasibility-aaacc-witness.md`, which also exhibits the smallest
same-length flow-feasible counterexample found.

Primary source for the open question and the `I_s` hypothesis:
Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, and David N. C. Tse,
“Information-optimal genome assembly via sparse read-overlap graphs,”
*Bioinformatics* 32(17), 2016, i494–i502, DOI 10.1093/bioinformatics/btw450.
The repeat/interleaving/bridging definitions are attributed by that paper to
Guy Bresler, Ma'ayan Bresler, and David Tse, “Optimal assembly for high
throughput shotgun sequencing,” *BMC Bioinformatics* 14(Suppl 5):S18, 2013,
DOI 10.1186/1471-2105-14-S5-S18.
