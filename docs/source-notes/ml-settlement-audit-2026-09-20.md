# Source-fidelity audit: is the 2016 bridging→ML question negatively settled?

_Status: primary-source audit, 2026-09-20. Scope restricted to the interpretation
of the Shomorony et al. (2016) phrase “the maximum-likelihood formulation of the
AP (Medvedev and Brudno, 2009)” and “the maximum-likelihood sequence” against
Medvedev–Brudno (2009). It re-verifies the primary sources, reconciles the
existing on-`main` notes, and records the one decisive caveat the on-`main`
referent notes do not carry. It does not modify any intent record. Claims are
labelled **source fact**, **interpretation**, **mathematical fact**, or
**repo-kernel-checked**._

## 0. Verdict

**The published open question cannot be called negatively settled without
qualification.** What the repository can support is a conditional statement:

> For the per-instance (finite read-set) reading, with the objective taken to be
> either determinate sequence-valued Medvedev–Brudno §6.1 model, and with any
> candidate universe that contains the same-length circular competitors, the
> implication “bridging ⇒ truth is maximum-likelihood” is false by a
> kernel-checked finite counterexample.

It is **not** an unconditional negative settlement of the published sentence,
because three source choices remain genuinely open (probability model,
candidate-length/tie convention, and — decisively — the finite-sample vs
high-coverage regime), and under the high-coverage fixed-length reading the
answer is *positive*. The accepted publisher supplement also remains
uninspected.

## 1. What the primary sources say (re-verified this run)

### 1.1 Shomorony et al. (2016), accepted typeset article

DOI `10.1093/bioinformatics/btw450`; retrieved from
`https://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf`,
SHA-256 `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da`
(matches the ledger in
[`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md) §2).

**Source fact.** Section 5 (Discussion), final paragraph, verbatim (typography
normalised):

> “The maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009), on
> the contrary, seems to be robust to these issues, and thus a good candidate
> for the ‘correct’ formulation. Understanding whether bridging conditions can
> be used to guarantee that the maximum-likelihood sequence is the true sequence
> is currently an open question.”

The sentence names Medvedev–Brudno only by a paper-level bibliography entry. It
contains no section, equation, figure, or page pointer, and the accepted main
text contains no likelihood formula and no occurrence of
`multinomial`/`binomial` (independently re-scanned this run).

**Source fact (data-generating model).** Section 2:

> “… each of the `N` reads is drawn independently and uniformly at random from
> the set of length-`L` substrings of `s`; `{s[t : t+L−1] : t = 1, …, G}`.”

This is the only likelihood the citing paper defines or uses. For a candidate
`x`, a single read has probability `d_x(r)/|x|`, so the read-set likelihood is
the exact-multinomial factor `∏_r (d_x(r)/|x|)^{x_r}` up to an observation-only
coefficient. **Interpretation.** Of MB09's three levels (§1.2 below) this
matches the exact multinomial, not the fixed-`N` product of binomials; but the
paper itself never connects its sampling model to an MB09 objective, so this is
an objective-level plausibility argument, not a source denotation.

### 1.2 Medvedev–Brudno (2009): three distinct objects

Re-verified this run from the authors' short/conference version,
`http://www.cs.toronto.edu/~brudno/medvedev_brudno_short.pdf`, SHA-256
`6304cad502e64eb7…` (prefix); §2.3 “Maximizing the Global Read-Count
Likelihood”, verbatim:

> “Let `G` be a circular genome of length `N(G)`, and let `g_i` denote the
> number of times the `k`-mer `i` appears in `G`. … their joint distribution is
> exactly the multinomial distribution … which we call the **global read-count
> likelihood** … In our approach, we attempt to assemble the genome with the
> maximum global read-count likelihood.”

then, after noting `N(G) = Σ g_i` blocks separability:

> “Because the number of trials (sampled `k`-mers) is typically large, we can
> **approximate** the multinomial distribution as the product of the individual
> binomial distributions of each `X_i`. Since in the binomial approximation the
> length of the genome `N(G)` is a constant that is independent of each `g_i`,
> we can replace it by `N`, which is the length of the actual genome … **For our
> experiments, we assume that the genome size is known.**”

and, on the §6.2 algorithm:

> “Each vertex has a lower bound of 1 since it represents a read that must be
> present in the genome at least once. … Since any flow can be decomposed into a
> collection of walks, our flow represents a **(non-contiguous) assembly** of the
> genome … we want to find a **flow** that minimizes `− log L`.”

**Source fact.** MB09 contains (a) the named exact global read-count multinomial
with candidate-intrinsic `N(G)`, which is sequence-valued; (b) an explicitly
labelled fixed-`N` product-of-binomial-marginals *approximation*, which is
sequence-valued; and (c) the §6.2 convex min-cost bidirected flow *algorithm*,
whose output MB call a “(non-contiguous) assembly,” i.e. flow-valued.

**Interpretation.** Because the 2016 sentence says “the maximum-likelihood
**sequence**,” (c) is not the direct referent absent an unstated flow→sequence
step; the referent is sequence-valued, i.e. (a), (b), or the broad “ML
framework.” This agrees with
[`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md)
§4 and is a source-supported inference, not a source fact.

## 2. Negative witnesses already in the repository

These are finite instances in which the source bridging hypothesis `R ∈ I_s`
holds, the truth is an admissible candidate, and a competitor has strictly
greater likelihood.

- **Exact multinomial, fixed length:** `AAABB` vs competitor `AAAAB`,
  likelihood ratio `2`, kernel-checked by
  `AssemblyP1.FixedLengthExactCounterexample.fixed_length_exact_counterexample`
  ([note](../fixed-length-exact-counterexample.md)).
- **Fixed-`N` binomial approximation, fixed length:** `AAACC` vs competitor
  `AAAAC`, ratio `1125/512`, kernel-checked by
  `AssemblyP1.FixedLengthBinomialCounterexample.fixed_length_binomial_counterexample`
  ([note](../fixed-length-binomial-counterexample.md)).
- **§6.2 lower-bound-1 bidirected reading:** `AAATT` vs competitor `AAAATT`,
  §6.1 binomial ratio `9/8`; the exact graph/flow admissibility is checked by
  `scripts/verify_se62_mb09_bidirected_graph.py`
  ([audit](../section62-mb09-bidirected-graph-audit.md)). On `main` the Lean
  module `AssemblyP1.Section62BridgingCounterexample` kernel-checks only the
  sequence-level `SeqSupportLB` certificate plus the ratio, **not** the
  bidirected flow; the flow certificate is computational.

**Mathematical fact (candidate-set inclusion).** A same-length competitor that
beats the truth is also an arbitrary-length competitor, so the same-length
negative results transfer to the larger circular-candidate class; the converse
transfer fails for positive results
([`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md) §3).

## 3. The decisive open choice: finite-sample vs high-coverage

This is the point the on-`main` referent notes
([`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md),
[`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md))
do not record, and it is why §0 says “not unconditionally.”

**Source fact.** The open-question sentence carries no sample-size or coverage
qualifier. The hypothesis set `I_s` is a set of realized read sets `R`
(accepted text, Eq. (1)), and the paper uses explicit “with high probability”
language elsewhere in its Introduction but not here. The literal reading is
therefore per-instance.

**Mathematical fact.** Fix the truth `S` of length `G`, read length `L`, and
truth window distribution `p(i) = d_S(i)/G`. For a length-`G` candidate `D` with
`q_D(i) = d_D(i)/G`, the law of large numbers and Stirling give

`(1/n) log L_exact(D|x) → −KL(p ‖ q_D) ≤ 0`,

with equality iff `q_D = p`. The candidate spectra are finite, so almost surely
for all sufficiently large `n` the truth's spectrum is the **unique** maximizer.
Hence, in the high-coverage (consistency) regime with fixed candidate length,
the answer to the published question is **yes** (and, with the repository's
spectrum-uniqueness bridge, the ML sequence is `S` up to cyclic shift). The
kernel-checked witnesses in §2 are low-coverage phenomena: each winning
competitor omits an observed truth read type, so its likelihood is zero for
large `n`.

**Interpretation.** The sentence is plausibly intended per-instance: if it meant
the asymptotic statement, the fixed-length answer would be essentially
immediate, making “currently an open question” surprising. But this is an
inference about intent, and the accepted text does not settle it. A negative
settlement must therefore state the regime, just as it must state the
probability model and the candidate-length/tie convention.

## 4. Exact conclusion for the repository

| Claim | Status |
|---|---|
| Accepted 2016 text names no MB09 section/equation/formula and writes no likelihood | source fact (re-verified) |
| Shomorony's own sampling model induces the exact-multinomial factor | mathematical fact; objective-level interpretation |
| MB09 has a named exact sequence objective, a labelled fixed-`N` sequence approximation, and a flow algorithm | source fact (re-verified) |
| The 2016 sentence is sequence-valued; §6.2 flow is not the direct referent | source-supported interpretation |
| Same-length kernel-checked witnesses refute both determinate §6.1 sequence objectives, and transfer to arbitrary length by inclusion | mathematical fact + repo-kernel-checked |
| Under high-coverage fixed length the truth is (a.s., eventually) the unique MLE, so the answer is positive | mathematical fact |
| The published sentence selects neither the objective, the length/tie convention, nor the regime | source gap |
| No located post-2016 work settles or restates the question | source-analysis ([citation-chain audit](../literature/post2016-bridging-ml-citation-chain-2026-09-20.md)) |
| Accepted publisher supplement uninspected (HTTP 403) | source gap |

**Determination.** The published open problem is **not** negatively settled as
published. It is negatively settled only in the explicitly qualified form of §0,
which the repository should state whenever it reports the finite-counterexample
result. The remaining obligations for an unconditional negative settlement are
source-level, not mathematical: fix the referent among MB09's levels, fix the
regime/quantifier, and rule out a supplementary section that names an objective.

## 5. Locators

- I. Shomorony, S. H. Kim, T. A. Courtade, D. N. C. Tse, “Information-optimal
  genome assembly via sparse read-overlap graphs,” *Bioinformatics* 32(17)
  (2016) i494–i502, DOI `10.1093/bioinformatics/btw450`; §2 sampling model and
  §5 Discussion open-question paragraph. SHA-256
  `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da`.
- P. Medvedev, M. Brudno, “Maximum Likelihood Genome Assembly,” *J. Comput.
  Biol.* 16(8) (2009) 1101–1116, DOI `10.1089/cmb.2009.0047`; §6.1–6.2. Short
  version §2.2–2.3, `http://www.cs.toronto.edu/~brudno/medvedev_brudno_short.pdf`,
  SHA-256 `6304cad502e64eb7…`.
- G. Bresler, M. Bresler, D. Tse, “Optimal assembly for high throughput shotgun
  sequencing,” *BMC Bioinformatics* 14(Suppl 5):S18 (2013), Theorem 1.
