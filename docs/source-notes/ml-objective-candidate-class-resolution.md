# Published maximum-likelihood objective and candidate class: primary-source resolution

_Status: independent source resolution, 2026-09-19. Answers, as far as the primary
sources permit: fixed vs variable length, circular equivalence, tie/uniqueness
semantics, and sampling model. Records unresolved ambiguity instead of choosing._

This note was produced by independently retrieving and reading the primary
sources (not by summarizing existing repository notes). It also records one
correction to `docs/literature/ml-tie-semantics.md`.

## 0. Answers at a glance

| Sub-question | Most source-faithful answer | Status |
|---|---|---|
| Sampling model | Circular true sequence `s` of length `G`; `N` error-free reads of common length `L`; start positions i.i.d. uniform over the `G` circular positions | Source fact |
| Exact ML objective | Multinomial over all `4^k` read types with probability `d_i/N(D)`, candidate-dependent `N(D)`, constraint `N(D) = Σ_i d_i` | Source fact |
| Fixed vs variable candidate length | Exact objective uses candidate-dependent `N(D)`; **no fixed competitor length** is imposed. The binomial approximation replaces `N(D)` by an external constant `N` in the denominator but does not state a candidate-length restriction. The 2016 paper fixes the true `G`, not competitors | Source fact + reading |
| Candidate class | `D` is a circular genome; the objective is literally a function of the copy-count vector `(d_i)`. Genome-realizability of `(d_i)` and the §6.2 flow restriction are further constraints, not part of the §6.1 formula | Source fact + interpretation |
| Circular equivalence | Cyclic shift is required by the 2016 circular exposition. Whether reverse complement is also quotiented is unresolved | Cyclic shift: source fact. Reverse complement: unresolved |
| Tie / uniqueness | Unresolved. Neither paper gives a tie-break; Bresler (2013) produces *equal-likelihood same-length* alternatives for unbridged repeats | Unresolved |
| Which 2009 layer the 2016 sentence intends | Exact multinomial vs binomial approximation vs §6.2 flow set: the 2016 text does not select | Unresolved |

## 1. Source inventory and retrieval provenance

### 1.1 Medvedev–Brudno (2009) — fully retrieved

Paul Medvedev and Michael Brudno, "Maximum Likelihood Genome Assembly,"
*Journal of Computational Biology* 16(8), 2009, 1101–1116,
DOI [10.1089/cmb.2009.0047](https://doi.org/10.1089/cmb.2009.0047),
full text [PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/).

The body text and the displayed equation images were retrieved directly. The
displayed equations quoted below were read from the PMC image assets `M26.gif`,
`M27.gif`, `M28.gif`, `M30.gif`, `M31.gif`, `M33.gif`, because the formulas are
images in the HTML. This makes the formula claims in §3–§5 below independently
verified rather than transcription-dependent.

### 1.2 Shomorony et al. (2016) — accepted version not independently re-fetched

Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, and David N. C. Tse,
"Information-optimal genome assembly via sparse read-overlap graphs,"
*Bioinformatics* 32(17), 2016, i494–i502,
DOI [10.1093/bioinformatics/btw450](https://doi.org/10.1093/bioinformatics/btw450).

The accepted version is Open Access at Oxford (Unpaywall reports a CC-BY-NC
publisher PDF), but the publisher endpoint returns HTTP 403 to automated
retrieval (Cloudflare bot verification), and no PMC/Europe PMC deposit exists.
The open-question sentence used by this repository
(`docs/open-problem.md:9`) therefore could **not** be re-verified from the
publisher text in this run. It continues to rest on the repository's earlier
source recovery.

### 1.3 Shomorony et al. — author-hosted early preprint (retrieved and read)

<https://web.stanford.edu/~gkamath/nsgIlan.pdf>, titled "Optimal Sequence
Assembly via Sparse Read-Overlap Graphs" (23 pages). Independently retrieved:

- size 1 607 838 bytes;
- SHA-256 `f2a9f6a64f75cbf4c2cfaec6f794c779907f165c986261bec7a2aa72a3e6954a`;
- PDF `CreationDate` and `ModDate` both `D:20160123235649-08'00'`.

It contains a body plus an appended "6 Supplementary Material". Its
information-theoretic sampling discussion and the Bresler same-likelihood
theorem were read directly.

### 1.4 Bresler–Bresler–Tse (2013) — fully retrieved

Guy Bresler, Ma'ayan Bresler, and David Tse, "Optimal assembly for high
throughput shotgun sequencing," *BMC Bioinformatics* 14(Suppl 5):S18, 2013,
DOI [10.1186/1471-2105-14-S5-S18](https://doi.org/10.1186/1471-2105-14-S5-S18),
full text [PMC3706340](https://pmc.ncbi.nlm.nih.gov/articles/PMC3706340/).

## 2. Sampling model (source fact)

Author-hosted manuscript, §1 (Introduction), on the Bresler framework:

> "by considering a probabilistic framework where `N` reads of length `L` are
> sampled independently and uniformly at random from the sequence, it is
> possible to characterize the pairs `(N,L)` that guarantee that these bridging
> conditions are met …"

Author-hosted manuscript, appended Supplementary Material §6.4 "Bridging
Conditions and Information Limits":

> "Under the uniform sampling model described in Section 2, and given a known
> genome sequence `s`, one can compute the pairs `(N,L)` …"

Medvedev–Brudno §6.1 defines the same trial model for the likelihood:

> "In each trial, a position is uniformly sampled from `D` and the outcome of
> the trial is the `k`-molecule beginning at that position."

So the data-generating and likelihood models agree: i.i.d. uniform sampling of
start positions on a circular genome. Shomorony's true sequence is fixed to
length `G`; this fixes the *data-generating* genome, not the likelihood
competitor class (see §6).

## 3. Exact maximum-likelihood objective (source fact)

Medvedev–Brudno §6.1, first definition (body text):

> "Let `D` be a circular genome of length `N(D)`, and let `d_i` denote the
> number of times the `k`-molecule `i` appears in `D`. … Let the random variable
> `X_i` denote the number of trials whose outcome is `i`. There are `4^k` such
> variables … When taken together, their joint distribution is exactly the
> multinomial distribution, given by"

Verified displayed equation (`M27.gif`):

```text
P[X_1 = x_1, ..., X_{4^k} = x_{4^k}]
    = n! / (∏_i x_i!) · ∏_i ( d_i / N(D) )^{x_i}
```

with the per-trial probability read from `M26.gif` as `d_i / N(D)`, and the
multinomial constraint read from `M30.gif` as

```text
N(D) = Σ_i d_i .
```

The **global read-count likelihood** (`M28.gif`, body text: "the likelihood of
the parameters of the distribution `(d_i)` given the outcome of the trials
`(x_i)`") is the same expression regarded as a function of the copy-count
vector:

```text
L[d_1, ..., d_{4^k} | x_1, ..., x_{4^k}]
    = n! / (∏_i x_i!) · ∏_i ( d_i / N(D) )^{x_i} .
```

Three source facts about this objective:

1. The product ranges over **all `4^k` read types**, including types with
   `d_i = 0` (which contribute `0` if `x_i > 0`, and `1` if `x_i = 0`).
2. The denominator is the **candidate's own length** `N(D)`, and
   `N(D) = Σ_i d_i` links length to copy counts.
3. The likelihood is written as a function of the parameters `(d_i)`. A
   candidate `D` is a circular genome realizing those counts; the source does
   not separately formalize the set of realizable count vectors.

## 4. Binomial/separable approximation (source fact)

Medvedev–Brudno §6.1, second half:

> "Because the number of trials (sampled `k`-molecules) is typically large, we
> can approximate the multinomial distribution as the product of the individual
> binomial distributions of each `X_i`. Since in the binomial approximation the
> length of the genome `N(D)` is a constant that is independent of each `d_i`,
> we can replace it by `N`, which is the length of the actual genome from which
> the reads were sampled. … For our experiments, we assume that the genome size
> is known."

Verified displayed equation (`M31.gif`):

```text
L[d_1, ..., d_{4^k} | x_1, ..., x_{4^k}]
    ≈ ∏_i P[X_i = x_i]
    = ∏_i C(n, x_i) ( d_i / N )^{x_i} ( 1 - d_i / N )^{n - x_i} .
```

Verified convex cost (`M33.gif`), with the separability identity
`-log L = K · Σ_i c_i(d_i)` (`M32.gif`):

```text
c_i(d_i) = -( x_i log d_i ) - ( n - x_i ) log( N - d_i ) .
```

The retained `(1 - d_i / N)` factor is direct source evidence that the literal
approximation is **not** simply `∏_i d_i^{x_i}`; the zero-count factors are part
of it. (This independently confirms `docs/audit-binomial-marginals-issue32.md`.)

## 5. Section 6.2 flow feasible set (source fact)

Medvedev–Brudno §6.2 turns the optimization into a bidirected min-cost flow on
the transitively reduced read-overlap graph. The source states:

> "Each vertex has a lower bound of 1 since it represents a read that must be
> present in the genome at least once."

and

> "Since any flow can be decomposed into a collection of walks, our flow
> represents a (non-contiguous) assembly of the genome, and the flow going
> through each vertex represents the number of time the read is present in the
> assembly."

The feasible objects here are flows satisfying graph-derived lower bounds, not
arbitrary circular genomes. A theorem over this set is not automatically a
theorem over the §6.1 candidate class.

## 6. Fixed versus variable candidate length

- **Exact objective (§6.1):** candidate-dependent `N(D)`, no fixed length. The
  only length statement is the internal constraint `N(D) = Σ_i d_i`.
- **Binomial approximation (§6.1):** the *denominator* is the external true
  length `N`. This is a change of the probability model, not a statement that
  candidates must have length `N`. The formula remains a function of `(d_i)`
  and is well-defined only where `d_i ≤ N` for all `i` (so that
  `1 - d_i/N` is a probability). A candidate may therefore have length other
  than `N` while remaining in the approximation's domain, and a candidate with
  some `d_i > N` falls outside the domain for a reason unrelated to length.
- **Flow set (§6.2):** length is implicitly determined by the flow/overlap
  graph, not fixed externally.
- **Shomorony (2016):** fixes the true genome length `G` for the data model and
  proves recovery up to cyclic shift. It does not state that ML competitors
  have length `G`.

**Unresolved.** Nothing in the retrieved primary sources restricts §6.1
competitors to a fixed length, nor explicitly allows every length: the source
does not state the competitor universe. Treat fixed-length as a named
restriction, not a default.

**Additional version evidence on length.** The author-hosted early preprint's
Discussion (which, unlike the accepted version, contains no ML open question)
explicitly discusses a *genie-aided formulation where the target genome length
`G` is given*, and says fixing `G` "excludes the possibility of shrinking the
sequence by compressing repeats." This is a fixed-length formulation the
authors considered in their complexity discussion. It is **not** the
Medvedev–Brudno likelihood and should not be substituted for it, but it shows
that length assumptions were an explicit modeling axis in this line of work.

## 7. Circular equivalence and double strands

- Shomorony's true model is a **circular** sequence, and its reconstruction
  conclusion is "up to cyclic shift."
- Medvedev–Brudno model double-stranded DNA with **bidirected** graphs; a
  molecule is an unordered reverse-complement pair of strands.
- Bresler et al. handle double strands explicitly (§ Discussion, "double
  strand") by **not** quotienting: they map the model to a single strand of
  length `2G` (the concatenation of `u` and its reverse complement) and double
  the reads, then look for two Eulerian paths. They also note that reverse
  complement repeats on `u` induce interleaved repeats on the length-`2G`
  sequence.

**Unresolved.** The 2016 open-question text does not say whether the ML
candidate identity is cyclic shift only or cyclic shift plus reverse
complement. The two cited models treat the second strand differently (implicit
bidirected molecule vs explicit length-`2G` concatenation), so the repository
must keep the equivalence relation a parameter.

## 8. Tie and uniqueness semantics

- The 2016 sentence says "the maximum-likelihood sequence is the true
  sequence"; it gives no tie-break, no uniqueness claim, and no equivalence
  relation for uniqueness.
- Medvedev–Brudno say only that they "attempt to assemble the genome with the
  maximum global read-count likelihood" and give no tie rule.
- **Bresler et al. Theorem 1** is a same-likelihood (tie) construction:

  > "Given a DNA sequence `s` and a set of reads, if there is a pair of
  > interleaved repeats or a triple repeat whose copies are all unbridged, then
  > there is another sequence `s'` **of the same length** under which the
  > likelihood of observing the reads is the same."

So ties are a real, source-demonstrated phenomenon (not only a hypothetical),
and Bresler's ambiguity competitor has the **same length**. This is consistent
with either: (a) truth-is-a-maximizer, or (b) all-maximizers-are-truth-up-to-
equivalence, only the latter survives ties. Both schemas must be preserved.

## 9. Version fork in the primary source (material finding)

The author-hosted 23-page manuscript (created 2016-01-23, SHA-256 above) does
**not** contain the accepted paper's ML open-question sentence. Its complete
Discussion (section 5, read end to end) instead says:

> "In this context, a natural question is whether this approach is also solving
> some combinatorial optimization problem."

and then discusses parsimony, the genie-aided fixed-`G` formulation, and
NP-hardness of finding a generalized Hamiltonian cycle of a desired length. The
phrases "open question", "maximum-likelihood sequence", and the accepted
sentence do not occur; the only "likelihood" statement in the manuscript is the
appended Bresler same-likelihood theorem (Supplementary §6, Theorem 2). The
Manuscript title also differs ("Optimal Sequence Assembly…" vs accepted
"Information-optimal genome assembly…").

**Consequence.** The accepted Oxford text is the controlling source for
the open problem, but it could not be re-fetched in this run. The accessible
preprint is an **earlier version** and does not corroborate the accepted
Discussion wording. This should be recorded as a provenance limitation, not
resolved by treating the preprint as equivalent.

## 10. Correction issued to an existing note

`docs/literature/ml-tie-semantics.md` previously stated that the author-hosted
manuscript "uses the same substantive open-question wording." The direct
reading above does not support that; the preprint predates and lacks the
accepted open-question sentence. That sentence in the note has been corrected
to record the version fork. The note's substantive conclusion (tie semantics
are unresolved) is unchanged and is if anything strengthened: neither version
supplies a tie convention.

## 11. Unresolved-ambiguity register

1. **ML layer intended by the 2016 sentence:** exact multinomial (§6.1 first
   half) vs binomial approximation (§6.1 second half) vs §6.2 flow set. The
   retrieved 2016 preprint selects none; the accepted text (not re-fetched)
   selects none per the repository's earlier recovery.
2. **Competitor universe / length:** all circular genomes of any length vs
   fixed-length genomes vs copy-count vectors vs flow-feasible objects. The
   §6.1 definition does not state the universe; §6.2's set is a genuine
   restriction.
3. **Reverse-complement equivalence:** cyclic shift is required; whether the
   second strand is identified is not resolved by the 2016 text.
4. **Conclusion semantics:** truth-is-a-maximizer vs all-maximizers-are-truth.
5. **Tie-breaking:** absent from both papers.
6. **Accepted-text provenance:** the exact accepted open-question wording and
   the publisher supplement were not independently re-retrieved.

## 12. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| Sampling: i.i.d. uniform circular start positions, `N` reads length `L` | Source fact | Shomorony preprint §1/supp.; Medvedev–Brudno §6.1 |
| Exact multinomial with `d_i/N(D)`, product over `4^k` types, `N(D)=Σ d_i` | Source fact | Medvedev–Brudno §6.1 body + images `M26/M27/M28/M30` |
| Binomial approximation with fixed external `N` and `(1-d_i/N)^{n-x_i}` | Source fact | Medvedev–Brudno §6.1 body + images `M31/M33` |
| §6.2 feasible objects are read-graph flows, not all genomes | Source fact | Medvedev–Brudno §6.2 |
| §6.1 imposes no fixed competitor length | Source reading (well-supported) | No restriction appears; length is candidate-internal |
| Exact objective is over `(d_i)`; genome realizability is extra | Source reading | §6.1 wording + `N(D)=Σ d_i` |
| Cyclic-shift equivalence | Source fact | Shomorony reconstruction "up to cyclic shift" |
| Reverse-complement equivalence unresolved | Source-analysis | Shomorony (cyclic) vs MB (bidirected) vs Bresler (`2G` concat.) |
| Ties exist; Bresler competitor has same length | Source fact | Bresler Theorem 1 |
| Tie/uniqueness conclusion unresolved | Source-analysis | Absence of tie rules in both papers |
| Author-hosted preprint lacks accepted ML open-question sentence | Source fact (verified extraction) | `nsgIlan.pdf` SHA-256 above, Discussion §5 |
| Accepted open-question wording | Not independently re-verified this run | Oxford HTTP 403 |

## 13. Consequences for formalization

1. Every concrete theorem must name its ML layer (exact / approximate / flow),
   its competitor universe, and its equivalence relation.
2. Do not bake a fixed competitor length into the exact objective; expose it as
   a named restriction if used.
3. Keep likelihood input (observable read multiplicities) separate from the
   latent start positions that witness bridging/coverage.
4. Keep truth-is-a-maximizer and all-maximizers-are-truth as separate schemas.
5. Record the version fork explicitly when citing the 2016 open question.
