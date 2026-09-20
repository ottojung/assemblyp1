# Medvedev–Brudno §6 objective semantics: copy-count vectors, the normalizer `N`, and what §6.2 changes

_Status: focused source note for issue #36, 2026-09-20. Primary-source quotations
independently re-verified this run from Medvedev–Brudno PMC3154397 and from the
accepted Shomorony et al. article. Every claim is labelled **source fact**,
**mathematical fact about the stated formulas**, or **interpretation**. This note
does not settle the open problem and does not select a single referent for
Shomorony's bare citation._

Issue #36 asks which Medvedev–Brudno (MB09) object the 2016 sentence
“the maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009)”
most faithfully denotes, and whether the kernel-checked fixed-length
exact/binomial witnesses already suffice or whether §6.2 feasibility remains
essential. This note addresses only the MB09 side of that question: what §6.1
defines, what the §6.1 approximation changes, and what §6.2 adds.

---

## 0. Answer at a glance

1. **Source fact.** The §6.1 likelihood is written as a function of the
   **copy-count vector** `(d_i)`, not directly of a sequence. The candidate's
   length enters as the normalizing constant `N(D) = Σ_i d_i`.
2. **Mathematical fact.** The exact §6.1 likelihood is invariant under positive
   scaling of `(d_i)`, hence under tandem duplication of the candidate. The true
   genome's length `G` does not occur in it, and candidate length is not
   identifiable from the exact objective alone.
3. **Source fact.** The §6.1 approximation replaces the candidate-dependent
   normalizer `N(D)` by an externally supplied constant `N` (the true or
   estimated genome length; “for our experiments, we assume that the genome size
   is known”), yielding a product of independent binomials with per-coordinate
   domain `0 ≤ d_i ≤ N`. This is a **different probability model**, not the exact
   objective with a length constraint attached.
4. **Source fact.** §6.2 restricts the copy-count vector to a
   **flow-conservation/lower-bound feasible set** and uses the approximation's
   convex costs. Its output is a flow, i.e. a “(non-contiguous) assembly”; a
   sequence is only produced later by the §7 contig heuristic.
5. **Mathematical fact.** §6.2 does not impose `Σ_i d_i = N`. The constant `N`
   stays an external parameter. Hence §6.2 restricts the **domain of copy-count
   vectors**, not the length of a candidate genome.
6. **Interpretation.** At the MB09 end, “the fixed-length exact §6.1 objective”
   is the hardest of the four issue-#36 readings to defend, because the fixed
   length there is not a restriction on sequences but a *replacement of the
   normalizer inside a different probability model*. The source nevertheless
   selects no referent, so the disjunction (1)/(2)/(3)/(4) of issue #36 remains
   live.

---

## 1. Provenance of the quotations

- **MB09.** Paul Medvedev and Michael Brudno, “Maximum Likelihood Genome
  Assembly,” *Journal of Computational Biology* 16(8), 2009, 1101–1116, DOI
  [10.1089/cmb.2009.0047](https://doi.org/10.1089/cmb.2009.0047), full text
  [PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/). The §6.1 and
  §6.2 body text quoted below was fetched and read this run. The displayed
  formulas (§6.1 multinomial, binomial product, and convex cost) are images in
  the PMC HTML; the equation contents cited here are the ones already read from
  the PMC image assets in
  `docs/source-notes/ml-objective-candidate-class-resolution.md` §3–§5, and are
  used only where the surrounding body text already states the structure.
- **Shomorony accepted article.** “Information-optimal genome assembly via
  sparse read-overlap graphs,” *Bioinformatics* 32(17), 2016, i494–i502, DOI
  [10.1093/bioinformatics/btw450](https://doi.org/10.1093/bioinformatics/btw450).
  Retrieved copy: `InfoOptimalAssy.pdf`, 9 pages, SHA-256
  `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da`; the
  open-question paragraph was read end to end and contains exactly three
  occurrences of “likelihood,” all inside that paragraph and the MB09
  reference title.
- **Author accepted manuscript.** `NSG.pdf`, 8 pages, SHA-256
  `daeb5b3163d92643affc2398a387217cb57e5e33ce0dd5ebbfccabf621454f2c`; same
  passage with copy-editing differences.

---

## 2. Source facts: the exact §6.1 objective

Direct body-text quotations (PMC3154397, §6.1):

> “Let `D` be a circular genome of length `N(D)`, and let `d_i` denote the
> number of times the `k`-molecule `i` appears in `D`.”

> “In each trial, a position is uniformly sampled from `D` and the outcome of
> the trial is the `k`-molecule beginning at that position. For a given `i`, the
> probability that the outcome of a single trial is `i` is simply `d_i/N(D)`.”

> “When taken together, their joint distribution is exactly the multinomial
> distribution …”

> “Thus, we can consider the likelihood of the parameters of the distribution
> `(d_i)` given the outcome of the trials `(x_i)`, which we call the **global
> read-count likelihood**.”

> “In our approach, we attempt to assemble the genome with the maximum global
> read-count likelihood.”

> “Unfortunately, since the multinomial distribution has the constraint that
> [`N(D) = Σ_i d_i`], this is not possible [to make `−log L` separable].”

The multinomial coefficient is `n! / ∏_i x_i!`, observation-only; the
candidate-dependent factor is `∏_i (d_i / N(D))^{x_i}`.

### 2.1 What is maximized

**Source fact.** The section defines the likelihood explicitly as a function of
the **parameters `(d_i)`**. A candidate genome `D` is a circular sequence that
*realizes* a copy-count vector; the objective value depends on `D` only through
`(d_i)`. The source does not separately formalize the set of realizable count
vectors at this point.

**Interpretation.** Therefore “a maximum-likelihood sequence” is not literally
what §6.1 maximizes; it is a sequence whose induced copy-count vector maximizes
the likelihood. This is a short, but real, semantic step beyond the source.

### 2.2 The role of `N(D)`

**Source fact.** `N(D)` is not an independent candidate-length parameter: it is
tied to the copy counts by the multinomial normalizing constraint
`N(D) = Σ_i d_i`. Length and copy counts are not two free axes.

---

## 3. Mathematical facts about the exact objective

Let `L_exact(d | x) = [n!/∏_i x_i!] · ∏_i (d_i / Σ_j d_j)^{x_i}` on the domain
`d_i ≥ 0`, `Σ_i d_i > 0`, and `d_i = 0 ⇒ x_i = 0`.

1. **Positive homogeneity.** For every `λ > 0`,
   `L_exact(λ d | x) = L_exact(d | x)`. Every per-trial probability is a ratio,
   so the normalizer cancels.
2. **Tandem invariance.** If `D` is a circular genome and `D^k` is its `k`-fold
   tandem repetition, then `Σ d_i` and every `d_i` scale by `k`, so
   `L_exact(D^k | x) = L_exact(D | x)`.
3. **Length non-identifiability.** Consequently the exact objective has no
   unique maximizer in the space of circular genomes: every scale ray
   `{D^k}` contributes the same likelihood value. The truth's length `G` is not
   recoverable from the exact objective, and neither is the candidate's length
   within a ray.

### 3.1 Consequence for the fixed-length question

**Mathematical fact.** Restricting competitors to a fixed length `G` is a
genuine **candidate-universe restriction** that selects one representative from
each scale ray (or excludes the ray). It is not a property implied by the exact
objective. This matches the repository's existing Variant E / fixed-length
distinction and the tandem-invariance lemma
(`docs/bridging-schemas-and-flow-feasibility-gaps.md`, Prop. A, on branch
`analysis/bridging-schemas-and-flow-gaps`).

**Interpretation.** The exact §6.1 objective is therefore intrinsically
*scale-degenerate*: it can support “the truth is a maximizer,” but it cannot by
itself support a uniqueness-up-to-equivalence conclusion in which length is
part of the identity, unless a length normalization or candidate restriction is
added.

---

## 4. Source facts: the §6.1 approximation

Direct body-text quotations (PMC3154397, §6.1, second half):

> “Because the number of trials (sampled `k`-molecules) is typically large, we
> can approximate the multinomial distribution as the product of the individual
> binomial distributions of each `X_i`.”

> “Since in the binomial approximation the length of the genome `N(D)` is a
> constant that is independent of each `d_i`, we can replace it by `N`, which is
> the length of the actual genome from which the reads were sampled. The
> approximate length of the actual genome can be ascertained through one of a
> number of biological experiments, or through an Expectation-Maximization type
> approach. For our experiments, we assume that the genome size is known.”

The retained approximation is (per the repository's image reading, `M31`/`M33`)

```text
L[d | x] ≈ ∏_i C(n, x_i) (d_i/N)^{x_i} (1 - d_i/N)^{n - x_i},
c_i(d_i) = -(x_i log d_i) - (n - x_i) log(N - d_i).
```

### 4.1 `N` is external, `N(D)` is gone

**Source fact.** The approximation explicitly treats the denominator as a
constant independent of the `d_i` and substitutes the true genome length `N`.
The source says this `N` can be measured or estimated by EM, and that the
experiments assume it known.

### 4.2 The approximation is a different probability model

**Mathematical fact.** The product of independent binomials is not the
multinomial distribution; it is a second probability model over the same count
vector. Its domain is `0 ≤ d_i ≤ N` for all `i` (so each `1 - d_i/N` is a
probability). It contains **no** constraint `Σ_i d_i = N`.

### 4.3 “Known genome size” is an assumption about `N`, not a length restriction

**Source fact / reading.** The sentence “we assume that the genome size is
known” fixes the *normalizer* `N`, not a candidate universe. The source does not
state that the approximate objective is optimized only over genomes of length
`N`. A count vector with `Σ_i d_i ≠ N` remains in the approximation's domain
provided every coordinate is at most `N`.

**Interpretation.** Calling the approximation “the fixed-length objective” is
shorthand for “the objective whose normalizer is the externally fixed `N`.” It
is not, on the primary text, an objective restricted to candidate sequences of
length `N`.

---

## 5. What §6.2 changes

Direct body-text quotations (PMC3154397, §6.2):

> “The vertices of this graph are the reads, and the edges are all possible
> bidirected overlaps of length at least `o_min`.”

> “Each vertex has a lower bound of 1 since it represents a read that must be
> present in the genome at least once. All other lower bounds are 0 and all
> upper bounds are infinity.”

> “By Observation 7, the `d_i`'s … actually correspond to the value of the flow
> through vertex `i`, and we let `c_i` be the convex cost functions for the
> vertices.”

> “Since any flow can be decomposed into a collection of walks, our flow
> represents a **(non-contiguous) assembly** of the genome, and the flow going
> through each vertex represents the number of time the read is present in the
> assembly.”

Observation 7:

> “The number of times `W` visits `r` is equal to the number of times `r`
> appears a submolecule of the molecule spelled by `W`.”

§6 intro also states the algorithm “finds the genome that maximizes the global
read-count likelihood,” but the algorithm's variables are vertex flows and its
stated output interpretation is a non-contiguous assembly.

### 5.1 Changes

| | §6.1 exact | §6.1 approximation | §6.2 optimization |
|---|---|---|---|
| Variable | copy counts `(d_i)`, `N(D)=Σd_i` | copy counts `(d_i)`, fixed `N`, `d_i ≤ N` | vertex flows `(d_i)` |
| Normalizer | candidate-dependent `N(D)` | external constant `N` | external constant `N` |
| Feasibility | count vector realizable by a circular genome (unstated) | same domain, no `Σd_i=N` | flow conservation + vertex lower bounds in read-overlap graph |
| Objective value | multinomial | product of binomials | product of binomials |
| Output | count vector | count vector | flow = non-contiguous assembly |
| Sequence? | only via realizability | only via realizability | not directly; §7 heuristic |

**Source fact.** §6.2 is downstream of the approximation: it uses the
approximation's convex costs. It is not a third independent likelihood.

**Mathematical fact.** The §6.2 flow polytope does not constrain the total
`Σ_i d_i` to equal `N`; the source imposes only conservation, vertex lower
bounds of `1`, and infinite upper bounds (with a supersource/sink). Hence §6.2
restricts the **copy-count domain**, not the length of a candidate genome.

**Source fact.** The source's own reading of a §6.2 optimal flow is a
non-contiguous assembly. A single spelled sequence is only obtained later, in
§7, by a heuristic walk decomposition; that decomposition is not itself the
optimization.

---

## 6. Reconciliation against the four issue-#36 readings

The readings offered in issue #36, assessed only from the MB09 side (Shomorony's
sentence names no section, formula, or equation — source fact):

1. **Exact multinomial with candidate-intrinsic `N(D)`.** Fully supported by
   §6.1 as a well-defined objective. Caveat: its natural argument is a copy
   vector; “sequence” requires the realizability step, and the objective is
   scale-degenerate (§3).
2. **§6.1 approximation with external known `N`.** Fully supported by §6.1's
   second half. It is a *different probability model*, not the exact objective
   with a fixed length. “Known `N`” is an experimental/estimability assumption
   (§4.3), not a length restriction on candidates.
3. **§6.2 bidirected-flow optimization.** Supported as what MB09 actually
   optimize, but its output is a flow with a non-contiguous interpretation and
   it adds no `Σd_i = N` constraint. Calling its solution “the maximum-likelihood
   sequence” requires a further step the §6.2 optimization does not itself take.
4. **A broader conceptual ML principle left underspecified.** Consistent with
   the observation that no §6 object is literally a sequence-maximization and
   that the 2016 sentence names none.

**Interpretation.** Reading (2) is the one most easily over-stated. Its “fixed
length” is a fixed *normalizer* inside a changed model; it does not by itself
select length-`N` sequences. Reading (1) has the strongest claim to the word
“formulation,” but its maximizers are count vectors, and it is scale-invariant.
Reading (3) is the actual published algorithm but is one level removed from a
sequence. Reading (4) is what remains if one insists on a literal
sequence-object.

This note does **not** decide among (1)–(4). It records that the MB09 text does
not force the fixed-length sequence class that the repository's fixed-length
witnesses inhabit.

### 6.1 Bearing on the witnesses

- The kernel-checked unrestricted-length exact Variant E counterexample needs no
  candidate-length assumption and is consistent with reading (1) as a
  count-vector objective whose competitors range over all realizable vectors.
- The kernel-checked fixed-length exact/binomial witnesses inhabit a
  **restricted** candidate universe. Whether they settle the published question
  turns on whether Shomorony's phrase denotes that restricted universe, which
  the MB09 text does not by itself supply.
- Whether either witness lies in the §6.2 flow-feasible class is a separate
  membership question, addressed in
  `docs/section-6-2-feasible-set-membership.md` (branch
  `analysis/bridging-schemas-and-flow-gaps`). This note's §5 supplies the MB09
  semantics that membership analysis relies on: §6.2's domain is flow-feasible
  copy vectors using the approximation cost, with no `Σd_i = N` constraint.

---

## 7. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| §6.1 likelihood is a function of `(d_i)`; `N(D)=Σd_i` | source fact | MB09 §6.1 body text |
| Approximation replaces `N(D)` by external `N`; genome size assumed known | source fact | MB09 §6.1 body text |
| Approximation is a product of independent binomials, domain `d_i ≤ N` | source fact + math | MB09 §6.1 + formula structure |
| §6.2 uses flows, lower bound `1`, non-contiguous assembly; uses approximation costs | source fact | MB09 §6.2 body text |
| §6.2 imposes no `Σd_i = N` | source reading / math | §6.2 states only conservation, bounds, supersource/sink |
| Exact likelihood is positive-homogeneous and tandem-invariant | mathematical fact | algebra of the stated formula |
| Candidate length is not identifiable from the exact objective | mathematical fact | consequence of homogeneity |
| Fixed length is a genuine candidate-universe restriction | interpretation (well-supported) | §3–§4 |
| Fixed-length exact is the hardest MB09 reading to defend | interpretation | §6 |
| Which MB09 object the 2016 sentence denotes | unresolved | Shomorony names no section/formula/equation |
| Accepted 2016 wording and 3× “likelihood” full-text fact | source fact (re-verified this run) | `InfoOptimalAssy.pdf` SHA-256 above |
| Accepted publisher supplement | not retrieved | not attempted this run |

---

## 8. What would change this reading

1. Recovering the accepted publisher supplement (Supplementary Material A–G) or
   an author statement that identifies a specific §6.1/§6.2 object would resolve
   the referent directly.
2. If Shomorony's intended competitor class is the §6.2 sequence-level feasible
   set, then the fixed-length witnesses are insufficient and the membership
   analysis of `docs/section-6-2-feasible-set-membership.md` governs.
3. Any later proof/claim that MB09 intended competitors of length `N` would have
   to cite a passage the current retrieval does not contain; §4.3 records why
   “we assume genome size is known” does not supply one.

---

## References

1. P. Medvedev and M. Brudno. “Maximum Likelihood Genome Assembly.”
   *Journal of Computational Biology* 16(8):1101–1116, 2009.
   DOI [10.1089/cmb.2009.0047](https://doi.org/10.1089/cmb.2009.0047);
   full text [PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/).
2. I. Shomorony, S. H. Kim, T. A. Courtade, and D. N. C. Tse.
   “Information-optimal genome assembly via sparse read-overlap graphs.”
   *Bioinformatics* 32(17):i494–i502, 2016.
   DOI [10.1093/bioinformatics/btw450](https://doi.org/10.1093/bioinformatics/btw450).
