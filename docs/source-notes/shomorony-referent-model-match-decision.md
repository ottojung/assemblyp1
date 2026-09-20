# The strongest defensible referent of “the maximum-likelihood sequence”: a model-match decision

_Status: independent primary-source decision note for issue #36, 2026-09-20. It
re-reads the accepted Shomorony et al. article and Medvedev–Brudno (2009)
directly, including the §6.1 display equations, and decides the referent question
that [`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md)
leaves open. Every claim is labelled **source fact**, **source-supported
inference**, **interpretation**, or **open**._

## 0. Decision

The strongest defensible reading of “the maximum-likelihood sequence” is the
**Medvedev–Brudno §6.1 global read-count likelihood**, evaluated on a candidate
circular sequence through its own length-`L` substring copy counts (issue reading
(1), with the §6.1 fixed-`N` binomial product (2) a close variant). **MB09 §6.2
flow feasibility is algorithmic machinery, not part of the referent.**

The decisive argument is a source-model match that the existing notes do not
state: Shomorony et al.'s own sequencing model — `N` error-free reads drawn
independently and uniformly from the `G` length-`L` substrings of a circular
sequence `s` — *is* the probability model of MB09 §6.1's exact multinomial, whose
displayed formula literally indexes `4^k` oriented read types. §6.2's
reverse-complement-collapsed, vertex-lower-bound-`1` flow is MB09's algorithm for
*solving an approximation*, and its stated output is a “(non-contiguous)
assembly,” not a sequence.

This decision is an **interpretation**: the accepted 2016 sentence still names no
section or equation (source fact). But it is the strongest sequence-level
referent the two primary texts jointly support, and the negative answer is robust
even if the referent were one of the other well-posed readings (§5).

## 1. The 2016 sentence and its citation context (source facts)

Accepted article, Section 5 (Discussion), final paragraph, printed page **i501**
(DOI `10.1093/bioinformatics/btw450`):

> “Another direction for future work … is understanding whether, in
> information-feasible instances of the AP, the output of NOT-SO-GREEDY coincides
> with the solution of a combinatorial optimization problem. Notice that while
> Theorem 1 guarantees the reconstruction of the true sequence s, there is no
> guarantee that **this sequence** corresponds to the solution of an
> optimization-based formulation of the AP such as those considered by Nagarajan
> and Pop (2009) and Medvedev and Brudno (2009). As mentioned by Medvedev and
> Brudno (2009), parsimony-based formulations tend to encourage an over-collapsing
> of the repeats … **The maximum-likelihood formulation of the AP (Medvedev and
> Brudno, 2009), on the contrary, seems to be robust to these issues, and thus a
> good candidate for the ‘correct’ formulation. Understanding whether bridging
> conditions can be used to guarantee that the maximum-likelihood sequence is the
> true sequence is currently an open question.**”

Three facts about the citation context:

1. The compared objects are **sequences**: “this sequence” is the NOT-SO-GREEDY
   reconstruction, and the question is whether it is “the maximum-likelihood
   sequence.” [source fact]
2. The contrast is at the level of **formulations** (parsimony-based vs
   maximum-likelihood), not algorithms. [source fact]
3. The phrase carries no subsection, equation, figure, or page pointer into
   MB09; the paper-level bibliography entry is “Medvedev,P. and Brudno,M. (2009)
   Maximum likelihood genome assembly. *J. Comput. Biol.*, **16**, 1101–1116.”
   [source fact]

The earlier author-hosted preprint (`nsgIlan.pdf`) does **not** contain this
sentence; it instead discusses a “genie-aided formulation where the target genome
length `G` is given” and “finding a GHC of a desired length `G`.” That earlier
passage is about the combinatorial *ordering* problem, not about the likelihood
model, so it does not by itself fix the ML normalizer (see §3–§4). [source fact]

## 2. MB09 §6.1–§6.2 as a formulation/algorithm pair (source facts)

The abstract and §1.2 of Medvedev–Brudno (2009) separate the objective from its
flow realization:

> Abstract: “we propose a **maximum likelihood framework** for assembling the
> genome that is the most likely source of the reads … **In this setting**, we
> give a bidirected network flow-based algorithm that … accurately estimates the
> copy counts of repeats.” [source fact]

> §1.2: “**We formulate the problem of genome assembly as maximizing the
> likelihood of the observed read frequencies** … **This problem can be
> formulated as a minimum cost bidirected flow (biflow) problem with convex
> costs** …” [source fact]

§6.1 then names and displays the exact objective. Its display equations (PMC3154397,
§6.1; equation-image IDs `M26`–`M33`) are:

```text
M26:  d_i / N(D)
M27:  P[X_1=x_1,…,X_{4^k}=x_{4^k}] = n!/∏_i x_i! · ∏_i (d_i/N(D))^{x_i}
M28:  L[d_1,…,d_{4^k} | x_1,…,x_{4^k}] = n!/∏_i x_i! · ∏_i (d_i/N(D))^{x_i}
M30:  N(D) = Σ_i d_i
```

and the explicitly approximate, separable objective MB actually optimizes:

```text
M31:  L[d_1,…,d_{4^k} | x_1,…,x_{4^k}] ≈ ∏_i C(n,x_i) (d_i/N)^{x_i} (1-d_i/N)^{n-x_i}
M32:  −log L = K · Σ_i c_i(d_i)
M33:  c_i(d_i) = −(x_i log d_i) − (n−x_i) log(N−d_i)
```

§6.2 is introduced as the algorithm:

> “**6.2. Putting it all together.** We are now ready to describe our **algorithm**
> for predicting copy counts. The first step is to build a bidirected overlap
> graph from the set of reads, which are DNA molecules. … Each vertex has a lower
> bound of 1 … By Observation 7, the `d_i`'s … correspond to the value of the
> flow through vertex `i` … Since any flow can be decomposed into a collection of
> walks, our flow represents a **(non-contiguous) assembly** of the genome …”
> [source fact]

So MB09 itself supplies the pair: a named likelihood formulation (`M28`, exact,
candidate-intrinsic `N(D)=Σd_i`) and an algorithm (`§6.2`) that optimizes a
different, explicitly labelled approximation (`M31`, external `N`). [source fact]

## 3. The model-match argument (source-supported inference)

Shomorony et al.'s sequencing model, Section 2 (printed page i495):

> “we will assume that `s` is a circular sequence of length `G` … each of the `N`
> reads is drawn independently and uniformly at random from the set of length-`L`
> substrings of `s`; `{s[t:t+L−1] : t = 1,…,G}`.” [source fact]

Match the quantities: `n = N` trials, read length `k = L`, candidate length
`N(D) = |D|`, `d_i = occ_i(D)` (the number of length-`L` windows of `D` equal to
type `i`), and `x_i` the observed read multiplicity. Under this identification,
MB09 `M27`/`M28` is *exactly* the likelihood of Shomorony's observed read multiset
under a candidate circular sequence. [source-supported inference]

Two consequences:

1. The §6.1 pair is not merely “the MB formulation”; it is the likelihood that the
   2016 paper's own probability model induces. Reading (1) is therefore the
   strongest sequence-level referent. [interpretation]
2. The literal `4^k` index set of `M27`/`M28` is the **oriented** length-`L`
   alphabet, which is what Shomorony's read strings are; the reverse-complement
   collapse and the per-read-vertex lower bound of `1` appear only in §6.2's
   graph algorithm. [source fact + interpretation]

## 4. Why §6.2 flow feasibility is machinery, not the referent

| Criterion | §6.1 exact (`M28`) | §6.2 flow |
|---|---|---|
| MB09's own label | “global read-count likelihood” | “our **algorithm** for predicting copy counts” |
| Input objects | `4^k` oriented read types | read DNA-molecule vertices |
| Principal constraint | multinomial normalizer `N(D)=Σd_i` | graph flow conservation + vertex lower bound `1` |
| Output | a genome `D` (via its counts) | a flow = “(non-contiguous) assembly” |
| Sequence? | yes, via `d_i = occ_i(D)` | only after the §7 heuristic decomposition |

Four source facts weigh against identifying the referent with §6.2:

1. MB09 route their concrete output to §7 (“From Flow to Contigs”) as a heuristic;
   the optimizer's object is a flow. [source fact]
2. Shomorony compares **formulations** and asks about a **sequence**; a flow is a
   different object type, needing an unstated flow→sequence bridge. [source fact]
3. The same authors' earlier preprint already distinguishes “the ML formulation”
   from “algorithms to find the ML sequence.” [source fact]
4. The §6.2 lower bound `1` and molecule collapse are graph/algorithm choices
   absent from `M27`/`M28`, which have no such bound and index oriented types.
   [source fact]

**Interpretation.** §6.2 is a computational reformulation/relaxation of the §6.1
optimization. It is legitimate to *ask* whether the published implication survives
the §6.2 restriction (the repository has done so), but §6.2 feasibility is not a
constitutive clause of “the maximum-likelihood sequence.”

## 5. The decision is robust: every well-posed reading is refuted

The referent ambiguity no longer blocks a negative settlement, because the
repository already contains kernel-checked witnesses whose hypotheses hold and
whose competitor wins under each well-posed reading:

| Reading | Objective / class | Refuting witness |
|---|---|---|
| (1) | §6.1 exact multinomial, candidate-intrinsic `N(D)`, oriented types | #31 (`AAABB → AAAAB`, exact ratio `2`); #43 also gives ratio `3` |
| (2) | §6.1 fixed-`N` binomial product | #32 (`AAACC → AAAAC`, ratio `1125/512`); #43 gives fixed-`N` ratio `5` |
| (3) | §6.2 read-molecule flow/circuit class | #43 (`AAATAT → AAAAAT`), both sides admissible §6.2 circuits |
| (4) | broad, objective-undetermined ML principle | not a definite mathematical statement |

[repository fact + kernel-checked for the listed witnesses]

Caveats kept explicit: the #43 same-length pair is a §6.2 witness under MB09's
molecule semantics; under a strict oriented §6.1 indexing its competitor drops an
observed type (recorded on the index-orientation packet), which is why readings
(1) and (3) are supported by *different* witnesses rather than one. The
conclusion “bridging does not force maximum-likelihood optimality” therefore
holds across (1)–(3); only the vague reading (4) is untouched, and it fixes no
objective to test.

## 6. What remains genuinely open

1. **Exact vs fixed-`N` probability model.** The accepted 2016 text chooses
   neither; the model-match argument favors the exact `M28` model, but the fixed-`N`
   `M31` is what MB09 actually solve. Both are already refuted, so this does not
   affect the negative answer. [open]
2. **Scale/tie semantics.** The exact `M28` objective is invariant under tandem
   scaling of `(d_i)`, so “the maximum-likelihood sequence” is not unique without a
   length/scale or equivalence convention. The 2016 text states none. [open]
3. **Publisher supplement.** The accepted supplementary ZIP remains uninspected
   (HTTP 403); it is the only unexamined accepted artifact that could name a
   specific likelihood object. [open]

## 7. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| 2016 sentence is sequence-valued, formulation-level, and points at no MB09 section | source fact | accepted text, p. i501 |
| MB09 §6.1 defines `L[d_1,…,d_{4^k}\|x]` with `N(D)=Σd_i`; §6.1 fixed-`N` binomial is an approximation | source fact | PMC3154397 §6.1, `M26`–`M33` |
| MB09 §6.2 is the “algorithm for predicting copy counts,” output a non-contiguous assembly | source fact | PMC3154397 §6.2, §7 |
| Shomorony's read model is independent uniform sampling of length-`L` substrings | source fact | accepted text §2, p. i495 |
| Shomorony's model instantiates §6.1's exact multinomial | source-supported inference | §3 identification of `n,k,N(D),d_i,x_i` |
| Reading (1) is the strongest sequence-level referent | interpretation | §3–§4 |
| §6.2 flow feasibility is algorithmic machinery, not the referent | interpretation | §4 |
| Readings (1)–(3) are already refuted by kernel-checked witnesses | mathematical fact + kernel-checked instances | §5 |
| Exact-vs-fixed-`N`, scale/tie, supplement remain open | source gap | §6 |

## 8. Locators

- I. Shomorony, S. H. Kim, T. A. Courtade, D. N. C. Tse, “Information-optimal
  genome assembly via sparse read-overlap graphs,” *Bioinformatics* 32(17) (2016)
  i494–i502, DOI `10.1093/bioinformatics/btw450`; sampling model printed p. i495;
  Discussion printed p. i501.
- Author-hosted earlier preprint `https://web.stanford.edu/~gkamath/nsgIlan.pdf`,
  Discussion (genie-aided fixed-`G` / GHC passage).
- P. Medvedev, M. Brudno, “Maximum Likelihood Genome Assembly,” *J. Comput.
  Biol.* 16(8) (2009) 1101–1116, DOI `10.1089/cmb.2009.0047`, PMC3154397;
  abstract, §1.2, §6.1 (equations `M26`–`M33`), §6.2, §7.
