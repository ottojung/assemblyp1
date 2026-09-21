# What "the maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009)" designates

_Status: focused primary-source provenance trace for issue #36, 2026-09-20.
Records source facts separately from interpretation. It sharpens, but does not
settle, the source ambiguity in
[`../open-problem.md`](../open-problem.md) and reconciles the reading against
[`../ml-formalization-contract.md`](../ml-formalization-contract.md)._

_See also the independent reconciliation
[`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md),
which re-verifies these source facts, adds the sequence-vs-flow structural
argument and the fixed-`N` domain refinement, and gives the witness-sufficiency
matrix across the four readings._

This note is deliberately about one phrase. It asks: when Shomorony et al.
(2016) write "the maximum-likelihood formulation of the AP (Medvedev and Brudno,
2009)", what does that phrase actually denote, given (a) Shomorony's own
bibliography and surrounding prose, (b) what Medvedev–Brudno call their own
formulation, and (c) how contemporary readers used the same term?

The answer splits sharply between **source fact** and **interpretation**. The
source never names a section, equation, or objective; everything that selects
one of the Medvedev–Brudno objects is inference.

## 1. The phrase and its immediate context (source facts)

### 1.1 Accepted text

Accepted article, Section 5 (Discussion), final paragraph. Verbatim from the
publisher-typeset text (`InfoOptimalAssy.pdf`, printed p. i501):

> "Another direction for future work, from a more theoretical standpoint, is
> understanding whether, in information-feasible instances of the AP, the output
> of N OT-SO-GREEDY coincides with the solution of a combinatorial optimization
> problem. Notice that while Theorem 1 guarantees the reconstruction of the true
> sequence s, there is no guarantee that this sequence corresponds to the
> solution of an optimization-based formulation of the AP such as those
> considered by Nagarajan and Pop (2009) and Medvedev and Brudno (2009). As
> mentioned by Medvedev and Brudno (2009), parsimony-based formulations tend to
> encourage an over-collapsing of the repeats, and the optimal solution is in
> general different from the true underlying sequence. **The maximum-likelihood
> formulation of the AP (Medvedev and Brudno, 2009), on the contrary, seems to be
> robust to these issues, and thus a good candidate for the 'correct'
> formulation. Understanding whether bridging conditions can be used to
> guarantee that the maximum-likelihood sequence is the true sequence is
> currently an open question.**"

Three source facts about the phrase:

1. It is embedded in a sentence that classifies the Medvedev–Brudno object as
   one of the "optimization-based formulation[s] of the AP".
2. It gives no subsection, equation, figure, or page pointer into
   Medvedev–Brudno.
3. It is the only place the accepted main text mentions a likelihood
   *formulation*; a full-text scan finds exactly three occurrences of
   `likelihood` — the two in this paragraph plus the Medvedev–Brudno reference
   title — and zero occurrences of `multinomial`/`binomial`, no likelihood
   formula, and no candidate-genome/length/tie discussion.

### 1.2 What "AP" abbreviates

Source fact, Introduction (`InfoOptimalAssy.pdf`, p. i494):

> "The task of reconstructing the original sequence from a large number of short
> reads is known as the Assembly Problem...
> While the assembly problem (AP) does not have a unique 'canonical'
> formulation agreed upon by all bioinformaticians, the problem is widely
> regarded as computationally hard..."

So "AP" is Shomorony's own abbreviation for the Assembly Problem, and the quoted
sentence operates at the level of *formulations of the AP*, not of one
algorithm.

### 1.3 Exact bibliography entry

Source fact. Accepted article, References (`InfoOptimalAssy.pdf`, p. i502):

> "Medvedev,P. and Brudno,M. (2009) Maximum likelihood genome assembly.
> *J. Comput. Biol.*, **16**, 1101–1116."

Author-accepted manuscript (`NSG.pdf`, reference [8]) carries the same entry.
The cited work is therefore unambiguously

- Paul Medvedev and Michael Brudno, "Maximum Likelihood Genome Assembly,"
  *Journal of Computational Biology* 16(8), 2009, 1101–1116,
  DOI [10.1089/cmb.2009.0047](https://doi.org/10.1089/cmb.2009.0047),
  full text [PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/).

## 2. Retrieval provenance (retrieved 2026-09-20)

| Artifact | Locator | SHA-256 |
|---|---|---|
| Published article, OUP typeset | `https://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf` | `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da` |
| Author-accepted manuscript | `https://people.eecs.berkeley.edu/~courtade/pdfs/NSG.pdf` | `daeb5b3163d92643affc2398a387217cb57e5e33ce0dd5ebbfccabf621454f2c` |
| Earlier author-hosted preprint | `https://web.stanford.edu/~gkamath/nsgIlan.pdf` | `f2a9f6a64f75cbf4c2cfaec6f794c779907f165c986261bec7a2aa72a3e6954a` |
| Howison–Zapata–Dunn (2013) author PDF | `https://mark.howison.org/Howison-Bioinformatics-2013.pdf` | `bc25681f820b151467df79d7122c5b16a64892b2f15fa3636ace09350762c935` |
| Medvedev–Brudno (2009) full text | `https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/` | `d52c6e8998e055de69782a98a162410e870a7263d6e13e076bc617d01d0c0c2f` (HTML) |

The first three hashes match the ledger already recorded on the unmerged
provenance branches (source notes `ml-objective-candidate-class-resolution.md`
and `primary-provenance-verification.md`), so this note is reading
byte-identical artifacts. The Oxford publisher article,
article PDF, and supplement endpoints still return HTTP 403; the publisher
supplement remains uninspected.

## 3. The authors' own use of "formulation" versus "algorithm" (source facts)

The earlier author-hosted preprint is one version *earlier* than the accepted
paper and contains no ML open question, but it is the same author group and uses
the exact term. Introduction (`nsgIlan.pdf`, PDF pp. 1–2):

> "To circumvent this issue, [8] proposed a **maximum likelihood (ML)
> formulation** for assembly. While such a formulation prevents the
> over-collapsing of repeats, **devising algorithms to find the ML sequence**
> given the read data is a daunting task, and existing approaches rely on the
> assumption of high coverage [8]."

Source fact about vocabulary: in the same research line, "the ML formulation" is
the *objective/problem*, and it is explicitly distinguished from the *algorithm*
that finds the ML sequence. Reference `[8]` is the same Medvedev–Brudno paper.

The accepted text uses the same split. Introduction (`InfoOptimalAssy.pdf`):
"As pointed out by Medvedev and Brudno, 2009, **parsimony-based
formulations** can fail at producing the true sequence because long repeats tend
to be under-represented in the shortest sequence that is consistent with the
data." The Discussion sentence then opposes "parsimony-based formulations" to
"the maximum-likelihood formulation". Both are objectives for the AP, not
algorithms.

## 4. What Medvedev–Brudno designate as their ML formulation (source facts)

All quotations below are from `PMC3154397`, read directly (§6.1 is the printed
section "Maximizing the global read-count likelihood"; §6.2 is "Putting it all
together").

### 4.1 Abstract — framework first, algorithm "in this setting"

> "Furthermore, we **propose a maximum likelihood framework for assembling the
> genome that is the most likely source of the reads**, in lieu of the standard
> maximum parsimony approach (which finds the shortest genome subject to some
> constraints). **In this setting**, we give a bidirected network flow-based
> algorithm that, by taking advantage of high coverage, accurately estimates the
> copy counts of repeats in a genome."

### 4.2 Introduction §1.2 — "we formulate the problem of genome assembly as..."

> "We propose that the overall goal of an assembler should be not to minimize
> the length of the assembled genome, but to maximize the likelihood that it was
> the source of the set of reads. ... **We formulate the problem of genome
> assembly as maximizing the likelihood of the observed read frequencies**,
> rather than minimizing the length of the genome. **This problem can be
> formulated as a minimum cost bidirected flow (biflow) problem with convex
> costs**, and we show that it can be effectively solved with a generic flow
> solver..."

### 4.3 Section 6.1 — exact objective, then the approximation actually used

> "In this section, we describe our **maximum likelihood framework** for genome
> assembly, and give an algorithm that, given a set of reads (DNA molecules),
> **finds the genome that maximizes the global read-count likelihood**."
>
> "Let `D` be a circular genome of length `N(D)`, and let `d_i` denote the
> number of times the `k`-molecule `i` appears in `D`. ... can consider the
> likelihood of the parameters of the distribution `(d_i)` given the outcome of
> the trials `(x_i)`, which we call the **global read-count likelihood**."
>
> "In our approach, we attempt to assemble the genome with the maximum global
> read-count likelihood. ... Unfortunately, since the multinomial distribution
> has the constraint that `N(D) = Σ_i d_i`, this [separable convex form] is not
> possible."
>
> "Because the number of trials (sampled `k`-molecules) is typically large, we
> can **approximate** the multinomial distribution as the product of the
> individual binomial distributions of each `X_i`. Since in the binomial
> approximation the length of the genome `N(D)` is a constant that is
> independent of each `d_i`, we can replace it by `N`, which is the length of
> the actual genome from which the reads were sampled. ... **For our
> experiments, we assume that the genome size is known.**"

### 4.4 Section 6.2 — the concrete optimization MB actually propose

Source fact: MB build the transitively reduced bidirected read-overlap graph,
add a supersource/supersink, and solve a convex min-cost biflow in which

> "Each vertex has a lower bound of 1 since it represents a read that must be
> present in the genome at least once. ... the `d_i`'s described above actually
> correspond to the value of the flow through vertex `i` ... Since any flow can
> be decomposed into a collection of walks, our flow represents a
> **(non-contiguous) assembly** of the genome."

### 4.5 Section 8.2 — genome length is a required input

> "**Our algorithm relies on having an estimate on the length of the genome**,
> and we tested to what extent the accuracy is affected when the length is
> mis-estimated."

So within MB09 there are three distinct objects, and MB's own text assigns them
different roles: the exact global read-count likelihood (`N(D)`, named as the
target), the separable/binomial approximation (external `N`, explicitly
labelled an approximation), and the §6.2 biflow (the algorithm that solves the
approximation). Only the first uses candidate-intrinsic length; only the
second/third use an externally supplied genome size.

## 5. How the term was read by contemporaries (source facts)

### 5.1 Howison, Zapata & Dunn (2013)

"Toward a statistically explicit understanding of *de novo* sequence assembly,"
*Bioinformatics* 29(23):2959–2963, DOI
[10.1093/bioinformatics/btt525](https://doi.org/10.1093/bioinformatics/btt525).
Section 5 ("Likelihood approaches"), verbatim:

> "In fact, a maximum likelihood genome assembler was already proposed based on
> similar principles (Medvedev et al., 2009). Like CGAL, it calculates
> likelihood based on the depth of read coverage, but it does not incorporate
> paired end information at this stage. Instead, it takes the approach typical
> of many genome assemblers of first assembling the contigs, then resolving
> conflicts by looking for contigs that agree with the orientation and insert
> size of the paired reads. **Also, it requires as a parameter the accurate size
> of the target genome, which is not available in all de novo assembly
> projects.** A related design for maximum likelihood assembly (Varma et al.,
> 2011) uses a different formulation that starts from an approximate size and
> estimates the actual size during the optimization."

(Howison's in-text "Medvedev et al., 2009" resolves to the bibliography entry
"Medvedev,P. and Brudno,M. (2009) Maximum Likelihood Genome Assembly. *J.
Comput. Biol.*, 16, 1101–1116.")

This is a **third-party source fact about how the Medvedev–Brudno ML method was
understood**: its formulation consumes "the accurate size of the target genome"
as a parameter, and a later formulation (Varma et al.) is contrasted precisely
because it estimates size during optimization.

### 5.2 Varma, Ranade & Aluru (2011) — "maximum likelihood formulation" as a term of art

Aditya Varma, Abhiram Ranade, and Srinivas Aluru, "An Improved Maximum
Likelihood Formulation for Accurate Genome Assembly," ICCABS 2011, pp. 165–170,
DOI [10.1109/ICCABS.2011.5729873](https://doi.org/10.1109/ICCABS.2011.5729873).

Source fact: the phrase "maximum likelihood formulation" was already a
recognizable term of art for the Medvedev–Brudno objective, and the improvement
Varma et al. advertise is a change in the genome-length assumption. This
corroborates Howison's contrast and shows that, in the community reading,
genome-size handling was *part of what the formulation was*.

## 6. Interpretation: what the phrase most plausibly designates

This section is **source analysis / interpretation**, not a source statement.

### 6.1 The phrase is an objective family, not one formula

The strongest textual reading is that "the maximum-likelihood formulation of the
AP" denotes the *maximum-likelihood objective/principle* as opposed to
"parsimony-based formulations" — i.e. the aim of selecting the genome that
maximizes the probability of the observed reads. Reasons:

- Shomorony's own framing (source fact, §1.1) opposes
  *formulations*: parsimony vs maximum likelihood. It never picks a section or
  equation.
- The same authors' earlier version distinguishes "the ML formulation" from "the
  algorithms to find the ML sequence" (source fact, §3).
- MB's abstract calls it a "maximum likelihood framework" and gives the
  flow algorithm "in this setting" (source fact, §4.1).

Under this reading the phrase ranges over both the exact multinomial and the
binomial approximation, because both are instances of the same ML objective
applied under different probability models.

### 6.2 But the *implemented/designated* MB formulation uses external genome size

If "formulation" is instead read as "the ML objective MB actually pose and
solve" — a reading invited by Shomorony calling it an "optimization-based
formulation" and by MB's own "we formulate the problem ... as a minimum cost
bidirected flow" — then the fixed/known genome size is not incidental:

- MB's own §6.1 replacement of `N(D)` by the actual `N`, and §8.2's "our
  algorithm relies on having an estimate on the length of the genome", are
  source facts (4.3, 4.5).
- Howison et al. (2013) independently describe the MB ML assembler as requiring
  "the accurate size of the target genome" (5.1).
- Varma et al. (2011) title their improvement as a "maximum likelihood
  formulation" distinguished by how they handle that size (5.2).

So the **known-genome-size / fixed-`N` reading has substantial source support**
as the denotation of the phrase, and reading the citation as specifically
designating the *candidate-intrinsic-`N` exact multinomial* is an
interpretation that runs against MB's own operative assumption.

### 6.3 Caveat: "known `N`" is not the same as "candidate length `= N`"

Source fact, §6.1 (4.3): in the approximation `N` is a constant used in each
marginal's denominator; the paper does not say competing genomes must have
length `N`. This distinction matters and is already recorded in
[`../ml-formalization-contract.md`](../ml-formalization-contract.md) §"Variant
A". "Requires the accurate size of the target genome" (Howison) is a statement
about the likelihood parameter, not an explicit competitor-length constraint.
Consequently the repository's "fixed-length" variants impose an *additional*
restriction; that restriction is not by itself what the phrase denotes.

### 6.4 §6.2 flow is an algorithm, not obviously "the formulation"

MB describe §6.2 as the algorithm ("we are now ready to describe our
algorithm"). The authors' own formulation/algorithm split (§3, §4.1) and
Howison's use of "formulation" both weigh against identifying "the
maximum-likelihood formulation" with the §6.2 flow construction. However, §6.2
is where MB's objective becomes a concrete constrained optimization, and
Shomorony's "optimization-based formulation" language makes it a live candidate.
Source text does not decide.

### 6.5 Ranking (interpretation)

| Reading of the phrase | Source support |
|---|---|
| (4) A broad ML principle / objective family, not one formula | Strongest direct textual fit ("formulations" contrast; author's formulation-vs-algorithm vocabulary) |
| (2) The binomial approximation with externally supplied genome size | Supported as MB's operative/implemented formulation (§6.1, §8.2) and by Howison/Varma |
| (3) The §6.2 biflow feasible optimization | Live if "optimization-based formulation" is pressed, but MB call it the algorithm and its object is a non-contiguous flow, not a sequence |
| (1) The exact multinomial with candidate-intrinsic `N(D)` | The named ideal target, but explicitly abandoned as not separable/usable; designating it is interpretation |

## 7. Consequence for the kernel-checked witnesses and issue #36

Source facts about the witnesses (from
[`../fixed-length-exact-counterexample.md`](../fixed-length-exact-counterexample.md)
and
[`../fixed-length-binomial-counterexample.md`](../fixed-length-binomial-counterexample.md)):
they are finite instances in which a *same-length* competitor strictly beats
the truth under, respectively, the fixed-length exact multinomial and the
literal fixed-`N` product-of-binomial-marginals objective, while the source
bridging hypotheses hold.

Their bearing on the published question depends entirely on which reading of the
phrase holds (interpretation):

- If the phrase denotes the **candidate-intrinsic-`N` exact multinomial over
  arbitrary circular candidates** (reading 1), the same-length exact witness
  refutes the unrestricted-length maximizer claim as well: it is a counterexample
  inside the length-`G` subclass, which is a subset of the arbitrary-length
  class, so it is also a counterexample in the larger class. (The length
  restriction is therefore not what limits this reading; see
  [`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md)
  §3–§4.)
- If the phrase denotes the **fixed-`N` binomial approximation over circular
  candidates** (reading 2), the same-length binomial witness is directly
  relevant in the same way — but still only after one decides that the
  competitor universe is the circular-sequence class rather than MB's §6.2
  read-overlap-graph flows.
- If the phrase denotes the **§6.2 flow feasible optimization** (reading 3), the
  witnesses settle nothing unless they are shown to lie in the §6.2 feasible
  class (or a theorem relates that class to circular candidates).
- If the phrase denotes the **broad ML principle** (reading 4), no single
  finite witness settles it, because the objective itself is not fixed by the
  source.

Therefore the source trace *does not* by itself validate the claim that the
existing same-length witnesses already suffice to answer the published question
negatively. At least one further step is needed:

1. a source argument fixing the phrase's competitor universe to the
   circular-sequence class with reading 1 or reading 2 (rather than the §6.2
   flow class) — **after which the existing same-length witnesses already supply
   the negative answer**, by candidate-set inclusion; or
2. a proof/construction placing a violating instance inside MB's §6.2
   flow-feasible class.

So the residual gap is the choice between the circular-candidate and §6.2-flow
universes (and the objective/strand/tie choices), not the length of the
competitors. This is why the §6.2 feasibility work remains essential rather than
optional.

## 8. Unresolved register

1. **Which MB object the phrase intends:** exact multinomial vs fixed-`N`
   approximation vs §6.2 flow vs broad principle. The accepted text selects
   none; this note narrows the ranking but does not prove a denotation.
2. **Competitor universe / length:** §6.1 imposes no fixed competitor length;
   "known `N`" is a likelihood parameter, not stated as a candidate-length
   constraint. Fixed length remains an added restriction.
3. **Controlling source:** the publisher supplement (sections A–G) is still
   unretrieved (HTTP 403); no cross-reference in the accepted text points to a
   likelihood/objective section. See
   [`shomorony-supplement-referent-evidence.md`](shomorony-supplement-referent-evidence.md):
   the accepted supplement is a single PDF (`supp_material.pdf`), and the
   accepted article's own six by-name pointers into sections A, B, C, E, F, G
   are all algorithm/proof/Lander–Waterman, none likelihood — so it is not a
   likely source of a referent selection.
4. **Consequence for settlement:** whether the kernel-checked witnesses are
   sufficient depends on (2) and on §6.2 feasibility, per §7.

## 9. Correction to the existing issue #36 comment

The existing issue #36 comment cites the Shomorony paper as
"DOI 10.1093/bioinformatics/btw267". Source fact (Crossref): `btw267` is
"Genome assembly from synthetic long read clouds," *Bioinformatics* 32(17),
i216–i224. The Shomorony et al. paper under discussion is
`10.1093/bioinformatics/btw450` (Bioinformatics 32(17), i494–i502), matching the
Reference section of the accepted PDF. The `btw267` DOI in that comment is a
transcription error and should not be propagated.

## 10. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| Shomorony names MB only by a paper-level bibliography entry; no section/equation/formula | **Source fact** | `InfoOptimalAssy.pdf` §5 + Reference list; full-text scan |
| "AP" abbreviates Assembly Problem in Shomorony | **Source fact** | `InfoOptimalAssy.pdf` §1 |
| Earlier Shomorony preprint distinguishes "ML formulation" from "algorithms to find the ML sequence" | **Source fact** | `nsgIlan.pdf` Introduction |
| MB09 propose a "maximum likelihood framework", then a flow-based algorithm "in this setting" | **Source fact** | MB09 abstract |
| MB09 §6.1 defines the exact multinomial with `N(D)`, then explicitly replaces `N(D)` by the actual `N`, assuming genome size known | **Source fact** | MB09 §6.1 |
| MB09 §8.2 says the algorithm relies on an estimate of genome length | **Source fact** | MB09 §8.2 |
| Howison et al. (2013) describe the MB ML assembler as requiring the accurate target genome size as a parameter | **Source fact** | Howison et al. §5 + bibliography |
| Varma et al. (2011) title "maximum likelihood formulation"; its improvement is genome-size handling | **Source fact** | Crossref + title/abstract |
| The phrase most plausibly denotes an ML objective family, not one formula | **Interpretation** | §6.1 |
| Known-genome-size reading has substantial support as the operative formulation | **Interpretation** | §6.2 |
| §6.2 flow is MB's algorithm, not the "formulation" | **Interpretation** | §6.4 |
| Existing same-length witnesses do not by themselves settle the published question | **Interpretation** | §7 |
| Publisher supplement contents | **Unretrieved (403)** | §2 |
