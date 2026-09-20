# Does “the maximum-likelihood formulation” mean the MB09 §6.2 flow now modeled as AssemblyP1 Variant F?

_Status: independent adversarial primary-source audit for issue #36, 2026-09-20. It
asks a single question, tries hard to falsify the negative answer, and labels every
claim **source fact**, **source-supported inference**, **interpretation**,
**repository fact**, or **open**. This note is written against `main`; it does not
rely on any unmerged branch artifact._

_Question. Medvedev–Brudno (2009) contain a sequence-valued likelihood
(“global read-count likelihood”, §6.1) and a bidirected flow algorithm whose output
is a “(non-contiguous) assembly” (§6.2). AssemblyP1 models both layers — Variant E
(`AssemblyP1/ExactVariantECounterexample.lean`) and Variant F
(`AssemblyP1/Section62BridgingCounterexample.lean`,
`AssemblyP1/SameLengthSection62Counterexample.lean`). Does Shomorony et al.’s
“the maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009)”
denote the §6.2 flow layer (Variant F)?_

## 0. Decision

**No.** The 2016 phrase is sequence-valued and names a *formulation* (objective).
MB09’s named formulation is the §6.1 global read-count likelihood; the §6.2
bidirected flow is what MB09 themselves call “our **algorithm** for predicting
copy counts,” and its stated output is a flow / “(non-contiguous) assembly,” not a
sequence. The strongest defensible sequence-level referent is the §6.1
candidate-intrinsic objective (AssemblyP1 Variant E), with the §6.1 fixed-`N`
binomial product (Variant A) a close and, for the citation, equally live variant.
The §6.2 flow identification is a *consequential* reading — does ML optimality
survive restriction to MB09’s algorithm/feasible set? — not the denotation of the
phrase. That consequential reading is separately refuted by a kernel-checked
same-length §6.2 witness, so the negative settlement does not depend on this
adjudication.

[source fact + source-supported inference + repository fact; §1–§6]

`main` currently carries no decision on this referent: the two on-`main`
provenance notes
([`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md),
[`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md))
explicitly leave it open and rank the fixed-`N` variant first on the
“operative” axis. This note reaches the sequence-level conclusion independently
and records three tests those notes do not run: a steel-man of the flow
identification (§4), the cross-paper strand-model mismatch (§5.2), and the
citing authors’ own formulation/algorithm vocabulary (§2.2). It preserves
reading (2)/Variant A as a live close referent rather than dropping it.

## 1. Independent verification of the quoted artifacts

All quotations were re-read from locally cached copies; the three Shomorony
artifacts are byte-identical to the hashes already recorded on `main`
([`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md) §2).

| Artifact | SHA-256 |
|---|---|
| Shomorony et al., OUP-typeset accepted article | `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da` |
| Shomorony et al., author-accepted manuscript | `daeb5b3163d92643affc2398a387217cb57e5e33ce0dd5ebbfccabf621454f2c` |
| Shomorony et al., earlier author-hosted preprint + supplement | `f2a9f6a64f75cbf4c2cfaec6f794c779907f165c986261bec7a2aa72a3e6954a` |
| Medvedev–Brudno, published typeset article (`pdftotext -layout`) | `bfeaec37de55e87c35438108c33a8052f0fd6eb56f2903bb1d50d2793d8a5aa3` |

[source fact]

## 2. Terminology trace: what each paper calls what

### 2.1 Shomorony et al. (2016) — formulation, sequence (source facts)

Accepted article, Section 5 (Discussion), printed p. i501:

> “Another direction for future work … is understanding whether, in
> information-feasible instances of the AP, the output of NOT-SO-GREEDY coincides
> with the solution of a combinatorial optimization problem. Notice that while
> Theorem 1 guarantees the reconstruction of the true sequence s, there is no
> guarantee that this sequence corresponds to the solution of an
> optimization-based formulation of the AP such as those considered by Nagarajan
> and Pop (2009) and Medvedev and Brudno (2009). … The maximum-likelihood
> formulation of the AP (Medvedev and Brudno, 2009), on the contrary, seems to be
> robust to these issues, and thus a good candidate for the ‘correct’ formulation.
> Understanding whether bridging conditions can be used to guarantee that the
> maximum-likelihood sequence is the true sequence is currently an open question.”

Three facts about the citing vocabulary:

1. The compared objects are sequences (“this sequence”, “the maximum-likelihood
   sequence”).
2. The contrast is at the level of *formulations* (parsimony-based vs
   maximum-likelihood).
3. No subsection, equation, figure, or page pointer into MB09 is given.
   [source fact]

The same authors’ Introduction (printed p. i494) fixes the type of
“optimization-based formulation” in this paper as a single-sequence path/cycle
problem (generalized Hamiltonian path/cycle), and lists Medvedev–Brudno among that
family. [source fact]

### 2.2 Shomorony et al., earlier author-hosted preprint — formulation ≠ algorithm (source fact)

The preprint `nsgIlan.pdf`, Introduction:

> “[8] proposed a **maximum likelihood (ML) formulation** for assembly. While such
> a formulation prevents the over-collapsing of repeats, **devising algorithms to
> find the ML sequence given the read data** is a daunting task …”

and Discussion (PDF p. 16):

> “rather than focusing on devising an **algorithm** to solve a specific
> **optimization-based formulation** of the AP (such as the shortest GHC, or the
> CPP), we design an **algorithm** which provably reconstructs the true underlying
> sequence …”

[source fact]

This is the citing authors’ own split: “the ML formulation” is the objective;
“algorithms to find the ML sequence” are a separate category. The accepted
sentence then speaks of “the maximum-likelihood sequence,” i.e. the objective’s
output, not the algorithm.

### 2.3 Medvedev–Brudno (2009) — framework, named likelihood, approximation, algorithm (source facts)

Abstract:

> “we propose a **maximum likelihood framework** for assembling the genome that is
> the most likely source of the reads … **In this setting**, we give a bidirected
> network flow-based **algorithm** that … accurately estimates the copy counts of
> repeats in a genome.”

§6 title: “PREDICTING COPY-COUNTS USING MAXIMUM LIKELIHOOD.” §6.1:

> “we can consider the likelihood of the parameters of the distribution (d_i)
> given the outcome of the trials (x_i), which we call the **global read-count
> likelihood** … In our approach, we attempt to assemble the genome with the
> maximum global read-count likelihood … Unfortunately, since the multinomial
> distribution has the constraint that N(D) = Σ d_i, this is not possible
> [to make −log L separable].”

Then the explicitly-labelled approximation:

> “we can **approximate** the multinomial distribution as the product of the
> individual binomial distributions … we can replace it by N … **For our
> experiments, we assume that the genome size is known.**”

§6.2:

> “We are now ready to describe our **algorithm for predicting copy counts**. The
> first step is to build a bidirected overlap graph from the set of reads, which
> are DNA molecules. The vertices of this graph are the reads … Each vertex has a
> **lower bound of 1** … By Observation 7, the d_i’s described above actually
> correspond to the value of the **flow** through vertex i … Since any flow can be
> decomposed into a collection of walks, our flow represents a **(non-contiguous)
> assembly** of the genome …”

§7 heading: “FROM FLOW TO CONTIGS AND THE USE OF MATEPAIRS … we use a heuristic.”
[source fact]

So MB09 supply four distinct objects: the named exact objective (§6.1, `M28`), its
labelled fixed-`N` binomial approximation (§6.1, `M31`), the §6.2 flow algorithm,
and the umbrella “maximum likelihood framework.” Only the first two are over
candidate genomes in the sense of the 2016 sentence; the §6.2 output is a flow.
This matches the object inventory already recorded in
[`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md)
§2 and [`medvedev-brudno-candidate-class.md`](medvedev-brudno-candidate-class.md).

## 3. The model match, and where it actually lands

Shomorony et al.’s theoretical model, Section 2 (printed p. i495):

> “we will assume that s is a circular sequence of length G … each of the N reads
> is drawn independently and uniformly at random from the set of length-L
> substrings of s; {s[t : t+L−1] : t = 1,…,G}.”

[source fact]

Match the quantities: `n = N` trials, read length `k = L`, candidate length
`N(D) = |D|`, `d_i = occ_i(D)`, `x_i` the observed multiplicity. Under this
identification MB09’s `M27`/`M28` is exactly the likelihood Shomorony’s model
induces on a candidate circular sequence. [source-supported inference]

The §6.2 flow does **not** match this model in the same way: its vertices are
“DNA molecules” and its objective is the fixed-`N` approximation over
reverse-complement classes, whereas Shomorony’s theoretical model is a
single-stranded circular string (see §5.2). [source fact + interpretation]

## 4. Steel-manning the flow identification, then falsifying it

The strongest case that the phrase denotes §6.2:

- MB09’s abstract attaches “maximum likelihood framework” directly to the
  bidirected-flow algorithm (“In this setting, we give …”); their §6 title names
  the flow method; the paper’s contribution *is* the flow. A reader citing “the
  maximum-likelihood formulation of MB09” could mean that method.
- AssemblyP1’s Variant F exists precisely because this reading is live enough to
  test. [repository fact]

Four source facts falsify the identification as the *denotation*:

1. **Object type.** The 2016 sentence asks whether a *sequence* is “the
   maximum-likelihood sequence”; §6.2’s optimizer returns a flow and MB09 route
   single-sequence output to a §7 heuristic. A flow≠sequence step is unstated in
   both papers. [source fact]
2. **The authors’ own formulation/algorithm split.** MB09 call §6.2 “our
   **algorithm**,” and the Shomorony preprint (§2.2) separately labels “the ML
   formulation” and “algorithms to find the ML sequence.” [source fact]
3. **The §6.2 objective is the approximation, not the named likelihood.** §6.2
   optimizes the fixed-`N` binomial costs (`M31`/`M33`), which MB09 explicitly
   introduce as an approximation to the named “global read-count likelihood”
   (`M28`). [source fact]
4. **Strand-model mismatch.** Shomorony’s theoretical reads are oriented
   substrings; §6.2’s vertices are DNA molecules (reverse-complement classes).
   See §5.2. [source fact]

**Interpretation.** The flow is MB09’s computational realization of the ML
objective under an approximation; it is a legitimate *restriction* to test, but it
is not what “the maximum-likelihood formulation” denotes in a sentence whose
subject is a sequence.

## 5. Two refinements the model-match argument needs

### 5.1 MB09’s §6.1 is internally split; the match selects the formula

MB09 §6.1 prose says “the number of times the **k-molecule** i appears in D,” but
the displayed formula indexes `X_1,…,X_{4^k}` and `d_1,…,d_{4^k}`. `4^k` is the
*oriented* `k`-mer alphabet; the `k`-molecule count is `(4^k+p_k)/2`. The two
halves cannot both be literal. The strand/involution analysis in
[`mb09-se61-index-orientation-resolution.md`](mb09-se61-index-orientation-resolution.md)
shows MB09’s §6.2 wiring (vertices are molecule reads; `d_i` = vertex flow) is
molecular, while the displayed `M27`/`M28` count is oriented.

The model match with Shomorony (§3) therefore selects the **oriented §6.1
formula**, not MB09’s molecular prose. This should be stated whenever the
referent is called “the §6.1 likelihood”: it is a reconstruction that makes the
cited paper’s objective agree with the citing paper’s own single-stranded model.
[source fact + interpretation]

### 5.2 Cross-paper strand mismatch is independent evidence against Variant F

Shomorony’s theoretical model (§2) contains no reverse-complement quotient; the
paper adds reverse complements only as an *experimental* preprocessing step
(§4.1): “In order to handle the fact that reads can come from both strands of the
genome, before running NOT-SO-GREEDY, we preprocess the set of reads to include
each read and its reverse complement.” [source fact]

MB09, by contrast, is built on molecules throughout (§1.1, §3.1, §6.2). Hence the
Variant F flow identification would import a double-stranded union-of-strands
semantics that the 2016 theoretical model does not use, while the §6.1 oriented
formula needs no such import. This is evidence against reading the phrase as
§6.2 that is independent of the sequence-vs-flow type argument. [interpretation]

The same mismatch is a live caveat for the *witnesses*, not just the referent: a
§6.2/ML-side winner computed on MB09 molecule classes may not satisfy a
Bresler/Shomorony double-strand `I_s` certificate. That issue is tracked on
issue #36; it does not change the referent conclusion here, because the
sequence-level readings (Variants E and A) are refuted by witnesses whose
bridging certificate is stated in Shomorony’s own single-strand model.

## 6. Falsification ledger

| Attempted falsification | Outcome |
|---|---|
| Find a 2016 sentence or pointer naming a flow/algorithm | None; the phrase names a formulation and a sequence. [source fact] |
| Read “maximum-likelihood sequence” as the §6.2 flow output | Requires an unstated flow→sequence bridge; MB09 assign that to a §7 heuristic. [source fact] |
| Read MB09’s own “maximum likelihood framework” as the §6.2 algorithm | True as a label for the method, but MB09 call §6.2 “our algorithm,” and the citing authors split formulation from algorithm. [source fact] |
| Deny the model match by noting MB09 is double-stranded | Partly succeeds: the match needs the oriented §6.1 formula, not MB09’s molecular prose or §6.2 graph (§5.1–§5.2); it does not restore §6.2 as referent. [interpretation] |
| Show the fixed-`N` variant (2) is the better referent | Partly succeeds: MB09 implement fixed-`N` and “assume the genome size is known.” Variant A stays a live close referent; it is still sequence-valued, so it does not help §6.2. [source fact + interpretation] |

No attempt re-establishes §6.2 (Variant F) as the denotation.

## 7. Consequence for the settlement

The referent reduces to a **sequence-level** objective; the exact (§6.1 `M28`) vs
fixed-`N` (§6.1 `M31`) choice is the residual formula ambiguity, and both are
already refuted by same-length kernel-checked witnesses (Variant E by
`AssemblyP1/FixedLengthExactCounterexample.lean`, Variant A by
`AssemblyP1/FixedLengthBinomialCounterexample.lean`). Independently, the strongest
consequential flow reading is refuted by the same-length §6.2 witness
(`AssemblyP1/SameLengthSection62Counterexample.lean`). [repository fact +
kernel-checked]

Thus the identification question is now *decision-relevant only* for exposition:
the published negative answer is robust whether “the maximum-likelihood
formulation” denotes Variant E, Variant A, or the §6.2 restriction. [interpretation]

## 8. Relation to the other open determinations

Independently produced, as-yet-unmerged notes on unmerged branches reach the same
sequence-level conclusion by a related model-match argument (branches
`agent/issue36-shomorony-referent-decision-0920`,
`source/issue36-referent-object-0920`). Agreement among agents is not evidence of
truth, but it means the open question is now a *reconciliation* task rather than a
fresh investigation. This note’s distinct contributions are the adversarial
falsification ledger (§6) and the cross-paper strand-model mismatch as independent
evidence (§5.2). The central [`../open-problem.md`](../open-problem.md) should, on
integration, link whichever decision note is accepted and state the current
best-supported reading (sequence-level §6.1 likelihood; §6.2 is MB09’s algorithm)
while keeping the exact-vs-fixed-`N`, length, and tie forks explicit.

## 9. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| 2016 sentence is sequence-valued, formulation-level, no MB09 pointer | source fact | accepted text p. i501 |
| 2016 “optimization-based formulation” is a single-sequence path/cycle objective | source fact | accepted text p. i494 |
| Preprint splits “ML formulation” from “algorithms to find the ML sequence” | source fact | `nsgIlan.pdf` Introduction, Discussion |
| MB09 call §6.1 the “global read-count likelihood” and §6.2 “our algorithm” | source fact | MB09 abstract, §6.1–§6.2 |
| §6.2 output is a flow / “(non-contiguous) assembly”; sequences via §7 heuristic | source fact | MB09 §6.2, §7 |
| Shomorony theoretical reads are oriented substrings; reverse-complement only in experiments | source fact | accepted §2, §4.1 |
| Shomorony’s model instantiates the oriented §6.1 formula | source-supported inference | §3 |
| The phrase does not denote the §6.2 flow (Variant F) | interpretation | §4 |
| The best sequence-level referent is §6.1 (Variant E), fixed-`N` (Variant A) close | interpretation | §3, §5.1 |
| The flow reading is a restriction to test, not the denotation | interpretation | §4 |
| E, A, and the §6.2 restriction are all refuted by kernel-checked witnesses | repository fact + kernel-checked | §7 |
| Exact-vs-fixed-`N`, tie, candidate length, publisher supplement remain open | open | prior notes |

## 10. Locators

- I. Shomorony, S. H. Kim, T. A. Courtade, D. N. C. Tse, “Information-optimal
  genome assembly via sparse read-overlap graphs,” *Bioinformatics* 32(17) (2016)
  i494–i502, DOI `10.1093/bioinformatics/btw450`; model printed p. i495;
  Discussion printed p. i501; experimental reverse-complement preprocessing §4.1.
- Author-hosted earlier preprint + supplement,
  `https://web.stanford.edu/~gkamath/nsgIlan.pdf`; Introduction; Discussion
  pp. 16–17.
- P. Medvedev, M. Brudno, “Maximum Likelihood Genome Assembly,” *J. Comput. Biol.*
  16(8) (2009) 1101–1116, DOI `10.1089/cmb.2009.0047`, PMC3154397; abstract,
  §1.1–§1.2, §3.1, §6.1 (`M26`–`M33`), §6.2, §7.
