# Is Medvedev–Brudno §6.2 feasibility necessary to settle the 2016 open question?

_Status: independent source reading + decision, 2026-09-20, for issue #36. It
re-reads the primary sources directly (accepted Shomorony PDF, author-hosted
preprint with appended supplement, MB09 full text, the MB09 short/conference
version, the 2010 thesis, Bresler–Bresler–Tse 2013) and reconciles the
conflicting repository positions in
[`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md)
§7 (“§6.2 feasibility work remains essential”) and
[`shomorony-ml-quantifier-sequence-resolution.md`](shomorony-ml-quantifier-sequence-resolution.md)
§5 (“the residual is not §6.2 feasibility”). Every claim is labelled **source
fact**, **source-supported inference**, **mathematical fact**, **verified
computation**, **kernel-checked**, **interpretation**, or **open**. This note
does not select a probability model or tie semantics by fiat._

## 0. Decision

**§6.2 feasibility is not genuinely necessary to settle the published open
question.** The 2016 sentence is paper-level and sequence-valued; Medvedev–Brudno
§6.2 is the *algorithm* that returns a possibly non-contiguous flow, not the
“maximum-likelihood sequence.” No primary source points the phrase at §6.2.
Independently of that text argument, the §6.2-restricted sequence-level
implication is already false with a kernel-checked finite counterexample, so
imposing §6.2 feasibility does not rescue the implication either.

The genuinely necessary residual source choices are instead:

1. the **probability model** — MB09’s exact candidate-intrinsic-`N(D)`
   multinomial vs the §6.1 fixed-`N` product-of-binomial marginals; and
2. the **candidate-length and tie conventions**.

[source reading + source-supported inference; §4–§7]

## 1. Method and independent verification of the quoted artifacts

All quotations below were extracted directly from the cached byte-identical
copies; hashes that the repository already records were re-checked:

| Artifact | SHA-256 | Match |
|---|---|---|
| Shomorony et al., OUP-typeset article `InfoOptimalAssy.pdf` | `ec17b16f…3acfce3c4da` | yes |
| Shomorony et al., author-hosted preprint + supplement `nsgIlan.pdf` | `f2a9f6a6…a3e6954a` | yes |
| Howison–Zapata–Dunn (2013) `Howison2013.pdf` | `bc25681f…762c935` | yes |
| MB09 full text (PMC3154397 extraction) | dynamically generated HTML; not hash-stable | n/a |

[source fact]

The §6.2 finite witness was re-derived from scratch by
`scripts/verify_se62_lb1_bidirected_determination.py` (all assertions passed) and
re-checked in the kernel:

```sh
python3 scripts/verify_se62_lb1_bidirected_determination.py
~/.elan/bin/lake build AssemblyP1.Section62LowerBoundOneCounterexample
# -> Build completed successfully (8924 jobs).
```

[verified computation + kernel-checked]

## 2. No primary source ties the phrase to a MB09 section

The accepted Discussion sentence, verbatim (printed p. i501):

> “The maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009), on
> the contrary, seems to be robust to these issues, and thus a good candidate
> for the ‘correct’ formulation. Understanding whether bridging conditions can
> be used to guarantee that the maximum-likelihood sequence is the true sequence
> is currently an open question.”

[source fact]

It carries no subsection, equation, figure, or page pointer into MB09. A
full-text scan of the accepted article finds no formula, no
`multinomial`/`binomial`, and no candidate-length or tie discussion in the
passage. The only structured object the sentence explicitly quantifies over is
“the maximum-likelihood **sequence**.” [source fact]

## 3. MB09 contains four distinct objects; only one is sequence-valued

Direct reading of MB09 (PMC3154397) confirms:

| Object | Output | Sequence-valued? | Source role |
|---|---|---|---|
| exact global read-count multinomial, candidate-intrinsic `N(D)` | circular genome `D` | yes | named target; explicitly *not* separable |
| §6.1 product of binomial marginals, external true `N` | circular genome `D` scored by `d_i` | yes | the approximation actually used |
| §6.2 convex min-cost bidirected flow | a flow / “(non-contiguous) assembly” | **no** | the algorithm |
| “maximum likelihood framework” | — | n/a | MB’s umbrella term |

[source fact]

The exact-vs-fixed-`N` text is:

> “Since in the binomial approximation the length of the genome `N(D)` is a
> constant that is independent of each `d_i`, we can replace it by `N`, which is
> the length of the actual genome from which the reads were sampled. … For our
> experiments, we assume that the genome size is known.”

and the §6.2 output is:

> “Since any flow can be decomposed into a collection of walks, our flow
> represents a **(non-contiguous) assembly** of the genome …”

[source fact]

## 4. Why §6.2 is not the direct referent: sequence versus flow

Three source facts weigh against reading the phrase as §6.2.

1. **MB’s own formulation/algorithm split.** The abstract calls the object a
   “maximum likelihood **framework**” and gives the bidirected-flow algorithm
   only “**In this setting**.” §6.2 opens “We are now ready to describe our
   **algorithm** for predicting copy counts.” [source fact]
2. **The short/conference version states the method is flow-valued.** In
   `medvedev_brudno_short.pdf` §2.3: “Within the biflow framework, `g_i`
   corresponds to the flow through a vertex (`k`-mer) in the overlap graph, and
   we want to find a **flow** that minimizes `−log L`.” [source fact]
3. **Sequences are a separate downstream step.** MB §7 (“From Flow to Contigs”)
   turns the flow into contigs with a heuristic; the §6.2 objective does not
   determine a single sequence. [source fact]

**Interpretation.** If the 2016 phrase designated §6.2 literally, the words “the
maximum-likelihood sequence” would change the *type* of the object, not merely
its objective. A flow→sequence bridge is required and is not supplied by either
paper. This is evidence *against* §6.2 being the direct referent, independent of
the length question. [interpretation]

## 5. Positive version evidence that the object is a single sequence

The author-hosted preprint is one version earlier. Its Discussion poses the
target as a single-sequence combinatorial problem:

> “rather than focusing on devising an algorithm to solve a specific
> optimization-based formulation of the AP (such as the shortest **GHC**, or the
> CPP), we design an algorithm which provably reconstructs the true underlying
> sequence … In this context, a natural question is whether this approach is
> also solving some combinatorial optimization problem.”

and later:

> “It is not difficult to see that, like most formulations of the AP, the
> problem finding a **GHC of a desired length `G`** is in general NP-hard.”

The accepted version deletes the GHC/fixed-`G` passage and installs the
parsimony-vs-maximum-likelihood contrast and the open question in the same
sequence-level slot. [source fact + interpretation]

The same group’s native likelihood is also sequence-valued and same-length:
Bresler–Bresler–Tse (2013), Theorem 1 states that an unbridged problematic repeat
yields “another **sequence `s'` of the same length** under which the likelihood of
observing the reads is the same,” and the Shomorony supplement restates this for
`s' ≠ s` with the same likelihood. [source fact]

## 6. Even the §6.2-restricted sequence-level implication is refuted

Make the §6.2 reading as strong as possible: restrict candidates to spelled
molecules, so they induce admissible §6.2 flows (MB Observation 7), and use the
literal §6.1 fixed-`N` binomial objective. The repository already has a
kernel-checked counterexample:

```text
truth S = AAATT (00011), G = 5, L = 3, N = 5, reads starts (0,1,4), n = 3
observed x      = { AAA:1, AAT:1, TAA:1 }
truth flow d_S  = { AAA:1, AAT:2, TAA:2 }        (x ≤ d_S)
competitor D    = AAAATT (000011), d_D = { AAA:2, AAT:2, TAA:2 }
strict I_s holds; L_{6.1}(D)/L_{6.1}(S) = 9/8 > 1.
```

Both `S` and `D` are spelled by their cyclic length-3 window walks, hence are
admissible §6.2 candidates by Observation 7, and both satisfy the §6.2 lower
bound `1` per observed vertex. The main theorem
`AssemblyP1.Section62LowerBoundOneCounterexample.se62_lower_bound_one_counterexample`
kernel-checks `SourceCertificate ∧ FeasibleType dS obs ∧ FeasibleType dD obs ∧
lik obs dS < lik obs dD`. [mathematical fact + verified computation +
kernel-checked]

**Consequence.** §6.2 feasibility is not a hidden necessary condition whose
imposition would preserve the implication. Under the corrected lower-bound-`1`
bidirected reading the implication is false. (The exact-multinomial §6.2 slice is
not separately kernel-checked here; the same-length exact witnesses already
refute the exact objective by candidate-set inclusion.) [source reading +
mathematical fact]

## 7. Decision table

| 2016 referent | Is §6.2 feasibility needed? | Why |
|---|---|---|
| (1) exact multinomial, candidate-intrinsic `N(D)`, over sequences | **No** | §6.2 is an algorithmic relaxation; the exact objective is defined on `D`. Witnesses apply by inclusion. |
| (2) §6.1 fixed-`N` binomial, over sequences | **No** | sequence-level objective; §6.2 only realizes it. Witness applies directly. |
| (3) §6.2 flow optimization | Referent itself, **but not selected by any source**; and its sequence-level restriction is **refuted** (§6) | phrase says “sequence”; MB call §6.2 the algorithm. |
| (4) broad ML principle | **No** | no fixed objective, so no feasibility constraint can settle it. |

Therefore the source-faithful settlement does **not** require exhibiting a
§6.2-feasible witness as a separate obligation. The remaining obligations are
source-fixing the probability model and the length/tie conventions.
[source reading + interpretation]

## 8. Reconciliation with the earlier repository positions

- `shomorony-mb-formulation-provenance.md` §7 concluded that “the §6.2
  feasibility work remains essential rather than optional,” on the ground that
  the residual gap was the circular-candidate vs §6.2-flow universe. That
  conclusion predates the sequence-quantifier/version-edit argument of
  `shomorony-ml-quantifier-sequence-resolution.md` and the kernel-checked §6.2
  determination of commit `65d9ea6`. The §6.2 packet was **valuable** — it
  produced the robustness witness — but it is not **logically necessary** for
  the published question as phrased. [interpretation]
- `mb-formulation-referent-reconciliation.md` §7 correctly leaves readings (3)
  and (4) open as *referents*. This note agrees that the source does not select
  (3); it adds that (3), read at the sequence level, is already refuted, so
  “open” there does not block a negative settlement of the sequence-level
  question. [interpretation]

## 9. What remains genuinely open

1. **Probability model:** exact intrinsic-`N(D)` multinomial vs §6.1 fixed-`N`
   product of binomials. The accepted text fixes neither. [open]
2. **Candidate length:** arbitrary circular candidates vs same-length as the
   truth. The group’s native comparison is same-length (BBT 2013), but the
   accepted text does not state it. [open]
3. **Tie semantics:** truth is *a* maximizer vs every maximizer is the truth up
   to genome equivalence. [open]
4. **Publisher supplement:** the accepted supplementary ZIP (sections A–G)
   remains uninspected (HTTP 403); it is the only unexamined accepted artifact
   that could name a §6.2/likelihood object. If it did, the §6.2 question would
   have to be revisited — though §6 already shows it would not by itself save the
   implication. [open]

## 10. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| The 2016 phrase carries no MB09 section/equation/formula pointer | source fact | accepted text §5 + full-text scan |
| The 2016 sentence quantifies over “the maximum-likelihood sequence” | source fact | accepted text §5 |
| MB09 §6.2 returns a non-contiguous flow; sequences come from a §7 heuristic | source fact | MB09 §6.2, §7; short version §2.3 |
| MB09’s own ML method is flow-valued (“find a flow that minimizes −log L”) | source fact | `medvedev_brudno_short.pdf` §2.3 |
| The accepted sentence replaces a “GHC of a desired length `G`” discussion | source fact | `nsgIlan.pdf` Discussion |
| The group’s native likelihood competitor is a same-length sequence | source fact | BBT 2013 Theorem 1; supplement Theorem 2 |
| §6.2 is not the direct referent of “maximum-likelihood sequence” | source-supported inference | §4–§5 |
| The §6.2-restricted sequence-level implication is false | mathematical fact + kernel-checked | §6, `65d9ea6` |
| §6.2 feasibility is not genuinely necessary for the published question | source reading + interpretation | §7 |
| Probability model, length, tie semantics remain open | source gap | §9 |

## 11. Locators

- I. Shomorony, S. H. Kim, T. A. Courtade, D. N. C. Tse, “Information-optimal
  genome assembly via sparse read-overlap graphs,” *Bioinformatics* 32(17) (2016)
  i494–i502, DOI `10.1093/bioinformatics/btw450`; Discussion printed p. i501;
  Introduction printed p. i494.
- Author-hosted version + appended supplement,
  `https://web.stanford.edu/~gkamath/nsgIlan.pdf`; Discussion PDF pp. 16–17;
  supplement §6.4 / Theorem 2, PDF p. 23.
- P. Medvedev, M. Brudno, “Maximum Likelihood Genome Assembly,” *J. Comput.
  Biol.* 16(8) (2009) 1101–1116, §6.1–6.2, §7, §8.2, PMC3154397.
- P. Medvedev, M. Brudno, short/conference version, §2.3 (“Maximizing the Global
  Read-Count Likelihood”), `cs.toronto.edu/~brudno/medvedev_brudno_short.pdf`.
- G. Bresler, M. Bresler, D. Tse, “Optimal assembly for high throughput shotgun
  sequencing,” *BMC Bioinformatics* 14(Suppl 5):S18 (2013), Theorem 1.
