# The 2016 ML open question quantifies over single sequences

_Status: focused evidence note for issue #36, 2026-09-20. It adds material not
present in [`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md),
[`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md),
[`shomorony-ml-reference.md`](shomorony-ml-reference.md), or the citation-context
audit. Source facts are separated from interpretation throughout._

## 0. Bottom line

1. **Source-supported resolution of one axis.** The 2016 open question
   ("binding conditions … guarantee that the maximum-likelihood **sequence** is
   the true sequence") quantifies over **single candidate sequences**. It does
   **not** quantify over Medvedev–Brudno (2009) §6.2 bidirected **flows**, and it
   is not merely an unspecified "principle" divorced from a candidate string.
2. **New discriminator.** The accepted Discussion sentence is a *rewrite* of an
   earlier author-hosted Discussion that explicitly posed the target as a
   single-sequence combinatorial problem — "finding a **GHC of a desired length
   `G`**". The accepted version swapped that objective for the Medvedev–Brudno
   ML objective while keeping the same single-sequence slot. This is stronger
   than the previously recorded "genie-aided fixed-`G`" observation.
3. **Not resolved.** The *probability model* (exact multinomial with
   candidate-intrinsic `N(D)` vs §6.1 product-of-binomial marginals with
   external `N`), the candidate-length convention, and tie semantics remain
   underdetermined by the accepted text.
4. **New supporting slant.** The research line's own notion of likelihood is a
   **same-length sequence** likelihood (Bresler–Bresler–Tse 2013, restated in
   the Shomorony supplement), which favors a fixed-length sequence comparison
   over an arbitrary-length one.

## 1. Source fact: the paper's own type for "optimization-based formulation" is a single sequence

Accepted article, Introduction (printed p. i494; PDF pp. 1–2):

> "A fundamental challenge in assembling from a read-overlap graph is that the
> true sequence corresponds to a Hamiltonian path on the graph, and, under most
> formulations, the assembly problem becomes NP-hard …"

> "As shown in Nagarajan and Pop (2009), if we model the AP as the problem of
> finding the shortest generalized Hamiltonian path or a generalized Hamiltonian
> path of a desired length, we have an NP-hard formulation."

> "The present paper should be understood as following the line of work of
> Medvedev and Brudno (2009), Nagarajan and Pop (2009) and Medvedev et al.
> (2007) in the study of the basic formulation of the AP …"

**Interpretation.** In this paper "optimization-based formulation of the AP"
denotes a **single-sequence** objective (generalized Hamiltonian path), and
Medvedev–Brudno is cited as one member of that family. The Discussion sentence
then says Theorem 1 gives no guarantee that the reconstructed sequence "corresponds
to the solution of an optimization-based formulation of the AP such as those
considered by Nagarajan and Pop (2009) and Medvedev and Brudno (2009)". The
referent is therefore sequence-valued by the paper's own construction.

## 2. New discriminator: the accepted sentence replaces a single-sequence objective

Author-hosted preprint `nsgIlan.pdf`, Discussion (PDF p. 16; printed §5), *before*
the sentential content that the accepted text replaced with the ML question:

> "Furthermore, rather than focusing on devising an algorithm to solve a specific
> optimization-based formulation of the AP (such as the shortest **GHC**, or the
> CPP), we design an algorithm which provably reconstructs the true underlying
> sequence, as long as certain bridging conditions are satisfied."

> "One way to prevent this undesirable property of the optimal solution, is to
> consider a genie-aided formulation where the target genome length `G` is
> given."

Same preprint, PDF p. 17:

> "It is not difficult to see that, like most formulations of the AP, the problem
> finding a **GHC of a desired length `G`** is in general NP-hard (as one could
> use it to solve the Hamiltonian cycle problem). In this context, the results of
> the present paper can be understood as characterizing a set of instances where
> this problem can be solved in linear time."

Same preprint, abstract/Introduction (PDF p. 2), on the cited Medvedev–Brudno work:

> "…[8] proposed a maximum likelihood (ML) formulation for assembly. … devising
> algorithms to find the **ML sequence** given the read data is a daunting task …"

**Source fact.** The authors' earlier version identifies the relevant
combinatorial optimization as a **generalized Hamiltonian cycle/path of a
desired length `G`** — an optimization over a single sequence — and claims their
algorithm solves it on bridging instances. The accepted version **deleted** this
GHC discussion and replaced it with the parsimony-vs-maximum-likelihood contrast
and the open question ([`shomorony-ml-reference.md`](shomorony-ml-reference.md)
§"Author-hosted version"; [`../literature/citation-context-and-referent-audit-2026-09-20.md`](../literature/citation-context-and-referent-audit-2026-09-20.md) §5.2
recorded only the genie-aided sentence, not the GHC target).

**Interpretation (strong).** The accepted open question is the rewrite of a
question about a **single-sequence** objective. Reading the MB09 phrase as the
§6.2 flow — a non-contiguous object — would make the rewritten sentence change
the *type* of the target, not just the objective, which the version evidence
does not support.

## 3. New supporting source: the line's native likelihood is a same-length sequence likelihood

Bresler–Bresler–Tse, *Optimal assembly for high throughput shotgun sequencing*
(2013), §1 (PDF p. 2):

> "… this objective of reconstructing the original DNA sequence from the reads
> contrasts with the many optimization-based formulations of assembly, such as
> shortest common superstring (SCS), maximum-likelihood, and various graph-based
> formulations. When solving one of these alternative formulations, there is no
> guarantee that the optimal solution is indeed the original sequence."

Same paper, Theorem 1 (PDF p. 5):

> "Given a DNA sequence `s` and a set of reads, if there is a pair of interleaved
> repeats or a triple repeat whose copies are all unbridged, then there is
> another **sequence `s'` of the same length** under which the likelihood of
> observing the reads is the same."

Shomorony preprint supplement §6.4, Theorem 2 (PDF p. 23), restating the same result:

> "If a triple repeat in `s` is not bridged or an interleaved repeat in `s` is
> not bridged, then there exists a **sequence `s' ≠ s`** with the same likelihood
> as `s`."

**Interpretation.** In the Shomorony group's own information-feasibility line,
"likelihood" is a function of a **candidate sequence**, and the ambiguity that
bridging conditions control is ambiguity between **same-length** sequences. This
coheres with the fixed-length `G` framing of §2 and with the model of the 2016
paper (§2 fixes a circular `s` of length `G`). It is evidence — not proof — that
the intended ML comparison is a same-length sequence comparison.

## 4. What is resolved and what is not

| Question | Status |
|---|---|
| Does the open question quantify over single sequences? | **Yes** (source-supported; §1–§2) |
| Could it denote MB09 §6.2 bidirected flows? | **No, not directly** (source-supported; §1–§2) |
| Is it a purely unspecified "broad principle"? | Not as the *specific* open question: the phrase names "the maximum-likelihood sequence" and the paper's framing is sequence-valued. A sequence-valued objective *family* with unspecified formula remains possible. |
| Exact multinomial (`N(D)` intrinsic) vs §6.1 binomial (external `N`)? | **Unresolved** by the accepted text |
| Candidate length fixed to the true `G`, or arbitrary? | **Unresolved**, but the group's native comparison is same-length (§3) |
| Tie semantics (truth is *a* maximizer vs *the* unique maximizer)? | **Unresolved**; see [`../literature/ml-tie-semantics.md`](../literature/ml-tie-semantics.md) |

## 5. Consequence for issue #36 and the kernel-checked witnesses

1. The new evidence does not create a settlement, but it removes one source-level
   obstacle. Treating the §6.2 flow class as the referent required an extra
   flow→sequence bridge; the accepted text's own construction and the version
   edit argue that the referent is already a single-sequence objective. So the
   residual is **not** "§6.2 feasibility" but the **probability model and length
   convention**.
2. The repository's same-length witnesses remain directly relevant: the #31 exact
   witness (`AAABB → AAAAB`) refutes the candidate-intrinsic-`N(D)` reading on
   nonempty circular candidates (by candidate-set inclusion); the #32 binomial
   witness (`AAACC → AAAAC`) refutes the literal fixed-`N` product-of-binomial
   objective on its domain. If the intended objective is the group's native
   same-length sequence likelihood, #32 is the closer witness; if it is MB09's
   exact sequence multinomial, #31 is.
3. This note does **not** claim a settled disproof of the published problem. It
   claims the *domain* is single sequences and that the open source question is
   now the formula/length/tie choice, not sequence-vs-flow.

See [`se62-feasibility-necessity-determination.md`](se62-feasibility-necessity-determination.md),
which turns this domain conclusion into the explicit decision that §6.2
feasibility is not a necessary condition and records the kernel-checked
§6.2-restricted witness.

## 6. Exact locators and retrieval

- Accepted article: Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N.
  C. Tse, “Information-optimal genome assembly via sparse read-overlap graphs,”
  *Bioinformatics* 32(17) (2016) i494–i502, DOI
  `10.1093/bioinformatics/btw450`. Locators used: abstract and Introduction,
  printed p. i494 (PDF pp. 1–2); Discussion, printed p. i501 (PDF p. 9).
  SHA-256 `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da`.
- Author-hosted version + appended supplement: “Optimal Sequence Assembly via
  Sparse Read-Overlap Graphs,” `https://web.stanford.edu/~gkamath/nsgIlan.pdf`.
  Locators: abstract/Introduction, PDF p. 2; Discussion, PDF pp. 16–17;
  Supplementary Material §6.4, Theorem 2, PDF p. 23. SHA-256
  `f2a9f6a64f75cbf4c2cfaec6f794c779907f165c986261bec7a2aa72a3e6954a`.
  (The publisher supplement remains HTTP 403; this is the author-hosted
  supplement, not verified byte-identical to the accepted ZIP.)
- Bresler, Bresler, Tse, “Optimal assembly for high throughput shotgun
  sequencing,” BMC Bioinformatics 14(Suppl 5):S18 (2013), arXiv:1301.0068.
  Locators: §1, PDF p. 2; Theorem 1, PDF p. 5.

## 7. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| Accepted Introduction frames AP optimization formulations as (generalized) Hamiltonian path, single-sequence problems | source fact | accepted text, printed p. i494 |
| Accepted Discussion places MB09 among those "optimization-based formulations" | source fact | accepted text, printed p. i501 |
| Preprint Discussion explicitly targets the "GHC of a desired length `G`" problem and says NSG solves it in linear time on bridging instances | source fact | `nsgIlan.pdf`, PDF pp. 16–17 |
| The accepted version replaced that GHC discussion with the MB09 ML question | source fact | comparison of `nsgIlan.pdf` §5 with accepted §5 |
| BBT 2013's ambiguity competitor is a same-length sequence with equal likelihood | source fact | BBT 2013, Theorem 1, PDF p. 5 |
| Shomorony supplement restates that result for `s' ≠ s` | source fact | `nsgIlan.pdf`, PDF p. 23 |
| The 2016 open question quantifies over single sequences | source-supported inference | §1–§2 |
| MB09 §6.2 flow is not the direct referent | source-supported inference | §1–§2 |
| The intended likelihood comparison is same-length | interpretation, supported | §2–§3 |
| Exact-vs-fixed-`N` formula, length, and tie semantics remain open | source gap | accepted text has no formula/length/tie statement |
| No later work settles the question | source-analysis | [`../literature/citation-context-and-referent-audit-2026-09-20.md`](../literature/citation-context-and-referent-audit-2026-09-20.md) |
