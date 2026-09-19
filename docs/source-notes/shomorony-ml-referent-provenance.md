# Shomorony et al. open question: primary-source provenance of the ML referent

_Status: independent source note, 2026-09-19. Independently re-retrieves and
reads the primary sources, records the source facts versus the interpretation,
and states which Medvedev–Brudno maximum-likelihood object the 2016 phrase can
most defensibly be taken to denote. It does not settle the published open
problem and it deliberately leaves the parallel formalization variants intact._

## 0. Scope and relation to existing notes

This note answers one question: when Shomorony, Kim, Courtade and Tse (2016)
ask whether bridging conditions guarantee that "the maximum-likelihood sequence
is the true sequence," which Medvedev–Brudno (2009) object is the published
question *justified* to mean?

It is not a substitute for, and does not contradict:

- `docs/source-notes/medvedev-brudno-candidate-class.md` (the exact objective,
  the fixed-length approximation, and the §6.2 flow set are distinct);
- `docs/source-notes/shomorony-ml-reference.md` (the accepted 2016 text names the
  referent only by bibliography);
- `docs/ml-formalization-contract.md` (the variant discipline).

It independently reproduces the source readings also reached on the unmerged
branches `agent/source-provenance-0919b` (`shomorony-open-question-denotation.md`)
and `agent/ml-layer-source-verification` (`ml-objective-candidate-class-resolution.md`),
and adds: (a) a retrieval-verification ledger, (b) a finer reading of what
"robust to these issues" does and does not claim, and (c) an explicit note on how
the repository's existing finite counterexamples interact with the referent
determination. It does **not** duplicate the binomial kernel-check packet
(issue #32).

## 1. Independent retrieval-verification ledger

Every quotation below was extracted by this note's own retrieval, using a
different extraction toolchain (`pypdf`) than the notes it reconciles. The
SHA-256 values are byte-level fingerprints of the retrieved PDFs.

| Source | URL | SHA-256 | This run |
|---|---|---|---|
| Shomorony et al. accepted (publisher-formatted) | `https://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf` | `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da` | retrieved, read |
| Shomorony et al. accepted manuscript | `https://people.eecs.berkeley.edu/~courtade/pdfs/NSG.pdf` | `daeb5b3163d92643affc2398a387217cb57e5e33ce0dd5ebbfccabf621454f2c` | retrieved, read |
| Shomorony et al. earlier author-hosted preprint | `https://web.stanford.edu/~gkamath/nsgIlan.pdf` | `f2a9f6a64f75cbf4c2cfaec6f794c779907f165c986261bec7a2aa72a3e6954a` | retrieved, read |
| Medvedev–Brudno (2009) | `https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/` | HTML body retrieved | retrieved, read |

The three PDF hashes match the values recorded independently on the unmerged
`agent/ml-layer-source-verification` and `agent/source-provenance-0919b` branches,
so all branches are reading the same artifacts.

The accepted Oxford article, its article PDF, and the `oup.silverchair-cdn.com`
supplement endpoints each return **HTTP 403** to this run's retrieval path
(re-confirmed 2026-09-19). The accepted publisher supplement therefore remains
the one primary artifact not inspected here.

## 2. Source facts

### 2.1 The accepted open-question paragraph

`InfoOptimalAssy.pdf` §5 (Discussion), and substantively the same in `NSG.pdf`:

> "Another direction for future work, from a more theoretical standpoint, is
> understanding whether, in information-feasible instances of the AP, the output
> of Not-So-Greedy coincides with the solution of a combinatorial optimization
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

"AP" is the paper's abbreviation for assembly problem. A full-text scan of the
accepted main text finds `likelihood` (3 occurrences: two inside this passage,
one in the Medvedev–Brudno bibliography entry), `multinomial` (0), `binomial`
(0), and no section/equation pointer into Medvedev–Brudno. The referent is a bare bibliographic citation.

### 2.2 The accepted bridging hypothesis `I_s`

Same paper, §3, displayed equation (1):

```text
I_s = { R : R covers s;
              triple repeats in s are all-bridged;
              interleaved repeats in s are bridged }.
```

The paper also states Theorem 1 under the weaker hypothesis (coverage + all
triple repeats all-bridged) and reconstruction "up to cyclic shifts." `I_s` is
described as "nearly match[ing] the set of information-feasible instances of the
AP (for most genomes considered)." The data model is a circular sequence of
length `G` with reads of common length `L` sampled independently and uniformly.

### 2.3 Medvedev–Brudno §6.1: exact global read-count likelihood

`PMC3154397` §6.1:

> "Let D be a circular genome of length N(D), and let d_i denote the number of
> times the k-molecule i appears in D. ... In each trial, a position is uniformly
> sampled from D and the outcome of the trial is the k-molecule beginning at that
> position. For a given i, the probability that the outcome of a single trial is
> i is simply d_i/N(D). ... When taken together, their joint distribution is
> exactly the multinomial distribution ... we can consider the likelihood of the
> parameters of the distribution (d_i) given the outcome of the trials (x_i),
> which we call the **global read-count likelihood**."

with the multinomial constraint `N(D) = Σ_i d_i`. The paper states the algorithm
"finds the genome that maximizes the global read-count likelihood."

### 2.4 Medvedev–Brudno §6.1: the separable/binomial approximation

Immediately after, MB introduce the approximation that makes the objective
separable:

> "Because the number of trials (sampled k-molecules) is typically large, we can
> approximate the multinomial distribution as the product of the individual
> binomial distributions of each X_i. Since in the binomial approximation the
> length of the genome N(D) is a constant that is independent of each d_i, we can
> replace it by N, which is the length of the actual genome from which the reads
> were sampled. ... For our experiments, we assume that the genome size is
> known."

The approximation retains the `(1 - d_i/N)^(n-x_i)` marginals and changes the
probability model, not merely the notation.

### 2.5 Medvedev–Brudno §6.2: the flow feasible set

The optimization is a bidirected min-cost flow on the transitively reduced
read-overlap graph, with "a lower bound of 1" on each read vertex. MB write:

> "Since any flow can be decomposed into a collection of walks, our flow
> represents a (non-contiguous) assembly of the genome."

### 2.6 Medvedev–Brudno framing

MB's abstract:

> "we propose a maximum likelihood framework for assembling the genome that is
> the most likely source of the reads, in lieu of the standard maximum parsimony
> approach ... In this setting, we give a bidirected network flow-based algorithm
> that, by taking advantage of high coverage, accurately estimates the copy
> counts of repeats in a genome."

The paper thus separates the ML *framework/objective* from the flow *algorithm*
that operationalizes it.

### 2.7 The version fork

The earlier author-hosted preprint (`nsgIlan.pdf`, PDF `CreationDate`
`D:20160123235649`) does **not** contain the accepted open-question sentence
(`open question` 0 occurrences; no `maximum-likelihood sequence`). Its
Introduction instead contains the authors' own, one-version-earlier vocabulary:

> "To circumvent this issue, [8] proposed a maximum likelihood (ML) formulation
> for assembly. While such a formulation prevents the over-collapsing of repeats,
> devising algorithms to find the ML sequence given the read data is a daunting
> task, and existing approaches rely on the assumption of high coverage [8]."

Its Discussion replaces the accepted ML sentence with a discussion of a
"genie-aided formulation where the target genome length G is given," which "excludes
the possibility of shrinking the sequence by compressing repeats," and a
Hamiltonian-cycle complexity remark. The accepted version keeps the circular
exposition but replaces this fixed-`G` discussion with the ML open question.

The accepted Oxford text is the controlling source; the preprint is earlier
version evidence.

### 2.8 Bresler et al. (2013) ties

Bresler–Bresler–Tse Theorem 1: if an interleaved pair or triple repeat has all
copies unbridged, then there is another sequence `s'` **of the same length** with
the same read likelihood. Ties are a source-demonstrated phenomenon.

## 3. Determination: what the published question can be justified to mean

Each item below is labelled with its epistemic class.

1. **The referent is an objective, not the flow algorithm (interpretation,
   strongly supported).** The sentence contrasts "parsimony-based formulations"
   with "the maximum-likelihood formulation." Both are optimization objectives
   for the AP; §6.2 is the algorithm that optimizes the approximation, and MB
   themselves call its output a "(non-contiguous) assembly," not a sequence. The
   earlier version's "ML formulation for assembly" versus "algorithms to find the
   ML sequence" reproduces exactly this distinction.

2. **Most defensible referent: the exact global read-count multinomial over
   circular candidate genomes with candidate-intrinsic length (repository
   Variant E) (interpretation).** Reasons: MB name this object as the target and
   reserve the word "approximate" for the binomial; the 2016 phrase says
   "formulation," not "algorithm"; the conclusion is about a "sequence"; and the
   earlier version separates the formulation from the algorithm.

3. **Second reading: the binomial/separable approximation (interpretation).**
   A reader who identifies "the MB formulation" with what MB's published
   algorithm actually optimizes lands here. Not excluded, but weakened by MB's
   own labelling and its fixed external `N`.

4. **Least defensible referent: the §6.2 flow feasible set (interpretation).**
   Its objects are read-graph flows with read-vertex lower bounds and a
   non-contiguous interpretation, not arbitrary circular sequences.

5. **Candidate length is not fixed by the 2016 text (source fact + reading).**
   The exact §6.1 objective uses the candidate's own `N(D)`; no fixed competitor
   length appears. Fixed length in 2016 appears only as the *data-generating*
   true `G`, and in the *earlier* preprint as a separately named genie-aided
   formulation. Fixed-length is therefore a named restriction, not a default.

6. **Genome equivalence: cyclic shift is required; reverse complement is
   unresolved (source fact + reading).** 2016 reconstruction is "up to cyclic
   shifts"; MB model double strands with bidirected graphs; Bresler uses a
   length-`2G` single-strand concatenation. The 2016 open-question text does not
   select the equivalence.

7. **Conclusion semantics: maximizer-only versus unique-up-to-equivalence is
   unresolved (source fact + reading).** The English sentence supplies no tie
   rule, and Bresler's equal-likelihood same-length construction shows ties are
   real, so the two schemas must remain distinct.

### 3.1 What "robust to these issues" does and does not claim

This is a refinement of the ranking, not a new source fact. Shomorony's "robust
to these issues" refers back to the immediately preceding clause: parsimony
"encourage[s] an over-collapsing of the repeats, and the optimal solution is in
general different from the true underlying sequence." "Over-collapsing" is
*shortening* by compressing repeats. The sentence therefore claims that the ML
objective does not systematically prefer the collapsed (shorter) genome; it is
not a claim of global optimality against *all* candidate lengths. This:

- supports the variable-length reading (a fixed-`G` formulation would make
  over-collapsing impossible by construction, and the earlier version treated
  fixed `G` as a separate genie-aided model); and
- does not conflict with a length-*increasing* competitor, which is exactly the
  mechanism of the repository's existing finite counterexamples.

## 4. Interaction with the repository's existing finite certificates

This note does not settle the open problem, and the following is stated to keep
the provenance and the certificates epistemically aligned rather than to upgrade
either.

Under the most defensible referent (item 2), the repository already records a
finite obstruction on `main`:

- `docs/exact-variant-e-counterexample.md`: true `S = ACGT` of length `G = 4`,
  read length `L = 2`, reads `{AC, AC, GT}`, competitor `D = ACACGT` of length 6,
  with exact likelihood `L(D) = 1/18 > 3/64 = L(S)`. `S` has no repeats, so the
  `I_s` bridging clauses are vacuous and only coverage is used.
- `docs/fixed-length-exact-counterexample.md` and
  `docs/fixed-length-binomial-counterexample.md`: same-length competitors also
  defeat the fixed-length exact objective and the literal binomial
  approximation. The exact same-length one is kernel-checked.

Two honest conclusions follow, and both must be stated together:

1. If "the maximum-likelihood formulation" is taken to mean the exact global
   read-count likelihood over circular candidates of unrestricted length, then
   the most defensible referent of the 2016 question is a proposition the
   repository has already refuted by an explicit finite instance.
2. This is **not** a settlement of the published question. The accepted 2016
   text does not uniquely select the exact objective, its candidate universe, or
   its conclusion semantics, and the accepted publisher supplement remains
   unretrieved. Under AGENTS.md and `docs/research-orchestration.md`, a
   counterexample only settles the published problem once the repository
   documents why the formal assumptions and conclusion match the published
   statement. That correspondence is precisely what is still missing.

The tension is real and should stay visible: the source reading most favorable
to the published question being well-posed also happens to be the reading under
which the repository's finite certificates already answer it negatively. The
remaining genuinely unrefuted layer is the §6.2 flow feasible set (Variant F),
which §3 argues is also the least plausible reading of the 2016 phrase.

## 5. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| Accepted 2016 paragraph, `I_s` equation, and absence of any formula/section pointer | **Source fact** | `InfoOptimalAssy.pdf`, `NSG.pdf` |
| MB exact multinomial `d_i/N(D)`, product over all types, `N(D)=Σ d_i` | **Source fact** | `PMC3154397` §6.1 |
| MB binomial approximation replaces `N(D)` by external `N` and assumes known genome size | **Source fact** | `PMC3154397` §6.1 |
| MB §6.2 feasible objects are read-graph flows, output is a non-contiguous assembly | **Source fact** | `PMC3154397` §6.2 |
| MB separate the ML framework from the flow algorithm | **Source fact** | MB abstract, §6 |
| Earlier preprint says "ML formulation for assembly" versus "algorithms to find the ML sequence," and lacks the accepted open-question sentence | **Source fact** | `nsgIlan.pdf` |
| Bresler Theorem 1 yields a same-length equal-likelihood competitor | **Source fact** | `PMC3706340` Theorem 1 |
| The referent is an objective, not the flow algorithm | **Interpretation** | contrast of "formulations"; MB framing; preprint |
| Exact global read-count multinomial (Variant E) is the most defensible referent | **Interpretation** | items 1–2, §3.1 |
| Approximation is a weaker but not excluded reading | **Interpretation** | MB's actual algorithm optimizes it |
| §6.2 flow set is the least plausible referent | **Interpretation** | non-contiguous flow vs. "sequence" |
| "Robust to these issues" concerns shortening, not global optimality | **Interpretation** | close reading of the surrounding sentences |
| Accepted publisher supplement contents | **Not retrieved (403)** | re-confirmed 2026-09-19 |

## 6. Remaining unresolved items

1. Exact objective vs approximation vs §6.2 flow set as the intended referent.
2. Competitor universe and length (unrestricted vs. fixed `G` vs. copy-count
   vectors vs. flow-feasible objects).
3. Reverse-complement equivalence alongside cyclic shift.
4. Maximizer-only versus unique-up-to-equivalence conclusion.
5. Tie-breaking (absent from both papers).
6. Contents of the accepted publisher supplement.

## 7. Handoff

- **No change to `docs/open-problem.md` is warranted by this note.** The
  ambiguity it records remains the correct status.
- Any theorem or counterexample aimed at the published question must name its ML
  layer, candidate universe, length convention, equivalence relation, and
  maximizer-vs-uniqueness conclusion, and must carry a prose correspondence
  argument, per `docs/ml-formalization-contract.md`.
- The cheapest discriminating source check that remains is the accepted
  supplement; it is HTTP-403-blocked from this environment. A different retrieval
  path (institutional access or a mirror) is the highest-value next packet.
- Reconciliation note: this note agrees with the unmerged
  `shomorony-open-question-denotation.md` and
  `ml-objective-candidate-class-resolution.md` on the ranking and on the
  unresolved items; it adds the retrieval ledger and the "over-collapsing"
  reading. Those branches and this one should be compared proposition-by-
  proposition before either is merged, to avoid landing two competing notes.
