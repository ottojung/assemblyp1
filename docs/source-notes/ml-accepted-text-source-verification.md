# Shomorony et al. accepted-text source verification and the §6.1/§6.2 relation

_Status: independent primary-source verification, 2026-09-19. Independently
re-retrieves and reads the **accepted** Shomorony et al. (2016) main text and
re-reads Medvedev–Brudno (2009) §6.1–§6.2, then records exactly what the
sources do and do not support about which maximum-likelihood object the 2016
open question intends. No new computation; does not touch the issue #32
binomial-marginal audit or any counterexample search._

This note closes the provenance limitation recorded in
`docs/source-notes/ml-objective-candidate-class-resolution.md:38-51,294-309`
(§1.2, §11 item 6): the accepted version had not been independently re-fetched.
It does not change that note's substantive conclusion; it re-grounds it on a
directly retrieved accepted text and adds the precise §6.1→§6.2 relation.

## 1. Independently retrieved accepted-version copies

Oxford Academic still returns HTTP 403 to the available retrieval paths
(`https://academic.oup.com/bioinformatics/article/32/17/i494/2450650` and the
`btw450_supplement.zip`/article-pdf endpoints). The accepted **main text** is
nonetheless independently retrievable through author-hosted copies:

| Copy | URL | Identity |
|---|---|---|
| Publisher-formatted accepted article | `https://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf` | 9 pages, PDF footer `Downloaded from https://academic.oup.com/bioinformatics/article-abstract/32/17/i494/2450780 ... on 26 June 2018`; SHA-256 `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043ac3fce3c4da` |
| Author accepted manuscript | `https://people.eecs.berkeley.edu/~courtade/pdfs/NSG.pdf` | 8 pages, header `MANUSCRIPT Pages 1–8`, pdfTeX `CreationDate D:20160506120616-07'00'`; SHA-256 `daeb5b3163d92643affc2398a387217cb57e5e33ce0dd5ebbfccabf621454f2c` |

The earlier author-hosted preprint already in the repository
(`https://web.stanford.edu/~gkamath/nsgIlan.pdf`, SHA-256 `f2a9f6a6…`)
is a **third, earlier** version and is not one of these. The existence of three
distinct author-hosted versions (preprint "Optimal Sequence Assembly…",
May-2016 accepted manuscript, publisher-formatted accepted article) must not be
collapsed when citing "the 2016 paper."

## 2. Verbatim accepted open-question paragraph

Section 5 (Discussion, final paragraph), publisher-formatted accepted text
(`InfoOptimalAssy.pdf`, p. i501–i502), read end to end:

> "Another direction for future work, from a more theoretical standpoint, is
> understanding whether, in information-feasible instances, the output of
> NOT-SO-GREEDY coincides with the solution of a combinatorial optimization
> problem. Notice that while Theorem 1 guarantees the reconstruction of the
> true sequence `s`, there is no guarantee that this sequence corresponds to the
> solution of an optimization-based formulation of the AP such as those
> considered by Nagarajan and Pop (2009) and Medvedev and Brudno (2009). As
> mentioned by Medvedev and Brudno (2009), parsimony-based formulations tend to
> encourage an over-collapsing of the repeats, and the optimal solution is in
> general different from the true underlying sequence. **The maximum-likelihood
> formulation of the AP (Medvedev and Brudno, 2009), on the contrary, seems to
> be robust to these issues, and thus a good candidate for the ‘correct’
> formulation. Understanding whether bridging conditions can be used to
> guarantee that the maximum-likelihood sequence is the true sequence is
> currently an open question.**"

The May-2016 accepted manuscript (`NSG.pdf`, p. 7) carries the same passage with
only copy-editing differences: "The maximum likelihood formulation of the AP
[8]", "a good candidate for the "correct" formulation", and "maximum likelihood
sequence". The open-question sentence itself is byte-for-byte substantively
identical across the two accepted copies.

## 3. What the accepted main text does and does not contain

A full-text scan of the accepted article for the strings `likelihood`,
`maximum likelihood`, `maximum-likelihood`, `multinomial`, `binomial`,
`copy count`, and `flow` establishes:

- `likelihood` occurs only in the Discussion passage above and in the
  Medvedev–Brudno reference title. There is **no** likelihood formula, **no**
  `multinomial`, **no** `binomial`, and **no** copy-count/flow ML discussion
  anywhere in the accepted main text.
- The phrase used to name the target is **"the maximum-likelihood formulation
  of the AP"** — an optimization-based *formulation of the Assembly Problem*,
  contrasted explicitly with "parsimony-based formulations." It is not named as
  an equation, a section pointer, or a variant of Medvedev–Brudno.
- The stated reason it is "a good candidate for the 'correct' formulation" is
  that it "seems to be robust to" the over-collapsing of repeats. That is a
  qualitative appeal to the *purpose* of Medvedev–Brudno's copy-count
  likelihood, not a selection among that paper's exact multinomial, its
  binomial approximation, or its §6.2 flow algorithm.
- No candidate class, no competitor length, no equivalence relation, and no
  tie/uniqueness convention is stated.

So the accepted main text **cannot** disambiguate the ML layer. This confirms,
on independently retrieved accepted text, the conclusion already recorded in
`docs/source-notes/shomorony-ml-reference.md:50-83` and
`docs/source-notes/ml-objective-candidate-class-resolution.md:294-309`.

### Accompanying §2 model (independently re-read)

The same accepted text fixes the data-generating model. Its Preliminaries
(§2) state the genome `s` has length `|s| = G`, that "each of the `N` reads is
drawn independently and uniformly at random from the set of length-`L`
substrings of `s`", and that `s` is treated as "a circular sequence of length
`G` ... `s[t+G] = s[t]`". Theorem 1's conclusion is `st(c_s) = s` "up to cyclic
shifts", and the paper's information-feasible set is defined as

```
I_s = { R : R covers s ;
             triple repeats in s are all-bridged ;
             interleaved repeats in s are bridged }.
```

(Exactly the three conjuncts already recorded in
`docs/bridging-source-semantics.md`; the accepted text also notes Theorem 1
itself needs only coverage + all-bridged triple repeats, while `I_s` is the
stronger set tied to the information-feasible region.)

## 4. Notation collision between the two sources (source-fidelity hazard)

The two papers overload symbols differently and this is easy to import
incorrectly into a formal statement:

| Quantity | Shomorony et al. (2016) | Medvedev–Brudno (2009) §6.1 |
|---|---|---|
| Number of reads / trials | `N` | `n` |
| Genome (candidate) length | `G` (true length) | `N` = `N(D)` (candidate's own length) |
| Read length | `L` | `k` (k-molecule) |

In particular, the repository's `literature-status.md` uses `N` for the read
count and `G` for the true length (the Shomorony convention). Under the
Medvedev–Brudno convention `N` is the candidate genome length and the binomial
approximation's external fixed constant. A formalization that mixes the two
conventions silently would misinterpret the §6.1 objective. This is a
notation hazard only; it is not an ambiguity in either source.

## 5. Relation exact multinomial → binomial approximation → §6.2 flow (source facts)

Re-reading Medvedev–Brudno §6.1–§6.2 (PMC3154397) supplies the precise chain,
which the 2016 text does not itself restate:

1. **Exact global read-count likelihood (§6.1, first half).** "Let `D` be a
   circular genome of length `N(D)`, and let `d_i` denote the number of times
   the k-molecule `i` appears in `D`." A trial samples a start uniformly in `D`
   and yields type `i` with probability `d_i/N(D)`; the joint counts are
   multinomial with constraint `N(D) = Σ_i d_i`. The denominator is the
   **candidate's own length**.
2. **Binomial approximation (§6.1, second half).** Because the multinomial is
   not separable in the `d_i`, the authors approximate it by a product of
   binomials: "in the binomial approximation the length of the genome `N(D)` is
   a constant that is independent of each `d_i`, we can replace it by `N`,
   which is the length of the actual genome from which the reads were sampled",
   with `c_i(d_i) = -(x_i log d_i) - (n - x_i) log(N - d_i)`. This is an
   explicit change of probability model (fixed external `N`), introduced for
   tractability.
3. **§6.2 optimization is downstream of the approximation.** The algorithm builds
   the transitively reduced **bidirected overlap graph on the reads**,
   adds lower bound 1 on every read vertex, and solves a **convex min-cost
   biflow** whose vertex costs are the `c_i` from step 2. Source text: "By
   Observation 7, the `d_i`'s described above actually correspond to the value
   of the flow through vertex `i`, and we let `c_i` be the convex cost functions
   for the vertices." and "Since any flow can be decomposed into a collection of
   walks, our flow represents a (non-contiguous) assembly of the genome, and the
   flow going through each vertex represents the number of time the read is
   present in the assembly."

Consequences (source-supported):

- §6.2 is **not** a third independent likelihood objective. It is the
  approximate (separable/binomial) objective optimized over read-derived graph
  flows. Its feasible objects are flows with read-vertex lower bounds and a
  non-contiguous-assembly interpretation, not "all circular genomes `D`" of
  §6.1.
- Therefore the three repository variants are not on equal footing as readings
  of the source phrase. The exact multinomial is the paper's *definition* of the
  likelihood; the binomial is explicitly labelled an approximation; §6.2 is the
  *algorithm* that optimizes the approximation. This ordering is a source fact,
  but it still does **not** tell us which object the 2016 open question intends,
  because the 2016 text names only the bibliography.
- A proof or counterexample over the §6.2 flow set is a statement about the
  approximate objective on a restricted feasible set. It is not automatically a
  statement about the exact multinomial over circular genomes, in either
  direction, without a separate correspondence argument.

## 6. Accepted supplement remains unretrieved

The accepted article cites "Supplementary Material A–G" (sections A, B, D, E, F,
G are named in the main text). Oxford exposes it as
`bioinformatics_32_17_i494_s1.zip` / `btw450_supplement.zip`, and the available
retrieval paths still return HTTP 403 (also at the `oup.silverchair-cdn.com`
backfile path). The author-hosted copies retrieved here are main text only and
do not include the supplement. So the accepted supplement has still not been
independently inspected, and it remains the one unexamined primary-source
artifact that could, in principle, add wording about the likelihood model.

## 7. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| Accepted 2016 open-question sentence and its full paragraph | **Source fact (independently verified)** | `InfoOptimalAssy.pdf` SHA-256 `ec17b16f…`; corroborated by `NSG.pdf` SHA-256 `daeb5b31…` |
| Accepted main text contains no likelihood formula and no exact/approx/flow selection | **Source fact** | Full-text scan of `InfoOptimalAssy.pdf`; only Discussion occurrence + reference title |
| Accepted §2 sampling: `N` reads length `L`, uniform over circular length-`L` windows of length-`G` `s`; conclusion up to cyclic shift | **Source fact** | `InfoOptimalAssy.pdf` §2 and Theorem 1 |
| `I_s` = coverage ∧ all-bridged triple repeats ∧ bridged interleaved pairs | **Source fact** | `InfoOptimalAssy.pdf` §2/§3 |
| Exact multinomial has candidate-dependent `N(D)`; binomial approximation replaces it by external `N`; §6.2 optimizes the approximation as a read-overlap biflow | **Source fact** | Medvedev–Brudno §6.1–§6.2, PMC3154397 |
| §6.2 is downstream of the binomial approximation, not a third exact likelihood | **Source reading (well supported)** | §6.2 uses the `c_i` of §6.1 and read-vertex flows |
| Which ML layer the 2016 sentence intends | **Unresolved source ambiguity** | Accepted text names only the bibliography |
| Candidate universe / length for the intended objective | **Unresolved source ambiguity** | Not stated in the accepted text |
| Tie/uniqueness and reverse-complement equivalence | **Unresolved source ambiguity** | Not stated in the accepted text |
| Accepted supplement contents | **Not retrieved** | OUP and silverchair-cdn return 403 |

## 8. Consequences

1. The provenance limitation in
   `docs/source-notes/ml-objective-candidate-class-resolution.md` is closed for
   the accepted **main text**; the accepted supplement limitation remains open.
2. The strongest source-supported statement about "which ML formulation is
   intended" is still a **disjunction**: the 2016 sentence names the
   Medvedev–Brudno maximum-likelihood formulation by bibliography only. The
   repository must keep naming its ML layer, candidate universe, equivalence,
   and conclusion schema in every theorem, as already required by
   `docs/ml-formalization-contract.md`.
3. Any claim that the published question "really means" the exact multinomial
   (or the approximation, or the flow set) is an interpretation, not a source
   fact. The source-supported ordering (definition vs. approximation vs.
   algorithm) may guide which is the most literal reading, but it does not
   select one.
