# Candidate-set inclusion and the scope of the same-length Medvedev–Brudno witnesses

_Status: independent primary-source re-check plus a logical correction for issue
#36, 2026-09-20. Corrects one inference in
[`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md)
§7 and one sentence in
[`../fixed-length-exact-counterexample.md`](../fixed-length-exact-counterexample.md).
It does not settle the source ambiguity; it sharpens what the existing
kernel-checked witnesses do and do not reach._

## 0. Summary

1. The three 2016 Shomorony artifacts and the Medvedev–Brudno (2009) full text
   were re-retrieved independently for this note; the PDF hashes match the
   ledger already recorded in `shomorony-mb-formulation-provenance.md` and in
   `primary-provenance-verification.md` on the unmerged branch
   `analysis/issue36-se62-bidirected-flow`, so the readings below are of
   byte-identical artifacts.

2. The source facts in `shomorony-mb-formulation-provenance.md` are
   independently corroborated: the accepted 2016 text names the
   Medvedev–Brudno work only by bibliography and the phrase “maximum-likelihood
   formulation of the AP”, and Medvedev–Brudno (2009) contains at least three
   distinct objects (exact multinomial with candidate-intrinsic `N(D)`, a
   fixed-`N` product-of-binomial-marginals approximation, and the §6.2
   read-overlap-graph flow algorithm).

3. **Correction.** The provenance note’s §7 first bullet says that under
   reading 1 (candidate-intrinsic-`N` exact multinomial over arbitrary circular
   candidates) “the fixed-length exact witness is a *restricted* result
   (competitors constrained to length `G`) and does not by itself answer the
   unrestricted question.” That inference is invalid. The length-`G` candidate
   class is a *subset* of the arbitrary-length class, and a same-length
   competitor that beats the truth belongs to both classes. Hence the witness
   answers the unrestricted question negatively as well. Candidate length is not
   what blocks the reading; the objective and the candidate-universe class are.

4. Consequence. Under reading 1 (exact multinomial over circular candidates) and
   under reading 2 (literal fixed-`N` product of binomial marginals over
   circular candidates), the repository’s existing kernel-checked same-length
   witnesses already refute the “truth is a maximizer” conclusion. The surviving
   obstacles to settlement are reading 3 (the §6.2 flow-feasible class), reading
   4 (the broad, objective-undetermined ML principle), and the
   strand/equivalence/tie choices.

For reading 2 the scope correction of issue #209 applies: the candidate class
must be restricted to `|D| ≤ N`, because the literal binomial marginal is
only a probability model there (see the caveat in §4 below, at the table). Reading 1, whose
objective uses the candidate's own `N(D)`, needs no such restriction.

## 1. Independent re-retrieval (source facts)

Retrieved 2026-09-20 with `urllib` + `pypdf`:

| Artifact | Locator | SHA-256 |
|---|---|---|
| Published OUP-typeset article | `https://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf` | `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da` |
| Author-accepted manuscript | `https://people.eecs.berkeley.edu/~courtade/pdfs/NSG.pdf` | `daeb5b3163d92643affc2398a387217cb57e5e33ce0dd5ebbfccabf621454f2c` |
| Earlier author-hosted preprint | `https://web.stanford.edu/~gkamath/nsgIlan.pdf` | `f2a9f6a64f75cbf4c2cfaec6f794c779907f165c986261bec7a2aa72a3e6954a` |
| Medvedev–Brudno (2009) full text | `https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/` | HTML body (equation images) |

The Oxford publisher article, article PDF, and supplement endpoints again
returned HTTP 403; the publisher supplement remains uninspected. This note adds
no new supplement evidence.

## 2. Corroborated source facts (independent reading)

### 2.1 Accepted 2016 text

Published typeset, Section 5 (Discussion), final paragraph (printed p. i501):

> “The maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009), on
> the contrary, seems to be robust to these issues, and thus a good candidate
> for the ‘correct’ formulation. Understanding whether bridging conditions can
> be used to guarantee that the maximum-likelihood sequence is the true sequence
> is currently an open question.”

A full-text scan of the 9-page typeset article finds three `likelihood`
occurrences (two in this paragraph and the reference title), zero
`multinomial`/`binomial`, one `open question`, and no section/equation/page
pointer into Medvedev–Brudno. The assembly problem’s true genome is fixed to
length `G` in the data-generating model (Section 2, p. i496), but the sentence
says nothing about the length of a maximum-likelihood *competitor*.

### 2.2 Medvedev–Brudno (2009)

§6.1 defines the exact multinomial with candidate-intrinsic `N(D)` and calls the
target the “global read-count likelihood”; the same section then explicitly
replaces `N(D)` by the actual genome length `N` and states “For our experiments,
we assume that the genome size is known”; §6.2 gives the read-overlap-graph
biflow whose output “represents a (non-contiguous) assembly of the genome”. The
exact quotes are recorded in
[`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md)
§4 and need not be repeated.

### 2.3 Preprint formulation/algorithm split

The earlier author-hosted preprint (Introduction) distinguishes “a maximum
likelihood (ML) formulation for assembly” from “algorithms to find the ML
sequence”. This is version evidence that “formulation” denotes the objective,
not the concrete §6.2 algorithm. It does not select between the exact
multinomial and the fixed-`N` approximation.

## 3. Candidate-set inclusion: negative results transfer, positive results do not

This is the only mathematical ingredient the correction needs.

**Lemma (negative transfer).** Let `X` be an observed read multiset and let
`L(· | X)` be an objective defined on a candidate class `C`. If `C' ⊆ C`,
`S ∈ C'`, `D ∈ C'`, and `L(D | X) > L(S | X)`, then `S` is not a maximizer of
`L(· | X)` over `C`.

**Proof.** Since `D ∈ C`, the maximum of `L(· | X)` over `C` is at least
`L(D | X)`, which is strictly greater than `L(S | X)`. ∎

The converse direction fails: a *positive* result over the restricted class
(`S` maximizes `L` over `C'`) does not imply the same over the larger class `C`,
because `C` may contain a better candidate. This asymmetry is exactly why the
repository rule “a theorem over a restricted candidate class is a restricted
result, not a settlement” is correct for **positive** theorems, and must not be
applied to **negative** counterexamples.

In the present case:

- `C'` = circular genomes of length `G`;
- `C` = all nonempty circular genomes (or all genomes for which the objective is
  defined);
- the same-length witnesses satisfy `|S| = |D| = G`, so both lie in `C'` and
  hence in `C`.

## 4. Application to the kernel-checked witnesses (mathematical argument + verified computation)

The instances are exactly as recorded in
[`../fixed-length-exact-counterexample.md`](../fixed-length-exact-counterexample.md)
and
[`../fixed-length-binomial-counterexample.md`](../fixed-length-binomial-counterexample.md).
In each, the source `I_s` certificate is non-vacuous (coverage plus an
all-bridged maximal triple repeat, no interleaved pair).

| witness | objective | `\|S\|`, `\|D\|` | ratio | refutes |
|---|---|---|---|---|
| `AAABB → AAAAB` (#31) | exact multinomial, candidate-intrinsic `N(D)` | `5, 5` | `2` | reading 1 `truthIsML` over **all** circular candidates |
| `AAABB → AAAAB` (#31) | literal fixed-`N` product of binomial marginals | `5, 5` | `1125/512 > 1` | reading 2 `truthIsML` over circular candidates with `\|D\| ≤ N` (in particular the length-`G` class) |
| `AAACC → AAAAC` (#32) | literal fixed-`N` product of binomial marginals | `5, 5` | `1125/512 > 1` | reading 2 `truthIsML` over circular candidates with `\|D\| ≤ N` (in particular the length-`G` class) |
| `AAABCBC → AAAAABC` | exact multinomial | `7, 7` | `27` | reading 1 `truthIsML` over **all** circular candidates, with a read-tiled competitor |

**Parameters of the `AAABCBC → AAAAABC` row (recorded by issue #209, second
pass).** This row was previously unparameterized: no read length, no realized
reads, no `I_s` certificate. A working realization is:

* read length `L = 3`;
* truth `S = AAABCBC`, competitor `D = AAAAABC`, both length `7`;
* observed read multiset `AAA`×3, `AAB`, `ABC`, `BCA`, `CAA` (`n = 7`), so the
  start `0` of `S` is used three times;
* distinct realized starts `R = {0, 1, 2, 5, 6}`.

Under this realization the exact-multinomial ratio is `3^3 = 27`. Write
`n!/∏ x_i!` for the observation-only multinomial coefficient, which is
`7!/(3!·1!·1!·1!·1!) = 840` here. The type `AAA` has multiplicity `1` in `S`
and `3` in `D`; every other observed type has multiplicity `1` in both; and the
unobserved types `BCB`, `CBC` are absent from both. Hence

`L_E(D) = 840 · (3/7)^3 · (1/7)^4 = 3240/117649` and
`L_E(S) = 840 · (1/7)^7 = 120/117649`, so `L_E(D)/L_E(S) = 3^{x_{AAA}} = 27`.

`R` covers `S`, and the full
source-faithful `I_s` (including both bridging clauses) holds for
`(S, L, R)` — confirmed by two independently written implementations. Of the
625 observations over `S`'s window types with per-type counts in `0..4` that
give ratio `27`, 256 are fully `I_s`-feasible and 400 give coverage; the
minimal feasible one is the realization above. The row remains **bounded
evidence, not a kernel check** — no Lean theorem states this instance — and it
still places only the competitor in the §6.2 spellable set.

Each entry is a same-length pair, so by §3 its refutation is not confined to the
length-`G` class. The different-length `ACGT → ACACGT` witness of issue #24 is
therefore not needed to negate the unrestricted-length exact-multinomial
statement; its distinct value is to exhibit an *unrestricted-length* competitor
and the length-dependence mechanism, not to establish the negation.

**Caveat that is a length caveat after all, for reading 2 (issue #209).** The
literal binomial marginal `Binom(n, x) (d/N)^x (1-d/N)^(n-x)` is a probability
only when `d ≤ N`, and `d_w ≤ N(D)` for any circular candidate. So with an
external fixed `N` the objective is automatically a product of probabilities on
`|D| ≤ N`, is *not* defined as a probability on the unrestricted class (for
`|D| > N` a read type can have `d_w > N` and the marginal becomes negative:
concretely, a length-6 all-`A` candidate with `N = 5` has `d_AAA = 6` and an
unobserved-type marginal of `(1-6/5)^3 = -1/125`), and between the two lies the
region `{D : ∀ w, d_w ≤ N}` where it happens to be well-defined. The reading-2
rows above are therefore scoped to `|D| ≤ N`, not to all circular candidates.
Under reading 1 (exact multinomial with candidate-intrinsic `N(D)`) no such
restriction exists, and "all circular candidates" is correct. See
[`../issue-209-ea-audit-ledger.md`](../issue-209-ea-audit-ledger.md) §5–§6.

**Caveat that is not a length caveat.** Under reading 1, `D = AAAAB` is an
admissible circular genome because reading 1 imposes no read-overlap-graph
feasibility. Under reading 3 (§6.2), `D` is not a sequence-level feasible object
(windows `ABA` resp. `ACA` are unobserved), so the same pair says nothing there.
Likewise, the exact multinomial candidate class is single-versus-double-strand
parameterized: `AAABB` uses an abstract alphabet, while the real double-stranded
reading changes which objects are §6.2-spellable (see the unmerged branch
artifact `docs/section62-bidirected-flow-feasibility.md` on
`analysis/issue36-se62-bidirected-flow`).
The length axis, however, is closed.

## 5. What still blocks settlement

1. **Reading 3, the §6.2 flow-feasible class.** No current witness has both the
   truth and the competitor in the sequence-level §6.2 feasible set. The
   membership table in the unmerged branch artifact
   `docs/section-6-2-feasible-set-membership.md` on
   `analysis/issue36-se62-bidirected-flow` §3 shows that in every witness either
   the competitor or the truth carries an
   unobserved length-`L` window; in the read-tiled witness only the competitor is
   spellable, so the truth is not even a candidate and the implication is not
   tested. This is a genuine gap, not a length gap. **Update (same-length
   packet).** Under the source-faithful per-vertex reading (support equality) the
   gap is now closed for the same-length sub-case: `S = AAATAT`, `D = AAAAAT`
   (`G = 6`) are both sequence-level §6.2-feasible and same-length, and `D`
   strictly improves the §6.1 objective; see
   [`../section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md).
   The gap remains under the per-occurrence strengthening.
2. **Reading 4, the broad ML principle.** If the phrase denotes an
   objective family rather than one formula, no finite witness settles it,
   because the objective is not fixed by the source.
3. **Strand and genome equivalence.** Cyclic shift is required by the 2016
   circular model; whether reverse complement is quotiented is not resolved
   (Medvedev–Brudno are bidirected/double-stranded, Shomorony is a circular
   string).
4. **Tie semantics.** “the maximum-likelihood sequence” does not distinguish
   truth-is-a-maximizer from all-maximizers-are-truth; #31/#32 refute both for
   their objectives, but the schemas remain distinct for reading 3.

## 6. Exact corrections issued

- `docs/source-notes/shomorony-mb-formulation-provenance.md` §7, first bullet:
  the claim that the fixed-length exact witness “does not by itself answer the
  unrestricted question” is replaced by a pointer to this note’s §3–§4.
- `docs/fixed-length-exact-counterexample.md` “What this refutes and what it
  does not” (the sentence beginning “It does **not** refute unrestricted-length
  exact Variant E”): the length-restriction inference is corrected; the witness
  refutes Variant E’s maximizer claim at every length, and the separate
  different-length witness remains useful only for exhibiting the
  length-dependence mechanism.

Neither correction changes any source fact, the witness arithmetic, or the
repository’s decision to keep the exact/binomial/flow variants distinct.

## 7. Epistemic status

| claim | status |
|---|---|
| Three 2016 artifacts and Medvedev–Brudno full text re-retrieved; hashes match | source fact (verified) |
| Accepted 2016 text names MB only by bibliography; no formula/variant/section pointer | source fact |
| MB (2009) contains the three distinct objects | source fact |
| Negative results transfer from a candidate subclass to any superclass | mathematical proof (§3) |
| #31/#32/read-tiled witnesses refute the maximizer claim over all circular candidates for reading 1, and over the class `\|D\| ≤ N` for reading 2 | mathematical proof + kernel-checked finite instances + §3 (reading-2 scoping added by issue #209; see §4 and its caveat) |
| No current witness has both truth and competitor sequence-level §6.2-feasible | verified computation (membership table) |
| The published question remains unresolved because readings 3–4 and strand/tie are open | source-analysis / open |

Primary sources: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116, §6.1–6.2, PMC3154397; Ilan
Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
Bioinformatics 32(17) (2016) i494–i502, §2 and §5.
