# Does the integrated same-length §6.2 witness settle the published question?

_Status: source-fidelity reconciliation for issue #36, 2026-09-20. Re-reads the
primary Medvedev–Brudno (2009) and Shomorony et al. (2016) texts and the
witnesses now integrated on `main` (commits `6256d46`, `8182e1b`). Every claim is
labelled **source fact**, **source-supported inference**, **mathematical fact**,
**verified computation**, **kernel-checked**, or **open**. This note does not
re-run any search and does not select a referent by fiat; it states how far the
integrated witness reaches and corrects stale claims on `main`._

## 0. Verdict

1. The integrated same-length witness `S = AAATAT → D = AAAAAT` is valid and
   kernel-checked. Under the source-faithful molecule-class reading it refutes
   the “truth is the maximum-likelihood maximizer” conclusion for the fixed-N
   §6.1 objective (ratio `5`) and for the same-length exact multinomial (ratio
   `3`), with both `S` and `D` admissible §6.2 spelled circuits.
2. Because a spelled circuit is a special admissible §6.2 flow, the same
   evidence also refutes flow-level optimality of the truth over the §6.2
   feasible set. The earlier `AAATT → AAAATT` witness already did this for
   variable length; the same-length witness removes candidate length as an
   escape.
3. **The same-length witness does not by itself negatively settle the published
   question.** Three source choices remain outside the witness’s reach, and each
   can reverse or block the conclusion: the referent itself (the 2016 sentence
   never selects §6.2 or any MB09 formula), the sample-size regime (the witness
   is a low-coverage, per-instance phenomenon), and the tie/strand conventions.
   In particular the sentence is quantified per read set and does not say
   “with high probability,” but MB09’s circuit claim is qualified “assuming high
   enough coverage,” and under the high-coverage fixed-length reading the truth
   is asymptotically the unique maximizer.
4. This note therefore contradicts the still-visible claims on `main` that
   reading (3) “is not refuted” or that no witness has both the truth and the
   competitor §6.2-feasible. Those statements are stale after PR #43. The
   corrections are itemized in §4.

## 1. Primary-source facts re-read for this note

### 1.1 The 2016 sentence is paper-level and sequence-valued (source fact)

Accepted article, Discussion (printed p. i501):

> “The maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009), on
> the contrary, seems to be robust to these issues, and thus a good candidate
> for the ‘correct’ formulation. Understanding whether bridging conditions can
> be used to guarantee that the maximum-likelihood sequence is the true sequence
> is currently an open question.”

It carries no section, equation, figure, or page pointer into MB09; a full-text
scan finds no `multinomial`/`binomial` and no candidate-length/tie discussion.
The only structured object the sentence names is “the maximum-likelihood
**sequence**.” [source fact]

### 1.2 MB09 §6.1 indexes by `k`-**molecule**, not by oriented `k`-mer
(source-supported inference)

MB09 §6.1 reads:

> “let `d_i` denote the number of times the **k-molecule** `i` appears in `D`.
> … the outcome of the trial is the **k-molecule** beginning at that position.
> For a given `i`, the probability that the outcome of a single trial is `i` is
> simply `d_i/N(D)`. Let the random variable `X_i` denote the number of trials
> whose outcome is `i`. There are `4^k` such variables …”

The last clause is inconsistent with the rest of the paragraph: over the
4-letter DNA alphabet there are `4^k` oriented `k`-mers but only `(4^k + p_k)/2`
`k`-molecules (`p_k` the number of self-reverse-complementary `k`-mers). The
probability model itself forces the molecule indexing: the trial outcome is a
`k`-molecule, and `d_i` counts occurrences of the `k`-molecule `i`. MB09 §4.1
independently states the bidirected de Bruijn graph represents “each `k`-molecule
… only once,” and §6.2 builds the flow graph on reads “which are DNA molecules”
and identifies `d_i` with the flow through vertex `i`. A flow through an
*oriented* `k`-mer vertex would contradict the “represented only once”
construction. [source fact + source-supported inference]

**Consequence.** The reverse-complement collapse used by the integrated
witnesses is the source’s own indexing, not an added convention. The loose
`4^k` phrase is a source inconsistency and is not evidence for the oriented
reading. (This does not by itself fix the *strand* convention of Shomorony’s
single-strand truth `s`; see §3.3.)

### 1.3 The §6.2 lower bound is per read vertex `1` (source fact)

MB09 §6.2:

> “Each vertex has a lower bound of 1 since it represents a read that must be
> present in the genome at least once. All other lower bounds are 0 and all
> upper bounds are infinity.”

`x_i` is a §6.1 trial count and appears only in the cost
`c_i(d_i) = −(x_i log d_i) − (n − x_i) log(N − d_i)`. The per-occurrence
requirement `d_i ≥ x_i` is a strengthening, not the source condition.
[source fact + source-supported inference]

### 1.4 §6.2 optimizes a flow; a sequence is downstream (source fact)

MB09 §6.2 calls the construction its “algorithm,” and:

> “Since any flow can be decomposed into a collection of walks, our flow
> represents a **(non-contiguous) assembly** of the genome.”

Single sequences are produced later by the §7 “From Flow to Contigs” heuristic,
which the source does not present as likelihood-optimal. [source fact]

## 2. What the integrated witnesses actually establish

The two kernel-checked witnesses now on `main` are:

| Witness | Truth `S` | Competitor `D` | Lengths | `I_s` | §6.2 admissibility | Ratios |
|---|---|---|---|---|---|---|
| variable-length | `AAATT` (5) | `AAAATT` (6) | `5→6` | holds, interleaving vacuous | both spelled bidirected circuits, verified computationally | §6.1 binomial `9/8` |
| same-length | `AAATAT` (6) | `AAAAAT` (6) | `6→6` | holds, interleaving **non-vacuous and bridged** | both spelled bidirected circuits, verified computationally | §6.1 binomial `5`; exact multinomial `3` |

[verified computation + kernel-checked; see
[`../section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md),
[`../bridging-se62-flow-ml-counterexample.md`](../bridging-se62-flow-ml-counterexample.md),
and [`../section62-mb09-bidirected-graph-audit.md`](../section62-mb09-bidirected-graph-audit.md)]

What follows for the candidate universes the repository has modelled, under the
source-faithful molecule-class indexing and per-vertex lower bound `1`:

| Candidate universe / objective | Status of “truth is an ML maximizer” | Basis |
|---|---|---|
| §6.1 fixed-`N` binomial over **molecule-class circular sequences** | **refuted** by same-length witness (ratio `5`, same length ⇒ inclusion transfers to arbitrary length) | kernel-checked |
| exact multinomial over **molecule-class circular sequences** | **refuted** by same-length witness (ratio `3`) | kernel-checked |
| §6.2 **spelled circuits** (single molecule, source lower bound `1`) | **refuted** by same-length witness | kernel-checked + explicit graph certificate |
| §6.2 **arbitrary feasible flows** | **refuted**: a spelled circuit is a feasible flow, and the spelled competitor strictly improves | mathematical fact + verified computation |
| Variant E exact multinomial over **single-strand circular sequences** | refuted by #31 (`AAABB → AAAAB`) | kernel-checked |
| literal §6.1 binomial over **single-strand circular sequences** | refuted by #32 (`AAACC → AAAAC`) | kernel-checked |
| broad ML “principle” with no fixed formula | **not refutable by any finite witness** | source analysis |

The nesting/inclusion step is the repository’s already-recorded lemma: a
same-length competitor that beats the truth lies in the length-`G` subclass and
hence in every superclass, so a negative result transfers upward. [mathematical
fact; [`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md) §3]

**Consequence for issue #36.** §6.2 feasibility is **not** a hidden necessary
condition that could rescue the implication; the §6.2-restricted
sequence-level statement is false under the source per-vertex reading. The
“§6.2 feasibility” obligation recorded on `main` is discharged.

## 3. Why this still does not settle the published question

### 3.1 The referent is not selected by the source (source gap)

The 2016 sentence names MB09 only by bibliography. MB09 contains the exact
multinomial, the §6.1 fixed-`N` approximation, the §6.2 flow algorithm, and the
umbrella “maximum likelihood framework.” No primary source fixes which one the
2016 phrase denotes; the reconciled ranking is even that the literal textual fit
favours the broad principle (reading 4) over §6.2 (reading 3). A witness
conditional on §6.2 cannot settle a sentence that may not denote §6.2.
[source gap + interpretation; [`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md) §5]

### 3.2 §6.2 optimizes flows, while the sentence says “sequence” (source fact)

Even granting §6.2, its optimized object is a possibly non-contiguous flow, and
the single-sequence step is the §7 heuristic. The same-length witness handles
this at its instance because the competitor is a *spelled molecule* — a special
flow — so it refutes both the flow-level and the spelled-sequence-level readings.
But the source itself provides no likelihood justification for restricting the
published “sequence” to spelled circuits, so the witness closes a well-posed
sub-statement rather than the paper-level question. [source fact + interpretation]

### 3.3 The regime (per-instance vs high-coverage) is a third escape
(mathematical fact + interpretation)

The sentence is quantified per read set and carries no coverage qualifier
[source fact]. But MB09’s “the original double-stranded genome corresponds to a
circuit” is qualified “assuming high enough coverage.” Under the high-coverage
reading with the true length `G` fixed, the empirical window distribution
concentrates and the asymptotic exact-multinomial criterion is the KL divergence
`−KL(p ‖ q_D)`, whose unique maximizer is `q_D = p`, i.e. `d_D = d_S`. The truth
is then the asymptotic ML spectrum, hence the truth up to the intended
equivalence [mathematical fact, conditional on the repository’s
spectrum-uniqueness bridge].

The same-length witness is a low-coverage phenomenon (`n = 5 < N = 6`): the
competitor keeps the observed support but does not match `d_S`, so it wins only
because `n` is finite. Unlike #31/#32 its competitor has positive likelihood for
large `n`; it is beaten by the truth through a strict KL inequality, not through
a vanishing likelihood factor. Either way, the witness settles only the
finite-sample reading. [mathematical fact + verified computation; the regime
fork is developed in `issue36-finite-vs-asymptotic-regime.md` on the unmerged
reconciliation branch `analysis/issue36-finite-vs-asymptotic-regime-0920`.]

### 3.4 Tie/equivalence and residue conventions remain open (open)

“The maximum-likelihood sequence is the true sequence” still does not separate
truth-is-a-maximizer from every-maximizer-is-truth-up-to-equivalence. MB09 is
double-stranded/bidirected; Shomorony’s `s` is a circular single string. The
2016 sentence does not select the equivalence. The publisher supplement
(sections A–G) also remains uninspected (HTTP 403). [open]

### 3.5 Bottom line

The strongest source-faithful conclusion currently justified is:

> Under the source-faithful MB09 §6.2 reading (vertices are read DNA molecules,
> per-vertex lower bound `1`, spelled circuits, §6.1 fixed-`N` objective), and
> over the molecule-class circular-sequence candidate universe, the published
> “truth is the maximum-likelihood sequence” conclusion is false with
> kernel-checked finite witnesses, at both fixed and variable candidate length.

> The published open question is **not** settled, because the 2016 phrase does
> not select the §6.2 referent, the witness is a low-coverage per-instance
> phenomenon, and the tie/equivalence convention is unresolved.

## 4. Corrections to `main`

The following `main` statements predate PR #40/#43 and are now false or
misleading. They are annotated here (and cross-linked by small edits).

1. [`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md)
   §0 item 5 (“neither touches reading 3”) and §7 row (3) (“**Not refuted.** No
   witness has both the truth and the competitor in the sequence-level §6.2
   feasible set”). Stale: the same-length witness has both §6.2-feasible and
   refutes reading (3). Remaining true content: no source selects reading (3),
   and the flow→sequence bridge is still not supplied by the source.
2. [`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md)
   §5 item 1 and the §7 table row “No current witness has both truth and
   competitor sequence-level §6.2-feasible.” Stale for the per-vertex reading;
   remains true only under the per-occurrence strengthening.
3. [`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md)
   §7 (“the §6.2 feasibility work remains essential rather than optional”) and
   §8 item 4. Superseded: §6.2 feasibility is not a necessary obligation, and
   the residual is the referent plus the regime/tie/strand conventions.

None of these corrections changes a source fact, a witness value, or the
repository’s decision to keep the exact/binomial/flow variants distinct.

## 5. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| 2016 sentence is paper-level and sequence-valued; no §6.2 pointer | source fact | accepted text p. i501 + scan |
| §6.1 indexes by `k`-molecule; `4^k` is a source inconsistency | source fact + source-supported inference | §6.1, §4.1, §6.2 |
| §6.2 vertex lower bound is `1`; `d ≥ x` is a strengthening | source fact | §6.2 |
| §6.2 optimizes a flow; sequence is a §7 heuristic | source fact | §6.2, §7 |
| Same-length witness refutes §6.1/§6.2 spelled-circuit optimality | kernel-checked + verified computation | PR #43 artifacts |
| Spelled-circuit counterexample refutes flow-level optimality | mathematical fact | special case |
| The witness is low-coverage; Regime-H fixed-length answer is positive | mathematical fact (conditional on spectrum uniqueness) | KL argument |
| The published question remains unsettled | source gap + interpretation | §3 |
| Main’s “reading (3) not refuted” claims are stale | repository fact | §4 |

## 6. Locators

- I. Shomorony, S. H. Kim, T. A. Courtade, D. N. C. Tse, “Information-optimal
  genome assembly via sparse read-overlap graphs,” *Bioinformatics* 32(17) (2016)
  i494–i502, DOI `10.1093/bioinformatics/btw450`; Discussion printed p. i501,
  Eq. (1) printed p. i497.
- P. Medvedev, M. Brudno, “Maximum Likelihood Genome Assembly,” *J. Comput.
  Biol.* 16(8) (2009) 1101–1116, DOI `10.1089/cmb.2009.0047`; §3.1, §3.4, §4.1,
  §6.1–6.2, §7, §8.2, PMC3154397.
- Integrated witnesses: `AssemblyP1/SameLengthSection62Counterexample.lean`,
  `AssemblyP1/Section62BridgingCounterexample.lean`;
  `scripts/verify_samelength_se62_counterexample.py`,
  `scripts/verify_se62_bridging_flow_counterexample.py`,
  `scripts/verify_se62_mb09_bidirected_graph.py`.
