# Sequence vs. flow/assembly and tie/equivalence semantics in Medvedev–Brudno (2009) and Shomorony et al. (2016)

_Status: independent primary-source audit for issue #36, 2026-09-20, written on
`main` at `488beda` after PR #40 (`6256d46`) was merged. It asks two questions
the existing issue-#36 material treats only in passing: (a) what each paper
means by a **sequence** as opposed to a **flow / (non-contiguous) assembly**;
and (b) what either paper says about **ties / equivalence** of maximum
likelihood. It then re-derives whether the merged PR #40 witness is sufficient
to falsify the published statement. Every claim is labelled **source fact**,
**mathematical fact**, **verified computation**, **interpretation**, or **open**.
It does not select a referent for the 2016 phrase by fiat._

_Companion artifacts on `main`: [`../bridging-se62-flow-ml-counterexample.md`](../bridging-se62-flow-ml-counterexample.md)
(the witness), [`../section62-mb09-bidirected-graph-audit.md`](../section62-mb09-bidirected-graph-audit.md)
(the §6.2 graph/flow construction), `AssemblyP1/Section62BridgingCounterexample.lean`
(the kernel check). An independent, **unmerged** claim-boundary note (`docs/aaatt-witness-claim-boundary-2026-09-20.md`
on branch `docs/aaatt-witness-claim-boundary`, commit `dcf353c`) reaches a
compatible verdict; §7 reconciles the two._

---

## 0. Bottom line

1. Shomorony et al. operate on **sequences**: the data-generating truth is a
   circular string `s`, and the reconstruction target is a cycle whose spelled
   string equals `s` **up to cyclic shifts**. The open-question sentence is
   sequence-valued and carries no formula, section, or tie rule. [source fact]
2. Medvedev–Brudno §6.2 optimizes over a **flow** whose output the authors
   explicitly call a “**(non-contiguous) assembly**”, and the transition from
   that flow to a sequence is deferred to a §7 **heuristic** over “an
   exponential number of decompositions”. In addition, MB09 §5.1 states that
   their implementation is “a **2-approximation algorithm in the worst case**”.
   So §6.2 is not an exact maximum-likelihood *sequence* optimizer. [source
   fact]
3. **Neither paper specifies a tie-breaking rule or a uniqueness claim for the
   maximum-likelihood object.** Shomorony’s equivalence is cyclic shift;
   reverse complement appears only as experimental read preprocessing. MB09’s
   underlying object is double-stranded, but §6.1/§6.2 state no maximizer
   uniqueness or tie convention. [source fact]
4. **PR #40 is not, by itself, enough to falsify the published statement.** It
   refutes one named conjunction of conventions (the §6.2 spelled-circuit
   reading with external-`N` §6.1 binomial, reverse-complement read molecules,
   per-vertex lower bound `1`, unrestricted candidate length, finite realized
   read set). The published sentence leaves the referent/objective, the
   sequence-vs-flow boundary, strand, candidate length, sample-size regime, and
   conclusion/tie semantics underdetermined; several of these can avoid or
   reverse the refutation. [interpretation]
5. **New refinement.** Under the exact *candidate-intrinsic-`N(D)`* multinomial
   of MB09 §6.1 — not just the external-`N` binomial — the same PR #40 instance
   still strictly beats the truth, with ratio `125/108`. Thus the
   exact-vs-binomial objective fork is **not load-bearing for this instance**.
   The load-bearing residual fork is the sequence-vs-flow/referent choice and
   the length/strand/regime/tie conventions. [verified computation]

---

## 1. Retrieval ledger (independent, 2026-09-20)

Retrieved with `urllib` and text-extracted with `pypdf`:

| Artifact | Locator | SHA-256 | Match to `main` ledger? |
|---|---|---|---|
| Shomorony et al., OUP typeset article | `https://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf` | `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da` | yes |
| Shomorony et al., author-accepted manuscript | `https://people.eecs.berkeley.edu/~courtade/pdfs/NSG.pdf` | `daeb5b3163d92643affc2398a387217cb57e5e33ce0dd5ebbfccabf621454f2c` | yes |
| Shomorony et al., earlier preprint + supplement | `https://web.stanford.edu/~gkamath/nsgIlan.pdf` | `f2a9f6a64f75cbf4c2cfaec6f794c779907f165c986261bec7a2aa72a3e6954a` | yes |
| Medvedev–Brudno (2009) full text | `https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/` | `db7b825aaafab587deefecb7824aa4e1c27de872f25d14cb48d6fba81b1e0e0e` (HTML) | **no** — dynamic page, hash not reproducible (as already recorded) |

The MB09 HTML byte-hash drifts across fetches; no claim below rests on that
hash. Quotations were re-read from the extracted text and cross-checked against
the author-accepted 2016 manuscript. The Oxford publisher supplement (sections
A–G) still returned HTTP 403 and remains uninspected.

---

## 2. “Sequence” vs. “flow / assembly”

### 2.1 Shomorony et al.: sequence-valued throughout

Accepted text (`InfoOptimalAssy.pdf`), §2 (printed p. i496): a read-overlap
graph has vertices carrying **strings**; an assembly is a path `p` with
`st(p) = s`, and — because the genome is circular — a cycle
`c = (v_1, …, v_N, v_1)` with `st(c) = s` **up to cyclic shifts**. [source fact]

Theorem 1 (printed p. i497): for `R ∈ I_s`, `st(c_s) = s` up to cyclic shifts.
Corollary 1 (printed p. i498): the graph then contains a **unique Eulerian
cycle**. The Discussion open-question sentence (printed p. i501) likewise asks
about “the maximum-likelihood **sequence**”. [source fact]

The only place reverse complement enters the *string* model is the experimental
preprocessing (printed p. i500): “to handle the fact that reads can come from
both strands of the genome, before running NOT-SO-GREEDY, we preprocess the set
of reads to include each read and its reverse complement.” That is an
experimental step, not a stated genome-equivalence relation. [source fact]

### 2.2 Medvedev–Brudno: the §6.2 output is not a sequence

MB09 §6.2 (PMC3154397): the vertices of the transitively reduced bidirected
overlap graph are **reads (DNA molecules)**, and the solved object is a convex
min-cost biflow:

> “Since any flow can be decomposed into a collection of walks, our flow
> represents a **(non-contiguous) assembly** of the genome, and the flow going
> through each vertex represents the number of time the read is present in the
> assembly.”

§7 (“From Flow to Contigs and the Use of Matepairs”) then says:

> “In general, any flow can be decomposed into a collection of walks, which, in
> our case, correspond to the assembled contigs. Since there is an **exponential
> number of decompositions possible**, we use a heuristic to find one where the
> length of the walks (contigs) is large and the accuracy of the contigs is
> high.”

So a §6.2 optimum determines a flow, and only a §7 **heuristic** selects a
sequence (or contig set) from it. [source fact]

### 2.3 The §6.2 implementation is not an exact optimizer

MB09 §5.1 (PMC3154397), on the monotonization reduction used by the
implementation:

> “Though this results in a **2-approximation algorithm in the worst
> case**, it found the optimal solution on almost all our input instances.”

This is a second, independent reason not to read the phrase “the
maximum-likelihood sequence” as “the output of MB09’s §6.2 algorithm”: the
algorithm is explicitly only a worst-case 2-approximation to the §6.1 optimum.
[source fact + interpretation]

### 2.4 The structural conclusion

The 2016 sentence compares **sequences**. MB09’s exact/binomial §6.1 objectives
are sequence-valued (a circular genome `D` scored through its window counts),
but MB09’s concrete §6.2 optimization is flow-valued and requires a non-unique
§7 heuristic to become a sequence. A statement about a “maximum-likelihood
sequence” is therefore **not** directly a statement about the §6.2 flow
optimum; the identification needs a flow→sequence bridge that neither paper
supplies as a theorem. [interpretation; consistent with
`../source-notes/mb-formulation-referent-reconciliation.md` §4]

---

## 3. Tie and equivalence semantics

### 3.1 Shomorony et al.

- The theory’s reconstruction target is `s` **up to cyclic shifts** (§2,
  Theorem 1). “Unique Eulerian cycle” (Corollary 1) is a statement about the
  *constructed graph*, not about uniqueness of a likelihood maximizer. [source
  fact]
- The open-question sentence (printed p. i501) says “the maximum-likelihood
  **sequence** … the true sequence”, with no tie rule, no uniqueness claim, no
  “up to equivalence”, and no candidate-class or length convention. [source
  fact]
- The accepted manuscript (`NSG.pdf`) has the same wording: “Understanding
  whether bridging conditions can be used to guarantee that the maximum
  likelihood sequence is the true sequence is currently an open question.”
  [source fact]

### 3.2 Medvedev–Brudno

- No occurrence of a maximizer tie rule or uniqueness theorem for the §6.1
  likelihood or §6.2 optimum was found in the retrieved full text. The only
  “unique”/“ties” language is about the Myers string-graph model and about
  sorting inside NOT-SO-GREEDY-like steps, not about the ML optimum. [source
  fact]
- The underlying object is a **double-stranded molecule** (an unordered
  reverse-complement pair), so reverse complement is an identity in MB09’s
  model; Shomorony’s circular-string model instead quotients by cyclic shift.
  The 2016 sentence does not say which equivalence is meant for its
  comparison. [source fact + open item]
- §7’s “exponential number of decompositions” means the flow does not even
  determine a unique **sequence**; a tie in the flow optimum compounds this.
  [source fact]

### 3.3 Two distinct conclusion schemas

The singular “the maximum-likelihood sequence is the true sequence” cannot, by
itself, distinguish:

- **(S1) truth-is-a-maximizer:** the truth attains maximum likelihood; from
- **(S2) all-maximizers-are-truth:** every maximizer is equivalent to the
  truth (the operational guarantee for an unspecified assembler).

Neither paper states (S1) or (S2), and the equivalence relation to use in (S2)
is itself unspecified (cyclic shift at least; reverse complement possibly).
[source-analysis; consistent with `../literature/ml-tie-semantics.md`]

---

## 4. What the merged PR #40 witness establishes

Kernel-checked in `AssemblyP1.Section62BridgingCounterexample` (no `sorry`,
`axiom`, `admit`, or `native_decide`; standard axioms only), for

```text
truth            S = AAATT            (length 5)
read length      L = 3, realized starts (0,1,4), n = 3, external N = 5
observed         x = { AAA:1, AAT:1, TAA:1 }        (reverse-complement classes)
truth spectrum   d_S = { AAA:1, AAT:2, TAA:2 }
competitor       D = AAAATT           (length 6), d_D = { AAA:2, AAT:2, TAA:2 }
```

the theorem `se62_bridging_flow_counterexample` proves
`SourceCertificate ∧ SeqSupportLB dS obs ∧ SeqSupportLB dD obs ∧ lik obs dS < lik obs dD`,
i.e. the `I_s` certificate, the sequence-level support/lower-bound certificate
for both `S` and `D`, and the literal §6.1 product-of-binomial-marginals ratio
`L_{6.1}(D)/L_{6.1}(S) = 9/8 > 1`. [kernel-checked]

Two scope boundaries internal to PR #40:

1. `SeqSupportLB` (support equality plus `x ≤ d`) is **not** MB09 §6.2
   feasibility; it is a stronger finite sufficient certificate. [source fact /
   repository]
2. The exact §6.2 bidirected graph/flow admissibility of both `S` and `D`
   (transitive reduction, signed incidence, balance, supersource/sink) is
   verified only computationally in `scripts/verify_se62_mb09_bidirected_graph.py`,
   **not** kernel-checked. [verified computation]

---

## 5. New refinement: the exact candidate-intrinsic multinomial is also beaten

The PR #40 witness is stated against the **external-`N`** §6.1 binomial. The
other determinate §6.1 objective is the exact global read-count multinomial
with candidate-intrinsic `N(D)`:

```text
L_exact(D | x)  ∝  ∏_i ( d_D(i) / N(D) )^{ x_i }.
```

For the PR #40 instance, over the observed class support `{AAA, AAT, TAA}`
(all other observed counts are zero, so their factors are `1`):

```text
S: N=5, d={AAA:1,AAT:2,TAA:2}  ⇒  (1/5)·(2/5)² = 4/125
D: N=6, d={AAA:2,AAT:2,TAA:2}  ⇒  (2/6)·(2/6)·(2/6) = 8/216 = 1/27
ratio = (1/27) / (4/125) = 125/108 > 1.
```

The same ratio `125/108` holds if reads are indexed by strand `k`-mers rather
than by reverse-complement molecule classes, because the only observed class
whose count changes is `AAA` (`1 → 2`); in the strand reading `S` contributes
`(1/5)³` and `D` contributes `(2/6)(1/6)²`, again ratio `125/108`. [verified
computation]

**Consequence.** For this instance the exact-vs-binomial objective fork does
**not** change the sign of the comparison. The witness therefore refutes the
§6.1 *truthIsML* conclusion under **both** determinate §6.1 objectives, not
only the external-`N` one — *provided* the other conventions (strand,
spelled-circuit candidate, unrestricted length, finite sample) are fixed as in
§4. The remaining obstacles are not objective-formula obstacles; they are the
referent/sequence-vs-flow choice and the length/strand/regime/tie choices.

Reproduce:

```sh
python3 - <<'PY'
from fractions import Fraction as F
# exact candidate-intrinsic multinomial ratio for AAATT -> AAAATT
S = (F(1,5)*F(2,5)*F(2,5))   # d_AAA=1, d_AAT=2, d_TAA=2, N=5
D = (F(2,6)*F(2,6)*F(2,6))   # d_AAA=2, d_AAT=2, d_TAA=2, N=6
print(D/S)                    # 125/108
PY
```

---

## 6. Is PR #40 enough to falsify the published statement?

**No — not by itself.** The published sentence is not a determinate formal
proposition, and PR #40 refutes only a named conjunction of conventions. The
distinction is not rhetorical: each row below can independently avoid or
reverse the refutation.

| Fork | PR #40’s setting | Source status | Effect if changed |
|---|---|---|---|
| Referent / objective | external-`N` §6.1 binomial | no source selects exact vs binomial vs §6.2 vs broad principle | §5 shows exact-vs-binomial does not flip *this* instance; a broad-principle reading (4) is not fixed by any single witness |
| Sequence vs flow | witnesses are spelled single molecules (special flows) | 2016 sentence is about a **sequence**; §6.2 returns a flow | a §6.2-flow result only bears on the sentence through a flow→sequence bridge neither paper states (§2.4) |
| Strand / read type | reverse-complement molecule classes | Shomorony’s theory is single-strand; MB09 is molecular | the witness’s collapse uses `ATT~AAT`, `TTA~TAA`; a bounded single-strand search found no witness (evidence, not proof) |
| Candidate length | unrestricted (`|D|=6 ≠ N=5`) | “known `N`” is a §6.1 parameter, not a stated competitor-length constraint | a fixed-length reading is handled by the separate same-length witnesses, not by this one |
| Sample regime | finite realized read set, `n=3` | the sentence has no coverage qualifier | under high coverage the fixed-length answer is the opposite (a.s. eventual uniqueness) |
| Conclusion / tie | strict inequality, so refutes both (S1) and (S2) for this panel | no tie rule or equivalence stated | (S1) vs (S2) remains a live fork for readings not covered by a strict witness |
| §6.2 admissibility | certified computationally, not kernel-checked | source defines flow feasibility | the graph/flow certificate is verified but not kernel-checked |

**Conditional negative result that *is* supported.** If one commits to the
sequence-level, §6.1-objective, reverse-complement-molecule, unrestricted-length,
per-instance reading and treats a spelled single molecule as a §6.2 candidate,
then PR #40 (together with the same-length witnesses `AAABB→AAAAB` and
`AAACC→AAAAC` for the length-fixed sub-case) yields a negative answer. That is a
conditional settlement of a formalization, not a settlement of the published
open question. [interpretation]

**Why PR #40 is still valuable.** Its distinctive content is that it removes the
hypothesis that §6.2 flow feasibility could rescue the implication for the
*spelled-circuit* sub-case, and it does so with a kernel-checked finite
instance. The same-length witnesses already refute the two determinate
sequence-level readings by candidate-set inclusion; PR #40 is complementary and
narrower, not the load-bearing settlement.

---

## 7. Reconciliation with the unmerged claim-boundary note (`dcf353c`)

The branch `docs/aaatt-witness-claim-boundary` (commit `dcf353c`, **not** on
`main`) records the same bottom line: PR #40 settles a named interpretation and
not the published question, and it lists substantially the same convention
panel. This note is independent and compatible; it adds:

1. the MB09 §5.1 “2-approximation in the worst case” source fact, which
   strengthens the sequence-vs-flow reading (§2.3);
2. the observation that the §7 flow→sequence step has an exponential number of
   decompositions and is a heuristic (§2.2);
3. the `125/108` computation showing the exact-vs-binomial fork is not
   load-bearing for this instance (§5), which refines that note’s statement that
   the exact objective’s status for this witness is untested;
4. an explicit statement of the two conclusion schemas (§3.3) in the same place
   as the sufficiency verdict.

No mathematical claim in that note is contradicted.

---

## 8. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| Shomorony’s target is sequence-valued and defined up to cyclic shifts; open question is sequence-valued | source fact | `InfoOptimalAssy.pdf` §2, Thm. 1, p. i501; `NSG.pdf` |
| Reverse complement enters only as experimental preprocessing in Shomorony | source fact | `InfoOptimalAssy.pdf` p. i500 |
| MB09 §6.2 output is a “(non-contiguous) assembly”; §7 uses a heuristic over exponentially many decompositions | source fact | MB09 §6.2, §7 |
| MB09’s implementation is a worst-case 2-approximation | source fact | MB09 §5.1 |
| Neither paper states a tie rule or ML-optimum uniqueness/equivalence | source fact / source-analysis | full-text scan |
| The 2016 sentence cannot denote §6.2 without an unstated flow→sequence bridge | interpretation | §2.4 |
| PR #40 witness: `I_s`, `SeqSupportLB` both, ratio `9/8` | kernel-checked | `AssemblyP1.Section62BridgingCounterexample` |
| Both `S`, `D` are admissible §6.2 bidirected circuits | verified computation, not kernel-checked | `scripts/verify_se62_mb09_bidirected_graph.py` |
| Exact candidate-intrinsic multinomial ratio is `125/108 > 1` | verified computation | §5 |
| PR #40 alone does not falsify the published statement | interpretation | §6 |
| Referent, sequence-vs-flow, strand, length, regime, tie remain open | source gap | §2–§6 |

---

## 9. Unresolved register

1. **Referent.** No primary source selects exact multinomial vs external-`N`
   binomial vs §6.2 flow vs broad principle. This note narrows the exact-vs-
   binomial sub-fork for the PR #40 instance only.
2. **Sequence vs flow.** The 2016 sentence is sequence-valued; MB09’s operative
   optimization is flow-valued with a heuristic decomposition. Whether the
   published question can be interpreted at the §6.2 flow level at all remains
   an interpretation question.
3. **Tie / equivalence.** Neither paper supplies a tie rule. Whether the
   published conclusion is (S1) or (S2), and whether the equivalence is cyclic
   shift and/or reverse complement, is unresolved.
4. **Length, strand, regime.** Each remains a live convention fork; the
   fixed-length sequence-level sub-cases are covered by the separate
   same-length witnesses, the §6.2 spelled-circuit sub-case by PR #40.
5. **Kernel status.** The §6.2 graph/flow admissibility of the PR #40 witness is
   computationally verified only; a kernel check would upgrade that boundary.
6. **Publisher supplement (sections A–G), HTTP 403**, remains the one
   unexamined accepted artifact that could name an objective.

Primary sources: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116, §5.1, §6.1–6.2, §7,
PMC3154397; Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
*Bioinformatics* 32(17) (2016) i494–i502, §2, Eq. (1), Theorem 1, Corollary 1,
§5, DOI `10.1093/bioinformatics/btw450`. Repository merge `6256d46` (PR #40);
unmerged claim-boundary branch `docs/aaatt-witness-claim-boundary` (`dcf353c`).
