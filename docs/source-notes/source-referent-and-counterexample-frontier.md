# Source referent of the 2016 open question vs. the counterexample frontier

_Status: source-fidelity synthesis, 2026-09-20. Separates source facts from
interpretation and states one conditional frontier consequence. It does not
settle the published problem and introduces no Lean claim._

## 0. Purpose

The repository now has kernel-checked negative results for three named
Medvedev–Brudno maximum-likelihood (ML) variants (PR #25, #33, #35, all on
`main`). It also has an unresolved source question: which Medvedev–Brudno (2009)
object does Shomorony et al. (2016) intend by "the maximum-likelihood
formulation?"

This note connects the two. Its substantive point is that the **most plausible
source referent is the variant already refuted on `main`**, so the remaining
source ambiguity is the only reason the published question is not read as
negatively settled. That is stated as a conditional interpretation, not a
settlement.

Related parallel source work (unmerged, for reconciliation by the orchestrator):
`agent/shomorony-ml-semantics` (`shomorony-open-question-referent.md`),
`agent/source-provenance-0919b` (`shomorony-open-question-denotation.md`),
`agent/source-provenance-0919c` (`shomorony-ml-referent-provenance.md`),
`agent/ml-layer-source-verification` (`ml-accepted-text-source-verification.md`).
This note does not re-derive that argument; it records the frontier consequence.

## 1. Accepted 2016 text (source fact)

Three distinct 2016 documents exist and must not be collapsed:

| Version | Date | Open-question sentence |
|---|---|---|
| Early author-hosted preprint "Optimal Sequence Assembly…" | 2016-01-23 | No |
| Accepted author manuscript, "MANUSCRIPT Pages 1–8" | 2016-05-06 | Yes |
| Publisher-formatted accepted article (OUP) | OUP typeset | Yes |

The publisher-formatted accepted article is independently retrievable at the
Berkeley mirror
`https://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf`
(SHA-256 `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043ac3fce3c4da`,
9 pages). Every page carries the OUP running head `i494`–`i502` and the footer
`Bioinformatics, 32, 2016, i494–i502`, `doi: 10.1093/bioinformatics/btw450`, plus
the download stamp `…academic.oup.com/bioinformatics/article-abstract/32/17/i494/2450780
… on 26 June 2018`. This closes the accepted-main-text provenance limitation in
`docs/source-notes/shomorony-ml-reference.md` and
`docs/literature/ml-tie-semantics.md`.

The accepted open-question sentence is verbatim `docs/open-problem.md:9`:

> "Understanding whether bridging conditions can be used to guarantee that the
> maximum-likelihood sequence is the true sequence is currently an open
> question."

The only ML property claim in the accepted text is qualitative:

> "The maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009), on
> the contrary, seems to be robust to these issues [over-collapsing of repeats],
> and thus a good candidate for the 'correct' formulation."

A full-text scan finds no likelihood formula, no "multinomial", no "binomial",
no flow-feasible set, no candidate class, no competitor length, no equivalence
relation, no tie rule, and no section/equation pointer into Medvedev–Brudno. The
accepted publisher supplement (Sections A–G) remains unretrieved.

## 2. The Medvedev–Brudno objects (source fact)

1. **Exact global read-count likelihood** (§6.1, first half): `D` is a circular
   genome of length `N(D)`; type `i` appears `d_i` times; a uniform start yields
   type `i` with probability `d_i/N(D)`; the counts are multinomial with
   `N(D) = Σ_i d_i`.
2. **Binomial / separable approximation** (§6.1, second half): `N(D)` is
   replaced by an external constant `N`, the true genome length; convex vertex
   costs `c_i(d_i) = −x_i log d_i − (n − x_i) log(N − d_i)`.
3. **§6.2 flow optimization**: convex min-cost bidirected flow on the
   transitively reduced read-overlap graph, lower bound 1 on every read vertex,
   optimizing the §6.1 approximation; a flow "represents a (non-contiguous)
   assembly."

Medvedev–Brudno name their target as "the genome that maximizes the global
read-count likelihood," contrast it with "the standard maximum parsimony
approach (which finds the shortest genome…)," and introduce object 2 with the
word "approximate." Object 3 is the algorithm that optimizes object 2.

## 3. Most plausible referent (interpretation)

Ranking, matching the parallel source notes:

1. **Exact global read-count multinomial over circular candidates with
   candidate-dependent length** (repository Variant E). "Formulation" contrasts
   objectives, not algorithms; the approximation is explicitly labelled
   approximate; §6.2 is the algorithm; and the open question's conclusion is
   about a *sequence*, whereas a §6.2 flow need not spell one.
2. **Binomial approximation** (Variant A). Matches what MB's published algorithm
   actually optimizes, but is labelled an approximation and fixes the external
   length to `N`.
3. **§6.2 flow-feasible set** (Variant F). An algorithmic feasible set with a
   non-contiguous interpretation; least plausible as "the maximum-likelihood
   formulation."

**Candidate length/universe:** the exact §6.1 objective imposes no competitor
length (`D` contributes its own `N(D)`); the approximation fixes the denominator
to the true `N`; the 2016 model fixes the true `G` but not competitors. A fixed
competitor length is an added restriction, not a default. **Unresolved.**

**Tie semantics:** neither paper gives a tie rule; Bresler et al. (2013)
Theorem 1 constructs a distinct *same-length* equal-likelihood competitor; the
singular phrase "the maximum-likelihood sequence" does not by itself imply
uniqueness. **Unresolved.** Cyclic shift is required by the 2016 circular model;
reverse-complement quotienting is unresolved (MB model double-stranded
bidirected molecules; Bresler map to a length-`2G` concatenation).

## 4. Frontier consequence (conditional interpretation)

Negative results already on `main`, all kernel-checked:

| Reading | Witness | Bridging hypothesis | Result |
|---|---|---|---|
| Variant E, unrestricted length | `ACGT` vs `ACACGT` (`ExactVariantECounterexample.lean`, PR #25) | coverage holds; truth repeat-free, so `I_s` bridging clauses are vacuous | competitor strictly better (`1/18 > 3/64`) |
| fixed-length exact multinomial | `AAABB` vs `AAAAB` (`FixedLengthExactCounterexample.lean`, PR #33) | genuine all-bridged length-1 triple repeat; no interleaved pair | ratio `2` |
| fixed-length literal §6.1 product-of-binomial-marginals | `AAACC` vs `AAAAC` (`FixedLengthBinomialCounterexample.lean`, PR #35) | same certificate, `B` relabelled to `C` | ratio `1125/512` |

**Consequence.** Conditional on the most plausible referent being Variant E
(unrestricted exact multinomial), the published question
`R ∈ I_s ⇒ truth is the ML sequence` is already refuted by an on-`main`,
kernel-checked, repeat-free witness, with no dependence on how the remaining
source ambiguity is resolved in any other direction.

A supporting structural fact: the exact multinomial is invariant under tandem
repetition. For `D^k` the `k`-fold tandem repeat, `d_{D^k}(w) = k d_D(w)` and
`|D^k| = k|D|`, so `d/|D|` is unchanged and `L_exact(D^k | x) = L_exact(D | x)`
for every sample. Hence under Variant E, uniqueness up to cyclic shift fails for
every truth independently of bridging; `S^k` is not a cyclic shift of `S` for
`k ≥ 2`. (Also recorded, with proof, on the unmerged branch
`analysis/bridging-schemas-and-flow-gaps`.)

**What the existing witnesses do not refute:**

- the binomial approximation over candidates of *arbitrary* length (the
  witnesses use candidate length `= N`);
- the §6.2 flow-feasible set (read-derived, not all circular genomes).

## 5. Remaining ambiguity and what would change the reading

1. The accepted publisher supplement (Sections A–G) is unretrieved and could
   name the likelihood model.
2. No author statement selects exact vs. approximation vs. flow.
3. Whether the open question is a deterministic "for all `R ∈ I_s`" claim or a
   high-probability claim over the sampling model. The witnesses refute the
   deterministic reading; a measure-zero counterexample would not refute a
   high-probability reading.
4. Whether reverse complement is quotiented, and whether uniqueness is intended.
5. Whether the `I_s` predicate used by each witness matches the accepted Eq. (1)
   exactly. The fixed-length witnesses exercise a genuine all-bridged triple
   repeat; the unrestricted witness is repeat-free, so its bridging clauses are
   vacuous (valid, but does not test bridging).

If (1) or (2) selects Variant E, the negative result is a settlement modulo
(3)–(5). If it selects the §6.2 flow set, the question remains open.

## 6. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| Accepted open-question sentence and full paragraph | source fact (independently verified) | `InfoOptimalAssy.pdf` SHA-256 `ec17b16f…`; corroborated by the accepted manuscript |
| Accepted main text names MB only by bibliography; no formula/variant pointer | source fact | full-text scan; only two `likelihood` occurrences in the paragraph plus the reference |
| MB exact vs. approximation vs. §6.2 chain | source fact | Medvedev–Brudno §6.1–§6.2 |
| Exact multinomial is the most plausible referent | source analysis / interpretation | §3, parallel notes |
| Candidate length/universe not fixed; fixed length is an added restriction | unresolved source ambiguity | accepted text fixes true `G` only |
| Tie/uniqueness and reverse-complement conventions absent | unresolved source ambiguity | neither paper supplies them |
| Tandem-repetition invariance of the exact multinomial | mathematical fact (elementary) | §4 |
| Three named variants refuted by `main` witnesses | kernel-checked | PR #25, #33, #35 |
| Variant E (top-ranked referent) is already refuted | conditional interpretation | §4 + §3 |
| Accepted publisher supplement contents | not retrieved | OUP/silverchair retrieval paths blocked |
