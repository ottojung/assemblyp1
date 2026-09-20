# Candidate-universe reconciliation for the 2016 maximum-likelihood open question

_Status: compact reconciliation for issue #36, 2026-09-20, written against
`origin/main` at `8b2f0fc`. It audits the remaining candidate-universe
distinctions — sequence candidates, spellable Section 6.2 circuits, arbitrary
feasible flows / non-contiguous assemblies, and lower-bound / copy-count
conventions — and states, per distinction, what the primary sources support and
which of the repository's kernel-checked strict witnesses already refute it. It
does not select the Medvedev–Brudno (2009) referent of the Shomorony et al.
(2016) sentence, does not invent a tie or equivalence rule, and does not change
any intent record. Every claim is labelled **source fact**,
**source-supported inference**, **mathematical fact**, **verified computation**,
**kernel-checked**, or **open**._

_Reproduce:_ `python3 scripts/verify_candidate_universe_reconciliation.py`
(self-contained, exact `fractions.Fraction`, deterministic, exits non-zero on
any failed assertion). It recomputes the witness ratios, the spelled-circuit
membership of each witness, the per-occurrence lower-bound split, and the
strict-oriented inversion checked below; it imports no repository predicate.

---

## 0. Bottom line

The four distinctions are not four independent open obligations. Under the
source's per-vertex lower bound:

1. **Sequence candidates** (`U_seq`, all circular words) are refuted under both
   source objectives by the two fixed-length witnesses already on `main`
   (`AAABB → AAAAB` exact, ratio `2`; `AAACC → AAAAC` literal binomial, ratio
   `1125/512`). [kernel-checked]
2. **Spellable Section 6.2 circuits** (`U_spell`) are a strictly smaller
   candidate class that those two witnesses **do not reach** (their spectra
   carry unobserved read windows) and that needed the two Section 6.2 witnesses
   (`AAATT → AAAATT`, `AAATAT → AAAAAT`). Those refute `U_spell` under the
   per-vertex reading. [kernel-checked]
3. **Arbitrary feasible flows / non-contiguous assemblies** (`U_flow`) are a
   superset of `U_spell`. Negative results transfer upward, so the two Section
   6.2 witnesses refute `U_flow` as well: the implication “the truth flow is
   maximum-likelihood” is already false. What is only branch-level evidence (and
   not needed for falsity) is the stronger claim that the *optimum itself* is
   non-spellable. [mathematical fact + verified computation]
4. **Lower-bound/copy-count conventions** are the load-bearing residual. The
   source lower bound is per read *vertex* and equals `1`; the strengthening
   `d_w ≥ x_w` is read-*instance* semantics the source does not state. Under
   `d_w ≥ x_w` the variable-length Section 6.2 witness still refutes the
   implication, but the same-length witness's truth is not even a candidate, so
   that sub-case remains **open**. Strict oriented `4^k` indexing inverts the
   Section 6.2 witnesses and is a separate unresolved fork. [source fact + open]

The genuinely open items after this reconciliation are: the referent choice
(sequence vs flow, exact vs binomial, or broad principle), the per-occurrence
same-length sub-case, strict-oriented indexing, the non-spellable-optimum
strengthening, and the sample-size regime. Tie/equivalence semantics are
irrelevant to the strict witnesses. [source gap + mathematical fact]

---

## 1. Sources and method

Primary sources read for this note (all already traced with pinned hashes in the
notes below; this note adds no new retrieval):

- Medvedev & Brudno (2009), *Maximum Likelihood Genome Assembly*,
  *J. Comput. Biol.* **16**(8) 1101–1116, §1.1, §3.1, §3.3–3.4, §4.1, §5.2,
  §6.1–6.2, §7, §8.2; DOI
  [10.1089/cmb.2009.0047](https://doi.org/10.1089/cmb.2009.0047),
  [PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/).
- Shomorony, Kim, Courtade & Tse (2016), *Information-optimal genome assembly
  via sparse read-overlap graphs*, *Bioinformatics* **32**(17) i494–i502, §2,
  §4.1, §5, Eq. (1); DOI
  [10.1093/bioinformatics/btw450](https://doi.org/10.1093/bioinformatics/btw450).
- Bresler, Bresler & Tse (2013), *Optimal assembly for high throughput shotgun
  sequencing*, *BMC Bioinformatics* **14**(Suppl 5):S18, source of the `I_s`
  bridging conditions.

Only English-language primary and secondary sources are used. The modeling
conventions, bridging predicate, and witness certificates are reconstructed in
the existing `main` notes
[`../bridging-source-semantics.md`](../bridging-source-semantics.md),
[`../section62-mb09-bidirected-graph-audit.md`](../section62-mb09-bidirected-graph-audit.md),
[`medvedev-brudno-candidate-class.md`](medvedev-brudno-candidate-class.md), and
[`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md);
this note does not re-derive them.

---

## 2. The four distinctions, defined and sourced

### 2.1 Sequence candidates (`U_seq`)

**Definition.** The nonempty circular words over the read alphabet for which the
read-count model is defined.

**Source support.** **Source fact.** MB09 §6.1 defines the exact global
read-count likelihood on “a circular genome `D` of length `N(D)`”, and then
defines the separable approximation with an external known `N`. Neither
objective imposes a support or graph condition on a candidate. Shomorony et al.
§2 samples from a circular truth, and the 2016 sentence speaks of “the
maximum-likelihood **sequence**”. So `U_seq` is the sequence-level candidate
class for both §6.1 objectives. The two objectives live in different variants
([`../ml-formalization-contract.md`](../ml-formalization-contract.md) Variants E
and A).

**Witnesses that reach it.** The two kernel-checked fixed-length witnesses
already on `main` carry the same alphabet equality pattern as issue #31/#32 and
are same-length, so negative transfer to the unrestricted-length class is by
candidate-set inclusion
([`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md)
§3):

| Witness | Objective | `\|S\|,\|D\|` | strict ratio | module |
|---|---|---|---|---|
| `AAABB → AAAAB` | exact multinomial (Variant E) | `5,5` | `2` | `FixedLengthExactCounterexample` |
| `AAACC → AAAAC` | literal product of binomial marginals (Variant A) | `5,5` | `1125/512` | `FixedLengthBinomialCounterexample` |

The literal product retains `x_i = 0` factors; dropping them gives the
positive-support objective, for which the same pair still gives a strict ratio
`9/8`, so the refutation does not depend on the zero-count convention. Both
instances satisfy the source `I_s` bridging hypothesis. [verified computation +
kernel-checked]

### 2.2 Spellable Section 6.2 circuits (`U_spell`)

**Definition.** Circular words `D` whose cyclic length-`L` window walk is an
admissible closed flow in the transitively reduced bidirected read-overlap graph
built from the observed read molecules. Under the source per-vertex lower bound
`1` and at `o_min = L−1`, this is exactly support equality,
`supp(spec_L(D)) = supp(x)` — every observed read molecule occurs in `D` and
every window of `D` is observed. At `o_min < L−1` the graph has additional
edges and support equality is only necessary, not sufficient. [source fact +
source-supported inference]

**Source support.** **Source fact.** MB09 §6.2: the graph’s vertices are the
reads, which “are DNA molecules”; “the original double-stranded genome
corresponds to a circuit (assuming high enough coverage)”; and “Each vertex has
a lower bound of `1`”. Observation 7 identifies visits to a read vertex with
occurrences of that molecule in the spelled molecule. `U_spell` is therefore a
source-supported *sequence-level restriction* of §6.2, not the whole §6.2 object.
[source fact]

**Why `U_seq` witnesses do not transfer here.** The `AAABB/AAAAB` and
`AAACC/AAAAC` pairs carry windows (`ABB`, `BBA`, `ABA` resp. `ACC`, `CCA`,
`ACA`) that were never observed, so their spectra leave the observed read-type
support. They are not graph-representable and say nothing about `U_spell`.
[verified computation]

**Witnesses that reach it** (both strict, both on `main`, both kernel-checked):

| Witness | `\|S\|,\|D\|` | objective | strict ratio | module |
|---|---|---|---|---|
| `AAATT → AAAATT` | `5,6` | §6.1 binomial | `9/8` | `Section62BridgingCounterexample` |
| `AAATAT → AAAAAT` | `6,6` | §6.1 binomial | `5` | `SameLengthSection62Counterexample` |
| `AAATAT → AAAAAT` | `6,6` | exact multinomial | `3` | `SameLengthSection62Counterexample` |

The graph/flow certificates (explicit edges, transitive reduction, incidences,
balance, vertex lower bound `1`, no supersource/sink use) are verified in
`scripts/verify_se62_mb09_bidirected_graph.py` and in
[`../section62-mb09-bidirected-graph-audit.md`](../section62-mb09-bidirected-graph-audit.md).
The Lean predicates are finite sufficient certificates: the same-length module
uses support equality, the variable-length module uses the stronger
support-plus-`x ≤ d` predicate
(`AssemblyP1/Section62BridgingCounterexample.lean`). [kernel-checked + verified
computation]

### 2.3 Arbitrary feasible flows / non-contiguous assemblies (`U_flow`)

**Definition.** All integral §6.2 feasible flows on the transitively reduced
read-overlap graph — throughput vectors realizable by a flow that may decompose
into several walks and therefore need not spell any single sequence.

**Source support.** **Source fact.** MB09 §6.2: “Since any flow can be
decomposed into a collection of walks, our flow represents a **(non-contiguous)
assembly** of the genome.” `U_flow` is the actual object MB09 optimize, so it is
source-supported *as the Section 6.2 object*. It is **not** directly denoted by
the 2016 sentence, which is sequence-valued ([`medvedev-brudno-candidate-class.md`](medvedev-brudno-candidate-class.md)
§3, [`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md) §4).
[source fact]

**Transfer from `U_spell`, and the limit of it.** `U_spell ⊆ U_flow`: a spelled
circuit is the special flow with zero supersource/sink usage and zero read-vertex
balance. The competitor in either Section 6.2 witness is such a spelled circuit
and therefore a feasible flow, while the truth is also a feasible flow and is
strictly beaten. So the Section 6.2 witnesses refute the implication over
`U_flow` immediately; no non-spellable flow is required for falsity. The
variable-length note already records this strengthening
([`../bridging-se62-flow-ml-counterexample.md`](../bridging-se62-flow-ml-counterexample.md)
§3.3). [mathematical fact + verified computation]

What remains genuinely weaker is the claim that the **optimum is not a sequence
spectrum at all**. A finite exact computation on an unmerged branch
(`docs/section62-arbitrary-flow-witness-and-search.md` on
`analysis/issue36-nonspellable-flow`, not on `main`) exhibits an `o_min = 1`,
repeated-read instance in which a strictly better feasible flow is
non-spellable (`256/81`). That is branch evidence, not a kernel-checked theorem,
and it depends on the corrected Myers transitive reduction. It is not needed to
refute `U_flow`; it is needed only for the stronger non-spellability statement.
[open on `main`]

**Exact-multinomial caveat on flows.** For a spelled molecule the exact
multinomial is well defined, so the same-length witness’s exact ratio `3`
transfers to `U_flow` when the candidate length of a flow is read as its total
throughput `Σ_i d_i`. Extending the exact objective to genuinely non-spellable
flows is a modeling choice the source does not make. [source-supported
inference]

### 2.4 Lower-bound and copy-count conventions

Three conventions must be kept separate; only the first is the source
definition. All three are about *which* flows are candidates and how observed
counts constrain them — not about the objective’s probability model.

**(a) Per-vertex lower bound `1` (the source).** “Each vertex has a lower bound
of `1` since it represents a read that must be present in the genome at least
once. All other lower bounds are `0` and all upper bounds are infinity.” For a
spelled molecule this is support equality. **Source fact.**

**(b) Per-occurrence strengthening `d_w ≥ x_w`.** The observed multiplicity `x_w`
becomes a lower bound. This is *not* stated in MB09: `x_i` is a trial count in
§6.1 that enters only the costs `c_i`, and the §6.2 feasible set is determined by
the observed *support* and the graph, not by the magnitudes `x_i`. It is the
natural semantics if the graph’s vertices are read *instances* rather than read
*molecule types*, which conflicts with §6.2’s own identification `d_i =` vertex
flow. **Source-supported inference that (b) is a strengthening, not the source
definition.**

**(c) Identity-indexed (read-instance) vertices.** Treating duplicate reads as
distinct parallel vertices is a variant, not the §6.2 object forced by
`d_i =` per-molecule vertex flow. Any amplification derived from parallel
vertices is a property of that variant. **Source-supported inference.**

The copy-count object itself is the flow through each read vertex; `x_i` is not
a flow bound, and the objective’s finite domain is `0 ≤ d_i < N` (for `x_i > 0`,
`1 ≤ d_i < N`), imposed by the `log d_i` and `log(N − d_i)` terms rather than by
an upper flow bound. **Source fact + source-supported inference.**

**Effect on the witnesses.** The variable-length Section 6.2 witness satisfies
(b) as well as (a), so it refutes the implication under both conventions. The
same-length witness satisfies (a) but not (b): its truth has `d_S(AAA) = 1`
while `x_AAA = 2`, so under (b) the truth is not a candidate. Hence the
per-occurrence same-length sub-case is untouched and remains **open** (bounded
zero evidence). [verified computation + open]

---

## 3. Master reconciliation

Each row is one candidate-universe / convention choice. “Refuted on `main`”
means a kernel-checked strict-inequality witness already on `main` applies.

| # | Universe / convention | Source support | Refuted on `main`? | Witness / reason |
|---|---|---|---|---|
| 1 | `U_seq`, exact multinomial | **source fact** (§6.1 named target) | **yes** | `AAABB → AAAAB`, ratio `2` (kernel); inclusion to unrestricted length |
| 2 | `U_seq`, literal binomial (full product) | **source fact** (§6.1 displayed product) | **yes** | `AAACC → AAAAC`, ratio `1125/512` (kernel) |
| 3 | `U_seq`, positive-support binomial | modeling choice (drops zero factors) | **yes** | same pair, ratio `9/8` (verified) |
| 4 | `U_spell`, per-vertex LB `1`, binomial | **source fact** (§6.2 + Observation 7 + LB `1`) | **yes** | `AAATT → AAAATT` (`9/8`) and `AAATAT → AAAAAT` (`5`), both kernel |
| 5 | `U_spell`, per-vertex LB `1`, exact | **source-supported inference** (spelled molecule) | **yes** | `AAATAT → AAAAAT`, ratio `3` (kernel) |
| 6 | `U_flow`, per-vertex LB `1` | **source fact** as MB09’s object (§6.2 non-contiguous assembly) | **yes**, by `U_spell ⊆ U_flow` | same Section 6.2 witnesses; non-spellability not needed |
| 7 | Optimal flow is non-spellable | **open** | **no** (branch finite computation only) | `256/81` on unmerged branch, `o_min = 1` |
| 8 | `U_spell`, per-occurrence `d ≥ x`, variable length | strengthening, **not** source | **yes** | `AAATT → AAAATT` also satisfies `x ≤ d` (kernel) |
| 9 | `U_spell`, per-occurrence `d ≥ x`, same length | strengthening, **not** source | **no** — **open** | truth `d_S(AAA)=1 < x_AAA=2`; bounded zero |
| 10 | Identity-indexed (read-instance) vertices | variant, **not** source | n/a (different universe) | not forced by §6.2 `d_i =` vertex flow |
| 11 | Strict oriented `4^k` index | source-internal tension; not forced given §6.2 | **no** | the same-length witness inverts (`d_D(TAT)=0`); unresolved fork |
| 12 | Candidate length fixed vs free | **source gap** (sentence silent) | both lengths covered | variable- and same-length witnesses jointly |
| 13 | Tie / equivalence convention | **source gap**, but irrelevant to strict witnesses | **yes** | strict ratios refute both schemas for every `≈` |

[verified computation + kernel-checked + source facts as cited]

Rows 1–3 are sequence-level; rows 4–7 are Section 6.2-level; rows 8–11 are
convention forks on the same objects; rows 12–13 are conclusion semantics.

---

## 4. Why the sequence witnesses do not reach Section 6.2, and why the Section 6.2 witnesses do reach arbitrary flows

This asymmetry is the core of the reconciliation.

- **Sequence ⊆ Section 6.2 fails.** A vector of observed reads determines a
  graph whose vertices are **only the observed read molecules**. A candidate
  word containing an unobserved window is not spelled by that graph. The
  fixed-length witnesses `AAABB/AAAAB` and `AAACC/AAAAC` each carry an
  unobserved window on both sides, so neither the truth nor the competitor is in
  `U_spell` or `U_flow`. Candidate-set inclusion transfers only between
  length-restricted and unrestricted **sequence** classes, not from sequences
  into the graph-defined flow class.
  [mathematical fact + verified computation]

- **Spelled circuit ⊆ feasible flow holds.** A spelled molecule’s cyclic window
  walk is a closed bidirected walk with all read-vertex balances zero, edge
  lower bound `0`, throughput `≥ 1` at every observed vertex, and no
  supersource/sink usage — a feasible §6.2 flow. Therefore any strict
  spelled-circuit competitor is also a strict `U_flow` competitor, and negative
  transfer to the superset is valid. The main Section 6.2 witnesses refute
  `U_flow` outright. [mathematical fact + verified computation]

Consequences: the “arbitrary flow / non-contiguous assembly” axis is **not** a
separate obligation blocking a negative answer; only the qualitatively stronger
“the optimum is non-spellable” statement is short of a kernel check. Conversely,
the sequence-level refutations are **not** evidence about the Section 6.2 object
until represented in its graph.

---

## 5. What remains genuinely open

1. **Referent of the 2016 phrase.** Which Medvedev–Brudno layer (exact
   multinomial, fixed-`N` binomial, §6.2 flow, or broad principle) the sentence
   denotes, and whether “sequence” is meant literally. No source selects one.
   [source gap]
2. **Per-occurrence same-length Section 6.2 sub-case** (row 9). Only bounded
   zero evidence; the truth of the known witness is not even a candidate.
   [open]
3. **Strict oriented `4^k` indexing** (row 11). The Section 6.2 witnesses invert;
   no refutation. Given §6.2 the index resolves to molecule classes, but whether
   the 2016 sentence imports §6.2 at all is item 1. [open]
4. **Non-spellable optimum** (row 7). Branch finite computation, not
   kernel-checked, not on `main`. Not needed for falsity. [open]
5. **Sample-size regime.** Per-instance versus high-coverage consistency. The
   witnesses are small finite per-instance instances. [source gap]
6. **Publisher supplement**, still unretrieved (HTTP 403), the last accepted
   artifact that could name a likelihood/tie object. [open]

Tie and equivalence semantics are **not** on this list for the integrated
witnesses: a strict competitor refutes the truth-is-a-maximizer schema and hence
every stronger schema for every genome equivalence
([`conclusion-semantics-strict-witness-robustness.md`](conclusion-semantics-strict-witness-robustness.md)
§3, [`equivalence-and-tie-wellposedness.md`](equivalence-and-tie-wellposedness.md)
Fact 5).

---

## 6. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| MB09 contains a sequence objective (`U_seq`) with no support condition, and a graph/flow object (`U_flow`) that may be non-contiguous | source fact | §6.1–6.2 |
| The truth is a circuit in the §6.2 graph; per-vertex lower bound is `1` | source fact | §6.2 |
| Spelled circuit = support equality at `o_min = L−1`; ⊆ feasible flows | mathematical fact | Observation 7 + flow definition |
| `x_i` enters only the objective; `d_w ≥ x_w` is a strengthening | source-supported inference | §6.1–6.2 |
| Identity-indexed vertices are a variant, not the §6.2 object | source-supported inference | §6.2 `d_i =` vertex flow |
| `AAABB → AAAAB` refutes `U_seq` exact (ratio `2`); `AAACC → AAAAC` refutes `U_seq` literal binomial (`1125/512`); neither is graph-representable | kernel-checked + verified computation | `main` modules/scripts |
| `AAATT → AAAATT` and `AAATAT → AAAAAT` refute `U_spell` and, by inclusion, `U_flow`, under per-vertex LB `1` | kernel-checked (Lean) + verified computation (graph) | `main` modules/scripts |
| Variable-length witness survives the per-occurrence strengthening; same-length witness does not | verified computation | this note’s script |
| Non-spellable optimum exists (`256/81`) | branch finite computation, **not** kernel-checked, not on `main` | unmerged branch |
| Strict oriented indexing inverts the same-length witness | verified computation | `mb09-se61-index-orientation-resolution.md` + script |
| The 2016 referent, per-occurrence same-length case, orientation, regime, supplement remain open | source gap / open | §§1, 5 |

---

## 7. Cross-references

- [`../open-problem.md`](../open-problem.md): the published sentence and what
  would count as settlement.
- [`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md),
  [`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md),
  [`medvedev-brudno-candidate-class.md`](medvedev-brudno-candidate-class.md),
  [`shomorony-ml-reference.md`](shomorony-ml-reference.md): the referent.
- [`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md):
  negative transfer across sequence candidate classes.
- [`mb09-se61-index-orientation-resolution.md`](mb09-se61-index-orientation-resolution.md):
  oriented `4^k` versus molecule-class indexing.
- [`conclusion-semantics-determination.md`](conclusion-semantics-determination.md),
  [`conclusion-semantics-strict-witness-robustness.md`](conclusion-semantics-strict-witness-robustness.md),
  [`equivalence-and-tie-wellposedness.md`](equivalence-and-tie-wellposedness.md):
  maximizer vs uniqueness, equivalence, ties.
- [`../literature/ml-tie-semantics.md`](../literature/ml-tie-semantics.md):
  the maximizer-vs-uniqueness source ambiguity.
- [`../ml-formalization-contract.md`](../ml-formalization-contract.md): the
  Variant E/A/F separation and candidate-universe discipline.
- [`../fixed-length-exact-counterexample.md`](../fixed-length-exact-counterexample.md),
  [`../fixed-length-binomial-counterexample.md`](../fixed-length-binomial-counterexample.md):
  the `U_seq` witnesses.
- [`../bridging-se62-flow-ml-counterexample.md`](../bridging-se62-flow-ml-counterexample.md),
  [`../section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md),
  [`../section62-mb09-bidirected-graph-audit.md`](../section62-mb09-bidirected-graph-audit.md):
  the `U_spell` / `U_flow` witnesses and their graph certificates.
- [`../bridging-source-semantics.md`](../bridging-source-semantics.md): the `I_s`
  predicate.

Primary sources: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* **16**(8) (2009) 1101–1116, §1.1, §3.1, §3.3–3.4,
§4.1, §5.2, §6.1–6.2, §7, §8.2, DOI `10.1089/cmb.2009.0047`; Ilan Shomorony,
Samuel H. Kim, Thomas A. Courtade, David N. C. Tse, *Information-optimal genome
assembly via sparse read-overlap graphs*, *Bioinformatics* **32**(17) (2016)
i494–i502, §2, §4.1, §5, Eq. (1), DOI `10.1093/bioinformatics/btw450`; Guy
Bresler, Ma’ayan Bresler, David Tse, *Optimal assembly for high throughput
shotgun sequencing*, *BMC Bioinformatics* **14**(Suppl 5):S18 (2013).
