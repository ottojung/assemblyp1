# Shomorony–Medvedev–Brudno referent reconciliation for the repository's concrete objectives

_Status: provenance-backed classification of the repository's formal surfaces
into the finite universe of readings, written for issue #208 (finite research
front), 2026-10-09. It does **not** select a referent, does **not** settle the
published question, and does **not** duplicate the mathematical-case work of
issues #209–#216._

_Why this file exists. This note is referenced by **name** at
[`../oriented-same-length-ml-88.md`](../oriented-same-length-ml-88.md) §1.3
("neither is advertised as *the* objective the 2016 sentence denotes
(`docs/source-notes/shomorony-mb-formulation-referent-reconciliation.md`)"), but
no file of that name had ever existed on any branch — a **repository defect**,
not an unmerged-branch artifact (unlike the other live dangling references such
as `docs/source-notes/shomorony-ml-quantifier-sequence-resolution.md`, which
existed on `analysis/issue36-*` branches and was recovered in this change). This
note supplies the missing content and records the defect in §6._

_Epistemic tags: **source fact**, **mathematical fact**, **verified
computation**, **kernel-checked**, **source-supported inference**,
**interpretation**, **repository fact**, **research choice**, **source gap**._

_Reproduce: `python3 scripts/verify_finite_interpretation_audit.py --sources
<dir>` for every source quotation used here (`<dir>` holds the artifacts of
[`finite-interpretation-universe-audit.md`](finite-interpretation-universe-audit.md)
§1; this front's cache is the untracked `scratch-208/sources`); `lake build`
for the kernel-checked Lean classification._

---

## 0. Bottom line

1. **The #88 module's two objectives are cells of a 4×2×4×2 grid, not the
   referent.** The finite universe of readings enumerated in
   [`finite-interpretation-universe-audit.md`](finite-interpretation-universe-audit.md)
   §3 has **64** cells (48 specific + 16 meta-reading `P`; 32 specific
   sequence-valued). `AssemblyP1.OrientedSameLengthML.exactLik` occupies `E ×
   R-oriented × U2 × {W,S}` and `binomialLik` occupies `A × R-oriented × U2 ×
   {W,S}`. [verified computation; kernel-checked]
2. **No primary source selects any cell.** The accepted 2016 text names
   Medvedev–Brudno by bibliography only: 3 occurrences of "likelihood" in the
   9-page typeset article, 0 of "multinomial"/"binomial", 10 of "Medvedev", and
   no section, equation, page or length/tie pointer. [source fact;
   finite-interpretation-universe-audit.md §2.1]
3. **The repository's kernel-checked surfaces already cover eight distinct
   cells**, six of them negatively and two positively (§2). Keeping them apart
   is a **research choice** mandated by
   [`../ml-formalization-contract.md`](../ml-formalization-contract.md)
   constraints 1, 3, 7 and 8, not a claim that any one of them is the published
   statement. [research choice; repository fact]
4. **Eight exclusions bound the classification** (§3). Each is a statement about
   source support, not mathematical legitimacy; excluded cells may still be
   legitimate restricted subproblems. The eighth (X8) excludes the doubled-strand
   `2G`/`2N` data model of the bridging literature as a reading of the 2016
   sentence, because no Shomorony version uses it
   ([`finite-interpretation-universe-audit.md`](finite-interpretation-universe-audit.md) §2.4, §5).
5. **Five unresolved source gaps remain** (§4), of which the referent itself and
   the publisher supplement (HTTP 403 behind Cloudflare, re-measured this run)
   are the only two that could *add* source support rather than refine a choice.
6. **A further convention axis is recorded, not assumed** (§6): the 2016 paper
   assumes the reads in `R` are all distinct (achievable by a preprocessing
   step, §3.2) while MB09 §6.1 defines the likelihood over raw read counts.
   Raw-sample vs deduplicated-algorithm-input is decision-relevant and is
   recorded as a distinct axis, integrating the post-terminal cross-check.

---

## 1. The classification rule

A cell is `(objective layer, representation panel, candidate universe,
conclusion schema)`, using the axis definitions of
[`finite-interpretation-universe-audit.md`](finite-interpretation-universe-audit.md)
§3. The axes are those of the published sentence, not of any Lean module:

| Axis | Values | What it fixes |
|---|---|---|
| `O` objective layer | `E` exact multinomial (candidate-intrinsic `N(D)`), `A` separable fixed-`N` binomial, `F` §6.2 bidirected-flow feasible set, `P` unspecified ML principle | the function being maximized |
| `R` representation panel | `R-oriented` (oriented length-`L` windows + cyclic shift), `R-molecule` (reverse-complement `k`-molecule classes + dihedral) | the index set and the genome equivalence, coupled |
| `U` candidate universe | `U1` all nonempty circular candidates, `U2` candidates of the true length `G`, `U3` §6.2 support-equality spelled candidates, `U4` §6.2 general flows | what the quantifier ranges over |
| `T` conclusion schema | `W` truth is a maximizer, `S` every maximizer is the truth up to `≈` | what "is the maximum-likelihood sequence" means |

Two facts make the axes non-interchangeable, both verified by execution in
`scripts/verify_finite_interpretation_audit.py`:

- **Objective layer is decision-relevant.** On `S = AAATAT`, `D = AAAAAT`,
  `G = 6`, `L = 3`, reads at starts `(0,0,2,4,2)`: `L_E(D)/L_E(S) = 9/8 > 1`
  while `L_A(D)/L_A(S) = 59049/62500 < 1`. The two objectives rank the same pair
  in opposite directions, so a theorem at one layer does not transfer to the
  other. [verified computation; mathematical fact]
- **Representation panel is decision-relevant for `E`.** The same instance gives
  `1/3 < 1` under `R-molecule` while `A` keeps its sign (`1/5`). Cross-check on
  `main`'s kernel-checked `AAATAT → AAAAAT` witness (starts `(0,0,1,3,5)`,
  molecule convention) the pair gives `3` (`E`) and `5` (`A`). [verified
  computation; kernel-checked]

---

## 2. Where the repository's formal surfaces sit

"Status" is the status **inside that cell only**. Every row is a declaration of
a module that CI audits and replays: the `axiom-audit` job runs with `--root
AssemblyP1 --modules-from AssemblyP1` (so every source module, not only those
the aggregator imports) allowing `propext`, `Classical.choice` and `Quot.sound`,
and a separate job replays the whole library through the kernel with
`leanchecker`. The explicit `#print axioms` list in `AssemblyP1.lean` names a
subset of declarations and does **not** name the three `OrientedSameLengthML`
maximizer theorems above, so their axiom status rests on the CI audit rather
than on the aggregator's list. [repository fact; the CI configuration was read
this run and the module and theorem names were resolved in the working tree,
but no rebuild was executed this turn] No row is advertised as the published
statement.

| Surface | `O` | `R` | `U` | `T` | Content | Status in the cell |
|---|---|---|---|---|---|---|
| `AssemblyP1/ExactVariantECounterexample.lean` | `E` | `R-oriented` | `U1` | `W` | `ACGT` (4) vs `ACACGT` (6); observed multiset `{AC, AC, GT}` (start `0` twice); full `I_s` kernel-checked | **Refuted** (`truth_not_maximum_likelihood`) |
| `AssemblyP1/FiniteSamplingCounterexample.lean` | `E` | `R-oriented` | `U1` | `W` | `AABBC` (5) vs `AABC` (4), `L = 3`; ratio `25/16`; full `I_s` | **Refuted** (population-line witness, not the 2016 sentence) |
| `AssemblyP1/FixedLengthExactCounterexample.lean` | `E` | `R-oriented` | `U2` | `W` | `AAABB` → `AAAAB`, ratio `2`, full `I_s` | **Refuted** (`fixed_length_exact_counterexample`) |
| `AssemblyP1/FixedLengthBinomialCounterexample.lean` | `A` | `R-oriented` | `U2` | `W` | `AAACC` → `AAAAC`, ratio `1125/512`, full `I_s` | **Refuted** |
| `AssemblyP1/SameLengthExactMLCounterexample.lean` | `E` | `R-oriented` | `U2`∩`U3` | `W` | `AABB` → `ABAB`, `1/4` vs `1/16`; literal `SpelledFeasible62` competitor | **Refuted** as *dominance*; the maximizer-with-membership claim has a false antecedent at this instance |
| `AssemblyP1/SameLength62Maximizer.lean` | `E` | `R-oriented` | `U3` | `W` | `informationFeasible_62_maximizer`: the truth maximises `exactLik` over **genuine** `SpelledFeasible62` candidates, under `hno` + a genuine §6.2 certificate | **Proved** with explicit premises |
| `AssemblyP1/OrientedSameLengthML.lean` | `E` and `A` | `R-oriented` | `U2` | `W` and `S` | `same_length_exactLik_maximizer`, `same_length_binomialLik_maximizer`, `same_length_unique_up_to_rotation_of_bbt` (external BBT premise) | **Proved** with explicit premises; two objectives, two names, no theorem relating them |
| `AssemblyP1/SameLengthSection62Counterexample.lean` | `E` (ratios `3`, `9`, `27`; `A` ratios `5`, `25`, `125`) | `R-molecule` | `U2`∩`U3` | `W` | `AAATAT` → `AAAAAT`, same length, molecule classes | **Refuted** |
| `AssemblyP1/Section62BridgingCounterexample.lean` | `E` | `R-molecule` | `U3`, variable length (5 vs 6) | `W` | `AAATT` → `AAAATT`, ratio `9/8`; literal `SpelledFeasible62` for **both** candidates plus the exact bidirected-graph/transitive-reduction/balance certificate | **Refuted** (`se62_bridging_bidirected_flow_counterexample`) |

**Three consequences for the #88 module that this note was written to justify.**

1. `exactLik` and `binomialLik` are **different cells** of the `O` axis, and the
   `9/8`-vs-`59049/62500` disagreement shows they can order the same pair
   oppositely. The module therefore gives them separate definitions, separate
   congruence lemmas and separate maximizer theorems, and no theorem relates
   them. That is contract constraint 3, not an accident.
2. Both objectives are instantiated at `U2` (`D : Fin G → α`, so competitor
   length is a **type**). A `U2` theorem is a restricted result; inclusion
   transfers it to `U1` for negative claims, but the restriction must stay in
   the theorem name. [mathematical fact for the inclusion; source-supported
   inference that `U2` is a restriction]
3. Neither objective is designated as the referent. The designation step would
   be a **source** step, and no source performs it (§4).

---

## 3. Exclusions (each is about source support, not mathematical legitimacy)

- **X1 — `F` as a sequence-level referent.** The 2016 sentence asks whether "the
  maximum-likelihood **sequence**" is the truth; §6.2 optimizes over flows and
  MB09 route the single-sequence question to a §7 heuristic. Reading `F` at the
  sequence level requires a flow→contig/decomposition step that neither source
  supplies. [source fact + interpretation; reconciliation §4;
  `shomorony-ml-quantifier-sequence-resolution.md` §1–§2]
- **X2 — `U4` crossed with `W`/`S`.** A flow witness does not answer a question
  phrased about sequences. `Section62BridgingCounterexample.lean` refutes the
  §6.2-flow-level statement (and its sequence-level support/lower-bound
  certificate); it therefore does **not** by itself refute the published
  sentence, which is sequence-valued. [source fact + interpretation]
- **X3 — `R-molecule` with cyclic-shift-only equivalence.** Under molecule read
  types every candidate ties with its reverse complement, so `S` would be false
  for every observation. The panel pairing is forced. [mathematical fact;
  `equivalence-and-tie-wellposedness.md`]
- **X4 — `U2` as a source reading of `E`.** MB09 §6.1 restricts nothing about
  competitor length; "known `N`" is a likelihood parameter, not a candidate-length
  constraint. `U2` is retained because the repository's witnesses and the
  operative lineage use it. [source-supported inference; research choice]
- **X5 — "all circular candidates" as `A`'s domain.** `A` is defined only where
  `d_i < N` for every type, because `c_i(d_i)` contains `log(N − d_i)`. The #32
  pair has every `d_i ≤ 2 < N = 5`, so it lies in the domain. [source-supported
  inference; reconciliation §6]
- **X6 — equivalences coarser than the panels.** No source proposes identifying
  candidates with different composition (e.g. by spectrum).
- **X7 — `P` admits no finite witness.** If the phrase denotes an objective
  family, no single proof or counterexample settles it, because the objective is
  not fixed.
- **X8 — the doubled-strand `2G`/`2N` data model as a reading of the 2016
  sentence.** Bresler–Bresler–Tse remap double-stranded DNA into their
  single-strand model by "defining `s` as the length-`2G` concatenation of `u`
  and `ũ` … so that there are `2N` reads". That is a real length/strand
  convention in the bridging literature, but the accepted 2016 text uses a
  single-stranded circular `s` of length `G` with `N` reads and mentions reverse
  complement once, as preprocessing that *adds* reads. A `2G`/`2N` reading is
  therefore a repository choice, not a source reading. [source fact for both
  models; interpretation for the exclusion]

---

## 4. Unresolved source gaps

1. **Referent.** No primary source selects among `E`, `A`, `F`, `P`. The
   accepted text, MB09's self-description, the 2010 thesis, Howison et al.
   (2013), Varma et al. (2011), Ghodsi (arXiv:1302.4391v3) and the earlier
   Shomorony preprint all bear on it and none decides it.
2. **Publisher supplement.** The accepted supplementary ZIP (sections A–G)
   returns HTTP 403 behind a Cloudflare challenge from every endpoint tried
   (re-measured this run). It is the last unexamined accepted artifact that
   could contain a likelihood, length or tie definition; the preprint's own
   supplement §6.1–6.4 was examined and contains no likelihood definition, which
   does not close the publisher's ZIP.
3. **MB09 `4^k` versus molecule classes.** §6.1 writes "There are `4^k` such
   variables" while its model vocabulary and §6.2 graph are molecular
   (`(4^k + p_k)/2` classes: `2, 10, 32, 136, 512, 2080` for `k = 1…6`). Given
   §6.2 the index set is molecule classes, but a formalization must name its
   choice.
4. **Maximizer versus uniqueness.** `W` versus `S` is not decided by the
   sentence or by MB09; the singular "the maximum-likelihood sequence" cannot
   distinguish them. Contemporary usage leans toward `W`: Howison, Zapata &
   Dunn (2013) define "a maximum likelihood assembly is the assembly that has
   the highest likelihood" (§5), and Ghodsi (arXiv:1302.4391v3) notes that "the
   resulting Eulerian graph may have many tours, all of which will have equal
   likelihood" — acknowledging ties without adopting schema `S`. Neither
   source states a tie-break or uniqueness claim. [source fact for both
   quotations; source gap for the schema selection]
5. **Composition.** Shomorony's bridging conditions and MB09's likelihood are
   never composed by any source (0 occurrences of "bridg*" in MB09 and in the
   2010 thesis; no likelihood formula in any Shomorony version). Every reading of
   the 2016 sentence is a proposed composition of two decoupled formalisms.
6. **Read-set convention (scope of the distinctness assumption).** Whether the
   2016 distinctness sentence (§6) limits only the complexity analysis or also
   the formal `I_s` input is not explicitly resolved by the paper. The set-based
   feasibility formalism is evidence for the latter reading but is not a
   statement of it.

The audit's gap register
([`finite-interpretation-universe-audit.md`](finite-interpretation-universe-audit.md) §6)
additionally records three items that are not source gaps about the referent:
the Varma et al. (2011) full text (abstract reproduced through OpenAlex only),
the repository-provenance repairs of this change, and one **dead citation
locator** in a sibling note (`se62-revcomp-index-decision.md` on
`analysis/se62-revcomp-index-decision-0920`, commit `7bb1f3a`), which
`scripts/audit_source_note_citations.py` detects by execution.

---

## 5. Epistemic classification (roll-up)

| Claim | Status | Basis |
|---|---|---|
| The #88 module's `exactLik`/`binomialLik` occupy distinct cells of the 64-cell grid | repository fact + kernel-checked | `AssemblyP1/OrientedSameLengthML.lean`; audit §3 |
| `E` and `A` order one pair oppositely; the panel moves `E` only | verified computation | `scripts/verify_finite_interpretation_audit.py` groups 1–2 |
| The nine surfaces of §2 cover eight cells, six negatively and two positively | kernel-checked | the listed modules |
| The accepted text selects no cell | source fact | audit §2.1 census |
| `F` is not sequence-valued without a bridge (X1–X2) | interpretation | reconciliation §4; quantifier note §1–§2 |
| `A`'s domain is definedness-limited (X5) | source-supported inference | reconciliation §6 |
| `U2` is a restriction without full source support (X4) | source-supported inference | audit §3.3 |
| Keeping `E`/`A`/`F`/`P` distinct is the repository's choice | research choice | `../ml-formalization-contract.md` |
| The 2016 §3.2 all-distinct-reads assumption, the §2 sampling model, and the set-based `R covers s` formalism | source fact | accepted OUP text §2, §3, §3.2 (p. i498) |
| MB09 §6.1 likelihood is over raw counts `x_i` from `n` independent trials; §6.2 gives one vertex per read, lower bound 1 | source fact | MB09 §6.1–6.2 |
| The 2016 ML question is stated over a deduplicated read set; MB09's over the raw sample | interpretation | §6 |
| Raw-sample vs deduplicated-algorithm-input is a distinct, decision-relevant convention axis | research choice | §6; issue #208 cross-check |
| The two-layer read-set model is standard in the contemporary ML-assembly lineage (Ghodsi's prefix graph) | source fact | §6; Ghodsi arXiv:1302.4391v3 §1 |
| Howison et al. define ML assembly as the highest-likelihood assembly (W schema) | source fact | §4.4; Howison §5 |
| Ghodsi notes equal-likelihood tours exist but does not adopt schema S | source fact | §4.4; Ghodsi §2 |
| The repository's witnesses use the raw-sample convention (observed multisets with multiplicity) | repository fact | `ExactVariantECounterexample.lean` et al.; §2 |
| Referent, supplement, `4^k`, tie semantics, composition, read-set convention scope | source gap | §4 |

---

## 6. Read-set convention axis: raw sample vs deduplicated algorithm input

Integrates the post-terminal independent primary-source cross-check
(research-assistant, issue #208, 2026-10-09) into this classification. The
cross-check surfaced a source-facing distinction that the 4×2×4×2 grid
records only implicitly: the two papers' read sets are different *data
layers*. The axis is recorded here alongside the grid rather than as a fifth
grid axis, because the grid's cardinality is owned by
[`finite-interpretation-universe-audit.md`](finite-interpretation-universe-audit.md)
and this integration does not reopen that enumeration. [research choice]

**Source facts (2016).** The accepted OUP text states, in §3.2 (p. i498), in
the running-time paragraph of the NOT-SO-GREEDY pruning discussion:

> "… the reads in `R` are assumed to be all distinct from each other (which
> can be achieved by a preprocessing step) …"

(the PDF extraction joins `R are` as `Rare`; normalized here). The same
paper's §2 draws the model — "each of the `N` reads is drawn independently
and uniformly at random from the length-`L` substrings of `s`" — under the
banner "two simplifying assumptions about the set of reads" (equal length;
error-free), so the sampling model itself permits duplicate reads. The
feasibility/bridging formalism is set-based: "`R` covers `s` (i.e. each base
is read by at least one read in `R`)."

**Source facts (MB09).** §6.1 defines the likelihood over the raw sample:
"the dataset of `n` reads corresponds to a set of outcomes from `n`
independent trials," with `X_i` = "the number of trials whose outcome is
`i`" — duplicate reads carry the coverage signal. §6.2 then gives the graph
one vertex per read, with "a lower bound of 1 since it represents a read that
must be present in the genome at least once" (§2.3 of the MB09-side
reconciliation).

**Source fact (contemporary usage, Ghodsi arXiv:1302.4391v3).** The same
two-layer separation appears in the contemporary ML-assembly literature.
Ghodsi's prefix graph gives "each read … correspond[s] to a vertex" (one
vertex per read type — deduplicated graph structure) while the objective
counts `n_i` = "the number of times read i 'appears' in `A`" (raw
multiplicities), and duplicate reads are handled as "two or more reads [that]
have the same sequence … connected by a zero length path." The two-layer
model is therefore not an artifact of the 2016/MB09 comparison but a standard
feature of the lineage's formalizations. [source fact; Ghodsi arXiv:1302.4391v3
§1, located in the hash-verified artifact]

**Source-supported inference.** In the 2016 paper the distinctness sentence
appears only inside the complexity argument (it yields `L ≥ log₄N`, hence the
`O(NL)` bound); the paper never restates it in the `I_s`/bridging definitions,
which are set-based throughout. The paper's own usage therefore reads the
reconstruction algorithm's input as a deduplicated read set (equivalently, a
preprocessed one), while its §2 sampling model remains a raw sample. Whether
the distinctness sentence limits *only* the complexity analysis or also the
formal `I_s` input is not explicitly resolved by the paper (§4.6). [source
gap for the scope question]

**Interpretation.** Read against its own stated assumptions, the 2016 ML
question is stated over a deduplicated read set, whereas MB09's §6.1
likelihood is defined over the raw sample. Raw-sample vs
deduplicated-algorithm-input is therefore a **distinct convention axis** of
the interpretation universe, not a presentational detail. [mathematical fact
for the mechanism] Duplicating one sampled start changes the counts `x_i`
and with them the exact ML likelihood, while leaving the deduplicated support
— and with it every existing bridging witness — unchanged.

**Research choice (axis recorded, not silently assumed).** When transferring
`I_s` to finite ML, the repository records two data layers per cell:
(i) the raw sampled-start/read multiset with `x_i`, `n` for the statistical
likelihood, and (ii) the deduplicated read/placement support fed to the
reconstruction graph and used for bridging. The repository's kernel-checked
witnesses already use layer (i) — e.g. `ExactVariantECounterexample`'s
observed multiset `{AC, AC, GT}` (start `0` twice) — matching MB09 §6.1's
`x_i` bookkeeping. [repository fact for the witnesses] The axis is
decision-relevant for likelihood values and must be recorded per cell, not
silently assumed. It is *not* a claim that the 2016 algorithm accepts
duplicate vertices: its complexity argument preprocesses them away. The axis
underwrites the #210 exact-ML amplification lemma without conflating the two
papers' input conventions (the cross-check's stated purpose).

## 7. Repository defect recorded (and repaired by this note)

`docs/oriented-same-length-ml-88.md` §1.3 referenced
`docs/source-notes/shomorony-mb-formulation-referent-reconciliation.md`, which
never existed on any branch (`git log --all --diff-filter=A` finds no such path).
The reference is a code-span, so `scripts/check-research-docs.py`'s markdown-link
checker does not flag it; the note's existence now makes the reference resolve.

**Terminology check (recorded because the front's task packet carried it).**
"MB09" abbreviates **Medvedev and Brudno**, *Maximum Likelihood Genome
Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116 — the paper the 2016 sentence
cites — and **not** Myers et al. Using "Myers et al. (MB09)" for it would
mis-attribute the source; every quotation in this note is from the Medvedev and
Brudno artifact hashed in
[`finite-interpretation-universe-audit.md`](finite-interpretation-universe-audit.md)
§1. [repository fact]

Distinct from the genuinely *unmerged-branch* references
(`shomorony-ml-quantifier-sequence-resolution.md` — recovered in this change;
`se62-feasibility-necessity-determination.md`, which exists on the unmerged
`analysis/issue36-*` branches and is currently uncited in the live tree;
`mb09-se62-likelihood-index-adversarial-audit.md`,
`oriented-se62-rigidity-audit-2026-09-20.md`, `se62-revcomp-index-decision.md`,
`uniform-oriented-rigidity-obstruction.md`, `ml-objective-candidate-class-resolution.md`,
`primary-provenance-verification.md`, and others), which are labelled as
unmerged-branch artifacts where they are cited.
[repository fact; verified by `git log --all --diff-filter=A`]

## 8. Relation to the other source notes

- [`finite-interpretation-universe-audit.md`](finite-interpretation-universe-audit.md)
  enumerates the universe, its arithmetic and its exclusions; this note maps the
  repository's formal surfaces into that universe.
- [`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md)
  is the **MB09-side** reconciliation (four objects, four readings, ranking by
  literal/named/operative fit, witness-sufficiency matrix). This note is the
  **Shomorony-side and repository-side** counterpart; it imports its §4 argument
  as X1 and its §6 refinement as X5.
- [`shomorony-ml-quantifier-sequence-resolution.md`](shomorony-ml-quantifier-sequence-resolution.md)
  fixes the quantifier axis (single sequences) that X1 relies on.
- [`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md)
  and [`shomorony-ml-reference.md`](shomorony-ml-reference.md) supply the
  version-history and accepted-text facts; neither is revised here.
- The post-terminal research-assistant cross-check (raw sample vs
  deduplicated algorithm input) is integrated in §6 and registered in
  §4.6; the MB09-side counterpart is
  [`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md)
  §2.5, §8–§9.

Primary sources: Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C.
Tse, *Information-optimal genome assembly via sparse read-overlap graphs*,
Bioinformatics 32(17) (2016) i494–i502, DOI `10.1093/bioinformatics/btw450`
(accepted text, author-accepted manuscript, earlier preprint + supplement); Paul
Medvedev, Michael Brudno, *Maximum Likelihood Genome Assembly*, J. Comput. Biol.
16(8) (2009) 1101–1116, §3.1, §6.1–6.2; Paul Medvedev, *Genome Graphs*, PhD
thesis, University of Toronto, 2010, Ch. 4; Guy Bresler, Ma'ayan Bresler, David
Tse, BMC Bioinformatics 14(Suppl 5):S18 (2013); Howison, Zapata, Dunn,
Bioinformatics 29(23) (2013) 2959–2963; Varma, Ranade, Aluru, ICCABS 2011;
Mohammadreza Ghodsi, arXiv:1302.4391v3.
