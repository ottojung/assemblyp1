# Interpretation matrix for the 2016 finite bridging ⇒ ML question (issue #217)

_Status: META front #217, 2026-10-09 (final synthesis round). The matrix was
built on `origin/main` at `cc0aa8a`; the board branch `agent/board-217-978a0a`
now carries, in order, the merged Lean CI repair PR #117 (`e9fcf01`), the #217
matrix commits, and the #221 white-paper correction `729f50c` (population
uniqueness is fully kernel-checked with no external BBT premise; LaTeX
`\range`/underscore/emphasis defects fixed; the finite same-length rotation
corollary kept distinct and still Lean-conditional). The previous integration
round added the novel artifacts of the live finite leaves #208 (provenance
docs/scripts), #211 (`SameLength62TieUniqueness`), #214
(`Section62NonSpelledFlow`), #215 (`TwoDisjointCirclesDuplex`,
`DoubleStrandBridgingTransfer`) and #216 (`ImplicationLattice`). The final
synthesis round added the two verified leaf modules the earlier round tracked
but did not integrate: #210 (`OrientedVariableLengthSe62`, the oriented
unrestricted-length classification, now kernel-checked and upgrading row R14)
and #213 (`Section62VarlenPerOccurrence`, the variable-length per-occurrence
audit that hardens rows R10/R12). **This V3-settle round** adds leaf #215's
`BreslerRemapCompatibility` module, script and appendix §11, which kernel-check
the exact V3↔V1/V2 compatibility locus (R1∧R2∧R3) and both incomparability
witnesses, sharpening R16's residue statement without closing its maximizer
question. **This #209 round** adds leaf #209's `Issue209EAudit` module, three
scripts and its audit ledger/terminal report: the same `AAABB → AAAAB` witness
is kernel-checked to refute the fixed-`N` binomial objective `A` as well as the
exact multinomial (ratio `1125/512`), and the external-`N` domain boundary
(`d_w ≤ N(D)`; the literal marginal is a probability only on `|D| ≤ N`) is
kernel-checked. The cc0aa8a-based **paper** edits on the leaf branches were
deliberately **not** merged, because they would have reverted the #217/#221
paper state; only their new, self-contained files were taken. **This terminal
round** adds leaf #219, which reached `B219 TERMINAL — state: done` (branch
`agent/board-219-547404`, `81d29c6`): its `FibreCountArithmetic` module now
**compiles** and is integrated, so the pending list is empty. All ten integrated
Lean modules build and are axiom-audited at `[propext, Classical.choice,
Quot.sound]`. #216's uncommitted sample-multiplicity `Part 6` is **resolved as
redundant**, not pending: its Lean does not compile, it has no committed or board
result, and its *result* is already kernel-checked via #210
(`OrientedVariableLengthSe62`), so the lattice needs no general amplification
theorem. No leaf item remains pending.
This document is the source-backed classification matrix for the finite
(finite-sample) reading of the 2016 sentence

> “Understanding whether bridging conditions can be used to guarantee that the
> maximum-likelihood sequence is the true sequence is currently an open
> question.”

in Shomorony, Kim, Courtade and Tse (2016), whose “maximum-likelihood
formulation of the AP (Medvedev and Brudno, 2009)” is **not** named down to a
section, equation, or objective. Its job is to make the claim “all
source-supported interpretations of the 2016 finite bridging⇒ML question are
resolved” auditable: every row is an interpretation instance, every axis value
is tagged, and every row ends in a reviewed proof or an exact counterexample.
Rows that cannot so end are listed explicitly as open, with the reason.

Every claim carries one of

* **[F]** source fact — located in a cited paper;
* **[I]** source-supported inference — follows from cited text plus a stated
  argument;
* **[C]** editorial/modelling choice — the repository chose it; the source does
  not say it;
* **[M]** mathematical fact — provable, independent of the source;
* **[K]** kernel-checked — a Lean module in `AssemblyP1/` proves it;
* **[V]** verified computation — an exact-arithmetic script in `scripts/`
  reproduces it;
* **[O]** open — no proof and no exact counterexample on `main`.

This document does **not** select a referent for the 2016 sentence. That
selection remains a source gap; see
[`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md).

---

## 1. The axes

### 1.1 Objective (the likelihood layer)

| tag | definition | source |
|---|---|---|
| `E` | exact MB09 multinomial, candidate-intrinsic length: `L_E(D\|x) = n!/∏x_i! · ∏ᵢ (dᵢ/N(D))^{xᵢ}` | **F**: MB09 §6.1, “Let `D` be a circular genome of length `N(D)` … the probability … is simply `d_i/N(D)`”; 2010 thesis Ch. 4 |
| `A` | MB09 §6.1 separable approximation, product of binomial marginals at an **externally fixed** `N`, zero-count factors retained: `L_A(D\|x) = ∏ᵢ C(n,xᵢ)(dᵢ/N)^{xᵢ}(1−dᵢ/N)^{n−xᵢ}` | **F**: MB09 §6.1, “we can replace it by `N`, which is the length of the actual genome … For our experiments, we assume that the genome size is known” |
| `U` | an unspecified general ML principle | **F** (that the 2016 text names no formula) + **I** (that the sentence may denote a family) |

`E` and `A` are **not** the same objective: `A` drops `N(D)` from the objective
and is only defined on `0 < dᵢ < N`. **[M]** The external `N` is a *domain
restriction*, not a scoring license: the occurrence multiplicity satisfies
`d_w ≤ N(D)` for every read type and candidate (`Issue209EAudit.winCount_le_len`),
so the literal marginal is a product of probabilities only on the class
`|D| ≤ N`; a length-`6` candidate scored at external `N = 5` has a *negative*
marginal factor for an unobserved type (`external_N_domain_boundary`). **[K]**
`AssemblyP1/Issue209EAudit.lean`

### 1.2 Candidate universe and length convention

| tag | definition | source status |
|---|---|---|
| `U1` | all nonempty circular genomes, length free | **F** for `E`: MB09 §6.1 imposes no competitor length. **I** that `A` inherits it |
| `U2` | circular genomes of the true length `G` | **C** on `main`: the 2016 text does not state it; the 2013 survey, Varma et al. (2011) and the authors’ own earlier fixed-`G` preprint make it the best operational fit |

`U2 ⊂ U1`, so a strict witness inside `U2` transfers to `U1` (negative
transfer); a positive theorem inside `U2` does **not** transfer to `U1`. **[M]**

### 1.3 §6.2 candidate-membership rule (the flow definition)

| tag | definition | source status |
|---|---|---|
| `F0` | no read-overlap-graph feasibility: any circular candidate | **F** for `E` (MB09 §6.1 quantifies over circular genomes) |
| `Fgen` | a **genuine** §6.2 candidate: a feasible flow in the transitively reduced bidirected read-overlap graph on the observed reads, vertex lower bound 1, edge lower bounds 0, §3.4 signed-incidence balance, no supersource/sink usage | **F**: MB09 §6.2, “Each vertex has a lower bound of 1 since it represents a read that must be present in the genome at least once … the `d_i`'s … correspond to the value of the flow through vertex `i`” |
| `Fspell` | a `Fgen` candidate that is a single spelled bidirected circuit | **I**: a spelled circuit is a special case of a flow, so negatives over `Fspell` transfer to `Fgen` **[M]**; positives do not |
| `Focc` | the per-occurrence strengthening `d_D(w) ≥ x(w)` for every observed type | **C**: **not** the §6.2 definition and **not** a source fact. MB09 §6.2 states only the per-vertex lower bound `1`; `Focc` is a **project-level strengthening** (a repository-added assumption surface) |

`Focc ⊂ Fgen` when both are applied to the same observation only if a
per-occurrence-feasible object is always a genuine §6.2 flow — that containment
is **not** proved on `main` for the molecule case, which is exactly why row
R9 below is open. **[O]**

### 1.4 Strand orientation / read-type space

| tag | definition | source status |
|---|---|---|
| `or` | oriented length-`L` read strings, no reverse-complement collapse | **F**: Shomorony §2 (circular `s`, reads are substrings `s[t:t+L−1]`); reverse complement is *preprocessing* in §4.1, which adds orientation nodes rather than identifying a read with its reverse complement |
| `mol` | reverse-complement molecule classes `{w, rc(w)}` | **F**: MB09 §3.1/§4.1 (“A `k`-molecule is a DNA molecule …”, “each `k`-molecule … only once”). **F**: MB09 §6.1 nonetheless writes “There are `4^k` such variables”, an internal tension recorded in [`mb09-se61-index-orientation-resolution.md`](mb09-se61-index-orientation-resolution.md), resolved to molecule classes *given* §6.2 |
| `2G` | Bresler–Bresler–Tse doubled-strand remap `u·u~` with `N(D)=2G` | **F** for BBT 2013; **C** as a reading of the 2016 sentence (a different paper’s convention) |

Strand convention and genome equivalence are **coupled**: under `mol`,
`L(rc(D);x) = L(D;x)`, so the strong schema forces reverse complement into the
equivalence; under `or` it does not. **[M]**, see
[`equivalence-and-tie-wellposedness.md`](equivalence-and-tie-wellposedness.md).

### 1.5 Bridging rule

| tag | definition | source status |
|---|---|---|
| `Is` | full source `I_s`: coverage of the genome by realized reads, every maximal triple repeat all-bridged, every interleaved maximal-repeat pair bridged; bridging = one read strictly straddling a copy on a single integer lift (`r < t`, `t+e < r+L`) | **F**: Shomorony Eq. (1); the single-lift straddle reading is **F** for BBT/Shomorony and is the reading `SourceFaithfulIs.BridgesCopy` implements after `docs/bridging-source-semantics-fix.md` |
| `¬LTR` | only the triple-repeat clause, as `¬ HasLongTripleRepeat` | **I**: `Is → ¬LTR` at `2 ≤ L` is kernel-checked (`BridgingBridge.informationFeasible_no_long_triple_repeat`), so `Is` is stronger |
| realized-start set | `I_s` evaluated at the **range of the realization** | **F/I**: `Is` is a statement about the reads actually taken; evaluating it at a superset `R ⊇ range ρ` is a strictly weaker hypothesis, because every clause is a “some `r ∈ R` …”. The repository keeps the faithful form and names the weak one (`…_of_superset_starts`) |

### 1.6 Maximizer / tie handling

| tag | definition | source status |
|---|---|---|
| `W` | truth is a maximizer: `∀ D, L(D;x) ≤ L(S;x)` | **I**: the plain reading of “the maximum-likelihood sequence is the true sequence” |
| `S` | `W ∧` every tied candidate is equivalent to the truth | **I**: the uniqueness reading; **F** that the sentence states no tie rule |
| `≈` | genome equivalence | **M**: cyclic shift is *forced* for `S` (the exact circular likelihood is rotation-invariant); reverse complement is forced **iff** `mol` read types are used; no coarser equivalence has source support |

A **strictly** better competitor refutes `W`, hence `S`, for **every** `≈` and
every tie convention. **[M]**, see
[`conclusion-semantics-strict-witness-robustness.md`](conclusion-semantics-strict-witness-robustness.md).

---

## 2. The matrix

Legend for the resolution column: **FALSE** (a strict counterexample refutes
`W`; therefore also `S`, for every `≈`), **TRUE** (a reviewed proof), **OPEN**.

| # | Objective | Universe / length | §6.2 membership | Strand | Bridging | Conclusion | Resolution | Evidence |
|---|---|---|---|---|---|---|---|---|
| R1 | `E` | `U1` (free) | `F0` | `or` | `Is` | `W` and `S` both false | **FALSE** | Strict witness `AAABB → AAAAB`, ratio `2`; same-length, so negative transfer gives `U1`. **This round** adds (leaf #209, `Issue209EAudit`): the *same* witness also refutes the fixed-`N` binomial objective `A` with ratio `1125/512` (the two witnesses differ only by a renaming of one unused symbol), so R1 is negative under **both** source-nameable objectives | **[K]** `AssemblyP1/FixedLengthExactCounterexample.lean`; **[K]** `AssemblyP1/Issue209EAudit.lean` (`aaab_refutes_fixed_N_binomial`) |
| R2 | `E` | `U1` (free) | `F0` | `or` | `Is` | as above | **FALSE** | Unrestricted-length witness `ACGT → ACACGT`, `1/18 > 3/64` | **[K]** `AssemblyP1/ExactVariantECounterexample.lean` |
| R3 | `E` | `U1` (free) | `F0` | `mol` | `Is` | as above | **FALSE** | Molecule-class witness `AAATT → AAAAT`, ratio `2` under `or`; under `mol` the truth is not `Fgen`, see R7 | **[V]** `scripts/uniform_strand_semantics_search.py --witness` |
| R4 | `E` | `U1` (free) | `F0` | `or` | `Is` | as above | **FALSE** | Read-tiled witness `AAABCBC → AAAAABC`, `G=7`, `L=3`, realized starts `(0,0,0,1,2,5,6)`, `n=7`, ratio `27`; `Is` non-vacuous (coverage + the all-bridged maximal length-1 triple repeat at `(0,1,2)`; interleaving vacuous) | **[V]** `scripts/verify_readtiled_exact_counterexample.py` |
| R5 | `A` | `U1` (on the domain `0<dᵢ<N`) | `F0` | `or` | `Is` | `W` and `S` both false | **FALSE** | Strict witness `AAACC → AAAAC`, ratio `1125/512 > 1`; same-length pair with every `dᵢ ≤ 2 < N`, so both lie in `A`’s domain | **[K]** `AssemblyP1/FixedLengthBinomialCounterexample.lean` |
| R6 | `E` | `U2` | `F0` | `or` | `Is` | `W` false | **FALSE** | `AABB → ABAB`, `G=4`, `L=2`, realized starts `{1,3}`; full `I_s` by computation; exact likelihoods `1/16` vs `1/4` | **[K]** `AssemblyP1/SameLengthExactMLCounterexample.lean` |
| R7 | `E`/`A` | `U2` **and** `Fgen` on *both* truth and competitor | `Fgen` | `or` | `Is` | `W` **true**; `S` true up to cyclic shift | **TRUE** | `informationFeasible_62_spelledML` / `informationFeasible_62_maximizer`: full `I_s` at the realized range, `2 ≤ L ≤ G`, truth a genuine §6.2 candidate ⇒ every same-length genuine §6.2 candidate scores at most the truth | **[K]** `AssemblyP1/MLEscape.lean`, `AssemblyP1/SameLength62Maximizer.lean` |
| R8 | `E`/`A` | `U2` ∩ `Fgen` | `Fgen` | `or` | `¬LTR` only | `W` true | **TRUE** | `same_length_exactLik_maximizer`, `same_length_binomialLik_maximizer` under `hno : ¬ HasLongTripleRepeat` — the kernel-checked conditional core, with no `I_s`, no primitivity, no period premise | **[K]** `AssemblyP1/OrientedSameLengthML.lean`, `AssemblyP1/OrientedFinalRigidity.lean` |
| R9 | `E` | `U2` ∩ `Fgen` | `Fgen` | `or` | `¬LTR` + external BBT input | `S` true, `≈` = cyclic shift | **TRUE, conditional** | `same_length_unique_up_to_rotation_of_bbt`, `same_length_maximality_and_rotation_uniqueness_of_bbt`; the complete-spectrum uniqueness input is an explicit premise `hBBT`, not formalized here | **[K]** conditional, `AssemblyP1/OrientedSameLengthML.lean` |
| R10 | `A` | `U3` flows, length free | `Fgen`/`Fspell` | `mol` | `Is` | `W` and `S` both false | **FALSE** | `AAATT → AAAATT`, `|D|=6 ≠ N=5`, external `N=5`, ratio `9/8`; literal §6.2 feasibility of **both** genomes, incl. the explicit graph, transitive reduction, vertex LB 1, signed-incidence balance. Leaf #213 hardens the cell: both throughput vectors lie in the §6.1 domain `0 ≤ dᵢ ≤ N` and in the terminal-allowed general flow universe, and the competitor is the **unique** maximizer of the literal §6.1 objective over the **entire** domain, so the refutation is not an artifact of a restricted candidate class | **[K]** `AssemblyP1/Section62BridgingCounterexample.lean` (`se62_bridging_bidirected_flow_counterexample`); **[K]** `AssemblyP1/Section62VarlenPerOccurrence.lean` (`truth_not_maximizer_in_general_flow_universe`, `competitor_is_unique_optimizer`) |
| R11 | `E`/`A` | `U3` flows, **same length** | `Fgen`/`Fspell` | `mol` | `Is` | `W` and `S` both false | **FALSE** | `AAATAT → AAAAAT`, `G=6`, `L=3`, starts `(0,0,1,3,5)`, `n=5`, external `N=6`; exact ratio `3`, §6.1 binomial ratio `5`; **the interleaving clause of `I_s` is non-vacuous here** | **[K]** `AssemblyP1/SameLengthSection62Counterexample.lean` |
| R12 | `E`/`A` | `U3` flows, length free | `Fgen` + `Focc` (per-occurrence) | `mol` | `Is` | `W` and `S` both false | **FALSE** | the same `AAATT → AAAATT` instance: `d_S = (AAA:1, AAT:2, TAA:2) ≥ x`, `d_D = (AAA:2, AAT:2, TAA:2) ≥ x`, so it satisfies the strengthening, and it is a spelled circuit, hence a general §6.2 flow. Leaf #213's audit kernel-checks both the per-vertex **and** the strictly stronger per-occurrence rule for truth and competitor, and the unique-optimizer lift of R10, so the cell is refuted without appealing to the weaker source bound; the audit also records that the witness sums to `6 ≠ 5 = N` and therefore does **not** reach the same-length cell | **[K]** same modules as R10 (`SeqSupportLB` conjuncts) plus `AssemblyP1/Section62VarlenPerOccurrence.lean` (`truth_per_occurrence`, `competitor_per_occurrence`, `competitor_is_unique_optimizer`, `competitor_outside_length_constrained_domain`); record `docs/section62-varlen-per-occurrence-audit-213.md`; **[V]** `scripts/verify_se62_varlen_per_occurrence_audit_213.py` |
| R13 | `E`/`A` | `U3` flows, **same length** | `Fgen` + `Focc` | `mol` | `Is` | `W` and `S` both false | **FALSE** | Strict witness `ATATACAC → ATACACAC`, `G=8`, `L=3`, o_min `2`, realized starts `(1,3,4,5,6,7)`, `n=6`, external `N=8`; `x = {ATA/TAT:1, TAC/GTA:1, ACA/TGT:2, CAC/GTG:1, CAT/ATG:1}`, `d_S = {…, ATA/TAT:3, ACA/TGT:2, …}`, `d_D = {…, ATA/TAT:1, ACA/TGT:3, CAC/GTG:2, …}`; both spectra support-equal to `x` **and** per-occurrence feasible (tight coordinate `ACA/TGT`, `x = d_S = 2`), `n = 6 < G = 8` so not read-tiled; exact ratio `3/2`, §6.1 binomial ratio `9/5`; both literal §6.2 bidirected circuits on the 16-edge graph, reduction vacuous under both readings. Census: 4 distinct beats at `(G,L,sigma)=(8,3,4)`, bounded evidence only. Harvested read-only from leaf #212 | **[K]** `AssemblyP1/PerOccurrenceSameLengthCounterexample.lean` (`peroccurrence_samelength_se62_bidirected_flow_counterexample`, `peroccurrence_samelength_maximality_refuted`), **V** `scripts/verify_peroccurrence_dna_samelength_212.py`, record `docs/peroccurrence-samelength-dna-counterexample-212.md` |
| R14 | `E`/`A` | `U1` (free length; the witness has `|D| ≠ G`) | `F0`; `Fgen`/`Fspell` (the certificate discharges the stronger reading too) | `or` | `Is` | `W` false as soon as `n > G` | **FALSE** | oriented single-strand variable-length §6.2, **infinite families** and not a bounded search. Truth `S = AAATT` (`G=5`), `L=3`, `R={0,1,2,3,4} ∈ I_s` at full strength (kernel-checked by `decide` on `SourceFaithfulIs.InformationFeasible`), all candidates genuinely §6.2-feasible under the per-vertex, spelled-support and single-circuit readings. Family A (growing `D_M = A^{3+M}TT`, exact objective) is strict for every `M ≥ 1` with closed form `(5/(5+M))^{5+M}(1+M)^{1+M}`; Family B (fixed `D = AAAATT`, exact) strict for every `M ≥ 1` with `(3125/3888)(5/3)^M`; Family C (fixed `D`, fixed-`N` binomial, `N=5`) strict for every `M ≥ 1` with `(81/128)2^M`. Kernel-checked instances at `M=1,2`: exact `15625/11664`, `2109375/823543`; binomial `81/64`, `27/16`. The truth wins exactly at `n=G`; a single extra observation of the over-represented `AAA` type overturns it (sampling instability). This is the amplification mechanism: each extra `AAA` multiplies the exact odds by `p_D(AAA)/p_S(AAA) = 5/3` and the binomial odds by `Q_AAA = 2` | **[K]** `AssemblyP1/OrientedVariableLengthSe62.lean` (`oriented_variable_length_se62_counterexample`, `…counterexample'`), integrated and axiom-audited; general proof + families in `docs/source-notes/oriented-variable-length-se62.md`; **[V]** `scripts/verify_oriented_variable_length_se62.py`, `scripts/verify_oriented_variable_length_se62_amplification.py` (families `M=0..200`) |
| R15 | `E`/`A` | `U2` ∩ `Fgen` | `Fgen` + `Focc` | `or` | `Is` | `W` true | **TRUE, inherited** | a per-occurrence-restricted candidate class is a *subclass* of the genuine §6.2 class quantified over by R7 — for a spelled circuit of length `G` whose window support is `supp(x)`, the walk flow is a feasible §6.2 flow with every vertex throughput `≥ 1` — so R7’s maximizer conclusion applies unchanged. No general theorem on `main` states the subclass containment as a lemma; it is the argument used case-by-case by the same-length §6.2 modules | **[K]** inherited from R7; containment is a **M** fact for spelled circuits, **O** as a named lemma |
| R16 | `E` | `U1`/`U2` | `F0` | `2G` (Bresler doubled-strand concatenation) | remapped `Is` on the length-`2G` circle | — | **Not a determinate source row** (project-level convention); open in both directions | **Qualification (project-level strengthening, not a source fact).** Under the source-faithful reading the 2016 sentence fixes no `2G` concatenation convention, so this row is **not a determinate source row**; it records a different paper's (`Bresler–Bresler–Tse`) convention only so the exhaustiveness claim is not overstated. **No bounded search is used as evidence in either direction**: the absence of a beat in the searched scopes is **absence of a known witness**, never evidence of openness. What *is* proved is negative admissibility — the known `AAATAT → AAAAAT` witness is **inadmissible** under the remap: the doubled circle `AAATATATATTT` (length `12`) carries the maximal length-`4` triple repeat `ATAT` at starts `2,4,6`, which no length-`3` read can bridge, kernel-checked for **every** read set (`doubled_not_information_feasible`) — so the row is open in **both** directions rather than refuted. **This round** adds the exact compatibility classification (leaf #215, commits `67de8b7`/`20b6c71`/`2a3d2cf`): V3 is exactly compatible with V1/V2 (≡ V5 circle-by-circle) **iff** (R1) read-seat preservation ∧ (R2) seam–wrap agreement ∧ (R3) doubled-circle feasibility; off that locus the models are **incomparable**, kernel-checked in both directions — `GGGA` satisfies the remapped `Is` on `GGGATCCC` with natural seats `{0,1,4,5,6,7}` while failing the oriented `Is` on `GGGA` with `{0,1,2}` (the wrapping read `GAG`/`rc` `CTC` has no faithful seat; seats `6,7` are spurious windows `CCG`/`CGG`), and `AAATAT` is the reverse direction. The faithful-occurrence reading is sound in the searched scope (`0/180` violations, binary+ternary, `L=3`, `3≤G≤7`) but a **conjecture** in general | **[K]** `AssemblyP1/DoubleStrandBridgingTransfer.lean` (`doubled_not_information_feasible`); **[K]** `AssemblyP1/BreslerRemapCompatibility.lean` (`remap_natural_seat_not_sound`, `remap_not_complete`, `seat6_spurious`, `seat7_spurious`, `v5_ggga_fails`); **[V]** `scripts/verify_bresler_remap_compatibility.py`; appendix §11 `docs/source-notes/oriented-to-double-strand-bridging-transfer-2026-10-09.md`; **[O]** `docs/source-notes/uniform-strand-convention-search-2026-09-20.md` |
| R17 | `U` | — | — | — | `Is` | — | **Not a determinate proposition; cannot be settled from source** | the 2016 text names no objective, so no finite witness can settle “the” ML formulation and **no source argument can settle it either** (the sentence does not determine the proposition). Decomposed into its three source-nameable members (`E`, `A`, the `Fgen` flow with `A` costs = R1/R5/R10/R11/R12), all of which are refuted. This row is a *qualification of the source*, not a project-level strengthening: it records that the source underdetermines the question | **[I]** |
| R18 | `E` | `U1`/`U2` | `F0` | `V5` **two disjoint circles** `(S, rc(S))` | componentwise `Is` (circle-by-circle) vs duplex-as-a-whole | `W`/`S` | **Disclosed project-level model, not a source row** | The physical double-stranded circle is modelled as **two disjoint cyclic strands** `S` and `rc(S)`, not one joined length-`2G` circle. Circle-by-circle `I_s` is **exactly equivalent** to `I_s(S)` — the rc map `ρ(i)=(G-1-i) mod G` reverses order and preserves strict bridging, so it is a bijection of `I_s`-solutions — hence the `AAATAT → AAAAAT` witness survives here (ratios `3` exact / `5` binomial). Duplex-as-a-whole is ill-defined (no cyclic order on two disjoint circles) and strictly stronger: six mixed cross-strand triple repeats of length `≥ L-1` are unbridgeable for every read set, so the witness is inadmissible there. Statistically, when orientation is **unobserved** the V5 duplex class count `2·m_S(C)` over `2G` normalizes to `m_S(C)/G`, **identical** to the MB09 molecule distribution (palindromes counted once), so V5 is not a distinct likelihood objective there; **oriented** reads are a distinct surface requiring explicit source justification. V5 is a disclosed **new modelling decision**, not a reading of the 2016 sentence, and it does not settle V3/R16 | **[K]** `AssemblyP1/TwoDisjointCirclesDuplex.lean`, `AssemblyP1/DoubleStrandBridgingTransfer.lean`; **[V]** `scripts/verify_two_disjoint_circles_duplex.py`, `scripts/verify_oriented_molecule_bridging.py`; appendix `docs/source-notes/oriented-to-double-strand-bridging-transfer-2026-10-09.md` |

### 2.1 What the matrix says about the schema

* Rows R1–R6, R10–R12, R14 are **strict** counterexamples, so they refute `W`
  and `S` simultaneously and for every `≈` and every tie convention. **[M]**
* Row R14 is the **variable-length** strict counterexample, and this round it is
  upgraded from an exact-arithmetic reproduction (`[V]`) to a kernel-checked
  certificate (`[K]`): `AssemblyP1/OrientedVariableLengthSe62.lean` checks the
  full-strength `I_s` certificate and the `M = 1, 2` instances, while the #210
  note proves the growing- and fixed-competitor families strict for every
  `M ≥ 1`. The mechanism is the sample-multiplicity **amplification** of an
  over-represented observed type.
* Rows R7–R9 are the only positive rows, and they are positive only on the
  `U2 ∩ Fgen ∩ or` slice. R9’s uniqueness needs `≈` = cyclic shift (forced)
  and the external BBT complete-spectrum input (not formalized). Leaf #211’s
  `SameLength62TieUniqueness` supplies the `I_s ⇒ ¬ interleaved long repeats`
  adapter and refutes the BBT premise on a concrete `G=6, L=2` instance, but
  the finite same-length rotation uniqueness remains **Lean-conditional** on
  that input; only the *population* theorem is now unconditional (below).
* Row R6 is the row that shows the **length restriction alone is not enough**:
  without the §6.2 membership conjunct the same-length question is already
  negative.
* Row R13 was the only **determinate** row that was open on `main`; it is now
  resolved to **FALSE** by a kernel-checked per-occurrence witness (see the
  row). Its assumption `Focc` is an editorial strengthening, not the source’s
  §6.2 rule, so its resolution is a mathematical service to a *repository*
  question, not the reading of a source statement that the other rows are.
* Row R18 records the #215 duplex finding in the form the board adopted: the
  physical double-stranded circle is **two disjoint cyclic strands** `S` and
  `rc(S)`, and circle-by-circle `I_s` is exactly equivalent to `I_s(S)`. This is
  a disclosed modelling decision, and when orientation is unobserved its
  normalized class likelihood coincides with the MB09 molecule distribution, so
  it adds no new *objective* row; it does settle the representation question the
  research synthesis raised.
* No determinate row remains open on `main`. The residue is R16 (**not a
  determinate source row** — a different paper's `2G` concatenation convention,
  with the known witness kernel-checked **inadmissible** and the V3↔V1/V2
  compatibility kernel-checked **incomparable off the R1∧R2∧R3 locus**; no
  bounded search is used as evidence either way) and R17 (not a determinate
  proposition, and not settleable from source) — neither is determinate, and
  neither is a source-supported reading of the 2016 sentence. R18 is a disclosed
  project-level model, not a source row. #216's `Part 6` amplification is
  **resolved as redundant**, not pending: it is uncommitted, does not compile, and
  is superseded by the already-`[K]` result via R14/R10–R12
  (`OrientedVariableLengthSe62`); the lattice claims no general amplification
  theorem and needs none. #219's fibre-count Lean core is **no longer pending**:
  leaf #219 reached terminal and its `FibreCountArithmetic` divisor-sum core is
  integrated and `[K]` (the BEST/Matrix-Tree graph content stays external); it is
  a population counting result, not a matrix row, so it changes no row
  resolution. The final unresolved-source-gap register is recorded in §3.1.

### 2.2 Front states, coordination, and the general-flow upgrade (final round)

The board coordinates the active leaves. None of their uncommitted work was
harvested or disturbed; the board tracks their status here so another invocation
can recover the research graph.

| leaf | branch / worktree | state this round | board action |
|---|---|---|---|
| #208 | `agent/board-208-0c8fcf` / `assemblyp1-finite-208` | source census + provenance audit committed (`3f532c5`); untracked `scratch-208/` preserved | **integrated** (novel docs/scripts only; its stale cc0aa8a-based paper edits were *not* merged); no matrix row change |
| #209 | `agent/board-209-6cf9bd` / `assemblyp1-finite-209` | **closed/terminal** (03:18): `Issue209EAudit` + 3 scripts + ledger + terminal report committed (`cf92561`…`5b18b1a`, pushed); `scratch-209/` preserved | **this round** integrates the module + scripts + ledger/report: R1 strengthened (same `AAABB` witness refutes `A` too, ratio `1125/512`); objective-`A` domain boundary kernel-checked (`d_w ≤ N(D)`, negative marginal off `|D| ≤ N`) |
| #210 | `agent/board-210-e8b6b2` / `assemblyp1-finite-210` | `OrientedVariableLengthSe62` + doc + 2 scripts committed (`7d48eab`); worktree clean | **module integrated** — R14 upgraded from `[V]` to `[K]`; the amplification families are the landed form of the sample-multiplicity axis |
| #211 | `agent/board-211-8d5103` / `assemblyp1-finite-211` | `SameLength62TieUniqueness` committed (`8bef1f6`); uncommitted umbrella wiring + 2 scripts preserved | **module integrated**; finite same-length uniqueness stays Lean-conditional on the complete-spectrum input |
| #212 | `agent/board-212-37b45b` / `assemblyp1-finite-212` | clean; module + script already harvested | **harvested** — R13 resolved FALSE (see §7.1) |
| #213 | `agent/board-213-5fff16` / `assemblyp1-finite-213` | `Section62VarlenPerOccurrence` + doc + script committed (`a47107c`); worktree clean | **module integrated** — R10/R12 hardened (per-occurrence + unique-optimizer over the whole §6.1 domain and the general flow universe); no new row |
| #214 | `agent/board-214-d0e372` / `assemblyp1-finite-214` | `Section62NonSpelledFlow` committed through `d2163b8`; worktree clean | **module integrated**; R10–R12 upgrade to the general `Feasible62` flow domain |
| #215 | `agent/board-215-745214` / `assemblyp1-finite-215` | `TwoDisjointCirclesDuplex` + `DoubleStrandBridgingTransfer` committed (`a852879`); **V3 row settled** (`67de8b7`+`20b6c71`+`2a3d2cf`): `BreslerRemapCompatibility` + script + appendix §11 | **modules integrated**; new row R18, R16 refined; **this round** integrates the V3-settle artifacts — R16 compatibility kernel-checked (incomparable off R1∧R2∧R3) |
| #216 | `agent/board-216-eb3281` / `assemblyp1-finite-216` | `ImplicationLattice` committed (`486d60f`); **uncommitted `Part 6` sample-multiplicity refinement does not compile** | base **module integrated** (conclusion-schema lattice, no matrix row change); `Part 6` **resolved as redundant, not integrated** — superseded by #210's already-`[K]` result (`OrientedVariableLengthSe62`), with the pointer recorded in `implication-lattice-216.md` §7 |
| #219 | `agent/board-219-547404` / `assemblyp1-finite-219` | **terminal** (`B219 TERMINAL`, 11:06): `FibreCountArithmetic.lean` + updated note + fixed audit script committed (`81d29c6`, doc cross-ref `1ec6195`); worktree clean | **fully integrated this round**: `AssemblyP1/FibreCountArithmetic.lean` (kernel-checked divisor-sum core), `docs/exact-fibre-count-theorem-219.md` (adds prior-art boundary and kernel check), `scripts/audit_fibre_count_219.py` (placeholder bug fixed); root-imported and axiom-audited; no matrix row change (population result) |

**PR #117 (merged Lean CI repair).** The board branch carries `e9fcf01`, the
merge of PR #117 ("Repair full-library CI compilation blockers (initial
fixes)"), which touches only `BBTTripleBridge`, `Issue94ComponentAlignedSwaps`,
`Issue94KShortGeneral`, `Issue94LongWindowSplit`. It is a CI/build repair, not
a mathematical result: it changes no matrix row, no witness, and no theorem
statement. It is recorded here so the board’s base is auditable.

**R9 stays Lean-conditional.** The 2013 BBT Theorem 3 input is *not* formalized
in this repository. `BBTEulerian.bbtCompleteSpec_of_obstruction` consumes it
as the explicit premise `hObs : EulerianCycleObstruction`, and
`OrientedSameLengthML.same_length_unique_up_to_rotation_of_bbt` /
`…maximality_and_rotation_uniqueness_of_bbt` consume it as the explicit premise
`hBBT`. Both are axiom-clean (`[propext, Classical.choice, Quot.sound]`) and
both keep the hypothesis as a premise — the uniqueness conclusion is **not**
kernel-checked unconditionally. This round did not discharge, weaken, or
re-state that hypothesis.

**The #214 general-flow upgrade, and the separation to keep.** Leaf #214
kernel-checks that the §6.2 refutation is not confined to spelled circuits:
over the *whole* `Feasible62` flow domain the truth is not a maximizer, and the
flow optimum `d* = (AAA:2, AAT:1, TAA:1)` (with `d*₃ = (AAA:3, AAT:1, TAA:1)`)
spells no circular molecule of any length. This upgrades R10–R12 from the
spelled sub-case to the general flow domain. Two objects must **stay separate**
in any tracking of this result:

* the **integer flow optimum** — the argmax of the §6.1 objective over the
  integer throughput vectors `1 ≤ d ≤ N` that are genuine §6.2 flows (the
  kernel-checked `d*`, `d*₃`); this is the §6.2 object the source defines;
* the **half-integral relaxation** — the argmax of the same objective when `d`
  is allowed to range over half-integers (the per-coordinate maximizer of
  `(d/N)^x((N−d)/N)^(n−x)` is `d = xN/n`, e.g. `5/2` for the `AAA` coordinate
  here, which is not an integer and not a §6.2 flow throughput).

The relaxation is a different, larger upper bound; conflating it with the
integer flow optimum would overstate what the §6.2 domain refutes. The board
records the integer optimum as the §6.2 result and does not substitute the
relaxation. Leaf #214 is now **terminal for its scope**: its
`AssemblyP1/Section62NonSpelledFlow.lean` is integrated here (root-imported and
axiom-audited at `[propext, Classical.choice, Quot.sound]`), it certifies that a
spelled candidate is a general `Feasible62` flow
(`spelled_subset_general`), exhibits the non-spelled flow optimum `d*`
(`star_argmax`), and proves no circular molecule realizes its throughputs
(`no_sequence_has_star_spectrum`). The paper’s flow-domain remark is updated
accordingly. The half-integral relaxation remains a *separate* object and is
never substituted for the integer flow optimum.

---

## 3. Source-fidelity column: what the source says vs. what we chose

| item | source status |
|---|---|
| “the maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009)” selects no section, equation, objective, or candidate class | **F** (accepted text §5; full-text scan) |
| MB09 contains four objects: `E`, `A`, the §6.2 flow, and the ML principle | **F** |
| §6.2 returns a “(non-contiguous) assembly”, not a sequence | **F** (MB09 §6.2) — so the §6.2 reading of a sentence about “the maximum-likelihood **sequence**” needs a flow→sequence step that MB assign to a §7 heuristic |
| treating `A` (fixed-`N` binomial) as the operative sequence-level objective | **I** |
| treating `E` as the named ideal that the sentence denotes | **I** |
| restricting competitors to `|D| = G` | **C** |
| the per-occurrence strengthening `d_D(w) ≥ x(w)` | **C** |
| molecule vs oriented read types for the 2016 sentence | **F** that the two cited papers differ; which applies is a **source gap** |
| `4^k` vs `(4^k+p_k)/2` read-type count in MB09 §6.1 | **F** source-internal tension, resolved to molecule classes *given* §6.2 |
| 2010 thesis Ch. 4 restates `E` and the fixed-`N` replacement | **F** |
| Howison–Zapata–Dunn (2013) §5: the MB assembler “requires as a parameter the accurate size of the target genome” | **F** (third-party evidence about how the method was read) |
| Varma–Ranade–Aluru (2011)’s advertised improvement is genome-size handling | **F** (same) |
| the accepted supplementary ZIP remains uninspected | **F** (HTTP 403 on both recorded retrieval paths) — the last unexamined accepted artifact that could contain a likelihood definition |

### 3.1 Final source-gap count

The canonical register is
[`finite-interpretation-universe-audit.md`](finite-interpretation-universe-audit.md)
§6. **Final source-gap count for the 2016 finite question: 7 unresolved items**
(items 1–6 and 8; item 7, the repository-provenance gap, was closed this run):

1. the 2016 likelihood **referent** — audit §6.1;
2. the publisher **supplement** (HTTP 403) — audit §6.2;
3. the MB09 `4^k` vs molecule-class index tension — audit §6.3;
4. the maximizer-vs-uniqueness schema selection — audit §6.4;
5. the composition of Shomorony's bridging with MB09's likelihood — audit §6.5;
6. the Varma et al. full-text gap — audit §6.6;
7. the out-of-scope dead provenance locator — audit §6.8.

The gaps that bear directly on this matrix's claim are the **referent** (item 1),
the **supplement** (item 2), and the **strand/equivalence** convention — the
latter recorded in this matrix §1.4/§3 and in
[`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md)
rather than as a separate numbered register item. None of the 7 is a matrix row,
and none is used to decide one.

---

## 4. The claim, stated precisely

Counting rows: R1–R6, R10–R14 are the **eleven** negative rows, of which the
kernel-checked ones are R1, R2, R5, R6, R10, R11, R12, R13, R14 (nine, sharing
eight modules) and the exact-arithmetic ones are R3, R4 (two). R7, R8, R9, R15
are the four positive rows (R9 conditional on the external BBT input, R15
inherited from R7). R9 and R8 are two views of one argument, and R10 and R12 are
one witness, so the row count overstates the number of distinct results and
underrates nothing. R18 is a **disclosed new model** (the two-disjoint-circles
duplex), not a reading of the 2016 sentence: circle-by-circle it is exactly
equivalent to `I_s(S)`, and when orientation is unobserved its normalized class
likelihood coincides with the MB09 molecule distribution.

**Resolved (with a reviewed proof or an exact counterexample):**

* every reading that selects the **exact** multinomial `E` over a circular
  candidate universe `U1`/`U2` without §6.2 feasibility (R1–R4, R6) — refuted by
  strict kernel-checked or exact-arithmetic witnesses;
* every reading that selects the **fixed-`N` binomial** `A` over `U1` on its
  domain (R5) — refuted by a strict kernel-checked witness;
* every reading that selects the **§6.2 bidirected flow** with the source’s
  per-vertex lower bound, under molecule read types, at either variable
  (R10, R12) or equal (R11) candidate length — refuted by strict
  kernel-checked witnesses, each of which certifies literal §6.2 feasibility;
* the oriented single-strand **variable-length** §6.2 reading (R14) — refuted in
  **infinite families** (growing and fixed competitor, exact and fixed-`N`
  binomial objectives), strict for every sample multiplicity `M ≥ 1`, with the
  kernel-checked instances `M = 1, 2` and the general proof + `M = 0..200`
  arithmetic in the #210 note/scripts. The mechanism is the amplification of an
  over-represented observed type; the truth wins exactly at `n = G`;
* the same-length §6.2 question under the **per-occurrence strengthening**
  `Focc` (R13) — refuted by a strict kernel-checked witness whose truth *is*
  per-occurrence feasible, on the real four-letter DNA alphabet
  (`ATATACAC → ATACACAC`, exact ratio `3/2`, binomial ratio `9/5`). This row’s
  assumption is a repository-added surface, so its resolution is **not** a
  reading of the 2016 sentence; it is closed because the matrix commits to
  reporting determinate rows as resolved or open, not because a source asks it;
* the one **positive** slice: oriented read types, same-length candidates that
  are genuine §6.2 candidates on both sides, full `I_s` (R7) or just its
  triple-repeat clause (R8) — the truth is a maximizer for both `E` and `A`,
  kernel-checked; and it is the unique maximizer up to cyclic rotation
  conditional on the external BBT complete-spectrum input (R9).

**Open / not determinate, stated explicitly:**

1. **R13 is resolved (FALSE).** It was open at the start of this round with
   bounded zeros only, and is now closed by the leaf-#212 witness integrated in
   `docs/peroccurrence-samelength-dna-counterexample-212.md`. Its assumption is
   not the source’s §6.2 rule, so it is outside the class of *source-supported*
   interpretations; it was a determinate mathematical question, and a determinate
   question with a counterexample is settled.
2. **R16** (Bresler doubled-strand **concatenation** convention, one length-`2G`
   circle) is bounded evidence only and is not a source-supported reading of the
   2016 sentence. It is open in **both** directions: no beat is known, and the
   known `AAATAT → AAAAAT` witness is kernel-checked **inadmissible** under the
   remap (`doubled_not_information_feasible`). The *compatibility* of this
   convention with the oriented reading is now kernel-checked: V3 is exactly
   compatible with V1/V2 (≡ V5 circle-by-circle) iff R1∧R2∧R3, and off that
   locus the two models are incomparable with kernel-checked witnesses in both
   directions (`GGGA` for R1, `AAATAT` for R3;
   `BreslerRemapCompatibility.remap_natural_seat_not_sound`, `…remap_not_complete`).
   The faithful-occurrence reading is sound in the searched scope but a
   conjecture in general.
3. **R17** (the unspecified general principle) is not a determinate
   proposition: the source fixes no objective, so no finite witness can settle
   it as stated. Its decomposition into the source-nameable members is
   refuted.
4. R15’s strengthening-containment (`Focc ⊆ Fgen` for the oriented reading) is
   inherited rather than proved.
5. The publisher’s supplementary ZIP is still uninspected; a likelihood or tie
   definition there is not excluded.
6. The referent question itself is untouched: no primary source selects among
   `E`, `A`, the §6.2 flow, and the principle. A negative settlement of the
   published sentence is therefore available *conditionally* on a source
   argument fixing the referent.
7. **R18** is a disclosed new model, not a source row. Its circle-by-circle
   reading is exactly `I_s(S)`; its duplex-as-a-whole reading is ill-defined and
   strictly stronger. It is recorded so that the exhaustiveness claim is not
   overstated by silently folding a new representation into a source reading.
8. **#216 `Part 6` (sample-multiplicity amplification) is resolved as
   redundant.** The general formalization in the uncommitted `Part 6` of
   `AssemblyP1/ImplicationLattice.lean` does not compile and is deliberately not
   integrated. It is **not** a matrix row and its absence opens no row, because
   the amplification result is already kernel-checked via #210
   (`OrientedVariableLengthSe62`, R14) and #213 (R10/R12). It is recorded so the
   schema lattice is not read as carrying a general amplification theorem it does
   not; the canonical carrier is `AssemblyP1/OrientedVariableLengthSe62.lean`
   (see `implication-lattice-216.md` §7).
9. **#219 (same-length complete-spectrum fibre count): fully integrated.**
   Leaf #219 is terminal (`B219 TERMINAL`, `81d29c6`). Its Theorems 1–3 are
   mathematical proofs in `docs/exact-fibre-count-theorem-219.md` (integrated),
   with an independent exact-arithmetic audit (`scripts/audit_fibre_count_219.py`,
   integrated, `AUDIT PASSED`, all claims verified against brute force on binary
   words of length `1..9`), and its Lean core
   `AssemblyP1/FibreCountArithmetic.lean` now **compiles** and is integrated: it
   kernel-checks the divisor-sum reindexing, the Möbius inversion
   (`fibre_mobius_inversion`) and the totient/Burnside rearrangement
   (`fibre_totient`). What is *not* formalized is the BEST/Matrix-Tree graph
   content (the weighted arborescence count `B_h` and the branching
   primitive-spelling construction); that remains **external** (classical BEST
   plus the kernel-checked `ScalarPrimitiveSpellings`). The closest prior art,
   the `g = 1` multiplicity-one-edge corner, is Shomorony–Kamath–Xia–Courtade–Tse
   ISIT 2016 Appendix C Corollary 1, cited and **not** claimed. It is a
   **population-level counting** result, not a finite-data matrix row; its
   integration changes no row's resolution. It is recorded so that the exact
   scope of the kernel-checked count is not overstated.

So: **every interpretation of the 2016 finite question that is both
determinate and source-supported is resolved — nine distinct results
negatively and one positively — and the residue is one row that is *not a
determinate source row* (R16, a different paper’s `2G` concatenation convention,
open in both directions with no bounded search used as evidence, its known
witness kernel-checked inadmissible and its compatibility with the oriented
reading kernel-checked incomparable off the R1∧R2∧R3 locus), one non-determinate
row (R17, not settleable from source), and one disclosed project-level model
(R18, not a source row).** No leaf artifact remains pending: #216 `Part 6` is
resolved as **redundant** (its result is already kernel-checked via #210) and
#219’s fibre-count core is **integrated** (`FibreCountArithmetic`, a population
result that changes no row). No determinate source-supported row remains open.
The claim “all source-supported interpretations are resolved” is therefore
justified for the source-supported class, and explicitly **not** extended to
R16, R17, R18, or the non-source artifacts; R13, which was determinate but not
source-supported, is now resolved in the same sense as the negative rows. The
finite same-length rotation-uniqueness half of the positive row (R9) remains
Lean-conditional on the external complete-spectrum input; only the *population*
theorem is now kernel-checked without it.

---

## 5. Cross-references

* [`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md) — the four readings and the witness-sufficiency matrix.
* [`conclusion-semantics-determination.md`](conclusion-semantics-determination.md) — conclusion semantics and the residual register.
* [`equivalence-and-tie-wellposedness.md`](equivalence-and-tie-wellposedness.md) — the invariance lemmas and the cyclic-shift/reverse-complement coupling.
* [`conclusion-semantics-strict-witness-robustness.md`](conclusion-semantics-strict-witness-robustness.md) — why a strict witness is equivalence- and tie-proof.
* [`oriented-se62-rigidity-theorem.md`](oriented-se62-rigidity-theorem.md) — the oriented same-length rigidity theorem (rows R7–R9).
* [`oriented-variable-length-se62.md`](oriented-variable-length-se62.md) — row R14, the oriented unrestricted-length §6.2 classification (infinite families + amplification), with the kernel-checked certificate `AssemblyP1/OrientedVariableLengthSe62.lean`.
* [`../section62-varlen-per-occurrence-audit-213.md`](../section62-varlen-per-occurrence-audit-213.md) — rows R10/R12, the #213 audit hardening the variable-length per-occurrence witness (per-occurrence rule + unique optimizer over the whole §6.1 domain).
* [`../implication-lattice-216.md`](../implication-lattice-216.md) — the #216 conclusion-schema transfer table (module `AssemblyP1/ImplicationLattice.lean`, script `verify_implication_lattice_216.py`), with the sample-multiplicity `Part 6` recorded as **redundant, superseded by #210**.
* [`../exact-fibre-count-theorem-219.md`](../exact-fibre-count-theorem-219.md) — the #219 same-length complete-spectrum fibre count (Theorems 1–3), with the exact-arithmetic audit `scripts/audit_fibre_count_219.py`; a population counting result whose Lean core (`AssemblyP1/FibreCountArithmetic.lean`) is integrated.
* [`../bridging-se62-flow-ml-counterexample.md`](../bridging-se62-flow-ml-counterexample.md), [`../section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md) — rows R10–R12.
* [`../peroccurrence-samelength-dna-counterexample-212.md`](../peroccurrence-samelength-dna-counterexample-212.md) — row R13, the per-occurrence same-length refutation, with the leaf-#212 provenance record.
* [`oriented-to-double-strand-bridging-transfer-2026-10-09.md`](oriented-to-double-strand-bridging-transfer-2026-10-09.md) — rows R16/R18, the three oriented↔double-strand bridging versions (V1/V2, V3, V5) and the two-disjoint-circles duplex model, with the kernel-checked V3 non-equivalence and the six mixed cross-strand triples.
* [`../section62-nonspelled-flow-domain.md`](../section62-nonspelled-flow-domain.md) — the #214 general `Feasible62` flow-domain countermodel and the integer/half-integral separation.
* [`finite-interpretation-universe-audit.md`](finite-interpretation-universe-audit.md) — the #208 source-exhaustiveness census behind the “source-supported” class.
* [`../issue-209-ea-audit-ledger.md`](../issue-209-ea-audit-ledger.md), [`../issue-209-terminal-report.md`](../issue-209-terminal-report.md) — the #209 E/A witness audit ledger and terminal report (module `AssemblyP1/Issue209EAudit.lean`, scripts `verify_issue209_ea_witnesses*.py`, `audit_issue209_axioms_full.py`).
* [`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md) — the negative-transfer lemma.
* [`../ml-formalization-contract.md`](../ml-formalization-contract.md) — Variants `E`/`A`/`F` and the two conclusion schemas.

## 6. Epistemic ledger

| claim | status |
|---|---|
| MB09 §6.1 defines `E` with candidate-intrinsic `N(D)` and `A` with external `N`, assuming genome size known | **F** |
| MB09 §6.2 defines a bidirected read-overlap-graph flow with per-vertex lower bound 1, returning a non-contiguous assembly | **F** |
| Shomorony 2016 names MB at paper level only; states no tie rule, uniqueness, or equivalence | **F** |
| Shomorony uses oriented read types; reverse complement is preprocessing there | **F** |
| MB09 models reads as reverse-complement molecules, each represented once | **F** |
| `Focc` (per-occurrence) is not the §6.2 definition | **M** + **C** |
| Rows R1, R2, R5, R6 are refuted by kernel-checked strict witnesses | **K** |
| Row R1's `AAABB → AAAAB` witness also refutes the fixed-`N` binomial objective `A` (ratio `1125/512`), not only the exact multinomial | **K** — `AssemblyP1/Issue209EAudit.lean` (`aaab_refutes_fixed_N_binomial`), integrated and axiom-audited |
| objective `A`'s external `N` restricts the candidate class to `|D| ≤ N` (`d_w ≤ N(D)`); the literal marginal is negative off that class | **K** — `AssemblyP1/Issue209EAudit.lean` (`winCount_le_len`, `external_N_domain_boundary`) |
| Rows R7, R8 are proved (maximizer) | **K** |
| Row R9 is proved conditional on an external BBT premise | **K** conditional |
| Rows R10, R11, R12 are refuted by kernel-checked strict witnesses certifying literal §6.2 feasibility | **K** |
| Row R13 is refuted by a kernel-checked strict witness certifying literal §6.2 feasibility on both sides under the per-occurrence strengthening (`ATATACAC → ATACACAC`, ratios `3/2` and `9/5`) | **K** |
| Rows R3, R4 are refuted by exact-arithmetic reproductions | **V** |
| Row R14 (oriented single-strand variable-length §6.2) is refuted by a kernel-checked certificate plus infinite strict families (`M ≥ 1`), exact `15625/11664`, `2109375/823543` and binomial `81/64`, `27/16` at `M=1,2` | **K** (`AssemblyP1/OrientedVariableLengthSe62.lean`) + **M** (families) + **V** (scripts) |
| Row R10/R12 is hardened by #213: both throughput vectors in the §6.1 domain and general flow universe, competitor the unique optimizer over the whole domain | **K** (`AssemblyP1/Section62VarlenPerOccurrence.lean`) |
| the #216 sample-multiplicity amplification `Part 6` | **redundant** (uncommitted, does not compile; superseded by #210, whose result is **K** via R14) |
| the #219 same-length complete-spectrum fibre count (Theorems 1–3) | **M** (note proof) + **V** (audit script) + **K** (the divisor-sum core: `fibre_mobius_inversion`, `fibre_totient`, integrated); the BEST/Matrix-Tree graph content is **external**, not formalized |
| Row R16 is open in both directions, under a non-source convention; the known witness is kernel-checked inadmissible under the `2G` remap | **O** + **K** (inadmissibility) |
| R16 compatibility: V3 exactly compatible with V1/V2 (≡ V5 circle-by-circle) iff R1∧R2∧R3; incomparable off the locus, kernel-checked both directions (`GGGA` for R1, `AAATAT` for R3) | **K** — `AssemblyP1/BreslerRemapCompatibility.lean` (`remap_natural_seat_not_sound`, `remap_not_complete`, `seat6_spurious`, `seat7_spurious`, `v5_ggga_fails`), integrated and axiom-audited; appendix §11 |
| the faithful-occurrence reading of the V3 remap is sound in general (V3 ⟹ V1/V2) | **conjecture** — verified computation in scope only (`0/180` violations, binary+ternary, `L=3`, `3≤G≤7`) |
| Row R17 is not a determinate proposition | **I** |
| Row R18 (two-disjoint-circles duplex) is a disclosed new model; circle-by-circle `I_s` exactly equals `I_s(S)`, duplex-as-a-whole is ill-defined/strictly stronger, and the unobserved-orientation class likelihood equals the MB09 molecule distribution | **K** + **C** |
| the leaf-#212 census is bounded evidence, not a proof of absence | **V** bounded |
| no determinate row remains open on `main` | repository fact |
| which MB object the 2016 sentence denotes | **source gap, unchanged** |
| the accepted supplementary ZIP (could hold a likelihood/tie definition) | **uninspected, unchanged** — HTTP 403 on both recorded retrieval paths; not reachable from this host |
| the #214 general-flow upgrade (§6.2 refutation over the whole `Feasible62` domain; optimum spells no genome) | **K** — `AssemblyP1/Section62NonSpelledFlow.lean`, integrated and axiom-audited (`d2163b8`) |
| the integer flow optimum vs. the half-integral relaxation | **kept separate** in §2.2; the relaxation is not the §6.2 object |
| R9’s BBT complete-spectrum input (finite same-length rotation uniqueness) | **O** (external) — carried as explicit `hObs`/`hBBT` premise, not discharged; the **population** theorem is now kernel-checked without it |
| leaf #211’s `I_s ⇒ ¬ interleaved long repeats` adapter and its `G=6, L=2` refutation of the BBT premise | **K** — `AssemblyP1/SameLength62TieUniqueness.lean`, integrated and axiom-audited |
| leaf #219’s exact fibre-count theorem | **M** + **V** + **K** (divisor-sum core) — note `docs/exact-fibre-count-theorem-219.md`, audit `scripts/audit_fibre_count_219.py` and Lean core `AssemblyP1/FibreCountArithmetic.lean` integrated and passing; the BEST/Matrix-Tree graph content is **external** |

---

## 7. Verification performed for this matrix (2026-10-09)

Everything below was run in `/workspace/assemblyp1-finite-217` at `cc0aa8a`
plus this document's own edits. The worktree shares the pre-built Mathlib
dependency tree through `.lake/packages` (a symlink to the host's shared
`assemblyp1/.lake/packages`), so no Mathlib rebuild was needed. Every command
ran inside a per-command fence: fresh `HOME`, `XDG_STATE_HOME`,
`XDG_CONFIG_HOME`, `XDG_CACHE_HOME`, `XDG_DATA_HOME` and `ELAN_HOME` under
`/tmp`, so no ambient agent state is read or mutated.

Rows R1–R12, R14–R15 carry the verification below, which was executed in the
first half of this round. Row R13 was resolved in the second half by the
leaf-#212 witness; the checks that changed it are listed separately in §7.1 and
were re-executed in this worktree after the copy.

| check | command | result |
|---|---|---|
| targeted library build | `LEAN_NUM_THREADS=8 lake build AssemblyP1.SourceFaithfulIs AssemblyP1.FixedLengthExactCounterexample AssemblyP1.FixedLengthBinomialCounterexample AssemblyP1.ExactVariantECounterexample AssemblyP1.FiniteSamplingCounterexample AssemblyP1.Section62BridgingCounterexample AssemblyP1.SameLengthSection62Counterexample AssemblyP1.SameLengthExactMLCounterexample AssemblyP1.MLEscape AssemblyP1.OrientedFinalRigidity AssemblyP1.OrientedSameLengthML` | **Build completed successfully (8935 jobs)** |
| kernel replay | `LEAN_NUM_THREADS=1 lake env leanchecker <module>`, one module per process (a single process over all 17 modules was killed by the OOM reaper, exit 137) | each replayed module reports **exit 0**; see the record below |
| axiom audit, theorem level | `lake env lean` with `#print axioms` on 18 headline theorems | every one depends only on `[propext, Classical.choice, Quot.sound]` |
| axiom audit, module level | the CI-pinned `axiom-audit` (`leanprover-community/axiom-audit` at `46024e005996495c65ef609368e11ab39c4222e3`, built with the pinned toolchain), run as `lake env axiom-audit --allow propext,Classical.choice,Quot.sound --root AssemblyP1 --modules <the 16 built modules>` | **`audited 1315 declaration(s) under 'AssemblyP1'; all within the allowlist [propext, Classical.choice, Quot.sound]`**, exit 0 |
| documentation integrity | `python3 scripts/check-research-docs.py` | **research documentation integrity checks passed** |
| uniform-strand witness reproduction | `python3 scripts/uniform_strand_semantics_search.py --witness` | **all checks passed** (oriented `AAATT→AAAAT` ratio `2`, binomial `1125/512`; molecule `AAATAT→AAAAAT` exact `3`, binomial `5`) |
| uniform-strand bounded search | `python3 scripts/uniform_strand_semantics_search.py --search` | **all checks passed**, matching the note's table (`(6,3)`: 960 beats, `(7,3)`: 0, `(6,4)`: 0, `(8,3)` maxmul 3: 4540) |
| read-tiled witness script | `python3 scripts/verify_readtiled_exact_counterexample.py` | **all checks passed** (`I_s` clause by clause, `L_E(S|x)=120/117649`, `L_E(D|x)=3240/117649`, ratio `27`) |

Theorem-level axiom results (`#print axioms`), all
`[propext, Classical.choice, Quot.sound]`:

* `AssemblyP1.MLEscape.informationFeasible_62_spelledML` (row R7)
* `AssemblyP1.SameLength62Maximizer.informationFeasible_62_maximizer` (row R7)
* `AssemblyP1.SameLengthExactMLCounterexample.same_length_exact_ML_refutation_62`, `…section62_maxLikelihood_refuted` (rows R6, and the §6.2-acceptance-boundary row)
* `AssemblyP1.SameLengthSection62Counterexample.samelength_se62_bidirected_flow_counterexample`, `…samelength_se62_counterexample` (row R11)
* `AssemblyP1.Section62BridgingCounterexample.se62_bridging_bidirected_flow_counterexample`, `…se62_bridging_flow_counterexample` (rows R10, R12)
* `AssemblyP1.FixedLengthExactCounterexample.fixed_length_exact_counterexample` (row R1)
* `AssemblyP1.FixedLengthBinomialCounterexample.fixed_length_binomial_counterexample` (row R5)
* `AssemblyP1.ExactVariantECounterexample.finite_unrestricted_exact_variant_e_counterexample` (row R2)
* `AssemblyP1.OrientedFinal.oriented_same_length_spectrum_rigidity`, `…rotation_uniqueness_of_bbt` (rows R8, R9)
* `AssemblyP1.OrientedSameLengthML.informationFeasible_exactLik_maximizer`, `…same_length_exactLik_maximizer`, `…same_length_maximality_and_rotation_uniqueness_of_bbt` (rows R7–R9)
* `AssemblyP1.OrientedRigidity.unique_positive_circulation` (row R8 core)
* `AssemblyP1.BridgingBridge.informationFeasible_no_long_triple_repeat` (the `Is ⇒ ¬LTR` transfer)
* `AssemblyP1.PerOccurrenceSameLengthCounterexample.peroccurrence_samelength_se62_bidirected_flow_counterexample`, `…peroccurrence_samelength_maximality_refuted` (row R13)

### 7.1 Row R13: the leaf-#212 harvest, re-verified here

The leaf-#212 worktree `/workspace/assemblyp1-finite-212` was consulted
**read-only**: it was never written to, its working directory was never reused
as a `cwd`, and no cherry-pick, merge, or deletion was performed. Two of its
shared dependencies — `AssemblyP1/SourceFaithfulIs.lean` and
`AssemblyP1/Section62BidirectedFlow.lean` — are **byte-identical** to this
worktree's copies (verified by `diff -q`), so the harvested module cannot have
been checking a different predicate. The module and the script were copied in
by path (Lean SHA-256 `96e44d42…ba7b2`, script SHA-256 `8c30c2ef…9c700`) and
then **rebuilt, replayed, re-axiom-checked and re-run in this worktree**, not
trusted from the leaf:

| check | command | result |
|---|---|---|
| build | `LEAN_NUM_THREADS=4 lake build AssemblyP1.PerOccurrenceSameLengthCounterexample` | **Build completed successfully (8926 jobs)**, exit 0 |
| kernel replay | `LEAN_NUM_THREADS=1 lake env leanchecker AssemblyP1.PerOccurrenceSameLengthCounterexample`, one module per process | **exit 0** |
| control for that replay | `LEAN_NUM_THREADS=1 lake env leanchecker AssemblyP1.NoSuchModuleXYZ` | **exit 1**, `uncaught exception: Could not find any oleans for: AssemblyP1.NoSuchModuleXYZ` — so the exit 0 above is a real check, not a silent no-op |
| axioms | `lake env lean` with `#print axioms` on `peroccurrence_samelength_se62_bidirected_flow_counterexample`, `peroccurrence_samelength_maximality_refuted`, and the `Prop` `PerOccurrenceSameLengthMaximality` | all three `[propext, Classical.choice, Quot.sound]` |
| witness script | `python3 scripts/verify_peroccurrence_dna_samelength_212.py` | **ALL CHECKS PASS** (46 assertions, non-zero exit on any failure) |
| bounded census | `python3 scripts/verify_peroccurrence_dna_samelength_212.py --search` | **ALL CHECKS PASS**; 4 distinct `(S,D)` beats at `(G,L,sigma)=(8,3,4)`, 0 at the other eight scopes |
| independent re-derivation | a separate from-first-principles script recomputing `x`, `d_S`, `d_D`, the supports, the per-occurrence conditions and both ratios from the two strings alone | agrees with the leaf script and the Lean module on every value |

The Lean module contains no `sorry`, `axiom`, `admit`, or `native_decide`
(scanned), and the strengthened statement is a `Prop`
(`PerOccurrenceSameLengthMaximality`) rather than a theorem, so refuting it
changed no definition.


**Not** done here, and deliberately left to CI: the full-library
`lake build --wfail` over every `AssemblyP1/*.lean` module, the whole-library
kernel replay, and the `axiom-audit` pass with `--modules-from`. The
whole-library runs need every `AssemblyP1/*.lean` module compiled, which is a
multi-hour job on this host (CI allows 360 minutes for it). The first half of
this round asserted results that live in the 16 modules audited here; after the
leaf-#212 harvest the per-occurrence module is a 17th, built, kernel-replayed
and axiom-checked on its own (§7.1) but **not** included in the 16-module
`axiom-audit --modules` tally of 1315 declarations, which predates it. The
one-process kernel replay over all 17 modules was killed by the memory reaper
(exit 137) and was redone one module per process. The PDF build
requires a Guix TeX profile that is not provisioned on this host, so the paper
edits in this round are verified by inspection and by LaTeX environment-balance
checks only; the CI `documents.yml` workflow is the arbiter of the PDF.

One source gap is unchanged: the publisher's supplementary ZIP remains
**uninspected** (HTTP 403 on both recorded retrieval paths). It was not
inspected during this round either — it is not reachable from this host — and it
remains the last unexamined accepted artifact that could contain a likelihood or
tie definition. No matrix row was decided by anything in it, and none can be.

### 7.2 This round’s scoped checks (board coordination pass)

The board branch `agent/board-217-978a0a` carries PR #117 (`e9fcf01`) on top of
`cc0aa8a`. The following scoped checks were re-executed in this worktree for the
coordination pass (the full-library build and whole-library kernel replay remain
CI’s job, as recorded in §7):

| check | command | result |
|---|---|---|
| scoped build | `LEAN_NUM_THREADS=8 lake build AssemblyP1.PerOccurrenceSameLengthCounterexample AssemblyP1.BBTEulerian AssemblyP1.OrientedSameLengthML AssemblyP1.OrientedFinalRigidity` | **Build completed successfully (8936 jobs)**, exit 0 |
| R9 conditional axioms | `#print axioms` on `same_length_unique_up_to_rotation_of_bbt`, `same_length_maximality_and_rotation_uniqueness_of_bbt`, `bbtCompleteSpec_of_obstruction` | all three `[propext, Classical.choice, Quot.sound]` — conditional structure intact (`hBBT`/`hObs` are premises) |
| #212 harvest axioms | `#print axioms` on `peroccurrence_samelength_se62_bidirected_flow_counterexample`, `peroccurrence_samelength_maximality_refuted` | `[propext, Classical.choice, Quot.sound]` |
| #212 witness script | `python3 scripts/verify_peroccurrence_dna_samelength_212.py` | **ALL CHECKS PASS** (exact ratios `3/2` and `9/5` reconfirmed) |
| branch divergence | `git diff --name-only origin/agent/board-217-978a0a HEAD` | only the four PR #117 Lean files; `docs/`, `paper/`, `AssemblyP1.lean` identical — a clean rebase |

The six active leaves were consulted read-only; their uncommitted work
(#208 `scratch-208/`, #210 `OrientedVariableLengthSe62.lean` + script, #211
umbrella wiring + 2 scripts, #214 `Section62NonSpelledFlow` refinements) was
preserved in place and not harvested, merged, or deleted.

### 7.3 Integration round (this pass), 2026-10-09

Base: `729f50c` (main `e9fcf01` + the #217 matrix commits + the #221 white-paper
correction). The #221 branch is a **linear descendant** of the #217 head, so it
was fast-forwarded, not merged. The other leaf branches (#208, #211, #214, #215,
#216) are all rooted at `cc0aa8a` and therefore **predate** the #217 matrix and
PR #117; merging them wholesale would have deleted the #217 artifacts and
reverted the #221 paper state. Only their **novel, self-contained files** were
taken (`git checkout <head> -- <new-path>`), never their paper or shared-file
edits:

| leaf | files integrated |
|---|---|
| #208 | `docs/source-notes/finite-interpretation-universe-audit.md`, `…/shomorony-mb-formulation-referent-reconciliation.md`, `…/shomorony-ml-quantifier-sequence-resolution.md`, `scripts/audit_source_note_citations.py`, `scripts/verify_finite_interpretation_audit.py` |
| #211 | `AssemblyP1/SameLength62TieUniqueness.lean` |
| #214 | `AssemblyP1/Section62NonSpelledFlow.lean`, `docs/section62-nonspelled-flow-domain.md`, `scripts/verify_se62_nonspelled_flow_domain.py` |
| #215 | `AssemblyP1/DoubleStrandBridgingTransfer.lean`, `AssemblyP1/TwoDisjointCirclesDuplex.lean`, `docs/source-notes/oriented-to-double-strand-bridging-transfer-2026-10-09.md`, `scripts/verify_two_disjoint_circles_duplex.py`, `scripts/verify_oriented_molecule_bridging.py`, `scripts/audit_215_transfer_reconciliation.py` |
| #216 | `AssemblyP1/ImplicationLattice.lean`, `scripts/verify_implication_lattice_216.py` |
| #219 | **none** — the uncommitted `FibreCountArithmetic.lean` does not compile (its Möbius-reindexing proofs fail: `rw [sum_congr rfl]` misuse and `Nat.cast_div`/`Nat.div_pos` type mismatches); recorded as pending |

The five integrated Lean modules were root-imported in `AssemblyP1.lean` and
checked here:

| check | command | result |
|---|---|---|
| integrated module build | `LEAN_NUM_THREADS=8 lake build AssemblyP1.{SameLength62TieUniqueness,Section62NonSpelledFlow,DoubleStrandBridgingTransfer,TwoDisjointCirclesDuplex,ImplicationLattice}` | **all five built** (`Section62NonSpelledFlow` 200s, `TwoDisjointCirclesDuplex` 209s) |
| `--wfail` recheck | the five modules rebuilt under `lake build --wfail AssemblyP1` | **no warnings** |
| axiom audit | `#print axioms` on 18 headline theorems of the five modules | all `[propext, Classical.choice, Quot.sound]`; `spelled_subset_general` depends on **no** axioms |
| population endpoint (user-flagged) | `LEAN_NUM_THREADS=1 lake build AssemblyP1.Issue94Complete` | **built**; `Issue94Complete.population_unique_ML` depends on `[propext, Classical.choice, Quot.sound]` — fully kernel-checked, **no external BBT premise** |
| paper build | `bash paper/build.sh`-equivalent (`latexmk -pdf -halt-on-error`) with the pinned Guix TeX profile | **`main.pdf`, 33 pages, 0 undefined references** |
| documentation integrity | `python3 scripts/check-research-docs.py` | **passed** |
| #214 script | `python3 scripts/verify_se62_nonspelled_flow_domain.py` | **ALL 37 CHECKS PASS** (flow optimum ratio `256/81`) |
| #215 scripts | `python3 scripts/verify_two_disjoint_circles_duplex.py`; `…verify_oriented_molecule_bridging.py`; `…audit_215_transfer_reconciliation.py` | **all assertions pass** |
| #216 script | `python3 scripts/verify_implication_lattice_216.py` | **79/79 checks pass** |
| #208 scripts | `python3 scripts/verify_finite_interpretation_audit.py` | **all checks pass** (64-cell interpretation universe) |
| #208 citation audit | `python3 scripts/audit_source_note_citations.py` | **exit 1 by design**: reports the one dead locator already recorded in `finite-interpretation-universe-audit.md` (`se62-revcomp-index-decision.md` on absent branch `analysis/se62-revcomp-index-decision-0920`, commit `7bb1f3a`); CI runs only `check-research-docs.py`, so this diagnostic does not gate CI |

**Host limitation, pre-existing.** The full `lake build --wfail` (CI's gate)
cannot complete on this host: `AssemblyP1/Issue94Transposition.lean` is
OOM-killed (exit 137) even at `LEAN_NUM_THREADS=1`, and the root imports it. The
module is byte-identical to `main` and untouched by this integration; the same
limitation is already recorded in §7. `AssemblyP1.Issue94OrbitSearch`, the other
heavy module, **does** build single-threaded (249s). CI's `build` job
(`LEAN_NUM_THREADS=1`, 6 GiB swap, 360-minute budget) remains the arbiter of the
whole-library `--wfail` build, the `leanchecker AssemblyP1` replay, and the
`axiom-audit --modules-from AssemblyP1` pass; the five new modules and the
population endpoint are each verified above on this host.

**Source fidelity unchanged.** The historical 2016 likelihood referent is still
unselected (no primary source fixes `E`, `A`, the §6.2 flow, or the general
principle), and the publisher's supplementary ZIP remains uninspected (HTTP
403). The population theorem's being kernel-checked does **not** settle the
finite 2016 sentence: it answers the project's own population model.

### 7.4 Final synthesis round (this pass), 2026-10-09

Base: `a4dbd0a` (the previous integration round on top of `729f50c`). The two
**verified** leaf modules the previous round tracked but did not integrate were
taken by `git checkout <head> -- <new-path>` (again never their paper or shared
`AssemblyP1.lean` edits):

| leaf | files integrated | why |
|---|---|---|
| #210 | `AssemblyP1/OrientedVariableLengthSe62.lean`, `docs/source-notes/oriented-variable-length-se62.md`, `scripts/verify_oriented_variable_length_se62.py`, `scripts/verify_oriented_variable_length_se62_amplification.py` | the module **builds**; it upgrades R14 to `[K]` and supplies the landed amplification families |
| #213 | `AssemblyP1/Section62VarlenPerOccurrence.lean`, `docs/section62-varlen-per-occurrence-audit-213.md`, `scripts/verify_se62_varlen_per_occurrence_audit_213.py` | the module **builds**; it hardens R10/R12 |

The two modules were root-imported in `AssemblyP1.lean` (after
`ImplicationLattice`) and checked here:

| check | command | result |
|---|---|---|
| integrated module build | `LEAN_NUM_THREADS=4 lake build AssemblyP1.OrientedVariableLengthSe62 AssemblyP1.Section62VarlenPerOccurrence` | **Build completed successfully (8928 jobs)**; both modules built (22s, 11s) |
| axiom audit | `#print axioms` on `oriented_variable_length_se62_counterexample`, `…counterexample'`, `truth_information_feasible`, `truth_not_maximizer_in_general_flow_universe`, `truth_not_maximizer_in_flow_universe`, `competitor_is_unique_optimizer`, `truth_per_occurrence`, `competitor_per_occurrence` | every one `[propext, Classical.choice, Quot.sound]` |
| #210 script | `python3 scripts/verify_oriented_variable_length_se62.py` | **ALL ASSERTIONS PASSED** (bound attained, closed form `M=0..4`) |
| #210 amplification script | `python3 scripts/verify_oriented_variable_length_se62_amplification.py` | **ALL ASSERTIONS PASSED** (families `M=0..200`) |
| #213 script | `python3 scripts/verify_se62_varlen_per_occurrence_audit_213.py` | **ALL AUDIT CHECKS PASS** (60 checks; ratio `9/8`, exact `125/108`) |
| #219 audit | `python3 scripts/audit_fibre_count_219.py` | **AUDIT PASSED** (all claims verified against brute force on binary words length `1..9`) |
| paper build | `latexmk -pdf -halt-on-error main.tex` with the pinned Guix profile | **`main.pdf`, 35 pages, 0 undefined references** |
| documentation integrity | `python3 scripts/check-research-docs.py` | **passed** |

**Resolved as redundant, deliberately not integrated (recorded, not claimed):**

* #216’s uncommitted sample-multiplicity `Part 6` in `AssemblyP1/ImplicationLattice.lean`
  **does not compile** (~40 errors: `unfold addRead`, `Finset` reindexing,
  `omega`, `Real.exp_inj`); it is left in its worktree. It is **resolved as
  redundant**, superseded by the already-`[K]` result via R14 (#210,
  `OrientedVariableLengthSe62`); the lattice claims no general amplification
  theorem. See [`../implication-lattice-216.md`](../implication-lattice-216.md) §7.
* #219’s `AssemblyP1/FibreCountArithmetic.lean` at the time of this round did
  **not** compile (Finset-reindexing / `omega` failures at lines 155/178/188/190)
  and was left in its worktree. **Superseded by §7.7:** leaf #219 reached terminal
  (`81d29c6`), the module now compiles, and it is integrated. Its Theorems 1–3
  are proved in `docs/exact-fibre-count-theorem-219.md` (integrated) and audited
  by `scripts/audit_fibre_count_219.py` (integrated; **AUDIT PASSED**). It is a
  population counting result, not a matrix row.

**Host limitation, unchanged.** The full-library `lake build --wfail` remains
CI’s job (`Issue94Transposition` OOM-kills on this host). The two new modules
are each built and axiom-audited above.

**Qualification (the gate’s requirement 5).** No **determinate source-supported**
row remains open. The claim “all source-supported interpretations of the 2016
finite bridging⇒ML question are resolved” is asserted for the source-supported
class only, and is explicitly **not** extended to: (i) R16, the Bresler
doubled-strand **concatenation** convention — **not a determinate source row**
(a different paper’s convention), open in **both** directions with no bounded
search used as evidence, the known witness kernel-checked inadmissible, and with
its compatibility with the oriented reading kernel-checked incomparable off the
R1∧R2∧R3 locus (the faithful-occurrence reading’s general soundness is a
conjecture); (ii) R17, the unspecified general ML principle — not a determinate
proposition and not settleable from source; (iii) R18, the disclosed
two-disjoint-circles duplex model — a project-level modelling choice, not a
source reading; (iv) #216 `Part 6` (**resolved as redundant**, superseded by
#210) and #219’s count theorem (**integrated**), neither of which is a matrix
row. R13 is resolved although it
is **not** source-supported (the per-occurrence strengthening is a
repository-added surface). The positive same-length **rotation-uniqueness** half
(R9) remains Lean-conditional on the external BBT complete-spectrum input; only
the *population* theorem is kernel-checked without it. The referent question
(which MB09 object the 2016 sentence denotes) remains an unselected source gap,
and the publisher’s supplementary ZIP remains uninspected.

### 7.5 V3-settle integration round (this pass), 2026-10-09

Base: `59cb40d` (the final synthesis round). Leaf #215 settled the residual V3
(Bresler `2G` remap) row at commits `67de8b7`+`20b6c71`+`2a3d2cf` on
`agent/board-215-745214` (not pushed; objects reachable from this worktree’s
shared store). The novel, self-contained artifacts were taken by
`git show <head> -- <path>` (never the leaf’s `AssemblyP1.lean` or paper edits):

| leaf | files integrated | why |
|---|---|---|
| #215 | `AssemblyP1/BreslerRemapCompatibility.lean`, `scripts/verify_bresler_remap_compatibility.py`, appendix §11 of `docs/source-notes/oriented-to-double-strand-bridging-transfer-2026-10-09.md` | the module **builds**; it kernel-checks the exact V3↔V1/V2 compatibility locus (R1∧R2∧R3) and both incomparability witnesses |

The module was root-imported in `AssemblyP1.lean` (after
`Section62VarlenPerOccurrence`) and checked here:

| check | command | result |
|---|---|---|
| integrated module build | `LEAN_NUM_THREADS=4 lake build AssemblyP1.BreslerRemapCompatibility` | **Build completed successfully (8928 jobs)**; module built (59s) |
| kernel replay | `LEAN_NUM_THREADS=1 lake env leanchecker AssemblyP1.BreslerRemapCompatibility` | **exit 0** |
| axiom audit | `#print axioms` on `gggaDbl_information_feasible`, `ggga_not_information_feasible`, `remap_natural_seat_not_sound`, `seat6_spurious`, `seat7_spurious`, `spurious_seats_are_the_wrapping_pair`, `remap_not_complete`, `v5_ggga_fails` | every one `[propext, Classical.choice, Quot.sound]` |
| forbidden-token scan | `grep -E '\b(sorry\|axiom\|admit\|native_decide)\b'` on the module and script | **no matches** outside docstrings/comments |
| #215 script | `python3 scripts/verify_bresler_remap_compatibility.py` | **all assertions passed** (30 assertions; R2 `254/508`, spurious seats, V5 reconciliation) |
| paper build | `latexmk -pdf -halt-on-error main.tex` with the pinned Guix profile | **`main.pdf`, 35 pages, 0 undefined references** |
| documentation integrity | `python3 scripts/check-research-docs.py` | **passed** |

**What this round changes, and what it does not.** R16’s *maximizer* question
(is the truth the ML maximizer under the V3 reading?) is **unchanged**: still
open in both directions, no beat known, the `AAATAT` witness inadmissible. What
is new is the *compatibility* classification: the V3 bridging predicate is
exactly compatible with the oriented one iff R1∧R2∧R3, and off that locus the
two are incomparable with kernel-checked witnesses in both directions. This
sharpens the residue statement but does not close R16, and it does not touch
R17/R18 or the then-pending leaf artifacts (#219 later integrated; #216 `Part 6`
later resolved as redundant). The faithful-occurrence reading’s
general soundness remains a **conjecture** (verified in scope only).

**Host limitation, unchanged.** The full-library `lake build --wfail` remains
CI’s job (`Issue94Transposition` OOM-kills on this host). The new module is
built, kernel-replayed and axiom-audited above.

### 7.6 #209 integration round (this pass), 2026-10-09

Base: `9627f18` (the V3-settle round). Leaf #209 is **closed/terminal** (board
comment 03:18) at commits `cf92561`…`5b18b1a` on `agent/board-209-6cf9bd`
(pushed). Its novel, self-contained artifacts were taken by
`git show <head> -- <path>` (never the leaf's `AssemblyP1.lean` or paper
edits; `scratch-209/` deliberately not taken):

| leaf | files integrated | why |
|---|---|---|
| #209 | `AssemblyP1/Issue209EAudit.lean`, `scripts/verify_issue209_ea_witnesses.py`, `scripts/verify_issue209_ea_witnesses_third_pass.py`, `scripts/audit_issue209_axioms_full.py`, `docs/issue-209-ea-audit-ledger.md`, `docs/issue-209-terminal-report.md` | the module **builds**; it strengthens R1 (the `AAABB` witness refutes `A` too) and kernel-checks the external-`N` domain boundary |

The module was root-imported in `AssemblyP1.lean` (after
`BreslerRemapCompatibility`) and checked here:

| check | command | result |
|---|---|---|
| integrated module build | `LEAN_NUM_THREADS=4 lake build AssemblyP1.Issue209EAudit` | **Build completed successfully (8925 jobs)**; module built (5.7s) |
| kernel replay | `LEAN_NUM_THREADS=1 lake env leanchecker AssemblyP1.Issue209EAudit` | **exit 0** |
| axiom audit | `#print axioms` on `aaab_refutes_fixed_N_binomial`, `truth_information_feasible`, `truth_not_maximum_likelihood`, `likelihood_ratio`, `winCount_le_len`, `binomial_marginal_probability_on_le_len`, `external_N_domain_boundary` | every one `[propext, Classical.choice, Quot.sound]` |
| module-level axiom audit | CI-pinned `axiom-audit --allow propext,Classical.choice,Quot.sound --root AssemblyP1 --modules AssemblyP1.Issue209EAudit` | **audited 174 declaration(s); all within the allowlist**, exit 0 |
| forbidden-token scan | `grep -E '\b(sorry\|axiom\|admit\|native_decide)\b'` on the module | **no matches** outside the docstring |
| #209 witness script | `python3 scripts/verify_issue209_ea_witnesses.py` | **all checks passed** |
| #209 third-pass script | `python3 scripts/verify_issue209_ea_witnesses_third_pass.py` | **all checks passed** (91 checks) |
| #209 full axiom sweep | `python3 scripts/audit_issue209_axioms_full.py --write` | **116/116 theorems reported; 105 on exactly the permitted three, 11 axiom-free, 0 outside** |
| documentation integrity | `python3 scripts/check-research-docs.py` | **passed** |

**What this round changes, and what it does not.** R1 is strengthened: the
`AAABB → AAAAB` witness refutes **both** source-nameable objectives (`E` ratio
`2`, `A` ratio `1125/512`), so the row's negativity does not depend on which
of the two the 2016 sentence denotes. The objective-`A` axis gains the
domain-boundary fact: the external `N` restricts the admissible class to
`|D| ≤ N` (kernel-checked), which is why R5's witness is chosen with every
`dᵢ ≤ 2 < N`. No other row changes; R16/R17/R18 and the then-pending leaf
artifacts are untouched (#219 later integrated; #216 `Part 6` later resolved as
redundant).

### 7.7 Terminal round: #219 integration and pending-leaf reconciliation (this pass), 2026-10-09

Base: `5e79745` (the #209 integration round on top of `9627f18`). This is the
META front's terminal pass. It reconciles the two leaf artifacts the earlier
rounds tracked as pending, without writing into any live leaf worktree.

**#219 `FibreCountArithmetic` — integrated.** Leaf #219 reached
`B219 TERMINAL — state: done` at `81d29c6` (doc cross-reference `1ec6195`) on
`agent/board-219-547404`, pushed. Its novel, self-contained artifacts were taken
read-only by path (never the leaf's `AssemblyP1.lean` or paper edits):

| leaf | files integrated | why |
|---|---|---|
| #219 | `AssemblyP1/FibreCountArithmetic.lean`, `docs/exact-fibre-count-theorem-219.md`, `scripts/audit_fibre_count_219.py` | the module now **compiles**; it is the kernel-checked divisor-sum core. The updated note adds the prior-art boundary (§11, Shomorony et al. ISIT 2016 App. C Cor. 1) and the kernel-check record; the updated audit script removes a dead placeholder helper and calls `spectrum_of_word` |

The module was root-imported in `AssemblyP1.lean` (after `Issue209EAudit`) and
checked here:

| check | command | result |
|---|---|---|
| integrated module build | `LEAN_NUM_THREADS=4 lake build AssemblyP1.FibreCountArithmetic` | **Build completed successfully (8924 jobs)**; module built (2.7s), exit 0 |
| kernel replay | `LEAN_NUM_THREADS=1 lake env leanchecker AssemblyP1.FibreCountArithmetic` | **exit 0** |
| axiom audit | `#print axioms` on `sum_antidiagonal_eq_sum_divisors`, `sum_divisors_inv_mul_eq`, `sum_divisors_divisors`, `sum_moebius_div_eq_totient`, `fibre_mobius_inversion`, `fibre_totient` | every one `[propext, Classical.choice, Quot.sound]` |
| forbidden-token scan | `grep -E '\b(sorry\|axiom\|admit\|native_decide)\b'` on the module | **no matches** |
| #219 audit script | `python3 scripts/audit_fibre_count_219.py` | **AUDIT PASSED** (exit 0; 88 `L=2` + 119 `L=3` binary spectra, 0 mismatches on Möbius/totient/primitive/root/criterion) |
| documentation integrity | `python3 scripts/check-research-docs.py` | **passed** (exit 0) |

**Scope of the kernel check, stated exactly.** What is kernel-checked is the
*arithmetic*: divisor-sum reindexing, Möbius inversion for the fibre count, and
the totient/Burnside rearrangement. The BEST/Matrix-Tree graph content — the
weighted arborescence quantity `B_h` and the branching primitive-spelling
construction — is **external** (classical BEST, plus the kernel-checked
`AssemblyP1/ScalarPrimitiveSpellings.lean`). The theorem note and audit script
carry the population-level proof and its exact-arithmetic reproduction. This is
a **population counting** result, not a finite-data matrix row; integrating it
changes no row's resolution.

**#216 `Part 6` — resolved as redundant, not integrated.** Leaf #216 is **live**
(`/workspace/assemblyp1-finite-216`, branch `agent/board-216-eb3281` at
`486d60f`, uncommitted `M AssemblyP1/ImplicationLattice.lean`, +534/−30). Its
worktree was consulted **read-only**: never written to, never used as a `cwd`,
never merged or cherry-picked. There is **no committed or board result** for
`Part 6`: the branch HEAD's `ImplicationLattice.lean` contains no
sample-multiplicity refinement (grep count `0`), the board's newest comments are
all `state: working`, and the uncommitted `Part 6` still does not compile. The
committed base module (`ImplicationLattice`, the conclusion-schema transfer
lattice) is already integrated and its result is already `[K]` via R14/R10–R12.
`Part 6` is therefore **resolved as redundant and deliberately not integrated**:
its *result* is carried by the already-`[K]` `OrientedVariableLengthSe62`
(#210), the lattice claims no general amplification theorem, and re-landing a
non-compiling duplicate would add no kernel-checked content. **Pointer:** the
canonical carrier is `AssemblyP1/OrientedVariableLengthSe62.lean` (row R14);
`implication-lattice-216.md` §7 records the same resolution. Its absence opens
no row.

**R16, R17 and R18, restated as bounded qualifications (no bounded search used
as evidence).** These are unchanged from the earlier rounds and are restated
here so the terminal verdict is self-contained:

* **R16** (Bresler–Bresler–Tse `2G` concatenation) is **open in both
  directions** under a *different paper's* convention, and is **not** a
  determinate source row or a source-supported reading of the 2016 sentence
  (project-level convention, not a source fact). What is *proved* is the
  negative admissibility of the known witness
  (`doubled_not_information_feasible`, kernel-checked) and the exact
  compatibility classification (`BreslerRemapCompatibility`: V3 is compatible
  with V1/V2 iff R1∧R2∧R3, incomparable off that locus in both directions,
  kernel-checked). The absence of a beat in the seven searched scopes is
  recorded only as **absence of a known witness**, never as evidence of
  openness; no bounded search is used to claim either direction. The
  faithful-occurrence reading's general soundness remains a **conjecture**
  (verified in scope only).
* **R17** (the unspecified general ML principle) is **not a determinate
  proposition and cannot be settled from source**: the 2016 text fixes no
  objective, so no finite witness and no source argument decides it. This is a
  qualification of the source, not a project-level strengthening.
* **R18** (two-disjoint-circles duplex) is a **disclosed project-level modelling
  decision**, not a source row. Circle-by-circle `I_s` is exactly equivalent to
  `I_s(S)` (kernel-checked), so the `AAATAT → AAAAAT` witness survives there;
  duplex-as-a-whole is ill-defined and strictly stronger. It settles no source
  row.

**Project-level strengthenings vs. source facts (labelling).** The
per-occurrence rule `d_D(w) ≥ x(w)` (`Focc`) is a **repository-added
assumption surface**, **not** Medvedev–Brudno's §6.2 rule (which states only the
per-vertex lower bound `1`); the same is true of the fixed-`G` candidate
restriction (`U2`) and the two-disjoint-circles duplex (`R18`). These are tagged
**[C]** in §1 and are called project-level strengthenings here, never source
facts. R13's resolution (FALSE) is a mathematical service to that repository
question, not a reading of the 2016 sentence. Historical ambiguity (the
unselected 2016 likelihood referent, the strand-convention gap, the
`4^k` vs molecule-class index tension, the uninspected publisher supplement)
stays explicit in §1.1/§1.4, §3, §4 and §6; it is not resolved by this pass.
**Final source-gap count: 7 unresolved items** for the 2016 finite question
(audit register §6 items 1–6 and 8; item 7 closed); the three bearing on the
matrix claim are the referent, the publisher supplement, and the
strand/equivalence convention. The full enumeration is §3.1.
