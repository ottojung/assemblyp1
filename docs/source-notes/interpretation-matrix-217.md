# Interpretation matrix for the 2016 finite bridging ⇒ ML question (issue #217)

_Status: META front #217, 2026-10-09. The matrix was built on `origin/main`
at `cc0aa8a`; the board branch `agent/board-217-978a0a` now also carries the
merged Lean CI repair PR #117 (`e9fcf01`, "Repair full-library CI compilation
blockers (initial fixes)") on top of that base. The #217 content is unchanged
by the rebase — `git diff origin/agent/board-217-978a0a HEAD` over `docs/`,
`paper/`, and `AssemblyP1.lean` is empty; only the four PR #117 Lean files
(`BBTTripleBridge`, `Issue94ComponentAlignedSwaps`, `Issue94KShortGeneral`,
`Issue94LongWindowSplit`) differ.
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
and is only defined on `0 < dᵢ < N`. **[M]**

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
| `Focc` | the per-occurrence strengthening `d_D(w) ≥ x(w)` for every observed type | **C**: **not** the §6.2 definition. MB09 §6.2 states only the per-vertex lower bound `1`; `Focc` is a repository-added assumption surface |

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
| R1 | `E` | `U1` (free) | `F0` | `or` | `Is` | `W` and `S` both false | **FALSE** | Strict witness `AAABB → AAAAB`, ratio `2`; same-length, so negative transfer gives `U1` | **[K]** `AssemblyP1/FixedLengthExactCounterexample.lean` |
| R2 | `E` | `U1` (free) | `F0` | `or` | `Is` | as above | **FALSE** | Unrestricted-length witness `ACGT → ACACGT`, `1/18 > 3/64` | **[K]** `AssemblyP1/ExactVariantECounterexample.lean` |
| R3 | `E` | `U1` (free) | `F0` | `mol` | `Is` | as above | **FALSE** | Molecule-class witness `AAATT → AAAAT`, ratio `2` under `or`; under `mol` the truth is not `Fgen`, see R7 | **[V]** `scripts/uniform_strand_semantics_search.py --witness` |
| R4 | `E` | `U1` (free) | `F0` | `or` | `Is` | as above | **FALSE** | Read-tiled witness `AAABCBC → AAAAABC`, `G=7`, `L=3`, realized starts `(0,0,0,1,2,5,6)`, `n=7`, ratio `27`; `Is` non-vacuous (coverage + the all-bridged maximal length-1 triple repeat at `(0,1,2)`; interleaving vacuous) | **[V]** `scripts/verify_readtiled_exact_counterexample.py` |
| R5 | `A` | `U1` (on the domain `0<dᵢ<N`) | `F0` | `or` | `Is` | `W` and `S` both false | **FALSE** | Strict witness `AAACC → AAAAC`, ratio `1125/512 > 1`; same-length pair with every `dᵢ ≤ 2 < N`, so both lie in `A`’s domain | **[K]** `AssemblyP1/FixedLengthBinomialCounterexample.lean` |
| R6 | `E` | `U2` | `F0` | `or` | `Is` | `W` false | **FALSE** | `AABB → ABAB`, `G=4`, `L=2`, realized starts `{1,3}`; full `I_s` by computation; exact likelihoods `1/16` vs `1/4` | **[K]** `AssemblyP1/SameLengthExactMLCounterexample.lean` |
| R7 | `E`/`A` | `U2` **and** `Fgen` on *both* truth and competitor | `Fgen` | `or` | `Is` | `W` **true**; `S` true up to cyclic shift | **TRUE** | `informationFeasible_62_spelledML` / `informationFeasible_62_maximizer`: full `I_s` at the realized range, `2 ≤ L ≤ G`, truth a genuine §6.2 candidate ⇒ every same-length genuine §6.2 candidate scores at most the truth | **[K]** `AssemblyP1/MLEscape.lean`, `AssemblyP1/SameLength62Maximizer.lean` |
| R8 | `E`/`A` | `U2` ∩ `Fgen` | `Fgen` | `or` | `¬LTR` only | `W` true | **TRUE** | `same_length_exactLik_maximizer`, `same_length_binomialLik_maximizer` under `hno : ¬ HasLongTripleRepeat` — the kernel-checked conditional core, with no `I_s`, no primitivity, no period premise | **[K]** `AssemblyP1/OrientedSameLengthML.lean`, `AssemblyP1/OrientedFinalRigidity.lean` |
| R9 | `E` | `U2` ∩ `Fgen` | `Fgen` | `or` | `¬LTR` + external BBT input | `S` true, `≈` = cyclic shift | **TRUE, conditional** | `same_length_unique_up_to_rotation_of_bbt`, `same_length_maximality_and_rotation_uniqueness_of_bbt`; the complete-spectrum uniqueness input is an explicit premise `hBBT`, not formalized here | **[K]** conditional, `AssemblyP1/OrientedSameLengthML.lean` |
| R10 | `A` | `U3` flows, length free | `Fgen`/`Fspell` | `mol` | `Is` | `W` and `S` both false | **FALSE** | `AAATT → AAAATT`, `|D|=6 ≠ N=5`, external `N=5`, ratio `9/8`; literal §6.2 feasibility of **both** genomes, incl. the explicit graph, transitive reduction, vertex LB 1, signed-incidence balance | **[K]** `AssemblyP1/Section62BridgingCounterexample.lean` (`se62_bridging_bidirected_flow_counterexample`) |
| R11 | `E`/`A` | `U3` flows, **same length** | `Fgen`/`Fspell` | `mol` | `Is` | `W` and `S` both false | **FALSE** | `AAATAT → AAAAAT`, `G=6`, `L=3`, starts `(0,0,1,3,5)`, `n=5`, external `N=6`; exact ratio `3`, §6.1 binomial ratio `5`; **the interleaving clause of `I_s` is non-vacuous here** | **[K]** `AssemblyP1/SameLengthSection62Counterexample.lean` |
| R12 | `E`/`A` | `U3` flows, length free | `Fgen` + `Focc` (per-occurrence) | `mol` | `Is` | `W` and `S` both false | **FALSE** | the same `AAATT → AAAATT` instance: `d_S = (AAA:1, AAT:2, TAA:2) ≥ x`, `d_D = (AAA:2, AAT:2, TAA:2) ≥ x`, so it satisfies the strengthening, and it is a spelled circuit, hence a general §6.2 flow | **[K]** same modules as R10 (`SeqSupportLB` conjuncts) |
| R13 | `E`/`A` | `U3` flows, **same length** | `Fgen` + `Focc` | `mol` | `Is` | `W` and `S` both false | **FALSE** | Strict witness `ATATACAC → ATACACAC`, `G=8`, `L=3`, o_min `2`, realized starts `(1,3,4,5,6,7)`, `n=6`, external `N=8`; `x = {ATA/TAT:1, TAC/GTA:1, ACA/TGT:2, CAC/GTG:1, CAT/ATG:1}`, `d_S = {…, ATA/TAT:3, ACA/TGT:2, …}`, `d_D = {…, ATA/TAT:1, ACA/TGT:3, CAC/GTG:2, …}`; both spectra support-equal to `x` **and** per-occurrence feasible (tight coordinate `ACA/TGT`, `x = d_S = 2`), `n = 6 < G = 8` so not read-tiled; exact ratio `3/2`, §6.1 binomial ratio `9/5`; both literal §6.2 bidirected circuits on the 16-edge graph, reduction vacuous under both readings. Census: 4 distinct beats at `(G,L,sigma)=(8,3,4)`, bounded evidence only. Harvested read-only from leaf #212 | **[K]** `AssemblyP1/PerOccurrenceSameLengthCounterexample.lean` (`peroccurrence_samelength_se62_bidirected_flow_counterexample`, `peroccurrence_samelength_maximality_refuted`), **V** `scripts/verify_peroccurrence_dna_samelength_212.py`, record `docs/peroccurrence-samelength-dna-counterexample-212.md` |
| R14 | `E`/`A` | `U1`/`U2` | `F0` | `or` | `Is` | `W` false as soon as `n > G` | **FALSE** | oriented variable-length boundary `AAATT → AAAATT` with `x = spec₃(S) + M·e_AAA`: exact ratio `3125/3888, 15625/11664, 78125/34992` at `M = 0,1,2` and binomial `81/128, 81/64, 81/32`; the truth wins exactly at `n = G` | **[V]** `scripts/verify_oriented_se62_rigidity.py` (leaf #210 owns the classification) |
| R15 | `E`/`A` | `U2` ∩ `Fgen` | `Fgen` + `Focc` | `or` | `Is` | `W` true | **TRUE, inherited** | a per-occurrence-restricted candidate class is a *subclass* of the genuine §6.2 class quantified over by R7 — for a spelled circuit of length `G` whose window support is `supp(x)`, the walk flow is a feasible §6.2 flow with every vertex throughput `≥ 1` — so R7’s maximizer conclusion applies unchanged. No general theorem on `main` states the subclass containment as a lemma; it is the argument used case-by-case by the same-length §6.2 modules | **[K]** inherited from R7; containment is a **M** fact for spelled circuits, **O** as a named lemma |
| R16 | `E` | `U1`/`U2` | `F0` | `2G` (Bresler doubled-strand) | remapped `Is` | — | **OPEN** | zero exact-multinomial beats in the seven searched scopes; at `G=3,5` the remapped `Is` is unsatisfiable, so those rows are vacuous rather than positive | **[O]** `docs/source-notes/uniform-strand-convention-search-2026-09-20.md` |
| R17 | `U` | — | — | — | `Is` | — | **not a determinate proposition** | the 2016 text names no objective, so no finite witness can settle “the” ML formulation. Decomposed into its three source-nameable members (`E`, `A`, the `Fgen` flow with `A` costs = R1/R5/R10/R11/R12), all of which are refuted | **[I]** |

### 2.1 What the matrix says about the schema

* Rows R1–R6, R10–R12, R14 are **strict** counterexamples, so they refute `W`
  and `S` simultaneously and for every `≈` and every tie convention. **[M]**
* Rows R7–R9 are the only positive rows, and they are positive only on the
  `U2 ∩ Fgen ∩ or` slice. R9’s uniqueness needs `≈` = cyclic shift (forced)
  and the external BBT complete-spectrum input (not formalized).
* Row R6 is the row that shows the **length restriction alone is not enough**:
  without the §6.2 membership conjunct the same-length question is already
  negative.
* Row R13 was the only **determinate** row that was open on `main`; it is now
  resolved to **FALSE** by a kernel-checked per-occurrence witness (see the
  row). Its assumption `Focc` is an editorial strengthening, not the source’s
  §6.2 rule, so its resolution is a mathematical service to a *repository*
  question, not the reading of a source statement that the other rows are.
* No determinate row remains open on `main`. The residue is R16 (bounded
  evidence under a different paper’s `2G` convention) and R17 (not a determinate
  proposition) — neither is determinate, and neither is a source-supported
  reading of the 2016 sentence.

### 2.2 Front states, coordination, and the general-flow upgrade (this round)

The board coordinates six active leaves. None of their uncommitted work was
harvested or disturbed; the board tracks their status here so another invocation
can recover the research graph.

| leaf | branch / worktree | state this round | board action |
|---|---|---|---|
| #208 | `agent/board-208-0c8fcf` / `assemblyp1-finite-208` | source census committed; untracked `scratch-208/` preserved | tracked; referent/2G-2N source audit, no matrix row change |
| #210 | `agent/board-210-e8b6b2` / `assemblyp1-finite-210` | untracked `OrientedVariableLengthSe62.lean` + script preserved | tracked; R14 classification owned by this leaf |
| #211 | `agent/board-211-8d5103` / `assemblyp1-finite-211` | `SameLength62TieUniqueness` committed; uncommitted umbrella wiring + 2 scripts preserved | tracked; uniqueness half of the same-length §6.2 tie |
| #212 | `agent/board-212-37b45b` / `assemblyp1-finite-212` | clean; module + script already harvested | **harvested** — R13 resolved FALSE (see §7.1) |
| #214 | `agent/board-214-d0e372` / `assemblyp1-finite-214` | `Section62NonSpelledFlow` committed (`6f024ba`); uncommitted refinements preserved | tracked below; **not** harvested (active leaf) |
| #216 | `agent/board-216-eb3281` / `assemblyp1-finite-216` | `ImplicationLattice` committed | tracked; conclusion-schema lattice, no matrix row change |

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
relaxation. #214 remains an active leaf with uncommitted refinements; the board
tracks its committed result here rather than harvesting the module.

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

---

## 4. The claim, stated precisely

Counting rows: R1–R6, R10–R13, R14 are the **eleven** negative rows, of which
the kernel-checked ones are R1, R2, R5, R6, R10, R11, R12, R13 (eight, sharing
six modules) and the exact-arithmetic ones are R3, R4, R14 (three). R7, R8, R9,
R15 are the four positive rows (R9 conditional on the external BBT input, R15
inherited from R7). R9 and R8 are two views of one argument, and R10 and R12 are
one witness, so the row count overstates the number of distinct results and
underrates nothing.

**Resolved (with a reviewed proof or an exact counterexample):**

* every reading that selects the **exact** multinomial `E` over a circular
  candidate universe `U1`/`U2` without §6.2 feasibility (R1–R4, R6, R14) —
  refuted by strict kernel-checked or exact-arithmetic witnesses;
* every reading that selects the **fixed-`N` binomial** `A` over `U1` on its
  domain (R5) — refuted by a strict kernel-checked witness;
* every reading that selects the **§6.2 bidirected flow** with the source’s
  per-vertex lower bound, under molecule read types, at either variable
  (R10, R12) or equal (R11) candidate length — refuted by strict
  kernel-checked witnesses, each of which certifies literal §6.2 feasibility;
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
2. **R16** (Bresler doubled-strand convention) is bounded evidence only and is
   not a source-supported reading of the 2016 sentence.
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

So: **every interpretation of the 2016 finite question that is both
determinate and source-supported is resolved — nine negatively and one
positively — and the residue is one bounded-evidence row using a different
paper’s convention (R16) and one non-determinate row (R17).** No determinate row
remains open. The claim “all source-supported interpretations are resolved” is
therefore justified for the source-supported class, and explicitly not extended
to R16 or R17; R13, which was determinate but not source-supported, is now
resolved in the same sense as the negative rows.

---

## 5. Cross-references

* [`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md) — the four readings and the witness-sufficiency matrix.
* [`conclusion-semantics-determination.md`](conclusion-semantics-determination.md) — conclusion semantics and the residual register.
* [`equivalence-and-tie-wellposedness.md`](equivalence-and-tie-wellposedness.md) — the invariance lemmas and the cyclic-shift/reverse-complement coupling.
* [`conclusion-semantics-strict-witness-robustness.md`](conclusion-semantics-strict-witness-robustness.md) — why a strict witness is equivalence- and tie-proof.
* [`oriented-se62-rigidity-theorem.md`](oriented-se62-rigidity-theorem.md) — the oriented same-length rigidity theorem (rows R7–R9).
* [`../bridging-se62-flow-ml-counterexample.md`](../bridging-se62-flow-ml-counterexample.md), [`../section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md) — rows R10–R12.
* [`../peroccurrence-samelength-dna-counterexample-212.md`](../peroccurrence-samelength-dna-counterexample-212.md) — row R13, the per-occurrence same-length refutation, with the leaf-#212 provenance record.
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
| Rows R7, R8 are proved (maximizer) | **K** |
| Row R9 is proved conditional on an external BBT premise | **K** conditional |
| Rows R10, R11, R12 are refuted by kernel-checked strict witnesses certifying literal §6.2 feasibility | **K** |
| Row R13 is refuted by a kernel-checked strict witness certifying literal §6.2 feasibility on both sides under the per-occurrence strengthening (`ATATACAC → ATACACAC`, ratios `3/2` and `9/5`) | **K** |
| Rows R3, R4, R14 are refuted by exact-arithmetic reproductions | **V** |
| Row R16 is bounded evidence only, under a non-source convention | **O** |
| Row R17 is not a determinate proposition | **I** |
| the leaf-#212 census is bounded evidence, not a proof of absence | **V** bounded |
| no determinate row remains open on `main` | repository fact |
| which MB object the 2016 sentence denotes | **source gap, unchanged** |
| the accepted supplementary ZIP (could hold a likelihood/tie definition) | **uninspected, unchanged** — HTTP 403 on both recorded retrieval paths; not reachable from this host |
| the #214 general-flow upgrade (§6.2 refutation over the whole `Feasible62` domain; optimum spells no genome) | **K** (committed `6f024ba`, active leaf) — tracked in §2.2, module not harvested |
| the integer flow optimum vs. the half-integral relaxation | **kept separate** in §2.2; the relaxation is not the §6.2 object |
| R9’s BBT complete-spectrum input | **O** (external) — carried as explicit `hObs`/`hBBT` premise, not discharged |

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
