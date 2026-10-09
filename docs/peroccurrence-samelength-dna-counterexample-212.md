# A same-length per-occurrence DNA counterexample: `ATATACAC → ATACACAC`

_Status: independent from-scratch computation + source reading + kernel-checked
finite certificate, 2026-10-09.  Front: issue #212, worktree
`/workspace/assemblyp1-finite-212`, branch `agent/board-212-37b45b`.  All claims
below are labelled **source fact**, **mathematical argument**,
**verified computation**, **kernel-checked**, **bounded**, or **open**.  This
note closes the fixed-length residue of the MB09 §6.2 flow-restricted statement
under the **per-occurrence strengthening**, and labels that strengthening as a
project-level hypothesis rather than a source definition._

_Reproduction:_

```sh
python3 scripts/verify_peroccurrence_dna_samelength_212_sourcefaithful.py
python3 scripts/verify_peroccurrence_dna_samelength_212_sourcefaithful.py --search
lake build AssemblyP1.PerOccurrenceSameLengthCounterexample
```

_The Python scripts (`..._sourcefaithful.py`, this front, and the previously
committed `..._212.py`) are self-contained, exact (`fractions.Fraction`),
deterministic, and exit non-zero on any failed assertion.  The Lean module
contains no `sorry`, `axiom`, `admit`, or `native_decide`; its main theorems
depend only on `propext`, `Classical.choice`, and `Quot.sound`._

---

## 0. Verdict at a glance

The strengthened same-length statement

> **(P_fix^occ)** `I_s` holds **and** the truth-induced flow is an admissible
> MB09 §6.2 bidirected **spelled** candidate **and** the competing candidate is
> a single spelled molecule `D` with `|D| = |S|` **and every observed read
> molecule occurs in each candidate at least as often as it was observed**
> (`d_w ≥ x_w`, the *per-occurrence* strengthening of the §6.2 lower bound)
> `⇒` the truth-induced flow maximizes the §6.1 likelihood,

is **false**.  The witness is

```text
alphabet          {A, C, G, T}, reverse-complement involution A <-> T, C <-> G
truth             S = ATATACAC          (G = 8)
read length       L = 3
realized starts   (1, 3, 4, 5, 6, 7)    (n = 6 reads, all distinct)
external size     N = |S| = 8
observed      x   = { ACA/TGT:2, ATA/TAT:1, ATG/CAT:1, CAC/GTG:1, GTA/TAC:1 }
truth spec    d_S = { ACA/TGT:2, ATA/TAT:3, ATG/CAT:1, CAC/GTG:1, GTA/TAC:1 }
competitor        D = ATACACAC          (|D| = 8, SAME LENGTH)
competitor spec   d_D = { ACA/TGT:3, ATA/TAT:1, ATG/CAT:1, CAC/GTG:2, GTA/TAC:1 }
```

`I_s` holds; **both** `S` and `D` induce admissible §6.2 bidirected circuits on
the transitively reduced read-overlap graph; **both** satisfy the strengthened
rule `d_w ≥ x_w`; and `D` strictly improves both same-length objectives:

```text
literal §6.1 product of binomial marginals   L(D)/L(S) = 9/5
candidate-intrinsic exact multinomial        L(D)/L(S) = 3/2
```

Unlike the merged `AAATAT → AAAAAT` witness, **neither molecule is read-tiled**
and **the truth itself is per-occurrence feasible**, which is what makes this a
refutation of the *strengthened* statement and not a restatement of the source
refutation. [verified computation + kernel-checked]

---

## 1. Source semantics, and where the strengthening enters

### 1.1 Medvedev–Brudno §6.2 (source fact)

Primary source: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116, §3.1, §4.1, §6.1–6.2,
PMC3154397.

- §3.1: a DNA molecule is an unordered pair of reverse-complement strands.
- §4.1: "each `k`-molecule is represented only once."
- §6.2: the vertices are the reads, which are DNA molecules; "each vertex has a
  lower bound of `1` since it represents a read that must be present in the
  genome at least once"; "all other lower bounds are 0 and all upper bounds are
  infinity"; supersource/supersink at prohibitive cost; "the original
  double-stranded genome corresponds to a circuit", while a general feasible
  flow is a "(non-contiguous) assembly".
- Observation 7: the number of visits of a walk to a read vertex equals the
  number of times that read appears as a submolecule of the spelled molecule.

**Source-supported inference.** A duplicated observed molecule is one *vertex*;
the observed multiplicity `x_w` enters only the §6.1 likelihood; and the lower
bound is **per vertex**.  For a spelled candidate this is exactly support
equality `supp(d) = supp(x)`.

### 1.2 The per-occurrence rule is a **project-level strengthening**

Requiring in addition `d_w ≥ x_w` for every observed type is strictly stronger
than the source's per-vertex lower bound.  **This is not the §6.2 definition and
it is not a source fact.**  It is the project-level hypothesis under test on this
front, and the module docstring and every script docstring say so.  The two
rules differ exactly at duplicated observations:

| witness | source rule (per-vertex `1`) | strengthened rule (`d ≥ x`) |
|---|---|---|
| `AAATAT → AAAAAT` | both candidates admissible | **truth fails**: `d_S(AAA) = 1 < x_AAA = 2` |
| `ATATACAC → ATACACAC` | both candidates admissible | **both candidates hold**; tight coordinate `ACA/TGT`, `x = d_S = 2` |

This front refutes `P_fix^occ`; the per-vertex statement `P_fix` was refuted
separately and earlier.  The two refutations are logically independent.

The explicit form on the DNA alphabet is also worth recording: no base is
self-complementary, so every `3`-mer pairs with a *distinct* reverse complement,
and the reverse-complement orbit of a `3`-mer has exactly two strands.  That is
what allows a molecule class to carry multiplicity `2` or `3` from distinct
positions without any symbol being read twice.

### 1.3 Shomorony `I_s` (source fact)

Shomorony, Kim, Courtade, Tse (2016), Eq. (1), attributed to Bresler, Bresler &
Tse (2013): a read realization `R ∈ I_s` iff it covers the circular truth, every
triple repeat is all-bridged, and every interleaved repeat pair is bridged.  The
repository encodes this predicate once, in `AssemblyP1.SourceFaithfulIs`
(`InformationFeasible`), with the *strict* bridging condition
`BridgesCopy` (`r < t'` and `t' + e < r + L` on a suitable lift, hence
`e + 2 ≤ L`) — not the older endpoint-only reading, which let a read reach a
long repeat's two endpoints around the complementary circular arc.  This front
uses that shared layer, and the Lean proof of `I_s` is the shared predicate
discharged by finite `decide`, not a stand-in.

---

## 2. Independent verification

The witness was found and checked by a from-scratch script,
`scripts/verify_peroccurrence_dna_samelength_212_sourcefaithful.py`, which
shares no code with the repository's existing searches and deliberately mirrors
*this repository's* definitions rather than re-deriving them (the class
representative `rep3`, the class code `cls`, the read vertices `readVerts`, the
literal `SourceFaithfulIs.InformationFeasible` clauses including the strict
`BridgesCopy`, and the `Section62BidirectedFlow.overlapEdges` construction).  It:

1. recomputes the windows, molecule classes, `x`, `d_S`, `d_D`;
2. re-checks both candidate rules (support equality = the source rule,
   `d ≥ x` = the strengthened rule) for both molecules;
3. re-checks `I_s` clause by clause under the strict bridging predicate, and
   runs **negative controls**: with start set `{1,3,4,5,6}` coverage fails, and
   with `{0,1,2,4,5}` coverage holds but clause 2 fails — so the bridging clause
   is genuinely evaluated, not vacuously satisfied;
4. builds the explicit bidirected overlap graph on the five observed molecules
   at `o_min = L − 1 = 2`, enumerating every edge with its incidence signs;
5. verifies that the cyclic window walks of both `S` and `D` are genuine
   bidirected circuits: every step is a real edge, consecutive windows overlap
   by `L − 1`, every read vertex carries flow `≥ 1`, all read-vertex balances
   are `0`, every visited vertex is an observed read molecule, and opposite
   incidences at every interior vertex;
6. checks that every employed edge has overlap `L − 1 = 2`, from which the
   transitive reduction is vacuous under both readings;
7. evaluates both same-length objectives exactly.

The script exits non-zero on any failure.  A second, earlier script
(`scripts/verify_peroccurrence_dna_samelength_212.py`, committed on this branch)
independently reproduces the witness with a different implementation of the same
facts; the two agree on every number.  **Difference noted and recorded:** that
earlier script's `interleaved_pairs` helper deduplicates the two maximal repeat
pairs by their four starts and therefore reports **one** interleaved pair where
the Lean predicate (and this front's script, which enumerates ordered pairs)
finds **two**.  The earlier script's `I_s` check is therefore *weaker* than the
authoritative one, not unsound, and both readings are satisfied by this witness.

### 2.1 The `I_s` certificate, in full

For the truth `ATATACAC`, `L = 3`, start set `R = {1, 3, 4, 5, 6, 7}`:

| clause | content |
|---|---|
| coverage | all eight positions covered (`{1,2,3} ∪ {3,4,5} ∪ {5,6,7} ∪ {6,7,0} ∪ {7,0,1} ∪ {0,1,2}`) |
| maximal triple repeats | four, all of length `1`: `A@{0,2,4}`, `A@{0,2,6}`, `A@{0,4,6}`, `A@{2,4,6}` |
| every copy bridged | yes.  With `e = 1`, `L = 3`, `BridgesCopy` forces `d = 0` and `t = r + 1`, so the bridging starts are exactly `R − 1 = {0, 2, 6, 7}`; every copy in every triple is bridged |
| interleaved repeat pairs | two (from the four maximal repeat pairs `A@{0,2}`, `A@{0,6}`, `A@{2,6}`, `A@{4,6}`), both bridged |

So **clause 3 of `I_s` is genuinely exercised** here, not vacuous: this is the
first same-length §6.2 witness on the repository's books in which the
interleaving clause has real content. [verified computation + kernel-checked]

### 2.2 The explicit bidirected overlap graph

Vertices are the five observed read molecules (class representatives, codes
`4, 12, 14, 17, 44`):
`ACA/TGT`, `ATA/TAT`, `ATG/CAT`, `CAC/GTG`, `GTA/TAC`.  The ten strands are
`ACA, ATA, ATG, CAC, GTA, TGT, TAT, CAT, GTG, TAC`.  At `o_min = 2` the graph
has exactly **sixteen** edges, each a proper overlap of length `2`:

```text
ACA/TGT  -> CAC/GTG   ACA -> CAC   signs (+1, -1)
ACA/TGT  -> ATG/CAT   ACA -> CAT   signs (+1, +1)
ATA/TAT  -> ATA/TAT   ATA -> TAT   signs (+1, +1)
ATA/TAT  -> GTA/TAC   ATA -> TAC   signs (+1, +1)
ATG/CAT  -> ACA/TGT   ATG -> TGT   signs (+1, +1)
CAC/GTG  -> ACA/TGT   CAC -> ACA   signs (+1, -1)
GTA/TAC  -> ATA/TAT   GTA -> TAT   signs (+1, +1)
GTA/TAC  -> GTA/TAC   GTA -> TAC   signs (+1, +1)
ACA/TGT  -> GTA/TAC   TGT -> GTA   signs (-1, -1)
ACA/TGT  -> CAC/GTG   TGT -> GTG   signs (-1, +1)
ATA/TAT  -> ATA/TAT   TAT -> ATA   signs (-1, -1)
ATA/TAT  -> ATG/CAT   TAT -> ATG   signs (-1, -1)
ATG/CAT  -> ATA/TAT   CAT -> ATA   signs (-1, -1)
ATG/CAT  -> ATG/CAT   CAT -> ATG   signs (-1, -1)
CAC/GTG  -> ACA/TGT   GTG -> TGT   signs (-1, +1)
GTA/TAC  -> ACA/TGT   TAC -> ACA   signs (-1, -1)
```

(The two self-loops are reads whose reverse complements overlap themselves, e.g.
`ATA → TAT` and `TAT → ATA` on the class `ATA/TAT`.)  The longest proper
overlap between two observed strands is `2 = L − 1`, so the transitive reduction
removes **no** edge: the literal reading needs `len₁, len₂ < len = 2` with
`len₁ + len₂ − L = 2`, and the alternative longer-overlap reading needs two
strictly longer proper overlaps, which do not exist. [verified computation +
kernel-checked]

### 2.3 The true feasible flow, and the competitor's

Both circuits use no supersource and no supersink, have zero read-vertex
balance, meet the vertex lower bound `1`, and have vertex throughputs equal to
their own molecule spectrum (MB09 Observation 7).  The hand-written flows in the
Lean module are proved equal to the flows the walks themselves carry.

```text
truth S = ATATACAC
  cyclic window walk:
     ATA/TAT -> TAT/ATA -> ATA/TAT -> TAC/GTA -> ACA/TGT -> CAC/GTG
             -> ACA/TGT -> CAT/ATG  -> (back to ATA/TAT)
  visits (molecule classes):  ATA, ATA, ATA, GTA, ACA, CAC, ACA, ATG
  throughput = d_S = { ACA/TGT:2, ATA/TAT:3, ATG/CAT:1, CAC/GTG:1, GTA/TAC:1 }
  per-occurrence: x <= d_S holds, tight at ACA/TGT (x = d_S = 2)

competitor D = ATACACAC
  cyclic window walk:
     ATA/TAT -> TAC/GTA -> ACA/TGT -> CAC/GTG -> ACA/TGT -> CAC/GTG
             -> ACA/TGT -> CAT/ATG  -> (back to ATA/TAT)
  visits (molecule classes):  ATA, GTA, ACA, CAC, ACA, CAC, ACA, ATG
  throughput = d_D = { ACA/TGT:3, ATA/TAT:1, ATG/CAT:1, CAC/GTG:2, GTA/TAC:1 }
  per-occurrence: x <= d_D holds
```

Note that the competitor's walk traverses `ACA → CAC` and `CAC → ACA` twice
each, so those two edges carry flow `2`, while the truth puts all of its extra
multiplicity on the self-loop pair of the class `ATA/TAT`. [verified computation
+ kernel-checked]

### 2.4 Both objectives

`N = 8`, `n = 6`.  Variant A is the literal §6.1 product of binomial marginals
with zero-count factors retained and the fixed external size; Variant E is the
exact candidate-intrinsic multinomial up to the observation-only constants,
which cancel between two same-length candidates.

| objective | `L(S)` (unnormalised) | `L(D)` (unnormalised) | ratio |
|---|---|---|---|
| Variant A, literal §6.1 binomials, `N = 8`, `n = 6` | — | — | **`9/5`** |
| Variant E, exact candidate-intrinsic multinomial | `12 = 2²·3` | `18 = 2·3²` | **`3/2`** |

Both ratios are strict, so the refutation does not depend on a choice of
objective, and neither molecule is read-tiled (`n = 6 < G = 8`), so the
strengthened rule is doing real work: the truth is not merely spelling the
observation back. [kernel-checked]

### 2.5 Kernel check (Lean)

`AssemblyP1/PerOccurrenceSameLengthCounterexample.lean` kernel-checks, for this
concrete data:

```text
peroccurrence_samelength_se62_bidirected_flow_counterexample
  : InformationFeasible truthGenome 3 realizedStarts
    ∧ (genomeLength truth = genomeLength competitor)
    ∧ (PerOccurrenceFeasible dS obs ∧ PerOccurrenceFeasible dD obs)
    ∧ SpelledFeasible62 … spellTruth  truthCircuitFlow  noTerm dS'
    ∧ SpelledFeasible62 … spellCompetitor competitorCircuitFlow noTerm dD'
    ∧ (lik obs dS < lik obs dD ∧ exactLik dD obs / exactLik dS obs = 3/2)

peroccurrence_samelength_maximality_refuted : ¬ PerOccurrenceSameLengthMaximality
```

Together with, in the same file: the sixteen edges written out and proved equal
to the generated graph; the two `Feasible62` certificates clause by clause
(edge lower bound `0`, vertex lower bound `1`, §3.4 balance `0`, no terminal
usage, throughput = spectrum); the four spelled-candidate components for both
molecules (`VisitsObserved`, `StepsInGraph`, `StepsSurviveReduction`,
`BidirectedCircuit`); the vacuity of the transitive reduction under both
readings; the walk transcripts; and the two objectives.  The main theorems
depend only on `propext`, `Classical.choice`, `Quot.sound`.

**Negative controls (kernel-checked in a scratch module, not committed):**
`¬ InformationFeasible truthGenome 3 {1,3,4,5,6}` (coverage fails) and
`¬ InformationFeasible truthGenome 3 {0,1,2,4,5}` (coverage holds, clause 2
fails); `TAC → ACA ∈ graphList` and `GTA → ACA ∉ graphList`.  These pin down that
the `decide`s are deciding the real predicates rather than something vacuous.

### 2.6 A defect found and fixed in the inherited state

The working tree inherited an **untracked, non-compiling** Lean module for this
witness.  Four real errors and one false docstring claim:

1. `code3_lt` was unprovable as written (the foldl form does not telescope under
   `omega`) and the class-code set `relevant` was stated without a provable
   bound on the code.  Replaced by a `Fin 3 → Base` strand representation with
   `codeW` bounded by three `≤ 3` facts.
2. `zero_off_relevant` used `decide` on a statement with free variables.
3. `decide` was invoked on `SupportEquality`/`PerOccurrenceFeasible` without
   unfolding the computational definitions, so no `Decidable` instance was
   synthesised.
4. `not_read_tiled : ∃ c, obs c < dS c := by decide` exceeded the recursion
   limit; it is now discharged from the already-checked single-coordinate
   values.
5. The docstring claimed the §6.2 graph, its sixteen edges, the flows and the
   circuit clauses were kernel-checked, but the file contained **none** of those
   theorems (and did not even import-compile).  The rewritten module proves
   them; the claim is now true.

---

## 3. Independent comparison with `section62-same-length-bidirected-counterexample.md`

The merged note records the `AAATAT → AAAAAT` witness.  Recomputed here from
scratch for the comparison, and every row below is a **verified computation**:
the per-vertex witness of that note has `x = {AAA:2, AAT:1, ATA:1, TAA:1}`,
`d_S = {AAA:1, AAT:1, ATA:3, TAA:1}`, `d_D = {AAA:3, AAT:1, ATA:1, TAA:1}`, so
`d_S(AAA) = 1 < 2 = x_AAA`: **its truth is not per-occurrence feasible and is
not a candidate at all under the strengthened rule.**  That note's §1.1 states
exactly this and leaves the strengthened case open in scope.

| | `AAATAT → AAAAAT` (merged) | `ATATACAC → ATACACAC` (this front) |
|---|---|---|
| alphabet / involution | `{A,T}`, `A ↔ T` | `{A,C,G,T}`, `A ↔ T`, `C ↔ G` |
| `G` | 6 | 8 |
| `L`, `o_min` | 3, 2 | 3, 2 |
| realized starts | `{0, 1, 3, 5}` (5 reads, start 0 twice) | `{1, 3, 4, 5, 6, 7}` (6 reads, distinct) |
| observed vertices | 4 | 5 |
| graph edges | 16 | 16 |
| `I_s` clause 3 | vacuous (no interleaved pair) | **non-vacuous** (2 interleaved pairs, bridged) |
| read-tiled? | truth `d_S = x + {ATA:2}`, `n = 5 < G = 6` | truth `d_S = x + {ATA:2}`, `n = 6 < G = 8` |
| source rule (per-vertex) | both candidates admissible | both candidates admissible |
| strengthened rule (`d ≥ x`) | truth **fails** (`AAA`: 1 < 2) | **both hold** |
| Variant E ratio | 3 | 3/2 |
| Variant A ratio | 5 | 9/5 |

Consequences of the comparison:

1. **The two refutations are logically independent.** One refutes
   `P_fix`, the other refutes `P_fix^occ`.  The strengthened case was *not*
   already settled by the merged witness, and this note supplies the missing
   instance.
2. **The mechanism is the same but now runs on the truth as well.**  Reverse
   complementarity creates multiplicity (`ATA/TAT` occurs three times in
   `ATATACAC` from three distinct positions), and the improvement moves one unit
   of multiplicity from the over-represented coordinate to the observation-heavy
   one at fixed length.  In the merged witness the over-represented coordinate
   `AAA` is *also* the over-observed one, which is exactly what makes the truth
   fail the strengthening; here the observation-heavy coordinate `ACA/TGT` is
   tight for the truth (`x = d_S = 2`), so the truth survives, and the gain
   comes from `ATA/TAT` (`d_S = 3 > 1 = d_D`) instead.
3. **Both notes' claim "clause 3 of `I_s` is vacuous for this truth" is true of
   the merged witness only.**  For `ATATACAC` the interleaving clause has real
   content, which matters for the repository's standing hygiene question about
   whether clause 3 is ever exercised.
4. **The graph is the same size but not the same graph.**  Both instances have
   sixteen edges; the DNA instance has five vertices and ten strands, the
   binary instance four vertices and eight strands, and the extra vertex is
   what carries the `CAC/GTG` and `GTA/TAC` classes that make the truth
   per-occurrence feasible.

Nothing in this note changes any source fact, the merged witness's arithmetic,
or the per-vertex/per-occurrence distinction.

---

## 4. Relation to existing repository results

| Existing claim | Location | Status after this note |
|---|---|---|
| Fixed-length §6.2 statement **open under the per-occurrence strengthening** (bounded zero evidence) | `main`, [`bridging-se62-flow-ml-counterexample.md`](bridging-se62-flow-ml-counterexample.md) §10.2 and §7 | **refuted** by this witness (both objectives) |
| Same-length per-occurrence census **zero** in `G ≤ 8, L = 3, σ = 4` rows | `main`, [`section62-same-length-bidirected-counterexample.md`](section62-same-length-bidirected-counterexample.md) §3 | superseded: the row's scope was `maxmul = 2` over `G = 6` only; the complete scope of this front contains four beats at `G = 8` (§5) |
| "The gap remains under the per-occurrence strengthening" for sequence-level §6.2 feasibility | `main`, [`source-notes/same-length-witnesses-candidate-set-inclusion.md`](source-notes/same-length-witnesses-candidate-set-inclusion.md) §5 | **closed**: this witness has both truth and competitor in the §6.2 feasible set *and* per-occurrence feasible, at the same length |
| Clause 3 of `I_s` vacuous in every same-length §6.2 witness | `main`, same notes | **not true of this witness** |
| Positive same-length maximizer theorem `informationFeasible_62_maximizer` | `main`, [`same-length-62-maximizer.md`](same-length-62-maximizer.md) | unchanged; that theorem quantifies over *genuine §6.2* candidates whose support is the observed set and is unrelated to the strengthened rule, and this witness is not a counterexample to it (see §6) |

---

## 5. Bounded census

`scripts/verify_peroccurrence_dna_samelength_212_sourcefaithful.py --search`
enumerates, over the stated scope, every cyclic-shift/reverse-complement orbit
representative `S`, every start set `R` with full `I_s` and a **per-occurrence
feasible truth** (`d_S ≥ x`), and every same-length competitor `D` with the same
support that is itself per-occurrence feasible, and counts cases where the
competitor strictly improves **both** objectives for the observation `x` that
`R` actually realizes.

| alphabet | `G` | `L` | truth orbits | truth-feasible start sets | both-objective beats |
|---|---|---|---|---|---|
| `{A,C,G,T}` | 4 | 3 | 39 | 375 | **0** |
| `{A,C,G,T}` | 5 | 3 | 104 | 1446 | **0** |
| `{A,C,G,T}` | 6 | 3 | 366 | 6816 | **0** |
| `{A,C,G,T}` | 7 | 3 | 1172 | 22492 | **0** |
| `{A,C,G,T}` | **8** | 3 | **4179** | **73919** | **4** |
| `{A,C,G,T}` | 9 | 3 | 14572 | 185074 | **80** |
| `{A,T}` | 5, 6, 7, 8, 9, 10 | 3 | 4, 9, 10, 22, 30, 62 | 29, 87, 72, 264, 249, 886 | **0** at every `G` |
| `{A,C,G}` | 5 | 3 | 30 | 329 | **0** |
| `{A,C,G}` | 6 | 3 | 74 | 905 | **0** |
| `{A,C,G}` | 7 | 3 | 171 | 1228 | **0** |
| `{A,C,G}` | 8 | 3 | 444 | 2214 | **1** — the `{A,C,G}` embedding of this very witness |
| `{A,C,G}` | 9 | 3 | 1138 | 2945 | **2** |

Three observations about the census.

1. **`G = 8` is the smallest alphabet size that works.**  Under the strengthened
   rule, no per-occurrence same-length beat exists at `G ≤ 7` for
   `σ = 4`, at `G ≤ 7` for `σ = 3`, or at any `G ≤ 10` for `σ = 2`.
2. **The binary alphabet never works.**  The mechanism needs at least three
   distinct symbols: with `σ = 2` and `A ↔ T` there are only four
   reverse-complement classes of `3`-mers, and no per-occurrence beat exists up
   to `G = 10`.  This is consistent with the merged note's `σ = 2` control row.
3. **The `G = 8` beats are four orbit-representative pairs, and all four have
   the same ratios (`3/2` and `9/5`):**

```text
ATATACAC -> ATACACAC     starts (1,3,4,5,6,7)
ATATAGAG -> ATAGAGAG     starts (1,3,4,5,6,7)
ACACGCGC -> ACACACGC     starts (0,1,2,4,6,7)
AGAGCGCG -> AGAGAGCG     starts (0,1,2,4,6,7)
```

Only two combinatorial patterns are present once the `C ↔ G` relabelling of the
alphabet is factored out: `ATATACAC → ATACACAC` (the second row is its
`C ↔ G` relabelling) and `ACACGCGC → ACACACGC` (the fourth row is that one's
`C ↔ G` relabelling).  At `σ = 3`, `G = 8` the census finds exactly one beat,
the `{A,C,G}` embedding of this witness (`ATATACAC → ATACACAC`, ratios `3/2` and
`9/5`), so the DNA witness is the first instance at each of `σ = 3` and
`σ = 4`.  At `G = 9` the `σ = 4` census finds 80 beats with larger ratios
(e.g. `ATATACGCG → ATACGCGCG` at `4/3`), so `G = 8` is the minimum, not the
only, size where the strengthened statement fails.

A separate script on this branch
(`scripts/verify_peroccurrence_dna_samelength_212.py`) searches a different,
larger family of observation vectors per `(S, D, R)` and reports 16 beats in the
same 4 orbit-representative pairs at `(G, L, σ) = (8, 3, 4)`, plus zero rows for
`σ ∈ {2, 3}` up to `G = 8` and `L = 4`.  The two scripts agree on the pairs.
These are **bounded** results — the completeness of each search is not proved,
and they are evidence, not a proof of absence. [verified computation, bounded]

---

## 6. What this does and does not settle

**Does.** It shows that under the §6.2 reading in which reads are
reverse-complement molecules, the truth is a per-occurrence feasible spelled
candidate, and the competing candidate is a single spelled molecule of the same
length, the same-length implication `P_fix^occ` still fails: `I_s` plus
per-occurrence §6.2 feasibility at fixed length does **not** imply ML maximality.
It closes the last open item of the fixed-length residue under the strengthened
rule.

**Does not.** It does not settle which Medvedev–Brudno object the Shomorony et
al. (2016) sentence intends; it does not address the single-strand reading; it
does not address the variable-length case; and it does not address tie or
equivalence semantics (the truth-is-a-maximizer versus
all-maximizers-are-the-truth distinction).  It is also not a counterexample to
the positive theorem of
[`same-length-62-maximizer.md`](same-length-62-maximizer.md), which is a
dominance statement about *genuine* §6.2 candidates under a different objective
normalisation; the two statements are different and both stand.

---

## 7. Epistemic status

| Claim | Status |
|---|---|
| §6.2 object, per-vertex lower bound `1`, reads are molecule classes, `k`-molecules represented once, Observation 7 | **source fact** (MB09 §3.1, §4.1, §6.2) |
| per-vertex lower bound is the source condition; per-occurrence `d ≥ x` is a **project-level strengthening** | **source-supported inference**, labelled as such |
| `S = ATATACAC`, `D = ATACACAC` witness: `I_s` (incl. non-vacuous clause 3), both §6.2 circuits, same length, both per-occurrence feasible, ratios `3/2` and `9/5` | **verified computation** + **kernel-checked** |
| `P_fix^occ` is false | **follows** |
| `P_fix` (source per-vertex rule) is false | **follows** from `section62-same-length-bidirected-counterexample.md`, independently |
| the two refutations are logically independent | **mathematical argument** (§3) |
| beats exist at `G = 8, L = 3, σ = 4` and nowhere smaller in the stated scope | **verified computation**, bounded |
| which §6.1/§6.2 object and strand/tie convention the 2016 sentence intends | **source interpretation, unresolved** |

---

## 8. Reproduce

```sh
python3 scripts/verify_peroccurrence_dna_samelength_212_sourcefaithful.py
python3 scripts/verify_peroccurrence_dna_samelength_212_sourcefaithful.py --search
lake build AssemblyP1.PerOccurrenceSameLengthCounterexample
```

Primary sources: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116, §3.1, §4.1, §6.1–6.2,
PMC3154397; Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
Bioinformatics 32(17) (2016) i494–i502, Eq. (1) and §5.
