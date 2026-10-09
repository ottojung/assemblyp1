# A disconnected-support feasible optimum at full overlap (`o_min = L − 1`)

_Terminal report for issue #214, Section 6.2 genuine target. 2026-10-09.
Independent from-scratch computation + primary-source reading + kernel-checked
finite certificate.  Every claim is labelled **source fact**, **modeling
choice**, **mathematical proof**, **kernel-checked**, **verified computation**,
**project-level strengthening**, or **open**._

_Reproduction:_

```sh
python3 scripts/verify_se62_full_overlap_disconnected_optimum.py
lake build AssemblyP1.Section62FullOverlapDisconnected
lake env leanchecker AssemblyP1.Section62FullOverlapDisconnected
```

_The script is self-contained, exact (`fractions.Fraction`), deterministic, exits
non-zero on any failed assertion, and shares no code with the earlier §6.2
searches.  The Lean module contains no `sorry`, `axiom`, `admit` or
`native_decide`; its theorems depend only on the standard axioms `propext`,
`Classical.choice`, `Quot.sound`._

---

## 0. Verdict at a glance

**Open question settled.**  At full overlap `o_min = L − 1` in the
bidirected / reverse-complement Medvedev–Brudno (2009) §6.2 model, the answer
to

> is every §6.1-optimal §6.2 flow positive-support connected?

is **no**.  There is an explicit §6.2-feasible flow, built from a truth that
satisfies the strict Shomorony `I_s` bridging predicate, whose throughput is the
**unique** global maximizer of the §6.1 objective over its whole domain and whose
positive support is **disconnected**.  So a genuine optimum of the full flow
optimizer need not be positive-support connected.  [kernel-checked]

The witness:

```text
alphabet        {A, T}, reverse-complement involution A <-> T
truth           S = AAATAT  (G = 6)
read length     L = 3,  o_min = L − 1 = 2   (full overlap)
realized starts (0, 1, 3, 5), start 0 sampled twice   (n = 5)
external size   N = |S| = 6
observed        x = { AAA:2, AAT:1, ATA:1, TAA:1 }
support         { AAA, AAT, ATA, TAA }   (all four molecule classes)
truth spectrum  d_S = (AAA:1, AAT:1, ATA:3, TAA:1)
optimum         d*  = (AAA:2, AAT:1, ATA:1, TAA:1)   [unique global max]
ratio           L(d*)/L(d_S) = 1280/243 > 1
```

The disconnected optimum `d*` is the throughput of two bidirected components
with no edge between them:

```text
component 1:  AAA.p -> AAA.p  (self-overlap "AA")  x2
component 2:  AAT.p -> ATA.p -> TAA.p -> AAT.p  (circuit)
positive support = { AAA } u { AAT, ATA, TAA }   -> two components
```

---

## 1. Source facts and named assumptions

### 1.1 Source facts

Primary source: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116, §3.1–3.4, §5.2, §6.1–6.2,
PMC3154397, as quoted in `docs/section62-mb09-bidirected-graph-audit.md` §1.

- §3.1 a DNA molecule is an unordered reverse-complement strand pair; §4.1 each
  `k`-molecule is represented only once, so a vertex is a *class*.
- §3.3 a bidirected edge carries a signed incidence at each endpoint.
- §3.4 a flow satisfies the signed-incidence balance `pos(f)(v) − neg(f)(v) = b(v)`.
- §5.2 the vertex split `v⁻ → v⁺` carries the vertex bounds, so `d_i` is the flow
  through vertex `i`.
- §6.1 the tractable objective is the product of per-type binomial marginals with
  the external known genome length `N`, `∏_w C(n, x_w) (d_w/N)^{x_w}
  (1 − d_w/N)^{n−x_w}`, `0 ≤ d_w ≤ N`.
- §6.2 vertices are the reads; edges are all bidirected overlaps of length ≥
  `o_min`; transitive edge reduction; every read vertex has lower bound `1`, all
  other lower bounds `0`, all upper bounds `∞`; a supersource/supersink is added
  with prohibitive cost so that its usage is minimized; the flow represents a
  "(non-contiguous) assembly of the genome" while "the original double-stranded
  genome corresponds to a circuit".
- Observation 7: the number of times a walk visits a read vertex equals the number
  of times that read appears as a submolecule of the molecule the walk spells.

[source fact]

`I_s` = coverage, every maximal triple repeat all-bridged, every interleaved
repeat pair bridged, with the strict copy-bridging normalization of
`docs/bridging-source-semantics.md`: a read `[r, r+L)` bridges the length-`e`
copy at `t` iff `r < t` and `t + e < r + L` on the integer lift. [source fact]

### 1.2 Modeling choices used here

| ID | Assumption | Justification | Kind |
|---|---|---|---|
| A1 | Vertices are read **molecule classes** `min(w, rc w)`; a duplicated read is one vertex and enters only `x_w`. | MB09 §3.1, §4.1 | modeling choice |
| A2 | Vertex lower bound `1`; the observed multiplicity `x_w` is **not** a lower bound on `d_w`. | MB09 §6.2 (per-vertex, not per-occurrence) | modeling choice |
| A3 | Candidate objects are **closed** integral flows (zero supersource/supersink usage), i.e. "non-contiguous assemblies". | MB09 §6.2 circuit observation + prohibitive terminal cost | modeling choice |
| A4 | Objective is the §6.1 separable binomial with external `N = \|S\|`. | MB09 §6.1 | modeling choice |
| A5 | Genome circular; starts and windows cyclic. | MB09/Shomorony exposition | modeling choice |
| A6 | `o_min = L − 1 = 2` (full overlap). Consecutive windows of a circular molecule overlap in exactly `L − 1` symbols, so every window walk uses length-`(L−1)` edges only. | MB09 §6.2 | modeling choice |
| A7 | `I_s` uses the strict bridging predicate. | `docs/bridging-source-semantics.md` | modeling choice |
| A8 | Bidirected balance is checked at **port (strand) level** as well as class level. The class-level signed-incidence balance of `Feasible62` is checked as well. | MB09 §3.3/§3.4 read at strand level; A8 is *stronger* | modeling choice |
| A9 | The vertex throughput is the departing flow, which A8 forces to equal the arriving flow. | MB09 §5.2, Observation 7 | modeling choice |
| A10 | No flow-to-sequence rule exists in the source; the question "is the ML sequence the truth" is therefore ill-posed over the flow domain. | absence of any such rule in MB09 §6.2 | modeling choice |
| A11 | Bridge-aware placement vs. sampled multiplicity: coverage and bridging see the *set* of realized placements; the sampled multiplicity is separate data (start `0` sampled twice here). | record, as in `AssemblyP1/SameLengthSection62Counterexample.lean` | modeling choice |

### 1.3 The "positive-support connectedness" predicate is a project-level strengthening

The phrase "positive-support connectedness of all optima" is **not** an MB09
notion.  MB09 §6.2 does not define it.  To state the question precisely this note
introduces it as a **project-level strengthening**:

> the *positive support* of a flow is the set of read vertices carrying positive
> throughput; the support is **connected** when the positive edges join it into a
> single component, and **disconnected** otherwise.

The §6.2 feasibility, the §6.1 objective, and `I_s` are source facts; the
connectedness predicate and the question "must every optimum be connected?" are
project-level.  The theorem proved here is a statement about §6.2-feasible flows
and their throughputs, and says so.

---

## 2. The witness and its certificates

The instance reuses the already-kernel-checked same-length witness truth `AAATAT`
and realized start set `{0, 1, 3, 5}` of
`AssemblyP1/SameLengthSection62Counterexample.lean`, so the `I_s` certificate is
literally the one already accepted for that truth.

### 2.1 `I_s` holds

- **Coverage.** Intervals `[0,3)`, `[1,4)`, `[3,6)`, `[5,8)` (on the lift) cover
  `0..5`.
- **Triple repeat.** The maximal triple repeats are the length-`1` runs of `A`
  at copies `{0,1,2}`, `{0,1,4}`, `{0,2,4}`, `{1,2,4}`; the reads at lifts `−1`,
  `0`, `1`, `3` bridge them.
- **Interleaved pairs.** The interleaved pairs are `(1@{0,2}) × (1@{1,4})` and
  its swap; the four starts do not cyclically alternate with any other pair, and
  these are bridged.

This is the `SourceFaithfulIs.InformationFeasible` certificate
`truth_information_feasible` of `SameLengthSection62Counterexample.lean`,
discharged by finite `decide` on the shared `Genome` object. [kernel-checked,
reused]

### 2.2 The disconnected optimum is an admissible §6.2 flow

`discFlow` puts flow `2` on the `AAA.p → AAA.p` self-overlap and flow `1` on
each of `AAT.p → ATA.p`, `ATA.p → TAA.p`, `TAA.p → AAT.p`.  All four steps are
genuine length-`2` bidirected overlap edges of the `o_min = 2` graph.  Certified:
edge lower bounds `0`; the §6.2 vertex lower bound `1`; class-level
signed-incidence balance `0` at every read vertex; **port-level balance at every
strand of every observed molecule**; no supersource/supersink usage; vertex
throughput equal to `d*`. [kernel-checked: `disc_feasible62`,
`disc_port_balanced`]

### 2.3 The positive support is disconnected

The positive edges are exactly the four above.  Their endpoints fall into two
sets with no edge between them: `{ AAA }` and `{ AAT, ATA, TAA }`.  So the
positive support has two components. [kernel-checked: `disc_support_disconnected`]

### 2.4 `d*` is the unique §6.1 optimum

The §6.1 objective is separable.  With `x = (AAA:2, AAT:1, ATA:1, TAA:1)`,
`n = 5`, `N = 6`:

```text
AAA coordinate (x_w=2):  (d/6)^2((6−d)/6)^3  maximized uniquely at d = 2
AAT, ATA, TAA (x_w=1):   (d/6)((6−d)/6)^4    maximized uniquely at d = 1
```

Hence the unconstrained integer maximizer over the domain `1 ≤ d ≤ 6` is attained
**exactly** at `d* = (2,1,1,1)` — exactly the throughput of `discFlow`.  The
complete maximizer set is `{d*}`. [kernel-checked: `lik_le_dStar`, `dStar_argmax`]

### 2.5 The truth is strictly beaten

```text
L(d*)/L(d_S) = [(2/6)^2(4/6)^3 / ((1/6)^2(5/6)^3)] · [(1/6)(5/6)^4 / ((3/6)(3/6)^4)]
             = (256/125) · (625/243) = 1280/243 ≈ 5.27
```

[kernel-checked: `lik_dStar_over_truth`, `star_better`]

---

## 3. Why this is distinct from the `o_min = 1` counterexample

The `o_min = 1` counterexample of `AssemblyP1/Section62NonSpelledFlow.lean`
uses the truth `AAATT` and produces an optimal throughput `(2,1,1)` that is
**not the spectrum of any circular molecule of any length** — the phenomenon is
*non-spellability of the throughput*.

Here, at `o_min = L − 1 = 2`, the optimal throughput `d* = (2,1,1,1)` **is** a
genome spectrum: it is the spectrum of the molecule `AAAAT` (windows
`AAA, AAA, AAT, ATA, TAA`).  So the phenomenon is **disconnectedness of the
flow**, not non-spellability of the throughput.  Indeed `d*` also has a
*connected* realization — the `AAAAT` window walk is a single connected circuit —
so the optimum set contains **both** a connected and a disconnected realization.
That is exactly why "all optima are positive-support connected" is false: a
disconnected flow is an optimum.

Both facts are recorded side by side:

| setting | truth | optimal throughput | spellable? | phenomenon |
|---|---|---|---|---|
| `o_min = 1` | `AAATT` | `(2,1,1)` | no (any length) | non-spellability |
| `o_min = L − 1 = 2` | `AAATAT` | `(2,1,1,1)` | yes (`AAAAT`) | disconnected support |

---

## 4. Answering the question

**Question.**  At full overlap `o_min = L − 1` in the bidirected/RC model, is
every §6.1-optimal §6.2 flow positive-support connected?

**Answer.**  No.  The explicit `I_s`-bridged disconnected feasible optimum
above refutes it.  For this instance,

```text
(∀ flow f admissible over the §6.2 feasible set, L(f) ≤ L(d_S))  ⇒  False,
```

because `discFlow` is admissible and `L(discFlow) = L(d*) > L(d_S)`.  And the
stronger "every optimum is positive-support connected" is false because the
unique optimal throughput `d*` is achieved by a flow whose positive support is
disconnected. [kernel-checked]

---

## 5. Relation to existing repository results

| Existing claim | Location | Status after this issue |
|---|---|---|
| `Feasible62` is the general §6.2 flow predicate; a spelled circuit is a feasible flow | `AssemblyP1/Section62BidirectedFlow.lean` | unchanged; reused here |
| `AAATT → AAAATT` and `AAATAT → AAAAAT` refute dominance over the flow domain | `docs/bridging-se62-flow-ml-counterexample.md`, `docs/section62-same-length-bidirected-counterexample.md` | unchanged; the `AAATAT` truth is reused here |
| `AAATT` `o_min = 1` non-spellable optimum | `docs/section62-nonspelled-flow-domain.md` | unchanged; kept distinct (§3) |
| whether a non-spellable *maximizer* exists at `o_min = L − 1` | `docs/section62-nonspelled-flow-domain.md` §6 | still open (bounded zero evidence); this note does not address it — its witness's optimum is spellable |
| whether MB09 §3.4's balance is class or strand level | `docs/section62-nonspelled-flow-domain.md` §6 | unchanged; the witness here satisfies both |

---

## 6. What this settles, and what it does not

**Settles (kernel-checked).**  For the literal §6.2 object with `o_min = L − 1`:

1. `I_s` holds for the truth `AAATAT`, and the truth is an admissible §6.2 flow.
2. Another admissible §6.2 flow has throughputs `d*`, the unique global maximizer
   of the §6.1 objective over its whole domain.
3. That flow's positive support is disconnected.
4. The truth is strictly beaten (ratio `1280/243`).

Hence a genuine optimum of the full §6.2 flow optimizer need not be
positive-support connected.  This is the answer to the open question.

**Does not settle.**

1. Which Medvedev–Brudno layer the Shomorony et al. (2016) sentence denotes —
   unchanged source ambiguity, owned by the provenance notes.
2. Whether a non-spellable *maximizer* exists at `o_min = L − 1` — still open;
   the bounded search found none in scope, and this note's witness does not
   address it.
3. Whether an unbounded family of disconnected-optimum witnesses exists, or one
   with all read starts distinct.  This witness samples start `0` twice (like the
   existing witnesses); whether a distinct-start witness exists is open.
4. Whether MB09 §3.4's balance is class or strand level — unchanged; the witness
   satisfies both.

---

## 7. Epistemic status

| Claim | Status |
|---|---|
| MB09 §6.1/§6.2 object, per-vertex lower bound `1`, molecule-class vertices | **source fact** |
| `I_s` definition and the strict bridging normalization | **source fact** |
| `o_min = L − 1 = 2` (full overlap) | **modeling choice** |
| "positive-support connectedness" predicate | **project-level strengthening** |
| `S = AAATAT` satisfies `I_s` with realized starts `{0,1,3,5}` | **kernel-checked** (reused `truth_information_feasible`) |
| `discFlow` is §6.2-admissible (class + port balance, vertex LB, no terminals) | **kernel-checked** (`disc_feasible62`, `disc_port_balanced`) |
| `discFlow`'s positive support is disconnected | **kernel-checked** (`disc_support_disconnected`) |
| `d* = (2,1,1,1)` is the unique global maximizer of the §6.1 objective over `[1,6]^4` | **kernel-checked** (`lik_le_dStar`, `dStar_argmax`) |
| `L(d*)/L(d_S) = 1280/243` | **kernel-checked** (`lik_dStar_over_truth`, `star_better`) |
| positive-support connectedness of all optima is false at `o_min = L − 1` | **follows** (kernel-checked ingredients) |
| `d*` is spellable (`AAAAT`) and also connectedly realizable | **verified computation** |
| whether a non-spellable maximizer exists at `o_min = L − 1` | **open** |
| which MB09 layer the 2016 sentence denotes; tie semantics; single strand | **open** |

---

## 8. Reproduce

```sh
python3 scripts/verify_se62_full_overlap_disconnected_optimum.py   # exact, deterministic
lake build AssemblyP1.Section62FullOverlapDisconnected             # kernel check
lake env leanchecker AssemblyP1.Section62FullOverlapDisconnected   # kernel replay
```

Primary sources: Medvedev & Brudno (2009), §3.1–3.4, §5.2, §6.1–6.2,
[PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/); Myers (2005),
*The fragment assembly string graph*, *Bioinformatics* 21(Suppl 2) ii79–ii85;
Shomorony, Kim, Courtade & Tse (2016), Eq. (1) and §5; Bresler, Bresler & Tse
(2013).
