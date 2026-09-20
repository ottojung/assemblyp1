# Independent exact §6.2 bidirected-flow model: the `AAATT → AAAATT` witness and a bounded neighbourhood search

_Status: independent primary-source reconstruction + exact finite computation,
2026-09-20. All claims are labelled **source fact**, **modeling choice**,
**mathematical proof**, **verified computation**, or **open**._

_Reproduction:_ `python3 scripts/independent_se62_bidirected_model.py`
(deterministic, exact `fractions.Fraction`, exits non-zero on any failed
assertion).

_Independence._ This note and its script were written from the MB09 primary
text (PMC3154397) and the repository's source-semantics notes, not from the
existing `Feasible` / `SeqSupportLB` support predicate and not from the
unmerged branch certificate `section62-mb09-bidirected-graph-audit.md`. The
point of the exercise is to model the actual bidirected **flow** object, since
the existing lower-bound determination
([`docs/section62-bidirected-lowerbound1-determination.md`](section62-bidirected-lowerbound1-determination.md))
explicitly downgrades its own feasibility predicate to a finite
support/lower-bound certificate rather than the §6.2 definition.

---

## 0. Verdict at a glance

1. **The `AAATT → AAAATT` witness survives the exact §6.2 object.** Under an
   independently built bidirected overlap graph (read molecules as vertices,
   §3.3 orientation incidence, transitive reduction, §5.2 vertex split,
   Observation 7 throughput), the truth `AAATT` and the competitor `AAAATT`
   are both admissible single-molecule circuits, with throughputs
   `d_S = {AAA:1, AAT:2, TAA:2}` and `d_D = {AAA:2, AAT:2, TAA:2}`, and §6.1
   separable-binomial ratio `L(D)/L(S) = 9/8 > 1`. The result is identical at
   both `o_min ∈ {1,2}` for `L = 3`. [verified computation]

2. **A bounded exhaustive flow check finds no better first-tier object than
   `d_D`.** Enumerating every integral circulation with balance `0`, vertex
   throughput `d_w ∈ [1,5]`, edge flow `≤ 5` and total edge flow `≤ 15` yields
   `10` distinct throughput vectors; the maximum-likelihood one is exactly
   `d_D`, at `9/8` over the truth. [verified computation, exhaustive in the
   stated box]

3. **A tightly bounded neighbourhood search finds other bridging truths beaten
   by spelled competitors.** For `G ≤ 6`, `L = 3`, `o_min = 2`, read starts
   drawn from distinct positions with `n ≤ 4`, strict `I_s` satisfied, and a
   single spelled competitor `|D| ≤ N+2`, there are `16` distinct
   (truth, starts, competitor-throughput) hits; the largest ratio is
   `243/128` (`S = AATAT`, starts `(0,2,4)`). The primary instance is among
   them. [verified computation, exhaustive in the stated box]

4. **Nothing here is promoted to proof.** The computations are finite and
   exact; completeness is claimed only inside the boxes named above. They are
   consistent with, and independently reproduce, the finite witness of the
   merged determination. [epistemic]

---

## 1. The model, from the source

Primary source: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116,
[PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/).

**Source facts used.**

- A **DNA molecule** is an unordered reverse-complement pair of strings; a
  read is a molecule (§3.1). On `{A,T}` the involution is `A ↔ T`.
- A **bidirected edge** carries a positive/negative incidence at each endpoint.
  For molecules `x,y` and strand choices it is a bidirected overlap exactly in
  one of four cases (§3.3):
  `p(x)~p(y) → (+x,−y)`, `p(x)~n(y) → (+x,+y)`,
  `n(x)~p(y) → (−x,−y)`, `n(x)~n(y) → (−x,+y)`; the edge length is the
  underlying string-overlap length.
- A **walk** requires opposite orientations at each interior vertex; a
  **loop** has incidence `+2`, `−2`, or `0` according to its two ends (§3.2).
- **§6.2.** Vertices are the reads; edges are all bidirected overlaps of length
  `≥ o_min`; the graph is **transitively reduced** (overlaps spelled by two
  shorter overlaps removed, Myers 2005); a supersource/supersink converts the
  flow to a circulation; **every read vertex has lower bound 1**; all other
  lower bounds are `0` and all upper bounds `∞`; and by **Observation 7** the
  vertex flow `d_i` equals the number of times the read occurs as a submolecule
  of the spelled molecule.
- **§5.2.** Splitting each vertex into `v⁻→v⁺` turns a vertex bound/cost into
  an edge bound/cost; `d_i` is the flow on the split edge.
- **§6.1.** Objective is the product of per-type binomials with the **external**
  true genome length `N`:
  `L(d) = ∏_w (d_w/N)^{x_w} (1 − d_w/N)^{n−x_w}`, `0 ≤ d_w ≤ N`.

**Modeling choices made explicit.**

- Reads are grouped into **molecule types** (per-type reading of the §1.3
  source ambiguity). The primary instance has three distinct observed types,
  each observed once, so the per-type and per-occurrence readings coincide
  there; the bounded search restricts to distinct start positions for the same
  reason.
- Overlaps are **proper** (length `1..L−1`); full self-overlaps are excluded, as
  is standard for overlap graphs of equal-length reads.
- `o_min ∈ {1,2}` are the only values at `L = 3`; both are tested.
- The transitive reduction is the **literal** reading ("spelled by two shorter
  overlaps"), implemented by brute-force composition
  `l = l1 + l2 − L` with orientation consistency at the middle read. For
  `L = 3`, `l = 2` would need `l1 + l2 = 5` with `l1,l2 < 2`, impossible, so no
  maximal-overlap edge is ever removed; the script also asserts this.
  **Correction (2026-09-20):** the implemented inequality
  `e1.length < e.length and e2.length < e.length` is unsatisfiable together
  with `l = l1+l2−L` for proper overlaps (it forces `l >= L+2 > L−1`), so the
  function removes nothing for *any* input. The source-supported reading is
  "spelled by two **proper** overlaps" (`l1,l2 < L`, which forces
  `l1,l2 > l`), as pinned in
  [`source-notes/se62-edge-and-transitive-reduction-rules.md`](source-notes/se62-edge-and-transitive-reduction-rules.md).
  At `o_min = 2` the true reduction is also empty, so the certificate here is
  unaffected; the `o_min = 1` edge count printed below is the *unreduced*
  graph.

**What is deliberately not claimed.** The model does not settle which MB09
layer the 2016 Shomorony sentence denotes; it does not model the
supersource/supersink cost numerically (a single spelled molecule uses no
source/sink edge, so it is a first-tier object a fortiori); and it does not
claim global optimality outside the enumerated boxes.

---

## 2. The primary instance

```text
truth      S = AAATT        G = 5, L = 3, N = 5
reads      starts (0, 1, 4)
observed   x = { AAA:1, AAT:1, TAA:1 },  n = 3
truth      d_S = { AAA:1, AAT:2, TAA:2 }
competitor D   = AAAATT     |D| = 6
           d_D = { AAA:2, AAT:2, TAA:2 }
```

Graph at `o_min = 2`: 7 undirected bidirected edges
(`AAA`, `AAT`, `TAA` molecules; the audit-branch "10 edges" counts the four
orientation traversals separately). Transitive reduction removes none. At
`o_min = 1` the graph has 12 edges; the certificate is unchanged.

The truth's cyclic window walk is a valid bidirected circuit

```text
AAA --(+,−)-- AAT --(+,+)-- AAT --(−,+)-- TAA --(−,−)-- TAA --(+,−)-- AAA
```

with opposite orientations at every interior vertex. Summing endpoint
incidences under the §5.2 split gives `d_S`. The competitor `AAAATT` has the
analogous circuit with one extra `AAA` visit.

The only coordinate that changes is `AAA` (`1 → 2`) with `x_AAA = 1`, so

```text
L(D)/L(S) = [ (2/5)(3/5)^2 ] / [ (1/5)(4/5)^2 ] = 18/16 = 9/8 > 1.
```

[verified computation; the exact arithmetic is `fractions.Fraction`]

### 2.1 Bounded exhaustive flow check

Enumerating integral circulations on the 7-edge graph with balance `0` at each
read vertex, `d_w ≤ N = 5`, `f_e ≤ 5`, `Σ_e f_e ≤ 15` gives `10` distinct
throughput vectors. The maximum-likelihood one is `d_D`, so within this box the
truth is beaten by a first-tier (single-circuit-quality throughput) flow, not
merely by a spelled molecule:

```text
best d* = { AAA:2, AAT:2, TAA:2 },   L(d*)/L(d_S) = 9/8.
```

A separate enumeration of **single spelled competitors** `D` with `|D| ≤ 7`
confirms the same throughput as the best spelled object. [verified computation,
exhaustive in the stated box]

---

## 3. Tightly bounded neighbourhood search

Box (all exact and exhaustive inside it):

- `G ∈ {4,5,6}`, circular binary truths up to rotation;
- `L = 3`, `o_min = 2`, external `N = G`;
- read starts: distinct positions, `2 ≤ n ≤ 4` (`I_s` strict bridging used);
- competitor: a single spelled molecule `D` with `|D| ≤ N+2`, every `L`-window
  an observed read type, support exactly the observed support, through the
  bidirected reduced graph, `d_w ≤ N`.

Results: `16` distinct `(truth, starts, competitor-throughput)` hits. The
strongest:

| truth `S` | starts | competitor `d_D` | `L(D)/L(S)` |
|---|---|---|---|
| `AATAT` | (0,2,4) | `{AAT:2, ATA:2, TAA:2}` | `243/128` |
| `ATATT` | (0,2,3) | `{AAT:2, ATA:2, TAA:2}` | `243/128` |
| `AAATAT` | (0,1,3,5) | `{AAA:2, AAT:2, ATA:2, TAA:2}` | `268435456/158203125` |
| `AAATT` | (0,1,4) | `{AAA:2, AAT:2, TAA:2}` | `9/8` |

The full list (including the `4/3` and `125/81` families) is printed by the
script. This is evidence that the phenomenon is not a knife-edge artefact of a
single instance; it is **not** a completeness claim beyond the box.

---

## 4. Relation to existing artifacts

| Artifact | This note's relation |
|---|---|
| [`docs/section62-bidirected-lowerbound1-determination.md`](section62-bidirected-lowerbound1-determination.md) | independent reproduction of its finite witness at the exact graph/flow level; its `9/8` and `d_S`/`d_D` are confirmed |
| `analysis/branch:section62-mb09-bidirected-graph-audit.md` | independent re-derivation with a separate implementation; agrees on the exposed edges, the two circuits, and `9/8` |
| [`docs/bridging-source-semantics.md`](bridging-source-semantics.md) | the strict bridging predicate reused for `I_s` |
| `Feasible` / `SeqSupportLB` Lean predicate | not used here; this note models the flow object instead |

---

## 5. Epistemic summary

| Claim | Status |
|---|---|
| Graph/flow model faithfully follows MB09 §3.1–3.4, §5.2, §6.1–6.2 | **source fact + modeling choice** (§1) |
| `AAATT → AAAATT` is a valid §6.2 pair with ratio `9/8` at `o_min ∈ {1,2}` | **verified computation** |
| Best circulation in the box `d_w ≤ 5, f_e ≤ 5, Σf ≤ 15` is `d_D` | **verified computation**, exhaustive in box |
| `16` neighbourhood hits for `G ≤ 6`, `n ≤ 4`, `|D| ≤ N+2` | **verified computation**, exhaustive in box |
| Global optimality / unbounded neighbourhood | **open** |
| Which MB09 layer the 2016 sentence denotes | **open** (unchanged) |

The task's guard applies: agreement with the merged determination is evidence,
not a new proof; no computation here is promoted to a theorem.

---

## 6. Reproduce

```sh
python3 scripts/independent_se62_bidirected_model.py
```

The script builds the graph, checks the transitive reduction, verifies both
bidirected walks and the walk condition, computes the exact ratio, enumerates
the bounded flow box, and runs the neighbourhood search. It exits non-zero on
any failed assertion.

Primary sources: Medvedev & Brudno (2009), §3.1–3.4, §5.2, §6.1–6.2,
[PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/);
Shomorony, Kim, Courtade & Tse (2016), Eq. (1);
Bresler, Bresler & Tse (2013).
