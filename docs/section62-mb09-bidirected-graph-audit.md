# Audit of the PR #39 / §6.2 witness `AAATT → AAAATT` against the exact Medvedev–Brudno (2009) §6.2 construction

_Status: independent primary-source reconstruction + explicit graph construction +
verified computation, 2026-09-20. This note reads PR #39
(`analysis/bridging-se62-ml-lean-0920`) adversarially against MB09 §6.2. It
does not assume that support equality or `x ≤ d` is §6.2 feasibility; it builds
the bidirected graph, applies the transitive reduction, and exhibits the flows.
All claims are labelled **source fact**, **mathematical proof**,
**verified computation**, or **open**._

_Reproduction:_ `python3 scripts/verify_se62_mb09_bidirected_graph.py` (exact
`fractions.Fraction`, deterministic, exits non-zero on any failed assertion).

_Stacked on_ PR #39's branch; it concerns only that branch's witness and claims.

---

## 0. Verdict at a glance

1. **The witness survives the exact §6.2 graph/flow check.** For the observed
   read molecules `{AAA, AAT, TAA}`, the truth `AAATT` and the competitor
   `AAAATT` each induce a genuine **bidirected circuit** in the transitively
   reduced read-overlap graph: every step is a real bidirected overlap edge of
   length `L−1 = 2`, consecutive edges have opposite orientations at each
   interior vertex, every read vertex has flow `≥ 1`, all edge lower bounds `0`
   hold, every read vertex is balanced (`b(v) = 0`), and **no
   supersource/supersink edge is used**. Their vertex throughputs are
   `d_S = {AAA:1, AAT:2, TAA:2}` and `d_D = {AAA:2, AAT:2, TAA:2}`, and the
   §6.1 separable binomial ratio is `9/8 > 1`. [mathematical proof +
   verified computation]

2. **The PR #39 prose contains a table error.** §0 and §3 print the truth
   spectrum as `d_S = {AAA:2, AAT:2, TAA:1}`; the start-3 window of `AAATT` is
   `TTA` (molecule class `TAA`), not `TTT`. The correct occurrence counts are
   `{AAA:1, AAT:2, TAA:2}` — the values the Lean module and the companion Python
   script already compute and kernel-check. The ratio is unchanged, so the
   witness is unaffected. [verified computation]

3. **The PR #39 "sequence-level §6.2 feasibility" criterion is not the source
   definition.** MB09 §6.2 feasibility is a *bidirected flow* condition on the
   *transitively reduced bidirected overlap graph* (vertex lower bound `1`,
   edge lower bounds `0`, signed-incidence balance, supersource/sink); support
   equality and `x ≤ d` are neither necessary nor the definition. They are a
   stronger finite certificate that happens to hold for this instance. The
   branch should present the graph/flow certificate (this note) and label the
   support/lower-bound predicate accordingly. [source fact; §1, §5]

4. **Transitive reduction does not remove any employed edge.** With read length
   `L = 3`, every edge employed by the two witness walks has the maximal proper
   overlap `L−1 = 2`; a `2`-overlap cannot be spelled by two strictly shorter
   overlaps, nor lie on a two-step path of strictly longer proper overlaps.
   Hence the reduction is vacuous on the employed subgraph under either reading
   of "transitive reduction". [mathematical proof; §3]

**Bottom line.** The witness is source-faithful at the level PR #39 claims; the
defects are in the prose (a wrong `d_S` row) and in the *scope label* of the
feasibility criterion. Both are corrected here and in the branch artifacts.

---

## 1. The exact §6.2 construction (source facts)

Primary source: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116, §3.1–3.4, §5.2, §6.1–6.2,
[PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/).

§6.2, verbatim (as read from PMC3154397 on 2026-09-20):

> "The first step is to build a bidirected overlap graph from the set of reads,
> which are DNA molecules. **The vertices of this graph are the reads**, and the
> edges are all possible bidirected overlaps of length at least `o_min` … We then
> perform **transitive edge reduction**, where we remove any overlap that is
> spelled by two shorter overlaps … the resulting graph [is] the **transitively
> reduced bidirected overlap graph**." — **Observation 7**: "The number of times
> `W` visits `r` is equal to the number of times `r` appears a submolecule of the
> molecule spelled by `W`."

> "In this graph, the original double-stranded genome corresponds to a circuit …
> We make a final change to the graph by adding a **supersource and supersink**
> … **Each vertex has a lower bound of 1** since it represents a read that must be
> present in the genome at least once. **All other lower bounds are 0 and all
> upper bounds are infinity.** We add **prohibitively large costs** to the edges
> from/to the supersource/sink so that their usage is minimized."

Supporting source facts: a **DNA molecule** is an unordered reverse-complement
strand pair (§3.1); a **bidirected edge** carries a positive/negative incidence
at each endpoint and exists when one of four strand-overlap cases holds, its
length being the underlying string-overlap length (§3.3); a flow satisfies the
signed-incidence balance `pos(f)(v) − neg(f)(v) = b(v)` (§3.4); the vertex split
`v⁻→v⁺` carries the vertex bounds and cost, so `d_i` is the flow through vertex
`i` (§5.2). [source fact]

**Feasibility of a throughput vector `d` (what replaces the PR #39 criterion).**
An integral bidirected flow `f` on the transitively reduced graph with the
supersource/sink reduction is *admissible with throughputs `d`* when:

1. `l(e) ≤ f(e) ≤ u(e)` on every edge, with `l ≡ 0` on overlap edges and
   `u ≡ ∞`;
2. the signed-incidence balance holds at every read vertex (the source/sink
   edges absorb any residual, at prohibitive cost);
3. the flow through each read vertex `i` is `d_i`, and `d_i ≥ 1` for every read
   vertex (the vertex lower bound).

A closed walk (circuit) is a special admissible flow with all read-vertex
balances `0` and zero supersource/sink usage. [source fact]

---

## 2. The explicit graph on `{AAA, AAT, TAA}`

Alphabet `{A, T}` (`A ↦ 0`, `T ↦ 1`); involution `T = rc(A)`. Label each
observed molecule by `p =` its class representative and `n = rc(p)`:

| molecule | `p` | `n` |
|---|---|---|
| `AAA` | `AAA` | `TTT` |
| `AAT` | `AAT` | `ATT` |
| `TAA` | `TAA` | `TTA` |

Taking `o_min = 2 = L−1` (the source's own experiments use `o_min < L−1`; `L=3`
gives only the values `o_min ∈ {1,2}`), the graph has **10 bidirected edges**.
Each row is one strand overlap; `sign(x)`/`sign(y)` are the incidences per
§3.3. Every edge has overlap length `2`.

```text
AAA -[p/p len 2]-> AAA   sign(+1, -1)
AAA -[n/n len 2]-> AAA   sign(-1, +1)
AAA -[p/p len 2]-> AAT   sign(+1, -1)
AAA -[n/n len 2]-> TAA   sign(-1, +1)
AAT -[n/n len 2]-> AAA   sign(-1, +1)
AAT -[p/n len 2]-> AAT   sign(+1, +1)     (twice-positive loop)
AAT -[n/n len 2]-> TAA   sign(-1, +1)
TAA -[p/p len 2]-> AAA   sign(+1, -1)
TAA -[p/p len 2]-> AAT   sign(+1, -1)
TAA -[n/p len 2]-> TAA   sign(-1, -1)     (twice-negative loop)
```

At `o_min = 1` the graph additionally contains the length-`1` overlaps; none is
needed by the witness. [verified computation]

### 2.1 Transitive reduction (checked)

**Claim.** No edge employed by either witness walk is removed by the transitive
reduction. [mathematical proof]

*Proof.* Every employed edge has overlap `2 = L−1`.

- *Literal reading* ("remove any overlap that is spelled by two shorter
  overlaps"). Two shorter overlaps are both length `1`. Placing the three reads
  with two length-`1` overlaps composes the outer reads at an offset
  `1 + 1 = 2`, i.e. an *implied* outer overlap of `1+1−L = −1 < 0`; it cannot
  spell a length-`2` overlap. More generally a length-`l` outer overlap spelled
  by lengths `l₁,l₂` satisfies `l = l₁ + l₂ − L`, so `l₁,l₂ < l` forces
  `l > L/2`, impossible for `l ≤ L−1` with the smaller lengths. The brute-force
  check over all middle reads confirms zero reducible edges. [verified
  computation]
- *Myers reading* (remove the outer overlap when a two-step path of strictly
  longer proper overlaps through a distinct read exists). Longer proper overlaps
  would need length `> 2`, but the maximal proper overlap is `L−1 = 2`. The
  only `3`-overlaps are full self-overlaps, which are not proper overlap edges
  and are excluded. The check again returns zero. [verified computation]

Hence the transitively reduced graph contains all edges the witnesses use. ∎

---

## 3. The two admissible circuits

### 3.1 Truth `S = AAATT` (`G = 5`)

Its cyclic length-`3` windows, as *strands*, are
`AAA, AAT, ATT, TTA, TAA`; their molecule classes are
`AAA, AAT, AAT, TAA, TAA`. The strand walk is a valid single-strand overlap
walk, and it lifts to the bidirected circuit

```text
AAA --(p/p, len2)-- AAT --(p/n, len2)-- AAT --(n/n, len2)--
TAA --(n/p, len2)-- TAA --(p/p, len2)-- AAA
```

where each `--(...)--` is a bidirected edge of §2 traversed with the stated
incidence. At every interior visit the arriving incidence and the departing
incidence are opposite (e.g. at the first `AAT` visit the incoming edge has
`sign(y) = −1` and the loop has `sign(x) = +1`). The walk is closed, so all
read-vertex balances are `0`; it carries flow `1` on each traversed edge (edge
lower bounds `0` hold), uses **no** supersource/supersink edge, and its vertex
throughputs by Observation 7 are

```text
d_S = { AAA:1, AAT:2, TAA:2 },   each ≥ 1.
```

[mathematical proof + verified computation]

### 3.2 Competitor `D = AAAATT` (`G = 6`)

Windows (strands) `AAA, AAA, AAT, ATT, TTA, TAA`; molecule classes
`AAA, AAA, AAT, AAT, TAA, TAA`. The bidirected circuit is

```text
AAA --(p/p, len2)-- AAA --(p/p, len2)-- AAT --(p/n, len2)--
AAT --(n/n, len2)-- TAA --(n/p, len2)-- TAA --(p/p, len2)-- AAA
```

with opposite incidences at every interior vertex, throughputs

```text
d_D = { AAA:2, AAT:2, TAA:2 },   each ≥ 1,
```

zero supersource/sink usage and zero read-vertex balance.
[mathematical proof + verified computation]

### 3.3 The §6.1 objective

The §6.1 separable binomial with external `N = 5`, `n = 3` (all observed
`x_w = 1`) gives

```text
L(D)/L(S)
  = [ (2/5)(3/5)² / ((1/5)(4/5)²) ] · 1 · 1
  = (18/25) / (16/25) = 9/8 > 1.
```

The only coordinate that changes is `AAA` (`1 → 2`); `d_S = d_D` on `AAT` and
`TAA`; both spectra have support exactly `supp(x)`, so every other factor is
`1` in both. [mathematical proof + verified computation]

---

## 4. The `d_S` prose error

`S = AAATT` has cyclic windows `AAA, AAT, ATT, TTA, TAA`. Start `3` reads
`S[3]S[4]S[0] = T T A = TTA`, whose reverse complement is `TAA`; it is **not**
`TTT`. PR #39's §0 and §3 table print `TTT` at start `3` and consequently
report `d_S = {AAA:2, AAT:2, TAA:1}`. The correct counts are
`{AAA:1, AAT:2, TAA:2}`. The Lean module
`AssemblyP1/Section62BridgingCounterexample.lean` already proves
`dS 0 = 1`, `dS 1 = 2`, `dS 4 = 2`, and the companion Python script computes
the same values, so the *certificates* were right and only the prose was wrong.
[verified computation]

---

## 5. What is and is not established

| Claim | Status |
|---|---|
| §6.2 vertices = read DNA molecules; edges = bidirected overlaps `≥ o_min`; transitive reduction; vertex LB `1`, edge LB `0`, `u = ∞`; supersource/sink with large cost; `d_i` = vertex flow | **source fact** (MB09 §3.3–3.4, §5.2, §6.2) |
| The 10-edge graph on `{AAA, AAT, TAA}` at `o_min = 2` and the two explicit circuits | **mathematical proof + verified computation** |
| Transitively-reduced graph retains every employed edge (both reduction readings) | **mathematical proof + verified computation** |
| `d_S = {AAA:1, AAT:2, TAA:2}`, `d_D = {AAA:2, AAT:2, TAA:2}` are admissible §6.2 flows (LB1, LB0, balance 0, no source/sink) | **mathematical proof + verified computation** |
| `L_{6.1}(D)/L_{6.1}(S) = 9/8 > 1` | **mathematical proof + verified computation** |
| PR #39 criterion "support equality ∧ `x ≤ d`" is §6.2 feasibility | **false as a source definition**; it is a stricter sufficient certificate for this instance and is exact only at `o_min = L−1` with a per-occurrence lower-bound reading |
| The witness decides the §6.2-restricted implication negatively | follows for the single-molecule sub-case: a spelled bidirected circuit is an admissible flow |
| Which MB09 layer the 2016 sentence denotes; single-strand / fixed-length sub-cases; whether a non-spellable flow is needed | **open** |

---

## 6. Note on the remaining scope

The graph certificate here does **not** claim anything about genuinely
non-spellable §6.2 flows, nor about the single-strand reading. It only places the
existing PR #39 witness on the exact source object, which it survives. The
fixed-length sub-case (`|D| = N`) is treated separately and is **refuted** under
the source per-vertex reading by a same-length spelled witness
(`S = AAATAT`, `D = AAAAAT`); see
[`section62-same-length-bidirected-counterexample.md`](section62-same-length-bidirected-counterexample.md). The structural mechanism
(separability of the §6.1 objective versus the support/bridging nature of
`I_s`) remains the reason the witness works, and it is independent of the
graph bookkeeping.

---

## 7. Epistemic summary

- The PR #39 *computation* and *Lean kernel check* of the sequence-level
  certificate and ratio are correct.
- The PR #39 *prose* misstates `d_S` and overstates the sequence-level
  predicate as "§6.2 feasibility"; both are corrected on this branch.
- The witness is valid at the exact §6.2 graph/flow level; the certificate for
  that is `scripts/verify_se62_mb09_bidirected_graph.py` and §2–§3 of this note.
