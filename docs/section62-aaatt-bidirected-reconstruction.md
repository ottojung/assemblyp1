# Independent MB09 §6.2 bidirected reconstruction of the PR #39 witness `AAATT → AAAATT`

_Status: independent primary-source reconstruction + explicit graph/flow
certificate, 2026-09-20. This note rebuilds the Medvedev–Brudno (2009) §6.2
transitively reduced bidirected overlap graph for the observed read vertices
`{AAA, AAT, TAA}` directly from the primary definitions, and decides whether the
PR #39 truth `AAATT` and competitor `AAAATT` induce admissible §6.2 flows and
whether the `9/8` comparison survives. It does **not** use the branch
`Feasible` / `SeqSupportLB` predicate, and it does not depend on any other
agent's packet._

_Reproduction:_ `python3 scripts/verify_se62_aaatt_bidirected_reconstruction.py`
(exact `fractions.Fraction`, deterministic, exits non-zero on any failed
assertion).

_Stacked on_ the PR #39 line (`analysis/bridging-se62-ml-lean-0920`); it concerns
only that witness's graph/flow layer.

All claims are labelled **source fact**, **mathematical proof**,
**verified computation**, or **open**.

---

## 0. Verdict

1. **Both molecules induce admissible §6.2 flows.** On the transitively reduced
   bidirected overlap graph with observed vertices `{AAA, AAT, TAA}` and
   `o_min = L−1 = 2`, the cyclic window walks of `AAATT` and `AAAATT` are valid
   bidirected circuits: every step is a genuine §3.3 bidirected overlap,
   consecutive edges have opposite orientations at every interior vertex, every
   read vertex has flow `≥ 1`, every edge lower bound `0` holds, every
   read-vertex balance is `0`, and no supersource/supersink edge is used. The
   induced vertex throughputs are `d_S = {AAA:1, AAT:2, TAA:2}` and
   `d_D = {AAA:2, AAT:2, TAA:2}`. [mathematical proof + verified computation]

2. **The `9/8` comparison survives.** The §6.1 separable product-of-binomial
   marginals with external `N = 5`, `n = 3`, observed `x = {AAA:1, AAT:1,
   TAA:1}` gives `L_{6.1}(D)/L_{6.1}(S) = (2/5)(3/5)^2 / ((1/5)(4/5)^2) = 9/8 > 1`.
   [mathematical proof + verified computation]

3. **PR #39's prose `d_S` table is wrong** (`{AAA:2, AAT:2, TAA:1}` in its §0 and
   §3.2); the source-faithful occurrence counts are `{AAA:1, AAT:2, TAA:2}`.
   The PR's Lean module and Python script already compute the correct values, so
   only the prose is affected. [verified computation]

**Bottom line.** Under the MB09 molecule reading (reads are reverse-complement
classes, each represented once; per-read-vertex lower bound `1`; objective the
§6.1 separable binomial with external `N`), the PR #39 witness is
source-faithful at the graph/flow level and the strict `9/8` inequality holds.

---

## 1. Primary-source definitions used

Primary source: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116,
[PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/), re-read
2026-09-20.

**§3.1 (molecules).** A *DNA molecule* is an unordered pair of reverse-complement
strands. A *k-molecule* has corresponding strings of length `k`; it is
represented **once**. On the binary alphabet used here the involution is
`A ↔ T`. [source fact]

**§3.2 (bidirected graphs).** Each edge carries a positive/negative incidence at
each endpoint. For a link, `I(x,e) = +1` if `e` is positive-incident to `x` and
`−1` if negative-incident. For a loop at `x`, `I(x,e) = +2` if twice
positive-incident, `−2` if twice negative-incident, and `0` otherwise. A
`(x₁,x_k)`-walk is a sequence `e₁,…,e_{k−1}` where `e_i` is incident to `x_i`
and `x_{i+1}`, and for all interior `i`, `e_{i−1}` and `e_i` have **opposite
orientations** at `x_i`. A walk is cyclical when its endpoints coincide and
`e₁`, `e_{k−1}` have opposite orientations at `x₁`. [source fact]

**§3.3 (bidirected overlaps).** For molecules `x, y` (possibly identical) with
strands `p(x), n(x)` and `p(y), n(y)`, an edge `e` is a bidirected overlap iff
one of:

| case | incidence at `x` | incidence at `y` | strand condition |
|---|---|---|---|
| 1 | `+` | `−` | `p(x)` overlaps `p(y)` |
| 2 | `+` | `+` | `p(x)` overlaps `n(y)` |
| 3 | `−` | `−` | `n(x)` overlaps `p(y)` |
| 4 | `−` | `+` | `n(x)` overlaps `n(y)` |

The *length* of the overlap is the length of the underlying string overlap.
[source fact]

**§3.4 (flow).** A flow satisfies `l(e) ≤ f(e) ≤ u(e)` and, at every vertex,
`Σ_e I(v,e) f(e) = b(v)`. [source fact]

**§6.2 (the graph and bounds).** "The vertices of this graph are the reads, and
the edges are **all possible bidirected overlaps of length at least** `o_min` …
we then perform **transitive edge reduction**, where we remove any overlap that
is spelled by two shorter overlaps … the transitively reduced bidirected overlap
graph." A supersource/supersink is added; "each vertex has a **lower bound of
1** … All other lower bounds are 0 and all upper bounds are infinity"; the
supersource/sink edges get prohibitively large costs. [source fact]

**Observation 7.** The number of times a walk `W` visits a read `r` equals the
number of times `r` appears as a submolecule of the molecule spelled by `W`.
[source fact]

**§6.1 (objective).** `d_i` is the number of occurrences of type `i`; the
multinomial is approximated by a product of per-type binomials
`∏_i (d_i/N)^{x_i}(1 − d_i/N)^{n − x_i}`, with `N` the **external** true genome
length (`N(D)` replaced by `N`). [source fact]

---

## 2. The instance

Alphabet `{A,T}` (`A↦0`, `T↦1`), read length `L = 3`, external `N = 5`.
Truth `S = AAATT` (length `5`), observed starts `(0,1,4)`, so `n = 3`.
Competitor `D = AAAATT` (length `6`).

Cyclic length-3 windows, as molecule classes (`min(strand, rc(strand))`):

| start | `S` window | class | | start | `D` window | class |
|---|---|---|---|---|---|---|
| 0 | `AAA` | `AAA` | | 0 | `AAA` | `AAA` |
| 1 | `AAT` | `AAT` | | 1 | `AAA` | `AAA` |
| 2 | `ATT` | `AAT` | | 2 | `AAT` | `AAT` |
| 3 | `TTA` | `TAA` | | 3 | `ATT` | `AAT` |
| 4 | `TAA` | `TAA` | | 4 | `TTA` | `TAA` |
|   |       |       | | 5 | `TAA` | `TAA` |

Hence

```text
observed reads     x   = { AAA:1, AAT:1, TAA:1 }
truth spectrum     d_S = { AAA:1, AAT:2, TAA:2 }
competitor spectrum d_D = { AAA:2, AAT:2, TAA:2 }
```

[verified computation]

The observed read molecules are exactly the three vertices
`{AAA, AAT, TAA}`. (The fourth binary length-3 molecule class is `ATA`; it does
not occur in `S` or `D`.)

---

## 3. The bidirected overlap graph

Take `o_min = L−1 = 2` (the strictest threshold; the source's own experiments use
`o_min < L−1`, and the witness is robust to that — see §4). The edges are all
bidirected overlaps of length `2`. With `p`/`n` the positive/negative strands
(`AAA/TTT`, `AAT/ATT`, `TAA/TTA`), there are exactly **10** edges:

```text
  x     y    len  case (I_x,I_y)   strands
 AAA   AAA    2   p/p  (+,-)       AAA / AAA
 AAA   AAA    2   n/n  (-,+)       TTT / TTT
 AAA   AAT    2   p/p  (+,-)       AAA / AAT
 AAA   TAA    2   n/n  (-,+)       TTT / TTA
 AAT   AAA    2   n/n  (-,+)       ATT / TTT
 AAT   AAT    2   p/n  (+,+)       AAT / ATT     (twice-positive loop)
 AAT   TAA    2   n/n  (-,+)       ATT / TTA
 TAA   AAA    2   p/p  (+,-)       TAA / AAA
 TAA   AAT    2   p/p  (+,-)       TAA / AAT
 TAA   TAA    2   n/p  (-,-)       TTA / TAA     (twice-negative loop)
```

Each row is one of the four §3.3 cases: `(sx,sy)=(p,p)` gives `(+,-)`,
`(p,n)` gives `(+,+)`, `(n,p)` gives `(−,−)`, `(n,n)` gives `(−,+)`. The two
same-vertex rows `AAT–AAT` and `TAA–TAA` are **loops** with incidences `+2` and
`−2` respectively (the two ends have the same sign); the two `AAA–AAA` rows are
loops with incidence `0` (one positive, one negative end). The graph is a
multigraph, as §3.2 permits. [verified computation]

---

## 4. Transitive reduction

§6.2 removes any overlap that is **spelled by two shorter overlaps**. For an
`x`–`y` overlap of length `l` realized by strands `(sx,sy)`, an intermediate
molecule `z` with strand `sz` spells it when `sx` overlaps `sz` in `l₁`, `sz`
overlaps `sy` in `l₂`, both `l₁,l₂ ∈ [o_min, l)`, and the composed outer overlap
is `l₁ + l₂ − L = l`.

- At `o_min = 2`, every edge has `l = 2`; a spelling pair would need
  `l₁, l₂ ≥ 2` and `l₁, l₂ < 2` simultaneously. None exists.
- At `o_min = 1`, the graph gains the length-1 overlaps (28 edges in total),
  but `l₁ + l₂ − L = 1 + 1 − 3 = −1 ≠ 2`, so still no length-2 edge is
  removable.

Therefore the transitive reduction removes **none** of the edges employed by the
two witness walks, at either threshold. [mathematical proof + verified
computation]

---

## 5. The two circuits

### 5.1 Truth `S = AAATT`

Visit order (molecule classes) `AAA, AAT, AAT, TAA, TAA` and the edge sequence

```text
AAA --(p/p)--> AAT --(p/n)--> AAT --(n/n)--> TAA --(n/p)--> TAA --(p/p)--> AAA
```

At each interior visit the arriving incidence and the departing incidence are
opposite (e.g. at the first `AAT` the arriving `(p/p)` end has `I = −1` and the
departing `(p/n)` end has `I = +1`). The walk is closed; by Observation 7 its
throughput is

```text
d_S = { AAA:1, AAT:2, TAA:2 },  each ≥ 1.
```

### 5.2 Competitor `D = AAAATT`

Visit order `AAA, AAA, AAT, AAT, TAA, TAA` and

```text
AAA --(p/p)--> AAA --(p/p)--> AAT --(p/n)--> AAT --(n/n)--> TAA --(n/p)--> TAA --(p/p)--> AAA
```

with opposite incidences at every interior visit and

```text
d_D = { AAA:2, AAT:2, TAA:2 },  each ≥ 1.
```

Both walks use only length-`(L−1)` overlap edges, all present in the reduced
graph. [mathematical proof + verified computation]

---

## 6. Flow admissibility

For each walk, let `f(e)` be the number of traversals of edge `e` (here `0` or
`1`), and let the vertex throughput be the visit count.

| condition | truth `AAATT` | competitor `AAAATT` |
|---|---|---|
| every step is a §3.3 bidirected edge | yes | yes |
| opposite orientations at each interior vertex | yes | yes |
| edge lower bounds `l(e)=0 ≤ f(e)` | yes | yes |
| vertex lower bounds `f(v) = d_v ≥ 1` | yes | yes |
| read-vertex balance `b(v)=0` | yes | yes |
| supersource/supersink usage | `0` | `0` |

Balance is computed from the incidence matrix: each traversal of an edge
contributes `I(v,e)` at each endpoint (a loop contributes its two end signs at
the same vertex, giving `±2` or `0` as §3.2 requires). A valid closed bidirected
walk is balanced because the two incidences at every visit cancel, so both
molecules are integral circulations and hence admissible §6.2 flows. [mathematical
proof + verified computation]

---

## 7. The §6.1 objective and the `9/8` ratio

With external `N = 5`, `n = 3`, and observed `x = {AAA:1, AAT:1, TAA:1}`, the
only coordinate that differs between `S` and `D` is `AAA` (`d_S = 1` vs
`d_D = 2`); `AAT` and `TAA` have equal throughput, and the class `ATA` has
`d = 0` in both (factor `1`). Hence

```text
L_{6.1}(D)/L_{6.1}(S)
  = [ (2/5)^1 (3/5)^2 ] / [ (1/5)^1 (4/5)^2 ]
  = (18/25) / (16/25)
  = 9/8 > 1.
```

So the competitor strictly wins, and the `9/8` comparison **survives** the exact
§6.2 graph/flow reconstruction. [mathematical proof + verified computation]

---

## 8. Source-fidelity boundaries and unresolved points

These are the points at which the conclusion depends on a reading; none of them
is resolved by this note.

1. **Read-type space (`4^k` vs molecule classes).** §6.1 literally writes "there
   are `4^k` such variables" for outcomes that it elsewhere calls `k`-molecules.
   The reconstruction above uses reverse-complement classes (`AAT = ATT`,
   `TAA = TTA`), which is the §3.1/§4.1 model vocabulary; under the literal
   oriented `4^k` reading the truth's windows `ATT`, `TTA` would be distinct
   unobserved types and the instance changes. This is a source-internal tension.
   [source fact / open]
2. **Multigraph vs maximal overlaps.** The reconstruction follows §6.2's "all
   possible bidirected overlaps of length at least `o_min`" and admits one edge
   per (strand pair, overlap length). A reading that keeps only maximal overlaps
   would change which edges exist, but the witness uses the length-`(L−1)`
   overlaps, which are present under either the "all lengths" reading and (for
   the non-self pairs) the maximal reading; the only difference is the
   `AAA–AAA` self-overlap, where a full length-3 overlap also exists. This is a
   modeling choice. [source fact / modeling]
3. **`o_min`.** §6.2 makes `o_min` a parameter; the source's own experiments use
   `o_min < L−1`. The witness is certified at `o_min = 2` and the employed edges
   survive the reduction at `o_min = 1`; it does not depend on `o_min > 1`.
   [source fact + verified computation]
4. **Per-vertex vs per-occurrence lower bound.** The literal §6.2 lower bound is
   per read vertex (`d_v ≥ 1`); the stronger per-occurrence reading
   (`d_v ≥ x_v`) also happens to hold here. [source fact]
5. **Candidate length.** §6.2 does not constrain the candidate-flow length, so
   `|D| = 6 ≠ N = 5` is admissible; adding a fixed-length restriction `|D| = N`
   would exclude this competitor. [source fact / modeling]
6. **`I_s`.** This note reconstructs only the graph/flow layer and the §6.1
   comparison; it does not re-derive the bridging predicate `I_s` of PR #39.
   [scope]
7. **PR #39 prose.** The PR's §0/§3.2 `d_S` table prints `{AAA:2, AAT:2,
   TAA:1}`; the correct counts are `{AAA:1, AAT:2, TAA:2}`. The PR's Lean and
   Python certificates are correct. [verified computation]

---

## 9. Epistemic summary

| Claim | Status |
|---|---|
| §3.1–3.4, §6.1–6.2 definitions (molecules, incidence, walk, balance, bounds, objective, Observation 7) | **source fact** |
| 10-edge bidirected overlap graph on `{AAA,AAT,TAA}` at `o_min=2`, with the stated incidences | **verified computation** |
| No employed edge is removed by the transitive reduction (`o_min ∈ {1,2}`) | **mathematical proof + verified computation** |
| `AAATT` and `AAAATT` are valid bidirected circuits with `d_S`, `d_D` as stated | **mathematical proof + verified computation** |
| Both induced flows are admissible (vertex LB 1, edge LB 0, balance 0, no supersource/sink) | **mathematical proof + verified computation** |
| `L_{6.1}(D)/L_{6.1}(S) = 9/8 > 1` with `N=5, n=3` | **mathematical proof + verified computation** |
| PR #39 prose `d_S` is a table error | **verified computation** |
| Read-type space, maximality, `o_min`, length restriction, `I_s` re-derivation | **open / out of scope** |

---

## 10. Reproduce

```sh
python3 scripts/verify_se62_aaatt_bidirected_reconstruction.py
```

The script builds the graph from the §3.3 four-case definition, performs the
§6.2 transitive reduction, checks both walks against the §3.2 orientation rule
and the §3.4 balance rule (loop-aware), computes the throughputs, and evaluates
the §6.1 ratio in exact rational arithmetic; it exits non-zero on any failure.
