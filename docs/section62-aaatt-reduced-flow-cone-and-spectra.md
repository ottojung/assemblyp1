# The §6.2 copy-count cone for the `AAATT` reads `{AAA, AAT, TAA}`: transitive reduction forces `AAT = TAA`, so the spectrum `(2,2,1)` is not a closed §6.2 flow

_Status: independent primary-source reading + hand graph/flow derivation +
exact computation, 2026-09-20. Independent of the branch summaries; it
adjudicates the copy-count spectra `2,2,1` and `2,2,2` directly from the
Medvedev–Brudno §6.2 object. All claims are labelled **source fact**,
**mathematical proof**, **modeling normalization**, **verified computation**,
or **open**._

_Reproduction:_ `python3 scripts/verify_se62_aaatt_flow_cone.py` (exact integer
arithmetic, deterministic, under a second, exits non-zero on any failed
assertion).

---

## 0. Verdict at a glance

Fix the Medvedev–Brudno §6.2 object: bidirected overlap graph on the observed
read **molecules**, overlaps of length `≥ o_min` and proper (`< L`),
transitively reduced as in Myers (2005), vertex lower bound `1`, edge lower
bound `0`, upper bounds `∞`, and a flow decomposed into walks. For the read set
`R = {AAA, AAT, TAA}` (`L = 3`, `o_min ∈ {1, 2}`, binary alphabet `A ↔ T`) the
transitively reduced graph is small enough to solve by hand.

**Result (mathematical proof + verified computation).** Every admissible
**closed** §6.2 flow has

```text
d_AAT = d_TAA        (in the ordering (AAA, AAT, TAA): b = c),
```

and consequently the feasible integer copy-count cone is exactly

```text
{ (a, k, k) : a ≥ 1, k ≥ 1 }         (with the §6.2 lower bound d_v ≥ 1).
```

Therefore:

| copy-count spectrum `(AAA, AAT, TAA)` | status as a closed §6.2 flow |
|---|---|
| `(1, 2, 2)` — the true `AAATT` | **feasible** (realized by the truth's window circuit) |
| `(2, 2, 2)` — the rival `AAAATT` | **feasible** (realized by its window circuit) |
| `(2, 2, 1)` | **not feasible** (it has `AAT ≠ TAA`) |

The `(2,2,1)` spectrum becomes feasible **only** under a weaker convention that
keeps the reducible length-1 overlap edges (see §5), or if open
source/sink paths — which are not circuits/genomes and carry the source's
prohibitive source/sink cost — are admitted. Neither is the primary-source
reading.

Two corrections follow for the current frontier:

1. The `AAATT` truth spectrum is `(1,2,2)`, **not** `(2,2,1)`. A branch artifact
   printed `(2,2,1)` by mislabelling the start-3 window `TTA` (`TAA` class) as
   `TTT` (`AAA` class). The `(2,2,1)` vector is not merely the wrong table entry;
   it is **not a feasible §6.2 flow at all**. [verified computation]
2. The finite Lean predicate `FeasibleType` (`d` has the observed support and
   `d_w ≥ 1` on observed vertices) is **strictly weaker** than §6.2 flow
   feasibility: it admits `(2,2,1)`. It is a legitimate support/lower-bound
   certificate, but it must not be quoted as "§6.2 feasibility".
   [mathematical proof]

---

## 1. Source facts

Primary source: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116, §3.1–3.4, §5.2, §6.1–6.2,
PMC3154397 (re-read 2026-09-20).

- **§3.1 (molecules).** "A DNA molecule is an unordered pair of strings … that
  are reverse complements of each other." Two reads that are reverse
  complements of the same sequence are **one** vertex. [source fact]
- **§3.3 (bidirected overlaps).** With positive/negative strands labelled, a
  bidirected edge between molecules `x, y` exists in one of four strand cases,
  and "the length of this bidirected overlap is the length of the underlying
  string overlap." [source fact]
- **§3.4 (flow).** A flow satisfies `l(e) ≤ f(e) ≤ u(e)` and, at every vertex,
  "the flow along the positive-incident edges minus the flow along the
  negative-incident edges is equal to `b(v)`". [source fact]
- **§6.2 (the graph).** "The vertices of this graph are the reads, and the edges
  are all possible bidirected overlaps of length at least `o_min` … We then
  perform transitive edge reduction, where we remove any overlap that is spelled
  by two shorter overlaps. **This procedure is identical to the one described in
  Myers (2005)**, and we refer to the resulting graph as the transitively
  reduced bidirected overlap graph." [source fact]
- **§6.2 (bounds and objective).** Each read vertex has lower bound `1`; all
  other lower bounds `0`; all upper bounds infinity; supersource/supersink edges
  carry prohibitively large cost. By Observation 7 the flow through vertex `i`
  is the number of occurrences of read `i` in the spelled molecules; the vertex
  cost is the §6.1 separable binomial with external known length `N`. [source
  fact]

**The one genuinely ambiguous phrase** is "spelled by two shorter overlaps."
Read literally it cannot reduce any edge of a length-`L` graph (a shorter
positive overlap of a length-1 overlap does not exist). MB09 immediately pins
the meaning to Myers (2005), whose transitive reduction removes an overlap that
is **implied by a two-step path through another read with longer proper
overlaps**. §5 analyses both readings; the Myers reading is the primary-source
supported one because the source names it, and the literal reading is retained
as a labelled alternative. [source fact + modeling normalization]

Finally, §6.2's flow is explicitly a "(non-contiguous) assembly", i.e. a
collection of walks, while "the original double-stranded genome corresponds to
a **circuit**." A **closed** flow (all balances zero, no source/sink usage) is
therefore the genome/circuit object; source/sink usage is permitted but
penalised. The main result is about closed flows. [source fact]

---

## 2. The graph on `{AAA, AAT, TAA}`, by hand

Write `A = 0`, `T = 1`, and `rc` for reverse complement. Fix the canonical
representatives

```text
AAA = 000   AAT = 001   TAA = 100
rc          TTT         ATT = 011        TTA = 110
```

Each molecule has two ports: port `0` is the 5' end of the canonical strand,
port `1` is the 5' end of its reverse complement. A read occurrence traversed
`0 → 1` uses the canonical strand, traversed `1 → 0` uses `rc`. Hence an overlap
from exit port `p` of `X` to entry port `q` of `Y` exists at length `ℓ` iff

```text
exitword(X,p,ℓ) = enterword(Y,q,ℓ),   where
  exitword(X,1,ℓ) = suffix_ℓ(w_X),   exitword(X,0,ℓ) = suffix_ℓ(rc(w_X)),
  enterword(Y,0,ℓ) = prefix_ℓ(w_Y),  enterword(Y,1,ℓ) = prefix_ℓ(rc(w_Y)).
```

Enumerating `ℓ = 2` gives the **10 directed port edges** (equivalently 6
undirected bidirected edges) that the `agent/exact-mb09-graph-audit` branch also
records:

```text
ℓ=2 undirected edges (port form):
  AAA.p0 -- AAA.p1        AAA.p1 -- AAT.p0
  AAA.p0 -- TAA.p1        AAT.p0 -- TAA.p1
  AAT.p1 -- AAT.p1  (loop)      TAA.p0 -- TAA.p0  (loop)
```

Enumerating `ℓ = 1` adds 18 directed port edges. [verified computation]

### 2.1 Transitive reduction

**Lemma 1 (which edges can be transitive).** Let `L` be the read length. If a
proper overlap of length `ℓ` (`1 ≤ ℓ ≤ L−1`) is spelled by a two-step path
`u → x → v` through a read `x` with proper overlaps `ℓ₁, ℓ₂`, then
`ℓ = ℓ₁ + ℓ₂ − L` and `ℓ₁, ℓ₂ > ℓ ≥ 1`. Hence `ℓ ≤ (L−1) + (L−1) − L = L−2`.
For `L = 3`, only `ℓ = 1` can be transitive; every length-2 edge survives.

_Proof._ Placing `u` at offset `0` and `x` at offset `L−ℓ₁` puts `v` at offset
`2L−ℓ₁−ℓ₂`; the `u`–`v` overlap is `L − (2L−ℓ₁−ℓ₂) = ℓ₁+ℓ₂−L`. The Myers
condition is `ℓ₁, ℓ₂ > ℓ`; with `ℓ₁,ℓ₂ ≤ L−1` this forces `ℓ ≤ L−2`. ∎
[mathematical proof]

For `ℓ = 1` the two path lengths are forced to `ℓ₁ = ℓ₂ = 2`, and the unique
candidate middle read is the offset-1 window of the spelled 5-mer `u·v` (with
`v` placed at offset `L−1 = 2`).

**Lemma 2 (the surviving length-1 edge).** Among the 18 length-1 directed port
edges, exactly the two directions of the undirected edge `AAT.p1 -- TAA.p0`
survive reduction. Both spell the 5-mers `AATAA` and `TTATT`, whose middle
windows `ATA` and `TAT` are **not** observed read molecules.

_Proof._ Direct enumeration of the offset-1 window of each length-1 edge's
spelled 5-mer (§2); a length-1 edge is reducible exactly when that window's
molecule class is one of `{AAA, AAT, TAA}`. The surviving edge and its spelled
words are as stated. ∎ [mathematical proof + verified computation]

Thus the **transitively reduced graph** on `{AAA, AAT, TAA}` is the 6
undirected length-2 edges of §2 **plus** the single undirected length-1 edge
`AAT.p1 -- TAA.p0`. (At `o_min = 2` the length-1 edges never exist, so the
reduced graph is the 6 length-2 edges alone; the conserved quantity below is the
same.) [mathematical proof + verified computation]

---

## 3. The conservation lemma

Write `d = (a, b, c) := (d_AAA, d_AAT, d_TAA)`. Use the directed flow variables
of §2 and impose the §3.4 balance `in = out` at every port (all vertex balances
`0` for a circuit). The reduced graph has:

```text
within AAA:        AAA.p1 → AAA.p0   and   AAA.p0 → AAA.p1
link AAA–AAT:      AAA.p1 → AAT.p0   and   AAT.p0 → AAA.p1
link AAA–TAA:      AAA.p0 → TAA.p1   and   TAA.p1 → AAA.p0
link AAT–TAA (ℓ2): AAT.p0 → TAA.p1   and   TAA.p1 → AAT.p0
loop AAT.p1:       AAT.p1 → AAT.p1
loop TAA.p0:       TAA.p0 → TAA.p0
link AAT–TAA (ℓ1): AAT.p1 → TAA.p0   and   TAA.p0 → AAT.p1
```

**Lemma 3 (conservation forces `b = c`).** Every admissible closed flow on the
reduced graph satisfies `d_AAT = d_TAA`, and `d_AAA` is otherwise free.

_Proof._ Port balance at `AAA`, `AAT`, `TAA` gives, with the self-loop flows
`ε` at `AAT.p1` and `ζ` at `TAA.p0` and the cross flows `β, γ, δ, λ` (§2
labels):

```text
at AAT:   β + δ' = ε + λ        and   ε + λ' = β' + δ
at TAA:   ζ + λ  = β + δ'       and   γ + δ   = ζ + λ'
at AAA:   β' = γ                and   γ' = β .
```

Adding the two throughputs,

```text
d_AAT = (β + δ') + (ε + λ')  =  (ε + λ) + ε + λ'  = 2ε + λ + λ' ,
d_TAA = (ζ + λ)  + (γ + δ)   =  (β + δ') + (ζ + λ') = 2ε + λ + λ' ,
```

where the last equality uses `ζ + λ = β + δ'` and `ζ + λ' = γ + δ`. Hence
`d_AAT = d_TAA` identically; `d_AAA = α + α' + β + γ` is unconstrained, and
`2ε + λ + λ'` ranges over all nonnegative integers. ∎
[mathematical proof]

**Corollary 3.1 (feasible cone).** With the §6.2 vertex lower bound `1` the
closed-flow copy-count cone is exactly `{(a,k,k) : a ≥ 1, k ≥ 1}`; without the
lower bound it is `{(a,k,k) : a, k ≥ 0}`. The generators are the tandem-`AAA`
loop `(1,0,0)` and the two-molecule circuit `AAT --(ℓ1)-- TAA --(ℓ2)-- AAT`
with vector `(0,1,1)`.

Equivalently: `(1,0,0)` is the closed walk `AAA → AAA` (the `AAA` self-loop),
and `(0,1,1)` is

```text
AAT --(AAT.p1→TAA.p0)-- TAA --(TAA.p1→AAT.p0)-- AAT .
```

[mathematical proof + verified computation]

**Remark (origin of the surviving odd counts).** Without the surviving length-1
edge, `d_AAT = d_TAA = 2ε` would be forced **even** (the two loops contribute in
pairs), so `(1,1,1)` and any odd common value would be infeasible. The single
long unobserved-middle edge `AAT -- TAA` is exactly what permits odd
`d_AAT = d_TAA`. It never permits `d_AAT ≠ d_TAA`. [mathematical proof]

---

## 4. Sequence-level check (single circular molecules)

The flow cone of §3 is confirmed by a second, independent argument on spelled
molecules. A circular binary molecule whose every length-3 window has a class
in `{AAA, AAT, TAA}` cannot contain `ATA` (`010`) or `TAT` (`101`), so no
maximal run of equal symbols has length `1`; every run has length `≥ 2`. If the
molecule has `2k` runs (`k ≥ 1`) of total length `G`, then

```text
d = (G − 4k, 2k, 2k),      and the homopolymer A^G gives (G, 0, 0).
```

In particular a single molecule **always** has `AAT = TAA`, so `(2,2,1)` is not
the spectrum of any supported molecule; `(1,2,2)` (e.g. `AAATT`, `G=5, k=1`) and
`(2,2,2)` (e.g. `AAAATT`, `G=6, k=1`) both are. [mathematical proof + verified
computation]

---

## 5. The convention split, and which reading the source supports

The adjudication of `(2,2,1)` is exactly a convention split. All three readings
are analysed explicitly.

- **Reading A (primary-source supported).** `o_min ∈ {1,2}` and Myers
  transitive reduction (MB09 cites Myers 2005 by name). The reduced graph is
  §2.1, Lemma 3 gives `b = c`, and `(2,2,1)` is **infeasible**.
  [mathematical proof]
- **Reading B (literal wording).** Take "remove any overlap that is spelled by
  two **shorter** overlaps" literally: a length-1 overlap cannot be spelled by
  two shorter positive overlaps, so no length-1 edge is removed. Then the cone
  gains `(1,1,2)`, `(2,1,2)`, `(2,2,1)`, … and `(2,2,1)` is **feasible**.
  This reading contradicts the sentence's own "identical to Myers (2005)"
  identification, because Myers reduction removes an edge implied by **longer**
  overlaps; it is retained only as a labelled alternative. [verified
  computation]
- **Reading C (open source/sink paths).** If the supersource/supersink
  modification is read as allowing arbitrary open paths (not just circuits),
  the path vectors include `(1,1,0)`, `(1,0,1)`, `(0,1,0)`, … and `(2,2,1)`
  becomes **feasible**, but only by using the source's prohibitively costly
  source/sink edges; the source says "the original double-stranded genome
  corresponds to a circuit", so this is not the genome object.
  [verified computation]

**Primary-source determination.** Reading A is the supported one: MB09 names the
Myers (2005) procedure, the geometric splitting condition (`ℓ₁, ℓ₂ > ℓ`) is the
one that composes to a spelled read in the middle, and §6.2's object is a
circuit. Under Reading A, `(2,2,1)` is not a feasible §6.2 flow, while
`(2,2,2)` is. The literal Reading B and the open-path Reading C must be quoted
with their labels if used. [source fact + modeling normalization]

### 5.1 Ordering caveat

The string "2,2,1" is order-dependent. In the read order `(AAA, AAT, TAA)` it is
infeasible. In the order `(AAT, TAA, AAA)` the same multiset is `(2,2,1)`, but
then its coordinates are `AAT = 2, TAA = 2, AAA = 1`, i.e. the truth `(1,2,2)`
reordered, which is feasible. Any statement about `2,2,1` must therefore fix
which coordinate is which. The invariant content is: **the two coordinates
`AAT` and `TAA` are equal in every feasible closed §6.2 flow; the `AAA`
coordinate is free.**

---

## 6. Relation to the existing artifacts

- `agent/exact-mb09-graph-audit` (`docs/section62-mb09-bidirected-graph-audit.md`,
  `scripts/verify_se62_mb09_bidirected_graph.py`) builds the 10-edge `o_min = 2`
  graph and exhibits the truth and rival circuits with throughputs `(1,2,2)` and
  `(2,2,2)`. Those circuits are correct and are the two feasible vectors used
  here. That note does **not** characterize the flow cone; it does not exclude
  `(2,2,1)`. This note supplies the missing conservation lemma. [agreement +
  extension]
- The earlier branch artifact (`docs/bridging-se62-flow-ml-counterexample.md`,
  corrected in commit `253aea1`) printed `d_S = (2,2,1)`; the corrected table
  `(1,2,2)` is the one consistent with the window enumeration and with Lemma 3.
  [verified computation]
- The Lean predicate `AssemblyP1/Section62LowerBoundOneCounterexample.FeasibleType`
  (`support equality ∧ d ≥ 1`) is **not** §6.2 flow feasibility: it admits
  `(2,2,1)`, which Lemma 3 forbids. The kernel-checked witness remains valid
  because the witness's `(1,2,2)` and `(2,2,2)` are themselves real circuits,
  but the predicate's name/scope should not be read as "admissible §6.2 flow".
  [mathematical proof]

---

## 7. Epistemic status

| Claim | Status |
|---|---|
| §6.2 vertices are read molecules; edges are bidirected overlaps `≥ o_min`; Myers transitive reduction; vertex LB `1`, edge LB `0`, UB `∞`; genome = circuit | **source fact** (MB09 §3.1, §3.3–3.4, §5.2, §6.2) |
| For `L=3`, only length-`1` overlaps can be transitive-reduced | **mathematical proof** (Lemma 1) |
| After reduction the graph is the 6 length-2 edges plus `AAT.p1 -- TAA.p0` | **mathematical proof + verified computation** (Lemma 2) |
| Every closed §6.2 flow has `d_AAT = d_TAA`; cone `= {(a,k,k)}` | **mathematical proof + verified computation** (Lemma 3) |
| `(1,2,2)` and `(2,2,2)` are feasible; `(2,2,1)` is not (Reading A) | **verified computation** |
| `(2,2,1)` is feasible under Reading B (literal wording) and Reading C (open paths) | **verified computation** |
| Myers reading A is primary-source supported; B/C must be labelled | **source fact + modeling normalization** |
| Single molecules have `AAT = TAA` (run structure) | **mathematical proof** |
| `FeasibleType` does not encode conservation and admits `(2,2,1)` | **mathematical proof** |
| Whether the 2016 Shomorony sentence denotes this §6.2 object at all | **open** (unchanged; referent reconciliation) |

---

## 8. Reproduce

```sh
python3 scripts/verify_se62_aaatt_flow_cone.py
```

The script re-derives the window spectra `(1,2,2)` / `(2,2,2)`, the `9/8` §6.1
ratio, the 10 `ℓ=2` and 18 `ℓ=1` port edges, the Myers reduction (only
`AAT.p1 -- TAA.p0` survives), the closed-flow cone (all generators have
`d_AAT = d_TAA`, generators `(1,0,0)`, `(0,1,1)`), the feasibility of
`(2,2,1)` under the unreduced reading, and the single-molecule run-structure
characterization. It uses only Python integers and `fractions.Fraction`.

Primary sources: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116, §3.1–3.4, §5.2, §6.1–6.2,
PMC3154397; Eugene W. Myers, *The fragment assembly string graph*,
*Bioinformatics* 21(Suppl 2) (2005) ii79–ii85, DOI `10.1093/bioinformatics/bti1114`.
