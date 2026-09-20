# A bridging truth whose feasible §6.2 flow is beaten by a strictly better *non-spellable* arbitrary flow

_Status: independent exact finite computation + source reading, 2026-09-20.
All claims are labelled **source fact**, **modeling choice**, **mathematical
proof**, **verified computation**, or **open**. Nothing here is promoted to
proof; the witness is a finite exact certificate, not a kernel-checked theorem._

_Reproduction:_ `python3 scripts/se62_bridging_arbitrary_flow_search.py`
(deterministic, exact `fractions.Fraction`/integers, exits non-zero on any
failed assertion).

---

## 0. Verdict at a glance

Fix the Medvedev–Brudno §6.2 object as the transitively-reduced bidirected
overlap graph on the observed read **molecules**, with vertex lower bound `1`,
closed integral flows (the genome is a circuit), and the §6.1 separable-binomial
objective with external `N = |S|`. Fix the strict Shomorony et al. Eq. (1)
bridging predicate `I_s`.

Then there is a truth `S` satisfying strict `I_s` such that

1. the truth-induced flow `d_S` **is** an admissible closed §6.2 flow; but
2. some **arbitrary** closed §6.2 flow `d*` has strictly larger likelihood,
   `L_{6.1}(d*)/L_{6.1}(d_S) = 256/81 > 1`; and, sharply,
3. `d*` is **not spellable** by any single circular molecule: no sequence — not
   even a same-or-longer circular genome over the observed read types — attains
   it. So the §6.2 maximiser beats the truth and is not a genome at all.

The witness:

```text
truth      S = AAATT   (00011)      G = 5, L = 3, N = 5, o_min = 1
read starts  (0, 0, 1, 4)           n = 4  (start 0 read twice)
observed   x = { AAA:2, AAT:1, TAA:1 }
truth flow d_S = { AAA:1, AAT:2, TAA:2 }        (closed circuit of S)
ML flow    d* = { AAA:3, AAT:1, TAA:1 }         (= 2·AAA-loop + AAA→TAA→AAT→AAA)
           (tie: {AAA:2, AAT:1, TAA:1} is equally optimal and also non-spellable)
L_{6.1}(d*)/L_{6.1}(d_S) = 256/81 > 1
```

[verified computation + mathematical proof; §2–§3]

This is stronger than the already-recorded `AAATT → AAAATT` witness, where the
better §6.1 object is a single spelled molecule: here the strictly better
object is reachable only by leaving the class of sequence spectra. [verified
computation; contrast §4]

The search that produced it also exposes a **repair**: the earlier independent
model's transitive reduction was inverted (it removed overlaps by *shorter*
composing overlaps), so at `o_min = 1` its flow cone was strictly too large.
The reduction used here is the source-supported Myers rule (`l1,l2 > l`,
`l = l1 + l2 − L`); it agrees with the independent rule audit
`docs/section62-edge-and-transitive-reduction-rules.md` and
`scripts/verify_se62_edge_and_reduction_rules.py`. The `o_min = 2` witness is
unaffected. [verified computation + mathematical proof; §1.2]

---

## 1. The model, with every assumption named

### 1.1 Source facts

Primary source: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116, §3.1–3.4, §5.2, §6.1–6.2,
DOI [10.1089/cmb.2009.0047](https://doi.org/10.1089/cmb.2009.0047),
[PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/).

- **§3.1** A DNA molecule is an unordered reverse-complement pair; on `{A,T}` the
  involution is `0 ↔ 1`, so a read is a *molecule class* `min(w, rc(w))`.
- **§3.3** A bidirected edge between molecules `x,y` is one of the four strand
  cases; its length is the underlying string-overlap length. A walk must use
  opposite orientations at each interior vertex; a loop contributes `±2`/`0`.
- **§3.4** A flow satisfies the bounds and, at every vertex, `in − out = b(v)`.
- **§5.2** Splitting each vertex `v → v⁻→v⁺` turns a vertex bound/cost into an
  edge bound/cost; the split-edge flow is `d_v`.
- **§6.1** Objective: product of per-type binomials with the external known
  genome length `N`, `∏_w (d_w/N)^{x_w}(1−d_w/N)^{n−x_w}`, `0 ≤ d_w ≤ N`.
- **§6.2** Vertices are the reads; edges are all bidirected overlaps of length
  `≥ o_min`; the graph is transitively reduced (**Myers 2005**); every read
  vertex has lower bound `1`, all other lower bounds `0`, all upper bounds `∞`;
  the supersource/supersink carries prohibitive cost; the flow is a
  "(non-contiguous) assembly" while the genome itself is a **circuit**.

Bridging `I_s` is from Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David
N. C. Tse, *Information-optimal genome assembly via sparse read-overlap graphs*,
*Bioinformatics* 32(17) (2016) i494–i502, Eq. (1), attributed to Bresler,
Bresler & Tse (2013): coverage, every triple repeat all-bridged, every
interleaved repeat pair bridged. The strict copy-bridging normalization is the
repository's accepted one (`docs/bridging-source-semantics.md`): a read
`[r, r+L)` bridges copy `[t, t+ℓ)` iff `r < t` and `t+ℓ < r+L`. [source fact]

### 1.2 Modeling choices used, and the corrected reduction

- **A1.** Graph vertices are the observed read **molecule types**; two reads in
  the same class are one vertex, and duplicate observed reads contribute to the
  observed count `x_w` but not to the vertex set. [source fact §3.1]
- **A2.** Every read vertex has lower bound `1`; the observed multiplicity `x_w`
  is **not** a lower bound on `d_w`. [source fact §6.2]
- **A3.** Candidate objects are closed integral flows (the genome is a circuit);
  an open source/sink walk is admissible in §6.2 but carries prohibitive cost.
  Our witness is a closed flow, hence first-tier. [source fact §6.2]
- **A4.** Objective is the §6.1 separable binomial with external `N = |S|`.
  [source fact]
- **A5.** Genome circular; starts and windows cyclic. [source fact]
- **A6.** `o_min ∈ {1,2}` at `L = 3`; the source's experiments use
  `o_min < L−1`. [source fact §8.2]
- **A7.** `I_s` uses the strict bridging predicate. [modeling normalization]
- **A8.** **Corrected Myers reduction.** An overlap `e` of length `l` is removed
  iff some observed read `z` gives a two-step path with proper overlaps
  `l1,l2 < L`, opposing interior incidences, matching boundary incidences, and
  `l = l1 + l2 − L`; since `l1,l2 < L` this forces `l1,l2 > l` for `l ≥ 1`.
  This is the source-named Myers reading and agrees with
  `docs/section62-edge-and-transitive-reduction-rules.md`. The competing
  "shorter composing overlaps" reading used by
  `scripts/independent_se62_bidirected_model.py:215` is unsatisfiable for proper
  overlaps and produces an unreduced `o_min = 1` graph; that script's
  `o_min = 2` search is unaffected because no length-1 edges exist there.
  [source fact + mathematical proof + verified computation]

For `L = 3` the reduced graph on `{AAA, AAT, TAA}` is the ten length-2 port
edges plus the two length-1 edges `AAT.p1 — TAA.p0`; every closed flow then has
`d_AAT = d_TAA`, so the closed-flow cone is `{(a,k,k)}` (independent hand proof
in `docs/section62-aaatt-reduced-flow-cone-and-spectra.md`; reproduced
computationally here). [mathematical proof + verified computation]

### 1.3 Completeness limits of the search

- Finite box: alphabet `{A,T}`; `L = 3`; `G = |S| ∈ {4,5,6,7}`; `N = G`;
  `o_min ∈ {1,2}`; read multiset size `n ∈ {2,3,4}`; **all** start multisets of
  that size; every circular truth up to rotation.
- Flows: the reachable throughput vectors are generated by elementary port
  circuits and enumerated with coordinates in `[1, N]`; each coordinate is the
  only binding bound (total visits `≤ n_molecules · N` automatically). This is
  exhaustive inside those coordinate bounds.
- Spellability: single circular molecules with length `≤ N + 2` whose every
  `L`-window is an observed read type.
- Nothing outside these boxes is claimed. Finite exact computation is
  **evidence**, not a proof of any global statement.

---

## 2. The witness and its certificates

### 2.1 Strict `I_s` holds

`S = 00011` (`AAATT`), `L = 3`, starts `(0,0,1,4)`.

- **Coverage.** Intervals `[0,3)`, `[0,3)`, `[1,4)`, `[4,7)` cover `0..4`.
- **Triple repeats.** The only maximal triple repeat is the length-1 run of `A`
  at copies `{0,1,2}` (left flanks `T,0,0`; right flanks `0,0,1`). Copies `0,1,2`
  are strictly bridged by the reads at lifts `−1, 0, 1` respectively.
- **Interleaved pairs.** The length-2 repeats are `00` at `{0,1}` and `11` at
  `{3,4}`; the four positions do not cyclically alternate, so the interleaving
  conjunct is vacuous.

Two independent implementations of `I_s` accept this read set: the strict
predicate of `scripts/verify_se62_lb1_bidirected_determination.py` and the
predicate of `scripts/independent_se62_bidirected_model.py`. [verified
computation]

### 2.2 The truth is a feasible closed §6.2 flow

The observed support `{AAA, AAT, TAA}` equals the full length-3 window spectrum
of `S`, so `S`'s cyclic window circuit is a flow on the read graph. On the
`o_min = 1` reduced graph its edge multiplicities are the vector
`(0,0,0,1,0,0,1,1,0,0,1,1)` over the script's reduced-edge indexing, i.e.

```text
edge 3  AAA.p0 → TAA.p1      1
edge 6  TAA.p0 → TAA.p0      1
edge 7  AAT.p0 → AAA.p1      1
edge 10 TAA.p1 → AAT.p0      1
edge 11 AAT.p1 → AAT.p1      1
throughput = (AAA:1, AAT:2, TAA:2) = d_S.
```

The script verifies port balance (`in = out`) at every state and recomputes the
throughput from the multiplicities. [verified computation]

### 2.3 A strictly better arbitrary flow, non-spellable

The unconstrained §6.1 target is `d*_w = N x_w / n = 5·(2,1,1)/4 =
(2.5, 1.25, 1.25)`. The reduced cone is `{(a,k,k)}`, so the integer optimum is
`a ∈ {2,3}`, `k = 1`; both `(2,1,1)` and `(3,1,1)` are optimal (the `AAA`
factor is symmetric about `2.5`). Taking `d* = (3,1,1)`,

```text
d* = 2·(AAA self-loop:  AAA.p0 → AAA.p1)
   + 1·(3-molecule circuit:
            AAA.p0 → TAA.p1,  TAA.p0 → AAT.p1,  AAT.p0 → AAA.p1)
```

with explicit edge multiplicities `(0,1,2,1,0,0,0,1,0,0,0,0)` (edges 1, 2,
3, 7); the script verifies port balance and throughput. The exact ratio is

```text
AAA factor: g(3)/g(1) = [(3/5)^2(2/5)^2] / [(1/5)^2(4/5)^2] = 36/16 = 9/4
AAT factor: g(1)/g(2) = [(1/5)(4/5)^3] / [(2/5)(3/5)^3] = 64/54 = 32/27
TAA factor: same                                                   32/27
L(d*)/L(d_S) = (9/4)·(32/27)^2 = 256/81 ≈ 3.1605 > 1.
```

The script recomputes this independently both through `fractions.Fraction` and
by a manual factor-by-factor check, and they agree. [verified computation +
mathematical proof]

**Non-spellability.** The `o_min = 1` reduced cone contains `(3,1,1)` only
because the single length-1 edge `AAT.p1 — TAA.p0` survives Myers reduction; the
two modules `AAA` and `AAT/TAA` are otherwise independent, which is exactly what
allows `d_AAT ≠ d_TAA`. But every **single circular molecule** whose length-3
windows lie in `{AAA, AAT, TAA}` has no run of length `1` and hence spectrum
`(G−4k, 2k, 2k)`, forcing `d_AAT = d_TAA`
(`docs/section62-aaatt-reduced-flow-cone-and-spectra.md` §4); independently, the
script enumerates all such molecules with `|D| ≤ 7` and confirms `(2,1,1)` and
`(3,1,1)` are absent. So the §6.2 likelihood optimum is not a sequence spectrum
at all. [mathematical proof + verified computation]

### 2.4 Independent sanity checks

| Check | Independent artifact | Result |
|---|---|---|
| strict `I_s` | `verify_se62_lb1_bidirected_determination.py` | accepts |
| strict `I_s` | `independent_se62_bidirected_model.py` | accepts |
| reduced graph = 10×ℓ2 + 2×ℓ1 | `verify_se62_edge_and_reduction_rules.py`, `verify_se62_aaatt_flow_cone.py` | agrees |
| cone `= {(a,k,k)}`, generators `(1,0,0)`,`(0,1,1)` | `verify_se62_aaatt_flow_cone.py` | agrees |
| `(3,1,1)` closed-flow feasible | explicit port-balance certificate (this script) | verified |
| `(3,1,1)` non-spellable | `verify_se62_aaatt_flow_cone.py` §4 + this script | verified |

---

## 3. Bounded search results and negative boundary

Inside the box of §1.3 the script finds `24` distinct
`(truth, starts, o_min)` hits where a strictly better feasible flow exists
(`d_S` feasible, `L(d*)/L(d_S) > 1`). The strongest is `2187/512` for
`S = AATAT`; the earlier `AAATT → (2,2,2)` instance at `o_min = 2` is
reproduced at `9/8`. Exactly `2` hits have a **non-spellable** optimum:

| truth `S` | starts | `o_min` | `d_S` | `d*` | ratio | `d*` spellable |
|---|---|---|---|---|---|---|
| `AAATT` | (0,0,1,4) | 1 | (1,2,2) | (3,1,1) | 256/81 | **no** |
| `AATTT` | (1,2,2,3) | 1 | (1,2,2) | (3,1,1) | 256/81 | **no** |

(the second is the reverse-complement/rotation image of the first).

**Negative boundary (useful if a future run wants to know what the box did not
show).**

1. Every hit in the box with **distinct** read starts has a spellable optimum:
   within `G ≤ 7, n ≤ 4` the non-spellable phenomenon needs a repeated read.
2. Every `o_min = 2` hit has a spellable optimum: without the length-1 edge the
   cone forces `d_AAT = d_TAA` even, and the spellable competitor matches.
3. The existence of a non-spellable better flow is therefore a genuine
   `o_min = 1` / repeated-read effect, not an artefact. Whether some
   distinct-start instance outside the box has a non-spellable optimum is
   **open**.

These are completeness statements only inside the stated boxes. [verified
computation + open]

---

## 4. Relation to existing artifacts

| Artifact | Relation |
|---|---|
| `docs/independent-se62-bidirected-model.md` | it enumerated **spelled** competitors and found `AAATT → AAAATT`; this note searches **arbitrary** flows and shows the relaxation is strict |
| `docs/section62-bidirected-lowerbound1-determination.md` | provides the source-faithful §6.2 reading and the `AAATT` witness this note extends |
| `docs/section62-aaatt-reduced-flow-cone-and-spectra.md` | supplies the cone `{(a,k,k)}` and the single-molecule run-structure fact used for non-spellability |
| `docs/section62-edge-and-transitive-reduction-rules.md` | independent audit of the corrected Myers rule; this search conforms to it |
| `FeasibleType` Lean predicate | not used here; it does not encode conservation and admits `(2,2,1)`, which this corrected cone forbids |

---

## 5. What this does and does not settle

**Does.** It produces a finite exact witness under the corrected §6.2 object in
which a strict-`I_s` truth is a genuine feasible flow but is beaten by an
arbitrary feasible flow that is not any genome spectrum — so the §6.2 optimum is
not the truth even after restricting to §6.2-feasible objects. It also records
the corrected Myers reduction and its effect on the `o_min = 1` cone, plus an
explicit negative boundary for the searched box.

**Does not.** It is a finite computation, not a kernel-checked theorem, and it
makes no global claim. It does not settle which Medvedev–Brudno layer the 2016
Shomorony sentence denotes (the repository's determination is that §6.2 is not
the direct referent), nor the probability-model, candidate-length, or tie
semantics. Whether an unbounded family of such non-spellable witnesses exists is
**open**, as is the corresponding question with distinct read starts.

---

## 6. Reproduce

```sh
python3 scripts/se62_bridging_arbitrary_flow_search.py
```

The script reconstructs the graph and reduction from the source rules, verifies
the strict `I_s` certificate, exhibits explicit balanced circulations for `d_S`
and `d*`, checks non-spellability by exhaustive single-molecule enumeration,
recomputes the ratio two ways, runs the bounded search, and asserts the negative
boundary. It exits non-zero on any failed assertion.

Primary sources: Medvedev & Brudno (2009), §3.1–3.4, §5.2, §6.1–6.2,
[PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/); Myers (2005),
*The fragment assembly string graph*, *Bioinformatics* 21(Suppl 2) ii79–ii85;
Shomorony, Kim, Courtade & Tse (2016), Eq. (1); Bresler, Bresler & Tse (2013).
