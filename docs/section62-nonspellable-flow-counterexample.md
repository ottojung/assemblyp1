# Can a non-spellable §6.2 flow beat a truth-feasible bridged genome?

_Status: source reading + mathematical reduction + bounded exhaustive exact-rational
computation. 2026-09-20. Not a Lean result. All claims are classified as
**source fact**, **source-supported inference**, **mathematical argument**,
**verified computation**, or **open**. This note addresses the residue recorded
in `docs/section62-bidirected-flow-feasibility.md` §6 (and §7.1): whether a
*spellable* truth can be beaten by a Medvedev–Brudno §6.2 feasible flow that is
**not** the window spectrum of any single molecule. It does not settle the
source-ambiguous Shomorony et al. open question._

_Reproduction: `python3 scripts/se62_nonspellable_flow_search.py` (all
assertions pass; exact `fractions.Fraction` arithmetic; about 7 minutes on the
development host; `--quick` runs a small subset)._

---

## 0. Answer at a glance

1. **The §6.2 feasible objects form a cycle cone, not a set of molecules.**
   A flow decomposes into closed walks, so its vertex-throughput vector `d` is
   any nonnegative integer combination of closed-walk visit vectors. Enumerating
   this cone is what the repository's earlier searches
   (`se62_bidirected_feasibility_search.py`, `se62_fixed_length_bidirected_search.py`)
   did **not** do: they enumerated only single spelled molecules.

2. **Under the per-occurrence reading, truth-feasibility forces `n ≤ G`.**
   `d_S(w) ≥ x_w` for all `w` gives `n = Σ_w x_w ≤ Σ_w d_S(w) = G`. Hence the
   search over the number of reads is *complete* once `n` runs to `G`
   (mathematical argument). This is why the repository's per-occurrence searches
   could be exhaustive in `n`.

3. **On the full (unreduced) overlap graph with `o_min = 1`, the answer is
   YES.** There is a `G = 5`, `L = 3` truth-feasible bridging instance and a
   **non-spellable** §6.2 flow `d` with strictly larger literal §6.1 binomial
   likelihood than the truth spectrum `d_S` (verified computation):
   ```
   S = 01011,  G = 5,  L = 3,  starts (0,1,2,3)
   d_S = {010:1, 101:2, 011:1, 110:1}
   x   = {010:1, 101:1, 011:1, 110:1} = d
   cycle   010 -> 101 -> 011 -> 110 -> 010   (step overlaps 2,2,2,1)
   binomial ratio L(d)/L(d_S) = 32/27 > 1.
   ```
   No circular molecule has window spectrum `d`, so `d` is genuinely
   non-spellable.

4. **The witness's key edge is transitively reducible.** The edge `110 -> 010`
   (overlap `1`) is spanned by the observed read `101`:
   `overlap(110,101) + overlap(101,010) = 2 + 2 ≥ 3 = L`. The source says the
   graph is *transitively reduced*, so this edge is exactly one that the
   reduction removes.

5. **On a transitive reduction that preserves spelled molecules (the
   junction-containment string graph), the answer is NO in the searched
   scope.** Over 6 134 per-occurrence truth-feasible instances per `o_min` for
   binary `G = 5,6,7`, `L = 3`, single-strand, both `o_min = 1,2`, there are
   **zero** flows (spellable or not) beating the truth; in every instance the
   truth spectrum `d_S` is itself a feasible flow of the reduced graph, so the
   comparison is well-posed. So the previously-open non-spellable gap does
   **not** produce a counterexample once the source's transitive reduction is
   applied, at least in this bounded scope.

6. **Per-type counterexamples persist and are spellable.** Under the per-type
   lower bound (`d_w ≥ 1` for every observed molecule), the reduced graph still
   has counterexamples at `G = 6` (48 instances at each of `o_min = 1,2`); the
   smallest is the spectrum of the spelled molecule `0000101`. These are not a
   new non-spellable phenomenon and lie outside the per-occurrence statement.

---

## 1. The model, stated exactly

**Source facts** (Medvedev–Brudno, §6.2, PMC3154397): the graph vertices are the
reads; edges are all bidirected overlaps of length at least `o_min`; the graph
is *transitively reduced*; every read vertex has lower bound `1`; the output is
a flow that "represents a (non-contiguous) assembly of the genome"; the
objective is the §6.1 separable binomial on the vertex flow, with external
denominator `N` (the true genome length) and `n` trials.

**Source-supported model used here.**

- `S` circular length `G`; reads length `L`; observed read-type counts `x`;
  `n = Σ_w x_w`.
- *Truth-feasible* (per-occurrence): `supp(spec_L(S)) = supp(x)` and
  `d_S(w) ≥ x_w`. This is the Observation-7 sequence-level §6.2 criterion of
  `docs/section62-bidirected-flow-feasibility.md` §2.
- *Feasible flow*: any integer circulation of the overlap graph on observed
  types; a directed edge `u → v` exists iff `u,v` share a proper overlap of
  length `≥ o_min`. The throughput vector `d` is feasible iff an integer
  circulation has `in = out = d_v` at every vertex, checked exactly by a
  lower-bound max-flow on the vertex-split graph (mathematical argument +
  verified computation).
- *Objective*: `∏_w C(n,x_w) (d_w/N)^{x_w}(1 - d_w/N)^{n-x_w}` with `N = G`,
  domain `d_w ≤ N`, exact rationals.

Because any flow decomposes into closed walks, the feasible set is the
**integer cycle cone** of the overlap graph. A *spellable* candidate is the
special case of a single closed walk whose overlaps are consistent; a
non-spellable flow is a general cone element.

**Transitive reduction.** The source does not give a reduction algorithm. This
note uses a spelled-molecule-preserving reduction: remove `u → v` when some
observed read `w` spans the `u`-`v` junction, i.e.
`overlap(u,w) + overlap(w,v) ≥ L + overlap(u,v)`. This is order-independent,
yields a subgraph of the raw overlap graph, and never removes the
overlap-`(L-1)` edges of a spelled molecule's circuit, so the truth remains an
admissible flow. A reachability-style "drop every edge with any 2-hop path"
rule is stricter and can remove the truth's own circuit (making the question
ill-posed); it was tested but is not used here. (The script additionally
asserts, for every searched instance, that `d_S` is a feasible flow of the
graph, so the per-occurrence comparison is well-posed.)

---

## 2. Why the full-graph witness exists

For the per-occurrence reading, truth-feasibility implies `n ≤ G`, so the
per-vertex binomial optimum `d*_w = G x_w / n` satisfies `x_w ≤ d*_w`. The
truth `d_S` lies at or above `x`, while the flow `d = x` is lower. The two
differ only in the repeated type `101 ∈ spec(S)` with `d_S(101) = 2 > x(101)`.
Since `d*_{101} = 5/4` is closer to `1` than to `2`, replacing `d_S` by `x`
improves the `101` factor enough to overcome the (unchanged) others:
`g(1)/g(2) = (64/625)/(54/625) = 32/27`, where
`g(d) = (d/5)(1-d/5)^3`.

`d = x` is realizable as a circulation only by using the overlap-`1` edge
`110 → 010`; that edge is exactly what the transitive reduction removes. This
isolates the whole phenomenon: **the non-spellable gap is populated solely by
transitively reducible short-overlap edges** in the tested scope.

---

## 3. Exhaustive search

For each truth `S`, each realized start multiset satisfying `I_s`, each read
count `n` (all `n ≤ G` for per-occurrence; `n ≤ G` recorded for per-type), and
each throughput vector `d` in the box `[lo_w, N]` (with `lo_w = x_w`
per-occurrence, `lo_w = 1` per-type), feasibility is decided by exact
lower-bound max-flow and the binomial ratio is computed exactly. The box is
complete because the binomial domain requires `d_w ≤ N`.

| graph | lower bound | `o_min` | `G` | instances | cex |
|---|---|---|---|---|---|
| full | per-occurrence | 1 | 5 | 422 | 20 |
| full | per-occurrence | 2 | 5 | 422 | 0 |
| full | per-occurrence | 1 | 6 | 1776 | 1368 |
| full | per-occurrence | 2 | 6 | 1776 | 0 |
| string | per-occurrence | 1 | 5,6,7 | 422 / 1776 / 3936 | 0 |
| string | per-occurrence | 2 | 5,6,7 | 422 / 1776 / 3936 | 0 |
| full | per-type | 1 | 5,6 | 482 / 2508 | 660 / 7032 |
| full | per-type | 2 | 5,6 | 482 / 2508 | 0 / 48 |
| string | per-type | 1 | 5,6 | 482 / 2508 | 0 / 48 |
| string | per-type | 2 | 5,6 | 482 / 2508 | 0 / 48 |

Single-strand, binary alphabet, `L = 3`. Full counts are deterministic and
asserted by the script. The string-graph per-occurrence zero is the central
bounded result; the string-graph per-type `o_min = 2` witness `0000101` is a
single spelled molecule, consistent with the known per-type fixed-length
counterexamples.

---

## 4. What this does and does not establish

| statement | status |
|---|---|
| §6.2 feasible objects are cycle-cone elements (non-contiguous assemblies) | source fact + mathematical argument |
| Per-occurrence truth-feasibility `⟹ n ≤ G`, so `n`-search is complete | mathematical argument |
| Full `o_min=1` graph: a non-spellable flow beats a truth-feasible truth (`S=01011`) | verified computation (hand-checkable) |
| That witness's winning edge is transitively reducible | mathematical argument |
| String graph, per-occurrence: no beating flow for binary `G ≤ 7`, `L=3`, `o_min ∈ {1,2}` | verified computation, bounded |
| Per-type string graph `o_min=2`: counterexamples exist, all recorded ones spellable | verified computation |
| “`I_s` ∧ `S ∈ F_flow(R)` ⇒ truth is ML over §6.2 flows” (per-occurrence) | **not refuted**; supported by the string-graph zero |
| The same for `G > 7`, other `L`/alphabets, revcomp reading | **open** |
| Whether the source's reduction is the Myers one used here | **unresolved source ambiguity** |

**Do not overclaim.** The zero count is bounded computational evidence, not a
proof of absence. The positive full-graph witness is genuine for the stated
model (no transitive reduction, `o_min = 1`) but is *not* a counterexample to
the source-faithful model, because the source reduces the graph and the witness
dies under that reduction.

---

## 5. Open questions / next packets

1. **Prove the per-occurrence string-graph zero.** The computation suggests the
   truth-induced flow `d_S` is the componentwise-least circulation dominating
   `x` on the string graph, which (for `n ≤ G`) makes `d_S` a maximizer. A proof
   would need a structural property of the string graph excluding
   visit-skipping circulations.
2. **Fix the reduction from the primary source.** The result is sensitive to
   the exact "transitively reduced" algorithm; the paper text does not pin it
   down.
3. **Reverse-complement / bidirected reading.** The bidirected orientation
   flips are not modelled here (molecule classes are collapsed, as in the
   repository's other §6.2 search). The #31 inversion shows this choice is
   material.
4. **Larger `L` and alphabets.** Only `L = 3`, binary, single-strand is
   exhausted.

---

## 6. Epistemic status

| claim | status |
|---|---|
| §6.2 flow = cycle cone; non-spellable = general cone element | source fact + mathematical argument |
| `n ≤ G` under per-occurrence truth-feasibility | mathematical argument |
| `S = 01011` full-graph non-spellable witness (ratio `32/27`) | verified computation, exact rationals, hand-checkable |
| `d = x` is not any molecule's spectrum | verified computation (exhaustive over length-`4` words) |
| Raw `o_min=1` winning edge is junction-reducible (removed by the reduction) | mathematical argument |
| String-graph per-occurrence zero over the printed scope | verified computation, bounded |
| Per-type `o_min=2` witness `0000101` spellable | verified computation |

Primary sources: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116, §6.1–6.2, PMC3154397;
Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
Bioinformatics 32(17) (2016) i494–i502. String-graph reduction: E. W. Myers,
*The fragment assembly string graph*, Bioinformatics 21 (Suppl. 2) (2005)
ii79–ii85.

Cross-references: `docs/section62-bidirected-flow-feasibility.md` (§6 residue,
§7 open questions); `docs/section-6-2-feasible-set-membership.md`;
`docs/bridging-schemas-and-flow-feasibility-gaps.md` (Propositions A, D);
`scripts/se62_nonspellable_flow_search.py` (reproduction).
