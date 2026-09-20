# Broader Section 6.2 non-spellable-flow search (issue #36)

_Status: source reading + mathematical reduction + bounded exhaustive
exact-rational computation. 2026-09-20. Not a Lean result. All claims are
classified as **source fact**, **source-supported inference**, **mathematical
argument**, **verified computation**, or **open**._

_Reproduction: `python3 scripts/se62_nonspellable_broader_search.py`
(all assertions pass; exact `fractions.Fraction`; about five minutes, `--quick`
skips the heavy `G = 6, L = 4` scopes)._

_Relationship to prior work. This note continues
`docs/section62-nonspellable-flow-counterexample.md` (branch
`analysis/issue36-nonspellable-flow`) and `docs/section62-bidirected-flow-feasibility.md`
§5. It does not repeat their single-strand `G <= 7, L = 3` enumeration; it
attacks the two axes those computations left open: (A) a number of reads
`n < G`, and (B) the bidirected / reverse-complement reading._

---

## 0. Answer at a glance

1. **The prior "no sequence-level §6.2 counterexample" search silently fixed
   `n = G` reads.** Reading `scripts/se62_bidirected_feasibility_search.py`
   shows `combinations_with_replacement(range(G), N)` with `N = G`. The
   Shomorony et al. model has the number of reads `N` as a free parameter, and
   per-occurrence truth-feasibility only forces `n <= G`. Allowing `n < G`
   exposes a source-faithful counterexample the earlier search could not see
   (source-supported inference + verified computation).

2. **A bridging-condition truth can be §6.2-feasible and still beaten, already
   on the single-strand graph** (source-faithful, `o_min`-independent, all
   edges overlap `L-1` so the transitive reduction cannot remove them):
   ```
   S = 000001 (G = 6), L = 4, starts (0,2,3,4,5), n = 5 < 6
   x   = {0000:1, 0001:1, 0010:1, 0100:1, 1000:1}
   d_S = {0000:2, 0001:1, 0010:1, 0100:1, 1000:1}
   D   = 00001,  d_D = x  (D is read-tiled by overlap-(L-1) edges)
   I_s holds; Section 6.1 binomial ratio L(d_D)/L(d_S) = 625/512 > 1.
   ```
   The competitor is a spelled molecule, so a fortiori a feasible flow
   (verified computation).

3. **Under the bidirected (reverse-complement) reading there is a genuinely
   non-spellable feasible flow that beats a §6.2-feasible bridging truth**
   at `o_min = 1` (the residue left open in the prior note):
   ```
   S = 000111 (G = 6), L = 4, reads comp 0<->1, starts (0,1,3,4), n = 4 < 6
   x   = {0001:1, 0011:1, 1000:1, 1100:1}
   d_S = {0001:2, 0011:1, 1000:2, 1100:1}
   d   = {0001:2, 0011:2, 1000:2, 1100:2}   (a feasible circulation)
   I_s holds; d_S is a feasible flow; no molecule has class spectrum d
   (sum(d) = 8, exhaustive over all 2^8 binary molecules);
   Section 6.1 binomial ratio = 16384/15625 > 1.
   ```
   The circulation is a sum of three cycles (below); it is a non-contiguous
   assembly, exactly the object §6.2 optimizes (verified computation).

4. **The non-spellable phenomenon is `o_min = 1` only.** At `o_min >= 2` the
   winning cycles' overlap-1 edges are gone and the bidirected
   `G = 6, L = 4` scope has zero non-spellable beats. The single-strand
   spellable beat of item 2 survives every `o_min in {1,2,3}`.

5. **Exact bounded scopes** (source-faithful junction-containment string
   reduction, per-occurrence lower bound, binary alphabet):

   | `G` | `L` | comp | `o_min` | truth-feasible instances | spellable beats | non-spellable beats |
   |---|---|---|---|---|---|---|
   | 5 | 4 | no | 1 | 482 | 0 | 0 |
   | 6 | 4 | no | 1 | 2676 | 24 | 0 |
   | 6 | 4 | no | 2 | 2676 | 24 | 0 |
   | 6 | 4 | yes | 1 | 2964 | 24 | 1260 |
   | 6 | 4 | yes | 2 | 2292 | 24 | 0 |
   | 5 | 3 | yes | 1 | 552 | 30 | 20 |
   | 6 | 3 | yes | 1 | 2504 | 72 | 96 |
   | 7 | 3 | yes | 1 | 3922 | 0 | 0 |

   Counts are exact (not capped) and asserted by the reproduction script.
   They are computational evidence, not a proof of absence beyond the scope.

---

## 1. Model, stated exactly

**Source facts** (Medvedev–Brudno 2009, §6.1–6.2, PMC3154397; quoted in
`docs/section62-bidirected-flow-feasibility.md` §1):

- §6.2 builds a transitively reduced *bidirected* overlap graph whose vertices
  are the reads (DNA molecules), lowers every read vertex by `1`, and maximizes
  the §6.1 separable binomial objective over **flows**.
- A flow "represents a (non-contiguous) assembly of the genome"; it need not be
  any single molecule.
- §6.1 treats `N(D)` as constant and replaces it by the *actual* genome length
  `N`; MB09 "assume that the genome size is known".

**Model used here** (as in the prior note):

- true circular `S` of length `G`; read length `L`; a read multiset with type
  counts `x`; `n = sum(x)` free (Shomorony et al.: `N` reads drawn i.i.d.
  uniformly from the `G` windows).
- *Truth-feasible* (per-occurrence): `supp(spec_L(S)) = supp(x)` **and**
  `d_S(w) >= x_w`. Observation 7 of the source makes this the exact
  sequence-level §6.2 feasibility criterion; it forces `n <= G`.
- *Feasible flow*: integer circulation of the overlap graph on observed types;
  a directed edge `u -> v` exists iff `u, v` have a proper overlap of length
  `>= o_min`. Feasibility of a throughput vector `d` is checked exactly by a
  lower-bound max-flow on the vertex-split graph.
- *Source-faithful reduction*: the junction-containment string reduction of the
  prior note (remove `u -> v` when an observed read `w` spans the junction,
  `overlap(u,w) + overlap(w,v) >= L + overlap(u,v)`); it is order-independent,
  a subgraph of the raw graph, and preserves a spelled molecule's own circuit.
- *Objective*: literal §6.1 separable binomial with external `N = G`, `n`
  trials, exact rationals; domain `d_w <= N`.
- *Bidirected reading*: reverse complements are identified (`mol` maps a word
  to the min of itself and its reverse complement); types and `x` are molecule
  classes. This is source-ambiguous (see the cross-referenced notes); both
  readings are reported.

Because a feasible flow is any circulation and circulations are sums of cycles,
the §6.2 feasible set is the integer cycle cone of the overlap graph. A
*spellable* candidate is a single cycle spelling a molecule; a non-spellable
flow is a general cone element (mathematical argument).

---

## 2. Witness 1: single-strand, `n < G`, spellable beat

```
G = 6, L = 4, S = 000001, starts = (0,2,3,4,5)   n = 5 < G   single-strand
windows of S at 0..5 : 0000, 0000, 0001, 0010, 0100, 1000
d_S = {0000:2, 0001:1, 0010:1, 0100:1, 1000:1}
x   = {0000:1, 0001:1, 0010:1, 0100:1, 1000:1}
D   = 00001 (length 5)
spec(D) at 0..4     : 0000, 0001, 0010, 0100, 1000 = x
```

Checks (verified computation, exact rationals):

- `I_s` holds: coverage, the single triple repeat `0` at positions `0,1,2` is
  all-bridged, and there are no interleaved pairs.
- `supp(x) = supp(d_S)` and `d_S >= x`, so the truth is sequence-level §6.2
  feasible. `d_S` is a feasible flow of the string graph.
- `supp(spec(D)) = supp(x)` and `d_D = x >= x`, so `D` is sequence-level §6.2
  feasible and read-tiled by overlap-`(L-1)=3` edges.
- Binomial ratio (all `C(n,x_w)` cancel; only `0000` differs):
  `[(1/6)(5/6)^4] / [(2/6)(4/6)^4] = 625/512 = 1.220... > 1`.

**Why the earlier search missed it.** `scripts/se62_bidirected_feasibility_search.py`
enumerates `combinations_with_replacement(range(G), G)`, i.e. exactly `G` reads
(`N = G` in the source's notation). This instance has `n = 5`. Running that
script's `search(6, 4, 2, N=6, maxD=18, comp=None)` reproduces its recorded
zero (1220 instances, 0 counterexamples), while the same scope with
`n` ranging over `ceil(G/L)..G` gives 24 spellable beats, all with `n = 5`
(verified computation).

**Robustness.** Both `d_S` and `d_D` are realized by circuits all of whose
edges have overlap `L-1 = 3`. The junction-containment reduction never removes
an overlap-`(L-1)` edge, and such edges exist for every `o_min <= 3`; the script
asserts flow-feasibility of both vectors for `o_min in {1,2,3}`. The comparison
is therefore independent of the unresolved `o_min` and transitive-reduction
conventions.

---

## 3. Witness 2: bidirected, non-spellable feasible flow

```
G = 6, L = 4, comp 0<->1, S = 000111, starts = (0,1,3,4)   n = 4 < G
class windows of S : 0001, 0011, 0001, 1000, 1100, 1000
d_S = {0001:2, 0011:1, 1000:2, 1100:1}
x   = {0001:1, 0011:1, 1000:1, 1100:1}
d   = {0001:2, 0011:2, 1000:2, 1100:2}
```

Checks (verified computation):

- `I_s` holds; `supp(x) = supp(d_S)` and `d_S >= x`; `d_S` is a feasible flow of
  the string graph.
- `d` is a feasible flow of the string graph. In the reduced graph the overlap
  edges are
  `0001->0011, 0001->1000, 0011->1100, 1000->0001, 1100->0011, 1100->1000`,
  and `d` is the sum of the three cycles
  ```
  0001 -> 0011 -> 1100 -> 1000 -> 0001        (one unit each)
  0001 -> 1000 -> 0001                         (one unit each)
  0011 -> 1100 -> 0011                         (one unit each)
  ```
  i.e. a non-contiguous assembly with vertex throughput `2` at each of the four
  molecules.
- `d` is **not spellable**: any molecule with class spectrum `d` has length
  `sum(d) = 8`; exhaustive enumeration of all `2^8 = 256` binary molecules
  finds none (verified computation).
- Binomial ratio: `(1/3)(2/3)... ` evaluated exactly gives `16384/15625 =
  1.048576 > 1`.

The winning cycles use overlap-1 edges (`0001->1000`, `1000->0001`,
`1100->0011`, `0011->1100` has overlap 2); at `o_min >= 2` the overlap-1 edges
disappear and the beating flow is gone. This is the precise `o_min` sensitivity
of the residue.

**Minimal instance** (same phenomenon, smaller): `G = 5, L = 3`, comp,
`S = 00101`, starts `(0,2,4)`, `n = 3 < G`,
`d_S = {001:1, 010:3, 100:1}`, `x = {001:1,010:1,100:1}`,
`d = {001:1, 010:2, 100:1}` (feasible via the cycle
`001 -> 010 -> 100 -> 001` plus the self-loop `010 -> 010`),
ratio `3/2`; `sum(d) = 4` and no binary molecule has this class spectrum.

---

## 4. Exhaustive scope and what it isolates

The reproduction script enumerates every truth `S`, every start multiset, every
`n` in `ceil(G/L)..G`, and every throughput vector in the box `x_w <= d_w <= G`,
for the scopes of §0 item 5. `n <= G` is complete for the per-occurrence
reading (truth-feasibility gives `sum d_S = G >= sum x = n`), so the search is
exhaustive in `n`.

Conclusions from the table:

- **Single-strand:** every beat found is a *spelled molecule*; there is no
  non-spellable beat in the searched scopes. The `G = 6, L = 4` scopes are the
  first single-strand sequence-level §6.2 counterexamples, and they exist only
  because `n` was allowed below `G`.
- **Bidirected, `o_min = 1`:** non-spellable beats exist and are abundant
  (`1260` at `G = 6, L = 4`; `96` at `G = 6, L = 3`; `20` at `G = 5, L = 3`).
- **Bidirected, `o_min = 2`:** zero non-spellable beats, and still `24`
  spellable beats at `G = 6, L = 4`.
- `G = 7, L = 3` bidirected is zero; `G = 5, L = 4` single-strand is zero.

This is bounded computational evidence; it is not a proof that the bidirected
`o_min = 2` residue is empty beyond the printed scope, nor that larger
alphabets or `L` behave the same.

---

## 5. Epistemic status

| claim | status |
|---|---|
| §6.2 optimizes over flows (non-contiguous assemblies); objective is the §6.1 binomial with external `N` | source fact |
| Sequence-level feasibility = support equality + per-occurrence lower bound | source-supported inference from Observation 7 (prior notes) |
| The prior sequence-level search fixed `n = G` | source-code fact (`se62_bidirected_feasibility_search.py`) |
| Witness 1 is `I_s` + §6.2-feasible and beaten by the spelled molecule `00001` (ratio `625/512`) | verified computation (exact rationals) |
| Witness 1 is `o_min`-independent for `o_min in {1,2,3}` | mathematical argument (all edges overlap `L-1`) + verified computation |
| Witness 2 flow is feasible on the source-faithful string graph and non-spellable | verified computation |
| Witness 2 beats the truth (ratio `16384/15625`) | verified computation |
| Non-spellable beats at `o_min = 1` only, in the printed scopes | verified computation, bounded |
| Which MB09 §6.1/§6.2 layer, reverse-complement reading, and `o_min` the 2016 sentence intends | **open** (source ambiguity, unchanged) |

**What is now settled at the level of this note.** The prior note's residue —
"a spellable, §6.2-feasible truth beaten by a non-spellable §6.2 flow" — is
**witnessed** under the bidirected reading with `o_min = 1`, and the
single-strand residue is **closed**: allowing `n < G` already produces a
sequence-level §6.2 counterexample whose competitor is a spelled molecule. The
single-strand `n = G` zero of the prior notes is unchanged.

**What is not settled.** Whether the published 2016 sentence intends the
bidirected reading, the value of `o_min`, or the §6.2 flow problem at all
remains the source ambiguity recorded across the issue #36 notes. The witnesses
above fix the model choices inside each row and do not silently promote them to
the published statement.

---

## 6. Cross-references and prior artifacts

- `docs/section62-nonspellable-flow-counterexample.md` — prior residue, the
  junction-containment reduction, the single-strand `L = 3` zero.
- `docs/section62-bidirected-flow-feasibility.md` §5 — the `n = G` sequence-level
  search reproduced here.
- `docs/section-6-2-feasible-set-membership.md` — feasibility criterion.
- `docs/section62-fixed-length-bidirected-counterexample.md` — the separate
  per-type fixed-length bidirected counterexample (a different statement).
- `scripts/se62_nonspellable_broader_search.py` — reproduction and assertions
  (imports `scripts/se62_nonspellable_flow_search.py`).

Primary sources: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116, §6.1–6.2, PMC3154397;
Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
Bioinformatics 32(17) (2016) i494–i502.

---

## 7. Reproduce

```sh
python3 scripts/se62_nonspellable_broader_search.py          # full, ~5 min
python3 scripts/se62_nonspellable_broader_search.py --quick  # witnesses only
```

The script prints both witnesses and the exhaustive scope table, and exits
non-zero on any failed assertion.
