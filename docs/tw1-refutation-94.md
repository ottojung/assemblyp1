# The `t_w = 1` step is **refuted** (board 94, front 94e7, branch `94-tw1-best`)

_Status: one theorem is kernel-checked (`AssemblyP1.Issue94TW1.not_UniqueInArb_3`);
everything else here is either a restatement of that theorem's content, a
computational **evidence** item, or an explicit non-result._

**Result.** `Ukkonen` at read length `L`, together with rotation-primitivity,
does **not** give a unique spanning in-arborescence of the `(L-1)`-mer
multigraph `D` of the truth. The board's own `t_w = 1` step --- the second half
of its own conditional BEST-theorem decomposition --- is **false as stated**.

**Kernel-checked instance.** `S = 10100` on the circle of `5` positions, read at
`L = 3`.

| declaration | content |
| --- | --- |
| `S10100_primitive` | `RepeatAdapter.IsPrimitive h5 S10100` |
| `S10100_ukkonen` | `Ukkonen h5 3 S10100` |
| `S10100_arb1` | `InArb h5 3 S10100 0 T₁`, with `T₁ = {0, 1, 3}` |
| `S10100_arb2` | `InArb h5 3 S10100 0 T₂`, with `T₂ = {0, 3, 4}` |
| `T1_ne_T2` | `T₁ ≠ T₂` |
| `S10100_two_arbs` | both in-arborescences, and they differ |
| `not_UniqueInArb_3` | `¬ UniqueInArb 3` |
| `T1_T2_differ_only_in_parallel_edge` | the two differ only in a parallel edge |

`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound` for
every one of these. No `sorry`, no `admit`, no new `axiom`, no `native_decide`,
no `unsafe`, no linter suppression.

## The instance in detail

With `L = 3` the `(L-1)`-mers at the five starts are

| start `r` | 0    | 1    | 2    | 3    | 4    |
| --- | --- | --- | --- | --- | --- |
| `vtx r` | `10` | `01` | `10` | `00` | `01` |

so `D` has three vertices `10`, `01`, `00` and five edges

```text
r = 0 :  10 -> 01
r = 1 :  01 -> 10
r = 2 :  10 -> 00
r = 3 :  00 -> 01
r = 4 :  01 -> 10          <-- parallel to r = 1
```

Rooted at the start-`0` vertex `10`:

* `T₁ = {0, 1, 3}`: at `01` take edge `1`; at `00` take edge `3`. Chain
  `00 -> 01 -> 10`, and `01 -> 10`.
* `T₂ = {0, 3, 4}`: at `01` take edge `4`; at `00` take edge `3`. Same chain.

Both are spanning in-arborescences; hence `t_w ≥ 2` at `w = 0`.

**Why `Ukkonen` does not see it.** At the threshold `L - 1 = 2` the only
maximal repeat pair of length at least `2` is `{1, 4}` at length `3`, and it
does **not** interleave with anything: the interleaving clause needs four
pairwise distinct starts, and the only other maximal repeat pair is `{3, 4}` at
length `1 < 2`, so the `Or.inr` disjunct is discharged. Every maximal triple
repeat is at length `1 < 2`. So the word is `Ukkonen` while `D` has out-degree
`2` at `01` and two in-arborescences.

## This is **not** a refutation of `Ukkonen` uniqueness

This is the crucial boundary, and it is recorded in the kernel, not only in
prose, by `T1_T2_differ_only_in_parallel_edge`.

`t_w > 1` and "more than one *edge-type* Eulerian circuit" are different
statements. At this instance the two in-arborescences differ **only** in which
of the two parallel `01 -> 10` edges they use, and the two resulting labelled
Eulerian circuits are the **same edge-type word**:
`00>01 | 01>10 | 10>01 | 01>10 | 10>00`.

`docs/exact-same-length-spectrum-fibre-count.md` works throughout with edge
*types*, copies of one type being indistinguishable, and BBT's Theorem 3 is a
statement about the **condensed** sequence graph, which is the same coarser
object. The parallel-edge labelling is exactly the over-count that the
`prod_e c_h(e)!` denominators of that note remove. So the refutation kills the
*stated* form of the split, not the theorem the split was aiming at, and it is
**not** evidence against `Ukkonen` uniqueness.

## Computational evidence, and its limits

`scripts/verify_tw1_94.js`. Over every binary circular word of length `K ≤ 12`
that is primitive and satisfies `Ukkonen` at some `2 ≤ L ≤ K` --- 52210
`(S, L)` instances, of which the edge-type circuit count was computed for all
`K ≤ 9` (4312 instances):

* `t_w ≠ 1` in **5704** instances, with `t_w` as large as `16`;
* **zero** instances with more than one edge-type circuit orbit.

This is **evidence, not proof**: the completeness of the search over those
ranges is not proved, and nothing is claimed for `K > 12` or for alphabets
larger than binary.

The evaluator carries three independent checks, and **two earlier versions were
wrong and were caught by them**: a fraction-free Bareiss variant missing the
division by the previous pivot, and a cross-multiplied fraction variant
dividing by zero. Both produced root-dependent `t_w` values, which is impossible
for an Eulerian `D`. Both were fixed before any output above was read. The
evaluator now computes `t_w` by the directed Matrix-Tree theorem, cross-checks
it against a brute-force enumeration of in-arborescences, checks that `t_w`
agrees across roots, and checks the BEST product against a **direct**
enumeration of Eulerian circuits that uses neither BEST nor any determinant.

## What replaces the split

The count that must be `1` is the number of *edge-type* circuit orbits. A
correct reduction must divide out the parallel-edge labellings rather than
demand `t_w = 1`. **That corrected obligation is now stated and identified
with the public endpoint**: `AssemblyP1/Issue94TW1EdgeType.lean`,
`edgeTypeUnique_iff_uniqueEulerianCycle` proves
`EdgeTypeUnique L ↔ BBTEulerian.UniqueEulerianCycle L`. It is still **not
proved** — but it is not a new obligation either.

## CORRECTION (board 94, front 94a10): the "208 simple-`D`" claim was an evaluator bug

The text formerly here read:

> One tempting sufficient condition is **also false**, and the search says so:
> "simple `D` (no parallel edges) implies `t_w = 1`". At `K ≤ 9` there are
> **208** instances with a simple `D` and `t_w > 1`. So the corrected
> obligation cannot be discharged by a parallel-edge argument alone.

**This is withdrawn.** `hasParallelEdges` in `scripts/verify_tw1_94.js`
iterated its outer loop over `edges` (an array of `[tail, head]` pairs) and its
inner loop over `edges[u].length` — it treated the edge array as an adjacency
structure. For every input the inner loop then ran exactly twice, over
`[tail, head]` and `[tail, head]` in the order of the two entries, so the `seen`
set was rebuilt from scratch each time and the predicate was **identically
`false`**. Every instance was classified "simple", which is exactly why
548 + 208 = 756 appeared (756 is the true count of `K ≤ 9` instances).

With the predicate corrected (group by tail, then by head, look for a repeated
head) and a self-check added that the old version fails on hand-built graphs:

| range | instances with `t_w > 1` | of those with a **simple** `D` |
| --- | --- | --- |
| `K ≤ 9`  | 562  | **0** |
| `K ≤ 10` | 630  | **0** |
| `K ≤ 11` | 2214 | **0** |
| `K ≤ 12` | 5142 | **0** |

So "simple `D` implies `t_w = 1`` is **not refuted** by the search; it is
merely *unexamined* by it. The corrected obligation therefore needs **no new
idea** beyond the parallel-edge division. This remains **evidence, not proof**:
the completeness of the sweep over those ranges is not proved, and nothing is
claimed for `K > 12` or for a larger alphabet. It is used here only to *kill* a
false claim and to motivate a design decision, never as a premise of a theorem.

Full details, the condensed-vs-un-condensed decision, and the interface audit:
`docs/edge-type-obligation-94.md`.

## Attribution

The `t_w = 1` split, the conditional BEST-theorem reduction, and the
identification of out-degree as the critical parameter are **the board's own
constructions**, not results imported from Pevzner 1995 or from
Bresler--Bresler--Tse. See `docs/best-tw1-attribution-94.md`. This module uses
**no counting input at all**: it exhibits two in-arborescences by hand, so no
BEST theorem, no Matrix-Tree determinant and no arborescence-counting theory is
invoked.

## What is NOT established

1. `Ukkonen` uniqueness (BBT's Theorem 3) is **neither proved nor refuted**
   here. The search found no refutation candidate; absence of one is not proof.
2. "Simple `D` implies `t_w = 1`" is **neither proved nor refuted** here. The
   original "208 instances" figure for it was an evaluator bug and is withdrawn
   (see the CORRECTION section above); with the predicate fixed the search finds
   **zero** counterexamples at `K ≤ 12`. Evidence, not proof.
3. Nothing is claimed for `K > 12`, or for alphabets larger than binary.
4. The corrected edge-type obligation is **stated** and **identified** with
   `BBTEulerian.UniqueEulerianCycle`
   (`Issue94TW1EdgeType.edgeTypeUnique_iff_uniqueEulerianCycle`) but is **not
   proved**. Neither is `BBTLadder.LadderVertexCycle`, nor
   `BBTEulerian.EulerianCycleObstruction`.
5. `BBTEulerian.EulerianCycleObstruction` (the `hPevzner` hypothesis of
   `PopulationUniqueness`) is **untouched and still without an inhabitant**. No
   proxy assumption of that shape was introduced or relied on.
