# The edge-type obligation on `D` (board 94, front 94a10)

Branch `94-tw2-edgetype`, base `7d50132`. Code:
`AssemblyP1/Issue94TW1EdgeType.lean`. Front report:
`/workspace/BOARD94-TW2-EDGETYPE.md`.

This note is about the three steps board issue 94 directed, in order, plus the
two results that are now settled and the three that are not.

---

## 1. Step 1: the "208 instances with a simple `D`" claim is an evaluator bug

Front 94e7's handoff said the search found **208** instances at `K ≤ 9` with a
**simple** `D` and `t_w > 1`, and read that as evidence that the corrected
obligation needs a genuinely new idea, not just a parallel-edge division.

**The count is wrong.** `hasParallelEdges` in `scripts/verify_tw1_94.js` read:

```js
function hasParallelEdges(edges) {
  for (let u = 0; u < edges.length; u++) {
    const seen = new Set();
    for (let v = 0; v < edges[u].length; v++) {
      const k = edges[u][v][0] + '>' + edges[u][v][1];
      if (seen.has(k)) return true;
      seen.add(k);
    }
  }
  return false;
}
```

`edges` is an array of `[tail, head]` **pairs**, not an adjacency structure. The
outer loop therefore runs over the `K` edges, and for each of them the inner
loop runs exactly twice — over `edges[u][0]` and `edges[u][1]`, which are the
tail and the head of the *same* edge. `seen` is a fresh `Set` each time and
receives a single key, so the predicate is **identically `false` for every
input**.

That is why 208 appeared. 548 + 208 = 756, and 756 is the number of `K ≤ 9`
primitive `(S, L)` `Ukkonen` instances in the histogram's two "simple" rows —
i.e. *all* of them were classified simple.

### The corrected predicate, and what the sweep says

Group the edges by tail and then by head, and report a parallel pair iff some
head occurs twice under one tail. With that, plus a **self-check on
hand-built graphs** (a witness taken from the kernel-checked refutation
instance `S = 10100`, `L = 3`, whose edges `1` and `4` are both `01 → 10`; a
two-edges-different-heads graph; a two-edges-same-head-different-tails graph)
that the old version fails:

| range | instances with `t_w > 1` | of those with a **simple** `D` |
| --- | --- | --- |
| `K ≤ 9`  | 562  | **0** |
| `K ≤ 10` | 630  | **0** |
| `K ≤ 11` | 2214 | **0** |
| `K ≤ 12` | 5142 | **0** |

Reproduce the first row with `node scripts/verify_tw1_94.js 9`:

```
checked 4312 primitive (S,L) Ukkonen instances, 562 with t_w != 1, 0 with MORE THAN ONE edge-type circuit orbit
edge-type-orbit histogram: [[1,4312]]
parallel-edges / t_w / edge-type-orbits joint histogram:
  par/t_w=>1/orbits=1 : 562
  simple/t_w=1/orbits=1 : 3750
```

**So the corrected obligation does *not* need a new idea.** The parallel-edge
division is the whole repair, over every range searched. "Simple `D` implies
`t_w = 1`" is *not refuted* by this; it is *unexamined* by it. This is
**evidence, not proof** — the completeness of the sweep over those ranges is
not proved, and nothing is claimed for `K > 12` or for a larger alphabet. It is
used here only to kill a false claim and to motivate a design decision, never
as a premise of any theorem.

The correction is recorded in the `Issue94TW1` module docstring and in
`docs/tw1-refutation-94.md`, and the buggy predicate and its self-check are
replaced in `scripts/verify_tw1_94.js`.

## 2. Step 2: un-condensed, on the vertex cycle — and the obligation is *not new*

BBT's Theorem 3 is phrased about the **condensed** sequence graph, and front
94e7 left open whether the corrected obligation should be stated there. The
answer is **no**, and the reason is that under the edge-type convention the
edge-type circuit orbits of `D` and the vertex cycles of `D` are *the same
object*. That is a kernel-checkable fact, not a remark.

`D(S, L)` has vertex `vtx r` at start `r` and edge `r : vtx r → vtx (nextPos r)`.
So the edge type of `r` is exactly the pair `(vtx r, vtx (nextPos r))`
(`EdgeTypeOf`), and an edge-type Eulerian circuit is a cyclic sequence of such
pairs. Then:

* `edgeTypeOf_eq_iff`: two starts have the same edge type **iff** they carry the
  same `(L-1)`-mer and the same successor `(L-1)`-mer. So the edge-type word
  determines the vertex word position by position.
* `VertexCycleEq_iff_EType_cycle`: for cycles `σ, τ`,

  ```text
    VertexCycleEq hK L S σ τ   <->   the edge-type words of σ and τ agree up to rotation
  ```

  proved in both directions (`VertexCycleEq_of_EType_cycle`,
  `EType_cycle_of_VertexCycleEq`). The first is a projection onto `Prod.fst`;
  the second composes `VertexCycleEq`'s witness at `i` and at `nextPos i`.

Note also that front 94e7's `VStep` **already is** the edge-type relation — it
is `∃ r' ∈ T, vtx r' = u ∧ vtx (nextPos r') = v`, so parallel edges are never
distinguished. Reusing it unchanged imports the convention for free.

**Consequence.** The corrected obligation is stated as
`EdgeTypeUnique L` and `edgeTypeUnique_iff_uniqueEulerianCycle` proves

```text
  EdgeTypeUnique L  <->  BBTEulerian.UniqueEulerianCycle L
```

so the board's "corrected obligation" is the statement the tree **already
has**, not a new `Prop` and not a new open problem. Condensing would build a
second formalisation of a statement already present, on objects
(`BBTCondense.Branch`, `branchVerts`, `branchStarts`, `Unambiguous`) that play
no part in the conclusion.

Kernel-checked at the refutation instance: `T1_T2_same_edgeTypes` — the two
in-arborescences `T1`, `T2` of front 94e7 are different `Finset`s of starts but
carry the **same** edge types edge by edge (start `1` of `T1` is matched by
start `4` of `T2`). That is why `not_UniqueInArb_3` is not a refutation of
`thm:BBT`, and it is the smallest instance of the corrected obligation being
the right one.

## 3. Step 3: the interface audit — option (b)

`BBTCrossingCoalesce.CrossingPairsCoalesce L` is inhabited at arbitrary
`[DecidableEq α]` by `Issue94CaseSplit.crossingPairsCoalesce_general` (`d0aa0aa`,
in `7d50132`), and its `2 ≤ L` and `L ≤ K` are **hypotheses of that `def`**.
`BBTLadder.CrossingChordsCoalesce L` does **not** carry them, so the direct
bridge does not typecheck and the bounds must not be smuggled in.

**The out-of-range cases are not vacuous**, so I did not attempt option (a):

* `P2 hG L S` is **satisfied** when `L > G`. Take `G = 2`, `S = (0, 1)`, `L = 3`:
  the first clause of `P2` needs three pairwise distinct starts and the second
  needs four, so both are vacuous on a two-start circle.
* `P2 hG L S` is **satisfied** when `L ≤ 1` on any word with no interleaved
  repeat pair, for the same reason: `IsRepeat` requires `1 ≤ e`, so with
  `L − 2 = 0` the interleaved clause can only fire when there *is* an
  interleaved repeat pair, and there need not be one.

(I did **not** prove either of these two facts in Lean. They are the reason I do
not attempt (a), not a claim in their own right.)

**So: option (b).** The interface is corrected explicitly, with the reason
recorded in the module docstring and at the theorem, and the exact statement
`BBTLadder.LadderVertexCycle` consumes is what is proved:

* `crossingChordsCoalesce_bounded` — `CrossingChordsCoalesce L` restricted to
  `2 ≤ L` and `L ≤ K`, at arbitrary `[DecidableEq α]`, from
  `crossingPairsCoalesce_general` and `BBTLadder.AltF_vtx'` unchanged. The two
  distinctness clauses `a ≠ b` and `c ≠ d` are **derived** from `Interleaved`'s
  own `FourDistinct` conjunct, not assumed.
* `support_blocks_coalesce` — the same, in exactly the shape
  `LadderVertexCycle`'s block condition takes. `LadderVertexCycle`'s context
  already has `P2`, primitivity, `2 ≤ L`, `L ≤ K` and `Ukkonen`, so this is
  immediately usable there.

## 4. `LadderVertexCycle`: the block half is discharged, the global half is not

`BBTLadder.LadderVertexCycle` takes as hypothesis that **every** crossing pair
of support chords of `AltF hK σ` coalesces. `support_blocks_coalesce` now
*derives* exactly that from the hypothesis set `LadderVertexCycle` already
carries. So the block half of `LadderVertexCycle` is **discharged**.

What remains is the global traversal-order step, and it is **not proved**.
`BlocklessLadderVertexCycle` states it with the block hypothesis already
supplied, and `ladderVertexCycle_of_blockless` records the one-line reduction, so
a proof of `BlocklessLadderVertexCycle` closes `LadderVertexCycle` outright.
`BlocklessLadderVertexCycle` has **no inhabitant**, here or anywhere in the tree.
The target is the exact `VertexCycleEq`, not a weakened listing invariant.

A proof would have to show the traversal walks the laminar block structure in
geometric order, from `ladder_of_coalescing` (each block is two rotations of one
pair), `ladder_arc_eq` (a block is vertex-invisible) and
`support_blocks_nonCrossing` (blocks are laminar). The obstacle recorded in
`BBTLadder` is that the tempting intermediate `nextSupport (f x) = f (nextSupport
x)` is **false** (refuted at `G = 10` by `S = 0010010101`, `L = 5`), so the
assembly must be genuinely global.

## 5. The public endpoint

**Not discharged.** `AssemblyP1/PopulationUniqueness.lean` still **retains**
`hPevzner : EulerianCycleObstruction` in

* `population_unique_ML_up_to_rotation` (line 178), and
* `population_unique_ML_up_to_rotation_same_length` (line 231),

and likewise in `population_tie_implies_rotation` (line 261). `BBTEulerian.
EulerianCycleObstruction` still has no inhabitant. Nothing in this front uses or
introduces such a premise.

By §2, `EulerianCycleObstruction` is equivalent to `UniqueEulerianCycle`, which
is equivalent to `EdgeTypeUnique`, which is equivalent to the residual
`BlocklessLadderVertexCycle` block of work. There is now **one** remaining
mathematical statement in this route, not three, and it is stated.

## 6. Validation

`export PATH=/home/lubko/.elan/bin:$PATH`; one build at a time, never
concurrent; no `lake build mathlib`, no `lake update`, no `cache get`; the
`.lake/packages` symlink was read through only.

```
$ lake build AssemblyP1.Issue94TW1EdgeType
✔ [8948/8948] Built AssemblyP1.Issue94TW1EdgeType (2.5s)
Build completed successfully (8948 jobs).

$ lake build --wfail
Build completed successfully (8980 jobs).
```

The full root build **succeeded** on this worktree, with `--wfail`, and the
`#print axioms` block appended to `AssemblyP1.lean` ran **in situ** as part of it
(front 94e7 could not do this; it OOM-killed on `Issue94OrbitSearch`, whose
`.olean` is present here). The axioms audit:

```
sameType_equiv                                does not depend on any axioms
vtx_eq_of_sameType                            does not depend on any axioms
edgeTypeOf_eq_iff                             does not depend on any axioms
EType_eq                                      does not depend on any axioms
VertexCycleEq_of_EType_cycle                  [Quot.sound]
EType_cycle_of_VertexCycleEq                  [Quot.sound]
VertexCycleEq_iff_EType_cycle                 [Quot.sound]
T1_T2_same_edgeTypes                          [propext, Classical.choice, Quot.sound]
edgeTypeUnique_iff_uniqueEulerianCycle         [Quot.sound]
crossingChordsCoalesce_bounded                [propext, Classical.choice, Quot.sound]
support_blocks_coalesce                       [propext, Classical.choice, Quot.sound]
Issue94TW1.not_UniqueInArb_3                  [propext, Classical.choice, Quot.sound]
population_unique_ML_up_to_rotation           [propext, Classical.choice, Quot.sound]
```

The allowed set — `propext`, `Classical.choice`, `Quot.sound` — only. No
`sorryAx`, no new axiom. `grep -nE "\bsorry\b|\badmit\b|native_decide|unsafe|partial"` over
`AssemblyP1/Issue94TW1EdgeType.lean` hits prose in the module docstring only.

## 7. NOT ESTABLISHED

1. `BBTLadder.LadderVertexCycle` — **not proved**. Block half discharged (§4);
   global traversal-order step open.
2. `BlocklessLadderVertexCycle` — **not proved**, no inhabitant.
3. `BBTEulerian.EulerianCycleObstruction` / `UniqueEulerianCycle` /
   `EdgeTypeUnique` — **not proved**; only the identifications between them.
4. The public endpoint — **not discharged**; `hPevzner` still present in
   `PopulationUniqueness`.
5. The unbounded `BBTLadder.CrossingChordsCoalesce L` — **not proved**, and I
   make **no claim it is true**. The `L < 2` and `L > K` halves are untouched
   and unexamined; I have neither a counterexample nor a search over them. Only
   the bounded bridge of §3 is proved.
6. "Simple `D` implies `t_w = 1`" — **neither proved nor refuted**; the
   "208 instances" refutation is withdrawn as an evaluator bug (§1).
7. `InArb` is still not derived from a Matrix-Tree determinant; the bridge
   "`t_w = 1` iff `UniqueInArb`" that front 94e7 recorded as unproved is still
   unproved here.
8. The sweep is evidence only; its completeness over `K ≤ 12` is not proved and
   nothing is claimed for `K > 12` or for larger alphabets.
9. I did **not** verify the two vacuity examples of §3 in Lean; they are stated
   as reasoning, not as theorems.
10. I did **not** touch `hPevzner`, and introduced no proxy assumption of that
    shape.
