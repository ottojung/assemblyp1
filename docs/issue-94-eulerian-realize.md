# Issue #89 / board 94, front `94real`: the converse bridge is closed

Branch `proof/94-eulerian-realize`. Module
`AssemblyP1/Issue94EulerianRealize.lean`. Namespace
`AssemblyP1.Issue94Realize`.

This note records what the front was asked and what it produced. It closes the
packet left open in `docs/issue-94-obstruction-equiv.md` §3 ("Whether *every*
`EulerianCycle σ` is the pull-back of some `Matching` … **not settled here**").
**The answer is yes**, and the extra condition that repairs the construction is
exactly the `traverses` clause of `EulerianCycle` — no more.

Nothing here is a solution of issue #89; `BBTUniqueAt` is still the external
`thm:BBT` and is still the single remaining mathematical input. What changes is
that it is now needed in exactly its source form.

## 1. The gap, and the reduction that made it decidable

`BBT94.ObstructionFromBBT L` (`BBTUniqueAt L → EulerianCycleObstruction L`) was
the open `Prop`. The natural route — realize the Eulerian-cycle listing `σ` as
the pull-back of some equal-`L`-spectrum matching — first requires knowing
*which* candidate word to use.

**The candidate is forced.** `eq_of_window_eq`: if `window hG E s = window hG S
(σ s)` then `E s = S (σ s)`, by offset `0`. So the only possible candidate is

```lean
traversalRead S σ  =  fun s => S (σ s)
```

and the whole question collapses to a single statement about `σ`:

> does the complete `L`-window of `traversalRead S σ` at `s` equal the complete
> `L`-window of `S` at `σ s`, for every `s` and every `d < L`?

## 2. The guardrail, and why the prior refutation still stands

`docs/issue-94-obstruction-equiv.md` §3 records that the killed front `94d4`'s
`readOff` construction is false, and instructs that it not be resurrected. It is
not resurrected here: `traversalRead` **is** that read-off, and the module proves
the refutation again, verbatim, at the same named instance.

| what | where | status |
|---|---|---|
| the read-off with no hypothesis on `σ` is `decide`-false | `traversalRead_window_refuted`, `traversalRead_window_refuted_instance` (`S = 0001`, `σ = (2 3)`, `G = 4`, `L = 3`) | kernel-checked |
| **that instance is not an `EulerianCycle`** | `not_eulerianCycle_refuted_instance` | kernel-checked |
| the window agreement holds for **every** `EulerianCycle` at `G = 4`, `L = 3` | `traversalRead_window_of_eulerianCycle_small` (`decide`, all `2⁴` words × all `4!` permutations) | kernel-checked |

So `BBT94.exists_matching_pullback_refuted` — *no* `Matching` has `(2 3)` as its
pull-back — remains true and is not contradicted: `(2 3)` is not an
`EulerianCycle`. The difference between the two statements is the hypothesis,
and §3 below shows the hypothesis is exactly what the proof consumes.

## 3. The construction lemma

`window_traversalRead_of_traverses`: at `2 ≤ L`, the **`traverses` clause alone**
gives the complete window agreement.

*Proof.* Fix `s`, and write `A_j (x) = cyc hG S ((σ (rotAdd hG j s)).val + x)`:
the truth's symbols read from the `j`-th start of the listing, at offset `x`.
`traverses` at `i := rotAdd hG j s` says exactly

> `A_{j+1} (x) = A_j (x + 1)` for every `x < L - 1`,

because the two `(L-1)`-mers it equates are `σ (nextPos i)` and `nextPos (σ i)`.
Hence `A_q (0) = A_{q-1} (1) = A_{q-2} (2) = … = A_0 (q)`, and the offsets used
are `0, 1, …, q - 1`, all in `Fin (L - 1)` because `q ≤ L - 1`. Taking
`q = j = d.val` reads off `S (σ (rotAdd hG d.val s)) = cyc hG S ((σ s).val +
d.val)`, i.e. offset `d` of the two windows.

The `single` clause, `Ukkonen`, `LongObstruction`, `P2` and `BBT` are not used
anywhere in the lemma. Consequences, all kernel-checked:

| statement | meaning |
|---|---|
| `matching_traversalRead_of_traverses` | `traversalRead S σ` is matched by `σ.symm` |
| `eulerianCycle_realized` | every `EulerianCycle σ` **is** the pull-back of a `Matching`, with the pull-back equation in the shape `BBTCondense.pullback_window` consumes |
| `eulerianCycle_specCount_eq` | the candidate has the truth's complete `L`-spectrum |
| `vertexCycleEq_of_RotEquiv_traversalRead` | a candidate which is a rotation of the truth forces `VertexCycleEq σ (refl)` |

## 4. The converse bridge

`obstruction_of_BBTUniqueAt`: at `2 ≤ L`,
`BBTUniqueAt L → EulerianCycleObstruction L`.

*Proof.* Let `σ` be an `EulerianCycle` of an `Ukkonen` truth `S`. By §3 the
traversal read-off is matched by `σ.symm`, hence has the truth's complete
`L`-spectrum; being a word of length `K` it is a candidate of the same class.
`BBTCompleteSpectrumUniqueness` demands `Ukkonen` of the **truth only** (the
invariant noted at the end of `docs/issue-94-obstruction-equiv.md`), so it
applies and returns `RotEquiv (traversalRead S σ) S`; by
`vertexCycleEq_of_RotEquiv_traversalRead` this forces `VertexCycleEq σ (refl)`,
the first disjunct. The theorem concludes the disjunction, so the `Ukkonen`
hypothesis discharges the second.

Consequences:

* `obstructionOfBBT_iff_of_le`: `BBT94.ObstructionFromBBT` is inhabited at `2 ≤ L`
  exactly when §4's statement is — the residual of #89 is now settled *modulo*
  `thm:BBT`, not modulo any Eulerian-touring lemma of this project's own;
* `obstruction_iff_bbtUniqueAt`: at `2 ≤ L`,
  **`EulerianCycleObstruction L ↔ BBTUniqueAt L`**, the reverse direction being
  the library's `BBTEulerian.bbtUniqueAt_of_obstruction`.

## 5. What this does *not* do

* It does not prove `BBTUniqueAt`. Per
  `docs/best-tw1-attribution-94.md`, `EulerianCycleObstruction` is a board
  construction and not an imported Pevzner/BBT statement; the equivalence in §4
  says the board construction coincides, at `2 ≤ L`, with the project-formatted
  `thm:BBT`, and the endpoint of #89 still terminates in one external input.
* It does not touch `hPevzner`, `EulerianCycleObstruction`, `BBTUniqueAt`,
  `Matching`, `pullback`, `window`, `vtx`, `Ukkonen` or `RotEquiv`. No definition
  was changed to make a theorem provable.
* It contains no `axiom`, `sorry` or `admit`; §7 of the module is the
  `#print axioms` audit and reports only `propext`, `Classical.choice`,
  `Quot.sound`.

## 6. Finite evidence

`scripts/verify_eulerian_realize_94.py` censuses the *exact* hypothesis of §3
(`traverses` alone, not `single`), for every `1 ≤ G`, `2 ≤ L` in range, binary
alphabet, all words and all permutations:

```
$ python3 scripts/verify_eulerian_realize_94.py 6 6
traverses-only instances: 17908 (of which Eulerian cycles: 17908)
window-agreement violations: 0
```

No violations; and no instance satisfying `traverses` but not `single` was found
up to `G = 8`, `L = 4`, so no claim is made about whether `single` is
redundant — the proof simply does not use it. This is evidence only; §3 is the
proof, and no completeness claim is made beyond the ranges searched.

## 7. Build note (concrete blocker, unrelated to this front)

A full `lake build` at this HEAD fails on two **pre-existing** heavy modules,
`AssemblyP1.Issue94Transposition` and `AssemblyP1.Issue94OrbitSearch`, both with
`Lean exited with code 137` (OOM kill) at 340 s and 1200 s respectively. Every
other module builds. `AssemblyP1.Issue94EulerianRealize` was verified with a
narrow build,

```
lake build AssemblyP1.Issue94Realize      # 6.3 s, clean
```

and its dependencies (`BBTEulerian`, `Issue94EulerianTheta`,
`Issue94ObstructionEquiv`) replay without recompilation. This is recorded as an
execution fact, not converted into scheduling policy.

## 8. Source fidelity

No modelling decision was changed. `EulerianCycle`, `VertexCycleEq`, `Matching`,
`pullback`, `window`, `nodeWindow`, `vtx`, `cyc`, `rotAdd`, `nextPos`, `Ukkonen`,
`LongObstruction`, `BBTCompleteSpectrumUniqueness`, `BBTUniqueAt`, `RotEquiv` and
`VisitsAll` are used exactly as `BBTEulerian.lean`, `P2.lean`, `BBTChords.lean`
and `BBTCondense.lean` state them. The candidate word `traversalRead S σ` is
derived from the traversal's own consistency (`traverses`), not assumed.