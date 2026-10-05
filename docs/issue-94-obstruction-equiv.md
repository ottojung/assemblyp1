# Issue #89 / board 94, front `94bbt` (recovery): auditing the residual hypothesis of the endpoint

Branch `proof/94-eulerian-obstruction`. Module:
`AssemblyP1/Issue94ObstructionEquiv.lean`. Namespace `AssemblyP1.BBT94`.

This note records what the front examined, what it kept, what it rejected and
what it could **not** establish. Nothing here is a solution of issue #89, and
nothing here is progress toward an inhabitant of the residual.

## 1. The gap, re-derived at this HEAD

`AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation`
(and `..._same_length`, `population_tie_implies_rotation`) are the endpoint of
#89. Each carries, besides `2 ≤ L`, one explicit hypothesis

```lean
hPevzner : AssemblyP1.BBTEulerian.EulerianCycleObstruction (α := α) L
```

`EulerianCycleObstruction` is a `def`, not an `axiom`, and this repository
contains no user `axiom`. `AssemblyP1.P2.BBTUniqueAt L` is likewise a `def` of
the external theorem `thm:BBT` (Bresler–Bresler–Tse 2013, Thm 3, read at
`K = L - 1`): the complete `L`-spectrum of an `Ukkonen` circular word
determines it up to cyclic rotation, uniformly over genome lengths.

So the endpoint is not provable in this project without importing `thm:BBT`;
the whole content of #89's residual is one inhabitant of that statement.

## 2. The claim that would be worth having

The natural reduction, at `2 ≤ L`, is

```lean
EulerianCycleObstruction L ↔ BBTUniqueAt L
```

**The front half is in the library** (`BBTEulerian.bbtUniqueAt_of_obstruction`,
`EulerianCycleObstruction L → BBTUniqueAt L`), and
`BBTEulerian.uniqueEulerianCycle_of_obstruction` /
`obstruction_of_uniqueEulerianCycle` already identify
`EulerianCycleObstruction` with `UniqueEulerianCycle`.

**The other half is not proved, by this front or by any residue it found.**
It is recorded as the `Prop` `BBT94.ObstructionFromBBT L`
(`BBTUniqueAt L → EulerianCycleObstruction L`) and left there, with no `axiom`,
`sorry` or `admit` anywhere in the library.

## 3. What was rejected, and why: the residue's "every permutation is a matching pull-back"

The residue left by the killed front `94d4` (committed unverified at
`14a80b1`) claimed, as its §1 and as the whole engine of the converse:

> every bijection `σ` of the starts is the pull-back of a `Matching`, with no
> hypothesis on `σ` — in particular no `EulerianCycle`.

with the read-off candidate `E s = S (σ s)` and the claim that the complete
`L`-window of `E` at `s` is "by construction" that of `S` at `σ s`.

**This is false, and it is `decide`-closed.** `window hG (readOff S σ) s d`
reads `S` at `σ ((s + d) mod G)`, whereas `window hG S (σ s) d` reads `S` at
`(σ s + d) mod G`; the two agree only when `σ` carries the shift. Two
kernel-checked refutations are in the module:

* `BBT94.window_readOff_refuted` — the engine itself, refuted at `S = 0001`,
  `G = 4`, `L = 3`, `σ = (2 3)`;
* `BBT94.exists_matching_pullback_refuted` — the conclusion, refuted at the
  same instance: **no** `Matching` whatsoever has `(2 3)` as its pull-back. A
  matching with that pull-back would have to present the truth's window `(0,0,1)`
  at candidate position `1` (so the candidate's symbol at position `2` is `0`)
  and the truth's window `(1,0,0)` at candidate position `2` (so the same
  symbol is `1`).

Two further defects of the residue, for the record:

* the repair it applied to its own elaboration failure passed through
  `equiv_apply_eq : ∀ σ x, σ x = x`, i.e. "an `Equiv` of `Fin G` is the
  identity". This is `decide`-refutable (`BBT94.equiv_identity_refuted`) and
  cannot have been proved; had it been, the residue's §1 would have been
  *vacuous* (every `σ` matched by `E = S`) rather than false.
* the committed version did not elaborate at all: the `Matching` step closed
  `window S r = window (readOff S σ) (σ.symm r)` with a term whose statement
  still mentioned `σ (σ.symm r)`, and `obstruction_iff_bbtUniqueAt` had its two
  implications swapped (`EulerianCycleObstruction → BBTUniqueAt` is the
  library's direction, not the new one).

So the route is closed for a substantive reason, not for want of elaboration
effort: the structural premise is false.

### The direction that *is* available

`Issue94EulerianTheta.theta_of_same_spectrum_is_one_cycle` (i.e.
`BBTEulerian.pullback_isEulerianCycle`): a `Matching` pull-back **is** an
`EulerianCycle`, together with the window agreement. So
`Matching`-pull-backs ⊆ `EulerianCycle`s. That is the direction the converse
needs and the only one available.

Whether *every* `EulerianCycle σ` is the pull-back of some `Matching` is a
narrower question than the residue's claim and is **not settled here**. A
`decide`-equivalent scan at `G = 4`, `L = 3`, binary alphabet (all `2⁴` words ×
all `4!` permutations, checking `EulerianCycle` against the existence of a
candidate word `E` with `window S r = window E (σ r)` for all `r`) found **no**
counterexample; this is evidence only. Constructing such a candidate requires
reading the traversal supplied by the `single` clause and rebuilding an
`L`-window sequence from it — a different word from `readOff S σ`, which reads
the truth at `σ`-permuted positions, which the `single` clause does not
control. This is the concrete next packet for the converse, and it is
distinct from the transposition-theorem line of work.

## 4. What this module contains

| class | statement | status |
|---|---|---|
| kernel-checked | `window_readOff_refuted`, `equiv_identity_refuted`, `exists_matching_pullback_refuted` | new; refutations of the residue's engine and conclusion |
| kernel-checked | `bbtUniqueAt_of_obstruction'` (restates the library direction) | proved |
| kernel-checked | `bbtUniqueAt_iff_residual`, `BBTResidual` | proved; decomposition of `BBTUniqueAt L` into the independent per-genome-length family |
| **open** | `ObstructionFromBBT L`, i.e. `BBTUniqueAt L → EulerianCycleObstruction L` | **not proved** |
| **open** | an inhabitant of `BBTUniqueAt` / `EulerianCycleObstruction` / `hPevzner` | **missing** |

§4 of the module is the `#print axioms` audit of all of the above: no
`sorryAx`, no user axiom.

## 5. Rejected: `bbt94/FiniteBase.lean`

The second residue file claimed `decide`-checked base cases of
`UniqueEulerianCycle` at `L = 3` (`K ≤ 7`) and `L = 4` (`K ≤ 5`) over the
binary alphabet. It was re-checked independently for this front and rejected;
both of its failure modes reproduce:

1. its `Decidable (Ukkonen …)` instance does not synthesise — verified directly
   in this session (`unfold Ukkonen; infer_instance` fails, the source-faithful
   repeat predicates having no instance-decidable form; `BBTChords`'s
   `InterleavedStarts` needs an explicit `unfold … infer_instance` for the same
   reason);
2. every theorem then ends in `of_decide_eq_true rfl` *after* `intro`-ing the
   word and the permutation, so the goal is `VertexCycleEq hK 3 S σ (refl)`,
   not `decide … = true`: a type error. No search ever ran.

So the "finite base case" claim was vacuous. It is not carried forward. The
residue itself remains in the history at `14a80b1`. Genuine (but unbounded)
finite evidence is instead available from
`scripts/verify_eulerian_cycle_uniqueness_89.py`, used by earlier fronts; ranges
searched there are stated in the front's own notes, and no completeness claim is
made beyond them.

## 6. Source fidelity

No modelling decision was changed, and no definition was touched:
`EulerianCycleObstruction`, `BBTUniqueAt`, `Ukkonen`, `Matching`, `vtx`,
`EulerianCycle` and `VertexCycleEq` are used exactly as `BBTEulerian.lean`,
`P2.lean`, `BBTChords.lean` and `BBTCondense.lean` state them. The refuted
claim was rejected because it is false about those definitions as written, not
because the definitions were inconvenient.

Note recorded for whoever attacks the converse:
`BBTCompleteSpectrumUniqueness` demands `Ukkonen` of the **truth only**
(`∀ E, Ukkonen hK L S → …`), never of the candidate. That is what makes
`theta_of_same_spectrum_is_one_cycle` usable with an arbitrary equal-spectrum
competitor, and it is a genuine invariant of the statement as written.