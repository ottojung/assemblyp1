# #89: the selected-support invariant for the one-cycle route

_Status: the target statement is isolated and formalized
(`AssemblyP1/BBTSupportInvariant.lean`); the reduction from it to `thm:BBT` is
**proved**; the three remaining mathematical inputs are **not** proved.  The two
tempting strengthenings of the invariant are **refuted**, one of them
kernel-checked._

## 1. Where this starts

`AssemblyP1.BBTEulerianSearch` (commit `ba91723`, integrated here) rephrases the
first clause of `thm:BBT` on the **successor** of a traversal rather than on the
presentation, and proves the equivalence in the kernel:

```text
UniqueAt hG L S
  <->  every bijective, FibrePreserving, OneCycle θ has OrbitVertexEq θ
```

(`uniqueAt_iff_orbit`, via `vertexCycleEq_iff_orbit` and
`isEulerianCycle_of_oneCycle`.)  So the endgame is exactly

```text
Bijective θ, FibrePreserving θ, OneCycle θ, and NOT OrbitVertexEq θ
    ==>  a triple repeat or an interleaved pair of maximal repeats,
         both of length >= L-1
```

which is the two-clause `BBTEulerian.LongObstruction`.  `P2` forbids exactly
that, so this closes `thm:BBT`.

## 2. What must *not* be proved

Three tempting strengthenings are all false, and it is worth recording exactly
why, because each of them looks like the natural next step.

| Claim | Status | Witness |
| --- | --- | --- |
| Interleaved doubled `(L-1)`-mers extend to two interleaved maximal repeats | **false** | `BBTChords.raw_node_crossing_not_maximal` (kernel-checked, `S = 00101`, `L = 3`); `S = AABCBCBAB` in the audit note |
| A good `θ` has crossing-free support, i.e. no selected crossing | **false** | `S = 00101`, `L = 3`: the rematching swapping the doubled `(L-1)`-mers `01`, `10` at the interleaving starts `1 < 2 < 3 < 4` gives the single cycle `0, 3, 2, 1, 4`, whose `(L-1)`-mer orbit is the truth's `00, 01, 10, 01, 10` |
| Hence `θ = nextPos` | **false** | same instance; kernel-checked as `harmless_selected_crossing_00101` |

The third is a consequence of the second, and both were tempting because the
first one fails in a way that looks like a gap rather than a falsity: the raw
lemma fails in **768 of the 1024** primitive `(word, K)` pairs with `G ≤ 8` and
`K ≤ 3` that have
interleaved doubled `(L-1)`-mers at all.

## 3. The invariant that survives

Everything must be phrased about the **deviation set**

```lean
BBTSupport.deviation θ = { x | θ x ≠ nextPos x }
```

--- the starts where the traversal actually departs from the truth --- and about
`¬OrbitVertexEq`, the statement that the departure changes the *spelled* vertex
cycle.  `deviation_ne_empty_of_not_orbitVertexEq` is proved: a one-cycle that
spells something other than the truth must deviate somewhere.  This is the
propositional content of "the transposition has a nontrivial effect", which the
`Arratia et al.` descent has to carry along.

The dichotomy itself (`BBTSupport.SupportDichotomy`) is:

```text
bad θ  ==>  (T) a vertex of multiplicity >= 3 is rematched
        or  (I) two interleaved doubled (L-1)-mers are both rematched
```

These are the two move types of *Arratia, Bogomolnyi, Brzuska, and Tse*, *Spectral
techniques in graph combinatorics* (1996), Theorem 6, in **selected** form.
Exhaustive search over primitive binary circular words, enumerating circuits
rather than `G!` presentations (`scripts/verify_support_dichotomy_89.py`):

```text
G <= 8, K = L-1 <= 3
  one-cycle fibre-preserving θ        : 50510
  ...of which good (truth's own cycle): 33430
  ...good AND with a selected crossing:   528    <- refutes the strengthening
  bad θ (wrong spelled vertex cycle)   : 17080
  ...NOT explained by (T) or (I)      :     0    <- dichotomy holds
```

## 4. What is proved, and what is left

`AssemblyP1/BBTSupportInvariant.lean` proves

* `deviation_eq_empty_iff`, `deviation_ne_empty_of_not_orbitVertexEq`,
  `deviation_is_a_choice_site` — nontriviality of a traversal;
* `interleaved_iff` — `SelectedInterleaved`'s interleaving clause **is** the
  source-faithful `SourceFaithfulIs.Interleaved` (an `Iff`, so the rephrasing for
  the sake of decidability weakens nothing);
* `orbitVertexEq_of_dichotomy` and `uniqueAt_of_dichotomy` — **the reduction**:
  the whole `#89` Eulerian-cycle gap follows from the three remaining inputs,
  and nothing else.  This is proved, so the residual content is exactly:

| Remaining `Prop` | Content |
| --- | --- |
| `SupportDichotomy` | a bad `θ` forces a selected three-way or selected interleaved configuration |
| `SelectedTriple_obstruction` | three occurrences of one `(L-1)`-mer extend *simultaneously* to a maximal triple repeat of length `≥ L-1` |
| `SelectedInterleaved_obstruction` | two *selected* interleaved doubled `(L-1)`-mers extend to two interleaved maximal repeats of length `≥ L-1` |

The last two are the maximal-extension content; `BBTMaximalExtension` currently
supplies maximal repeats for **pairs** (`maximalRepeat_of_branch`) and not for
triples, and `interleaved_disjunct` / `triple_disjunct` do the assembly.

Kernel-checked evidence: `supportDichotomy_00101` decides the dichotomy for
*every* `θ` on `Fin 5`, and `harmless_selected_crossing_00101` exhibits the
good `θ` with a selected crossing.  Both are `by decide`.  `#print axioms` on
every declaration in the module reports only `propext`, `Classical.choice`,
`Quot.sound`; no `sorryAx`.

## 5. The `Arratia` descent, and the missing case split

Per the source proof, for a nontrivial transposition using interleaved repeated
`t`-tuples `i < i' < j < j'`:

* if both pairs can shift left, shift both one step --- nontriviality is
  preserved;
* iterate;
* if one pair becomes leftmost first, keep shifting the other until either both
  are leftmost, or an endpoint collides (`j = i'`, `i' = i`, or `j' = j`);
* a collision yields a **three-way** repeated `t`-tuple, and the resulting
  triple-repeat transposition has the **same effect** as the original
  interleaved one, hence stays nontrivial.

The formal state must therefore carry the transposition's **effect** and its
**nontriviality**, not merely the raw chord configuration.  That is exactly what
`¬OrbitVertexEq` and `deviation θ ≠ ∅` supply at the label-orbit level, and they
are now in place.  What is not yet formalized is the descent itself: the
shift-left step, the termination measure, and the collision case split that
converts an interleaved pair into a three-way repeat while preserving the
effect.  That is the concrete shape of the remaining work.

## 6. Incidental repairs

Three modules had been merged without ever compiling; the `BA91723` docstring
itself warns about exactly this for an earlier file.

* `BBTMaximalExtension.lean` mentions `a b : Fin G` without binding them;
* `BBTEulerianSearch.lean` mentions `θ` without binding it, and was not imported
  by `AssemblyP1.lean`, so `lake build` never checked it;
* `BBTEulerianSearch.lean` had no `Decidable` instance for `FibrePreserving`,
  `OneCycle`, or `OrbitVertexEq`, which made the `decide` evidence impossible to
  state.
