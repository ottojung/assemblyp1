# `#89`: the support-permutation route --- master theorem, interface, and an
# obstruction to finishing it

Branch: `agent/issue89-alt-final2`.  Extends the WIP of `dae70b8`
(`AssemblyP1.BBTSupportChords`).

## 1. What the route is

`AssemblyP1.BBTSupportChords.support_dichotomy` is the combinatorial core of
`AssemblyP1.BBTEulerian.EulerianCycleObstruction` in the shape

```text
   f ≠ id  ⟹  (W) some label occurs at three distinct positions
              or (X) two doubled pairs whose four endpoints interleave.
```

The object `f` is not a new invention:
`AssemblyP1.BBTUniqueEulerian.AltF_vtx` says that the `traverses` clause of
`EulerianCycle hG L S σ` is exactly "`f = AltF hG σ` preserves the `(L-1)`-mer
at every start", `AltF_bijective` says `f` is a permutation, and
`Succ_eq_altF` says the successor of the alternative traversal is
`f ∘ nextPos`, so the `single` clause is
`VisitsAll (fun x => f (nextPos hG x)) (origin hG)`.  Hence the abstract
dichotomy applies with `W = vtx hG L S` and no new word layer, and the two
disjuncts are statements about **real** starts of the truth:

* **(W)** three distinct starts spelling the same `(L-1)`-mer;
* **(X)** two *doubled* `(L-1)`-mer pairs whose four starts interleave.

## 2. The master theorem (UNVERIFIED at this checkpoint -- see the status table)

`AssemblyP1.BBTSupportEulerian.vertexCycleEq_of_noTriple_noCross`:

```text
   σ is an Eulerian cycle
   ∧ ¬ (three distinct starts spell the same `(L-1)`-mer)
   ∧ ¬ (two doubled `(L-1)`-mer pairs interleave)
   ⟹ the vertex cycle of σ is a rotation of the truth's.
```

The proof is the short one:

1. `support_dichotomy` (`eq_id_of_noTriple_noCross`) forces
   `AltF hG σ = id`;
2. `Succ_eq_altF` then gives `Succ hG σ = nextPos hG`, i.e. `σ` *commutes with
   the generator* of the cyclic group of starts; a permutation commuting with
   the generator is a power of it
   (`eq_rotAdd_of_comm`: `σ i = rotAdd hG (σ (origin hG)).val i`);
3. a rotation of the circle gives `VertexCycleEq` at `k = σ (origin hG)`.

Step 2 is where the whole combinatorial content sits, and it is worth stating
plainly: **the vertex cycle of an alternative Eulerian cycle is a rotation of
the truth's as soon as the support permutation has no wide label and no
crossing pair.**  Nothing about repeats, spectra or graphs enters.

## 3. The interface theorem (UNVERIFIED at this checkpoint -- see the status table)

`obstruction_of_wordLevel` and `obstruction_of_P2_wordLevel` conclude
`EulerianCycleObstruction` --- the single hypothesis of
`AssemblyP1.PopulationUniqueness` --- from two **word-level** statements, each
about a single `(L-1)`-mer (resp. a single pair of them) of an `Ukkonen` word,
with no `EulerianCycle` anywhere in them:

* `NoTripleVertex` --- Lemma 1 of `AssemblyP1.BBTUniqueEulerian`.  This is the
  three-copy version of the two-sided maximal extension already proved in
  `AssemblyP1.P2RepeatResidual.maximal_extension_of_repeated`.  **Not proved
  here.**
* `NoCrossedDoubledPairs` --- Lemma 2 of `AssemblyP1.BBTUniqueEulerian`.
  **False**, see §4.

So the residual of `#89` is now stated as a two-clause word-level problem, and
the combinatorial part of the reduction is closed.

## 4. The obstruction: the crossing clause is false (`AssemblyP1.BBTSupportCrossing`)

The naive proof of the crossing clause is "extend each doubled pair maximally,
then read off the interleaving".  The last step is false.  The two maximal
extensions are shifted left by *different* amounts `ℓ₁ ≠ ℓ₂` --- the maximal
left extensions of the two pairs --- and interleaving on the circle is
invariant only under a *common* rotation.  The two pairs can even lie inside
**one** maximal repeat.

Kernel-checked instance (`BBTSupportCrossing`, all `by decide`):

| statement | content |
| --- | --- |
| `S5_is_P2` | `S = 00101`, `G = 5`, `L = 3` satisfies `P2` |
| `crossed` | the pairs `{1, 3}` and `{2, 4}` are doubled `2`-mers and interleave |
| `S5_primitive` | `S` is primitive, so primitivity is not the escape |
| `not_longObstruction` | no maximal triple repeat of length `≥ 2`, and no two interleaved maximal repeats both of length `≥ 2` |
| `collapse_oneMaximalRepeat` | the only maximal repeat of length `≥ 2` is `(3, 1, 3)`, and the pair `{2, 4}` carries no maximal repeat at its own starts |

`scripts/verify_support_crossing_collapse_89.py` searches exhaustively: over all
primitive binary words of length `≤ 7` and all `K`, 92 instances have a
crossing pair and `¬ LongObstruction`; the smallest is `S = 00101`, `G = 5`,
`K = 2`.  (Evidence, not a proved completeness statement.)

`S = 00101` is *not* a counterexample to `thm:BBT`.  Its only maximal repeat of
length `≥ 2` carries both crossing pairs, the involution `(1 3)(2 4)` on the
doubled pairs does give a genuine alternative Eulerian cycle (its successor is
the `5`-cycle `0 → 3 → 2 → 1 → 4 → 0`), and that cycle has the same vertex
cycle as the truth.  The collapse is **benign**; it has to be discharged, not
refuted.

## 5. The open core

What is left is a *block* statement, not a pair statement: for a maximal repeat
`(e, p, q)` and every transposition pair `(p + t, q + t)` of the support of
`f = AltF hG σ` inside it, the block cut must preserve the vertex sequence, so
that the support permutation moves whole blocks and the alternative traversal
induces the truth's vertex cycle.  The same object is reached independently on
`agent/issue89-rematch-final2` as `BBTLadder.LadderRotationGap`; the two
routes share this core and neither has closed it.  Consequently
`hPevzner` is still a hypothesis of `AssemblyP1.PopulationUniqueness`, and this
commit does not remove it.

Status of the pieces in this branch:

| module | status |
| --- | --- |
| `AssemblyP1.BBTSupportChords` | **UNVERIFIED** (drafted, never built) |
| `AssemblyP1.BBTSupportEulerian` | **UNVERIFIED** (drafted, never built) |
| `AssemblyP1.BBTSupportCrossing` | **UNVERIFIED** (drafted, never built) |
| `NoTripleVertex` for `Ukkonen` words | **open** (three-copy maximal extension) |
| block statement for the collapse regime | **open** |
| `EulerianCycleObstruction` | **open**; consequence of the two rows above |

## Status correction (independent audit pass)

The three modules above were **drafted but never compiled**: no `lake build`
in this worktree produced a single `AssemblyP1/*.olean` (the worktree's
`.lake/packages` is a symlink to a shared checkout, and the build never got
past dependency setup).  The earlier revision of this file described them as
"kernel-checked"; that was wrong and is corrected here.  Treat every claim
above about them as a *proof sketch*, not as a verified result, until a
`lake build` actually passes.

What **is** durable in this branch is the computational evidence, which
re-runs in seconds and is not a completeness claim:

| script | range | result |
| --- | --- | --- |
| `scripts/verify_support_chord_dichotomy_89.py` | `G ≤ 14`, binary-independent (all set partitions of the circle into classes of size ≤ 2) | 0 counterexamples; at `G = 14`, 97 724 419 nontrivial label-preserving permutations tested, **0** with `f ∘ ρ` a `G`-cycle outside the crossing regime |
| `scripts/verify_crossing_collapse_89.py` | `G ≤ 9`, binary words, all `K`, all single-circuit traversals | 392 `USABLE` rows and 2416 `COLLAPSE` rows; **all** 2416 collapse rows have the same vertex cycle as the truth, 0 with a different one |

The second row is the evidence for the collapse/ladder lemma: in the collapse
regime the alternative traversal always normalises to the truth's vertex
cycle, so non-`VertexCycleEq` forces the interleaving-extension case.  A
finite search is evidence, not a proved completeness statement.
