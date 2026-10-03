# The interleaved residual of board 94, discharged (front 94a09)

Front `94a09-INTERLEAVED-ADMISSIBLE`, worktree `/workspace/assemblyp1-94-endgame`,
branch `board/94-endgame`.  Full report:
`/workspace/BOARD94-INTERLEAVED-ADMISSIBLE-1120.md`.

## Target

`/workspace/BOARD94-ENDGAME-1000.md` §6 step 4:

```
SelectedInterleaved θ  ⟹  AdmissibleObstruction
```

## Outcome in one paragraph

The statement **as written is false**, and the refutation is kernel-checked at
`S = 0101`, `G = 4`, `L = 3`, `θ = (0 2)(1 3)`: the hypothesis holds
(`selectedInterleaved_0101`) and the conclusion fails
(`not_admissible_0101`, `selectedInterleaved_admissible_unconditional_false`).
That genome is `P2` (`p2_0101_L3`), so `P2` does not rescue the statement, and
`¬ LongObstruction` holds there too (`not_longObstruction_0101`); the single
missing ingredient is primitivity of the word (`not_primitive_0101`).  With
primitivity added --- the hypothesis the endgame already carries, and the one
the `#89` endpoint is stated on --- the residual is **proved** at general `G`
and general `L`, as `selectedInterleaved_admissible`, with the `P2` variant
`selectedInterleaved_admissible_of_P2`.

## The new ingredient

`rightMax_of_doubled`: every doubled `(L-1)`-mer of a primitive genome extends,
**at the same two starts**, to a right-maximal repeat of length `≥ L - 1`.
The genome-side `Preceding` clause of `maximalRepeat_of_branch` is circular
(94d05/94f01) and is not used; in the blocked case the extension is taken to the
*right*, and its boundedness is primitivity
(`RepeatAdapter.not_primitive_of_ge_G_agree`).  This is the right-maximality
the endgame report names as missing, and it keeps the four selected starts in
place, so the interleaving needs no case split.

## Files

* `AssemblyP1/BBTInterleavedAdmissible.lean` --- the statements and proofs
  (in the lake target `AssemblyP1`, imported by `AssemblyP1.lean`).
* `docs/board94-interleaved-admissible-axioms.txt` --- `#print axioms`
  transcript for every claimed theorem; no `sorryAx`, no new `axiom`.

Not proved here: the discharger (`P2 ∧ bad θ ∧ ¬ SelectedTriple ∧
SelectedInterleaved → False`), `SupportDichotomy`, and the `(L-1)`-mer
multiplicity lemma of §6 step 3.
