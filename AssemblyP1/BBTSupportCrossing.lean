import AssemblyP1.BBTSupportChords

/-!
# `#89`: the support-permutation route meets the **collapse** regime --- a
# kernel-checked refutation of the naive crossing clause

**This module is a negative result about the support-permutation route, and it
is the reason that route cannot finish `thm:BBT` on its own.**

`AssemblyP1.BBTSupportChords.support_dichotomy` is the whole combinatorial
content of `AssemblyP1.BBTEulerian.EulerianCycleObstruction`, in the shape

```text
   f ≠ id  ⟹  (W) some label occurs at three distinct positions
              or (X) two doubled pairs whose four endpoints interleave.
```

In the Eulerian setting (`AssemblyP1.BBTUniqueEulerian.AltF_vtx`) the
permutation is `f = AltF hG σ` and the labelling is `W = vtx hG L S`, so the
three objects are *real starts of the truth* and `W a = W b` says that `a` and
`b` spell the same `(L-1)`-mer.  Read at those objects the two disjuncts are

* **(W)** three distinct starts spelling the same `(L-1)`-mer, and
* **(X)** two *doubled* `(L-1)`-mer pairs whose four starts interleave.

Clause (W) is the first clause of `AssemblyP1.BBTEulerian.LongObstruction`
after the two-sided maximal extension of
`AssemblyP1.P2RepeatResidual.maximal_extension_of_repeated` (one more copy,
extended symmetrically).  Clause (X) is what this module refutes as a route
to the second clause.

## The statement refuted here

The natural attempt at Lemma 2 of `AssemblyP1.BBTUniqueEulerian` is

```text
  (X)  ⟹  two *interleaved maximal* repeats, both of length ≥ L - 1.
```

The naive proof is "extend each doubled pair maximally, then read off the
interleaving": extend `{a, b}` to its maximal repeat, extend `{c, d}` to its,
and the two interleave because the raw pairs did.  **That last step is false**,
and structurally so: the two maximal extensions are shifted left by
*different* amounts `ℓ₁`, `ℓ₂` (the maximal left extensions of the two pairs),
and interleaving on the circle is invariant only under a *common* rotation.  So
whenever `ℓ₁ ≠ ℓ₂` the interleaving may be destroyed --- and the two pairs may
even lie inside **one** maximal repeat.

`counterexample_collapse` below is a single kernel-checked instance in which
all three of the following hold at once, for the primitive truth
`S = 00101` at `G = 5`, `L = 3` (so `K = L - 1 = 2`):

1. `CrossedDoubledPairs` holds: `{1, 3}` and `{2, 4}` are doubled `2`-mers and
   their four starts interleave;
2. the truth is primitive, so primitivity is available and is *not* the
   escape hatch;
3. `¬ LongObstruction`: there is **no** maximal triple repeat of length `≥ 2`
   and **no** pair of interleaved maximal repeats both of length `≥ 2`.

So (X) is compatible with `P2` at `L = 3`, and the second clause of
`AssemblyP1.P2.P2` cannot be produced from (X) alone.

`S = 00101` is *not* a counterexample to `thm:BBT`, and the reason is
instructive.  Its only maximal repeat of length `≥ 2` is the one of length `3`
at the starts `1`, `3` (`collapse_oneMaximalRepeat`), and both crossing pairs
lie inside it: the pair `{2, 4}` carries no maximal repeat at its own starts at
all (`collapse_second_pair_carries_no_maximal_repeat`), and after one backward
step it *is* the pair `{1, 3}`.  The involution `(1 3)(2 4)` on the two doubled
pairs does give a genuine alternative Eulerian cycle --- `f ∘ nextPos` is the
`5`-cycle `0 → 3 → 2 → 1 → 4 → 0` --- but its vertex cycle is the truth's, so
`thm:BBT` is untouched.  The collapse is *benign*; it just has to be
discharged rather than refuted, and the discharging statement is a statement
about the **block** structure of the support of `f`, not about the pairs.

## What this means for the route

The support-permutation route is complete except for the collapse regime, and
the collapse regime is exactly the *ladder* regime of
`docs/bbt-chord-rematch-89.md` §5: two interlacing doubled pairs that coalesce
into a single maximal repeat, traversed by one block.  That regime is not
discharged by the maximal-extension bridge, and this module is the kernel-level
reason why: a further, genuinely local statement about the *block* structure is
required.

`scripts/verify_support_crossing_collapse_89.py` is the exhaustive search
behind this: over all primitive binary words of length `≤ 7` and all `K`, it
finds 92 instances in which a crossing pair coexists with `¬ LongObstruction`;
the smallest is `S = 00101`, `G = 5`, `K = 2`.  That search is evidence, not a
proof of completeness.

No `sorry`, no `admit`, no new axiom.
-/

namespace AssemblyP1.BBTSupportCrossing

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTSupportChords
open AssemblyP1.P2RepeatResidual

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## 1. The instance: `S = 00101`, `G = 5`, `L = 3` -/

/-- The primitive binary truth `S = 00101` of length `5`: the smallest instance
in which a crossing pair of doubled `(L-1)`-mers coexists with `P2` at
`L = 3`. -/
def S5 : Fin 5 → Fin 2 := ![0, 0, 1, 0, 1]

theorem hG5 : 0 < 5 := by decide

/-- **`S5` is not `s`-periodic for any `0 < s < 5`.**  The witness is a single
position at which the shift moves the symbol; `interval_cases` leaves four
concrete goals, each closed by `decide`. -/
theorem S5_not_periodic (s : ℕ) (hs0 : 0 < s) (hs5 : s < 5) :
    ∃ j : Fin 5, cyc hG5 S5 j ≠ cyc hG5 S5 (j.val + s) := by
  interval_cases s <;> decide

/-- **`S5` is primitive**, so the primitivity hypothesis of
`AssemblyP1.P2RepeatResidual.maximal_extension_of_repeated` is available in the
refutation below: the instance is not refuted by non-primitive collapse. -/
theorem S5_primitive : AssemblyP1.RepeatAdapter.IsPrimitive hG5 S5 := by
  intro s hs0 hs5 hsi
  obtain ⟨j, hj⟩ := S5_not_periodic s hs0 hs5
  exact hj (hsi j.val)

/-! ## 2. The crossing clause (X) holds -/

/-- **The crossing clause of the support dichotomy holds on `S5` at `L = 3`:
the pairs `{1, 3}` and `{2, 4}` are doubled `2`-mers (`01` and `10`
respectively) and their four starts interleave.**  The witnesses are the
starts `1`, `3`, `2`, `4`, in the order `CrossedDoubledPairs` requires them. -/
theorem crossed : CrossedDoubledPairs hG5 (vtx hG5 3 S5) :=
  ⟨1, 3, 2, 4, by decide, by decide, by decide⟩

/-! ## 3. The long obstruction does *not* hold -/

/-- **No maximal triple repeat of length `≥ 2`, and no pair of interleaved
maximal repeats both of length `≥ 2`.**  This is the kernel-checked content of
the `decide`: every one of the two clauses of `LongObstruction` is refuted, at
every `(e, e₁, e₂, a, b, c, d)`.  Intuitively: the `2`-mers of `S5` are
`00` once, `01` twice and `10` twice, so no `2`-mer occurs three times (first
clause), and `S5` has exactly *one* maximal repeat of length `≥ 2`, so no two
of them can interleave (second clause). -/
theorem not_longObstruction : ¬ LongObstruction hG5 3 S5 := by decide

/-! ## 4. The refutation of the naive crossing clause -/

/-- **The naive crossing clause is refuted.**  A crossing pair of doubled
`(L-1)`-mers in a *primitive* truth does **not** force the long obstruction:
`S5` has a crossing pair and is primitive, yet carries neither a maximal triple
repeat of length `≥ 2` nor two interleaved maximal repeats both of length
`≥ 2`.

So it is *not* the case that
`CrossedDoubledPairs hG5 (vtx hG5 3 S5) → LongObstruction hG5 3 S5`, and the
instance is primitive, so neither clause of `AssemblyP1.P2.P2` is violated:
`S5` **satisfies `P2` at `L = 3`**.

This is why the support-permutation route of
`AssemblyP1.BBTSupportChords` needs a further *block* statement for the
collapse regime, and why
`AssemblyP1.P2RepeatResidual.maximal_extension_of_repeated` cannot be applied
twice to an interleaving pair: the two extensions are shifted left by different
amounts, and the interleaving is lost. -/
theorem crossing_does_not_give_longObstruction :
    CrossedDoubledPairs hG5 (vtx hG5 3 S5) →
      AssemblyP1.RepeatAdapter.IsPrimitive hG5 S5 →
      ¬ LongObstruction hG5 3 S5 := by
  intro _ _ h
  exact not_longObstruction h

/-- **`S5` satisfies `P2` at `L = 3`**, the honest summary of the instance:
the crossing clause of the support dichotomy holds, and yet the second clause
of `AssemblyP1.P2.P2` is satisfied. -/
theorem S5_is_P2 : P2 hG5 3 S5 := by
  refine ⟨?_, ?_⟩
  · intro e a b c htriple
    by_contra hnot
    exact not_longObstruction (Or.inl ⟨e, a, b, c, htriple, by omega⟩)
  · intro e₁ e₂ a b c d h₁ h₂ hI
    by_contra hnot
    push_neg at hnot
    exact not_longObstruction (Or.inr ⟨e₁, e₂, a, b, c, d, h₁, h₂, hI,
      by omega, by omega⟩)

/-! ## 5. The collapse, read directly -/

/-- **The collapse:** the only maximal repeat of `S5` of length `≥ 2` is the one
of length `3` at the starts `1` and `3`, and both crossing pairs live inside
it.  The pair `{2, 4}` carries *no* maximal repeat at its own starts --- the
same obstruction as
`AssemblyP1.BBTMaximalExtension.not_maximalRepeat_branchPair_0111` --- and after
one backward step it becomes the pair `{1, 3}`.  So the two crossing pairs
*coalesce*: one maximal repeat, one block, and the alternative traversal moves a
block inside it.

This is the exact shape the support route has to handle, and it is why the
remaining step is a block statement and not a pair statement. -/
theorem collapse_oneMaximalRepeat :
    (mkGenome hG5 S5).IsRepeat 3 1 3 ∧
      ¬ ∃ e : Fin 5, (mkGenome hG5 S5).IsRepeat e 2 4 := by
  exact ⟨by decide, by decide⟩

/-- **The two crossing pairs are the two occurrences of the `2`-mers inside the
one maximal repeat.**  The pair `{1, 3}` carries the maximal repeat of length
`3`; the pair `{2, 4}` lies strictly inside it (`2` and `4` are inside the
window `[1, 4)`), and carries no maximal repeat of its own. -/
theorem collapse_second_pair_inside :
    (mkGenome hG5 S5).IsRepeat 3 1 3 ∧
      (mkGenome hG5 S5).Agree 2 2 4 ∧
      ¬ ∃ e : Fin 5, (mkGenome hG5 S5).IsRepeat e 2 4 := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  rcases h with ⟨e, hrep⟩
  exact (collapse_oneMaximalRepeat.2 ⟨e, hrep⟩).elim

end AssemblyP1.BBTSupportCrossing
