import AssemblyP1.BBTCrossingCoalesce
import AssemblyP1.Issue94HeadCollision
import AssemblyP1.Issue94NoCollision
import AssemblyP1.Issue94NoCollisionAlpha

/-!
# `Issue94CaseSplit`: `CrossingPairsCoalesce` by case split on a cross-head equality

Board issue 94, front G3 (direct assembly).  Work order: the external proof
pointer at 2026-09-28 21:33:33Z and the external orchestration pointer at
21:34:57Z on board issue 94.  Base: `2463a1f` (collision half) merged with
`a23872a` (no-collision half).

## The pointer being implemented

The 21:34:57Z pointer, item 3, reads:

> **Direct assembly front**: attempt `CrossingPairsCoalesce` directly as a case
> split between (1) and (2).  Avoid introducing a stronger `head_dichotomy`
> unless Lean actually needs it.  The target is the exact existing
> `CrossingPairsCoalesce` Prop inhabitant.

and the 21:33:33Z pointer names the two halves to split between:

> Then the direct proof strategy for `CrossingPairsCoalesce` becomes:
>
> - case on any cross-head collision: close immediately by the helper above;
> - otherwise all four cross-head inequalities are available;
> - use the already-proved step-2/path + `chord_shift_left`/`pairBack_shift` +
>   `step4_guarded` machinery to slide to the heads while preserving
>   interleaving;
> - the resulting head interleaving contradicts `P2.imp_ExtCrossing`.

So this module is the case split itself, and nothing else.  It introduces **no**
`head_dichotomy`, as instructed.

## The target, and how far this module reaches it

The target is the existing `Prop` `BBTCrossingCoalesce.CrossingPairsCoalesce`
(`AssemblyP1/BBTCrossingCoalesce.lean:212`), whose statement is

```lean
def CrossingPairsCoalesce (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α), 2 ≤ L → L ≤ K →
    P2 hK L S → RepeatAdapter.IsPrimitive hK S →
    ∀ (a b c d : Fin K),
      a ≠ b → c ≠ d →
      vtx hK L S a = vtx hK L S b → vtx hK L S c = vtx hK L S d →
      Interleaved (mkGenome hK S) a b c d →
      SameExtension K hK S a b c d
```

under `variable {α : Type} [DecidableEq α]`, i.e. `@CrossingPairsCoalesce :
{α : Type} → [DecidableEq α] → ℕ → Prop` — **`α` is a parameter of the
statement, not universally quantified inside it.**

The two halves do **not** have the same scope in `α`:

* `Issue94HeadCollision.head_collision_implies_sameExtension` is proved for
  **arbitrary** `{α : Type} [DecidableEq α]`;
* `Issue94NoCollision.no_collision_contradiction` is proved for
  **`S : Fin K → PopulationReduction.Bin` only**.

Consequently the case split closes for `α = PopulationReduction.Bin`, which is
what the two `*_bin` declarations below record.  `Issue94NoCollisionAlpha.lean`
additionally removes that restriction, and `crossingPairsCoalesce_general` below
is the α-general inhabitant.  This module therefore proves

* `crossingPairsCoalesce_of_noCollision` — the case split for **arbitrary**
  `{α : Type} [DecidableEq α]`, in the form
  "collision half, else a hypothesis `hnc` of no-collision type".  This is the
  honest general statement: it is `CrossingPairsCoalesce` **conditional on** the
  no-collision half being available at that `α`.  It shows the two halves
  compose, and it isolates the *only* thing that stops the α-general case split
  from being unconditional, which is the `Bin` restriction of the front-2 file
  and nothing else;
* `crossingPairsCoalesce_bin` — the **unconditional** case split at
  `α = Bin`, i.e. an inhabitant of the existing
  `BBTCrossingCoalesce.CrossingPairsCoalesce (α := Bin)`.

`crossingPairsCoalesce_bin` is the "exact existing `CrossingPairsCoalesce` Prop
inhabitant" of the pointer, at the alphabet the library's slide machinery is
actually stated over.

## The α-general inhabitant (added by front 94g4)

`Issue94NoCollisionAlpha.lean` removes the `Bin` restriction, and this module
then proves the pointer's target outright:

* `crossingPairsCoalesce_alpha` — the unconditional case split at arbitrary
  `{α : Type} [DecidableEq α]`;
* `crossingPairsCoalesce_general` — an inhabitant of the **existing** `Prop`
  `BBTCrossingCoalesce.CrossingPairsCoalesce (α := α) L` for **every**
  `[DecidableEq α]`, with its hypotheses verbatim that `def`'s.

So the residual-assumption item on definition-of-done item 2 is now closed:
`crossingPairsCoalesce_general` retains no assumption on the alphabet. The
earlier `crossingPairsCoalesce_bin` is kept as the `α := Bin` specialisation.

The `Bin` restriction turned out to be inherited plumbing, not mathematics. Every
dependency the no-collision argument uses is already stated for arbitrary
`[DecidableEq α]`; the three `Bin`-typed items on the old path were wrappers
(`Issue94Step4Prop.step4_guarded`, whose proof body is a call to the α-general
`step4_slide_iterates_word`; `Issue89GapMap.step3_shared_endpoint_forces_pair_readL`,
a four-case composition of α-general lemmas; and `Issue94Step5Heads.heads_of_one_chord_ne`,
replaced here by the existing α-general `Issue94HeadCollision.heads_ne_of_chord`).
See the table in `Issue94NoCollisionAlpha.lean`.

## The one bridging lemma the composition needed

Neither half applies directly to `CrossingPairsCoalesce`'s hypotheses, and the
bridge is not cosmetic.  `CrossingPairsCoalesce` hands over **`vtx` equalities**

```lean
hvab : vtx hK L S a = vtx hK L S b
hvcd : vtx hK L S c = vtx hK L S d
```

whereas the collision half `head_collision_implies_sameExtension` takes the
**pointwise `(L-1)`-mer** form

```lean
hagab : ∀ d : Fin (L - 1), cyc hK S (a.val + d.val) = cyc hK S (b.val + d.val)
```

These are different propositions, and this is the defect that made the earlier
committed call ill-typed (recorded as the `hvab`-versus-`hag` mismatch in the
orchestrator's 01:29Z comment on issue 94).  The bridge is the already-proved
`BBTCrossingCoalesce.vtx_eq_iff`, read in the `.mp` direction:

`vtx_eq_iff hK S : vtx hK L S a = vtx hK L S b ↔ ∀ d, cyc … = cyc …`.

So no new lemma was needed for the forward direction, and nothing is weakened:
`crossingPairsCoalesce_bin`'s hypotheses are verbatim `CrossingPairsCoalesce`'s.

## The two branches

* **Some cross-head equality holds** (`hAC ∨ hAD ∨ hBC ∨ hBD`).  This is
  `Issue94HeadCollision.head_collision_implies_sameExtension`, verbatim and
  unmodified, applied to the head pairs.  Front 2463a1f.
* **No cross-head equality** (all four inequalities).  This is
  `Issue94NoCollision.no_collision_contradiction`, which returns `False`.  The
  branch is closed by `.elim`.  Front a23872a.

The `.elim` is what the pointer's "the resulting head interleaving contradicts
`P2.imp_ExtCrossing`" becomes at this level: the contradiction is already
inside `no_collision_contradiction`, so this module neither re-derives it nor
re-states it as a weaker hypothesis.
-/

namespace AssemblyP1.Issue94CaseSplit

open AssemblyP1 AssemblyP1.PopulationReduction AssemblyP1.RepeatAdapter
open AssemblyP1.SourceFaithfulIs AssemblyP1.OrientedRigidity AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTChords AssemblyP1.BBTUniqueEulerian AssemblyP1.P2RepeatResidual
open AssemblyP1.BBTLadder AssemblyP1.BBTCrossingCoalesce
open AssemblyP1.Issue94HeadCollision AssemblyP1.Issue94NoCollision
open AssemblyP1.Issue94NoCollisionAlpha

set_option maxHeartbeats 800000

variable {K L : ℕ}

/-- **The case split, for arbitrary `{α} [DecidableEq α]`, with the no-collision
half supplied as a hypothesis.**

This is `BBTCrossingCoalesce.CrossingPairsCoalesce` at an arbitrary `α` *given*
that the no-collision branch is available at that `α`; `hnc` is exactly
`Issue94NoCollision.no_collision_contradiction` at `S := S`.  Instantiating
`hnc` at `α = Bin` recovers `crossingPairsCoalesce_bin` below.

The proof is the pointer's two bullets and nothing more. -/
theorem crossingPairsCoalesce_of_noCollision {α : Type} [DecidableEq α]
    (hK : 0 < K) (S : Fin K → α) (h2L : 2 ≤ L) (hLK : L ≤ K) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) {a b c d : Fin K}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : vtx hK L S a = vtx hK L S b) (hvcd : vtx hK L S c = vtx hK L S d)
    (hI : Interleaved (mkGenome hK S) a b c d)
    (hnc : ∀ (_hab : a ≠ b) (_hcd : c ≠ d)
      (_hvab : vtx hK L S a = vtx hK L S b) (_hvcd : vtx hK L S c = vtx hK L S d)
      (_hI : Interleaved (mkGenome hK S) a b c d)
      (_hAC : maxPairStart hK S a b ≠ maxPairStart hK S c d)
      (_hAD : maxPairStart hK S a b ≠ maxPairStart hK S d c)
      (_hBC : maxPairStart hK S b a ≠ maxPairStart hK S c d)
      (_hBD : maxPairStart hK S b a ≠ maxPairStart hK S d c), False) :
    SameExtension K hK S a b c d := by
  -- `vtx` equality read as the pointwise `(L-1)`-mer the collision half wants.
  have hagab : ∀ t : Fin (L - 1), cyc hK S (a.val + t.val) = cyc hK S (b.val + t.val) :=
    (vtx_eq_iff hK S).mp hvab
  have hagcd : ∀ t : Fin (L - 1), cyc hK S (c.val + t.val) = cyc hK S (d.val + t.val) :=
    (vtx_eq_iff hK S).mp hvcd
  -- Pointer bullet 1: case on any cross-head collision, close immediately.
  by_cases hAC : maxPairStart hK S a b = maxPairStart hK S c d
  · exact head_collision_implies_sameExtension hK S h2L hLK hP2 hprim hab hcd
      hagab hagcd (Or.inl hAC)
  by_cases hAD : maxPairStart hK S a b = maxPairStart hK S d c
  · exact head_collision_implies_sameExtension hK S h2L hLK hP2 hprim hab hcd
      hagab hagcd (Or.inr (Or.inl hAD))
  by_cases hBC : maxPairStart hK S b a = maxPairStart hK S c d
  · exact head_collision_implies_sameExtension hK S h2L hLK hP2 hprim hab hcd
      hagab hagcd (Or.inr (Or.inr (Or.inl hBC)))
  by_cases hBD : maxPairStart hK S b a = maxPairStart hK S d c
  · exact head_collision_implies_sameExtension hK S h2L hLK hP2 hprim hab hcd
      hagab hagcd (Or.inr (Or.inr (Or.inr hBD)))
  -- Pointer bullet 2: no cross-head equality, so all four inequalities hold and
  -- the front-2 theorem refutes the configuration outright.
  exact (hnc hab hcd hvab hvcd hI hAC hAD hBC hBD).elim

/-- **The case split, unconditional, at `α = PopulationReduction.Bin`.**

An inhabitant of the existing `BBTCrossingCoalesce.CrossingPairsCoalesce` at
`α = Bin`: the hypotheses are verbatim that `def`'s, and the conclusion is
verbatim `SameExtension K hK S a b c d`.  This is the pointer's item 3, at the
alphabet the two halves are actually proved over. -/
theorem crossingPairsCoalesce_bin (hK : 0 < K) (S : Fin K → Bin)
    (h2L : 2 ≤ L) (hLK : L ≤ K) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) {a b c d : Fin K}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : vtx hK L S a = vtx hK L S b) (hvcd : vtx hK L S c = vtx hK L S d)
    (hI : Interleaved (mkGenome hK S) a b c d) :
    SameExtension K hK S a b c d :=
  crossingPairsCoalesce_of_noCollision hK S h2L hLK hP2 hprim hab hcd hvab hvcd hI
    (fun hab hcd hvab hvcd hI hAC hAD hBC hBD =>
      no_collision_contradiction hK S h2L hLK hP2 hprim hab hcd hvab hvcd hI
        hAC hAD hBC hBD)

/-- **The `def` itself, inhabited at `α = Bin`.**  The hypotheses below are
copied verbatim from `BBTCrossingCoalesce.CrossingPairsCoalesce`
(`AssemblyP1/BBTCrossingCoalesce.lean:212`); this is a restatement, not a
weakening. -/
theorem crossingPairsCoalesce (L : ℕ) :
    BBTCrossingCoalesce.CrossingPairsCoalesce (α := Bin) L := by
  intro K hK S h2L hLK hP2 hprim a b c d hab hcd hvab hvcd hI
  exact crossingPairsCoalesce_bin hK S h2L hLK hP2 hprim hab hcd hvab hvcd hI

/-- **The case split, unconditional, at an arbitrary `[DecidableEq α]`.**

The α-general analogue of `crossingPairsCoalesce_bin`, discharging the
no-collision branch with `Issue94NoCollisionAlpha.no_collision_contradiction_alpha`
rather than with the `Bin`-only `Issue94NoCollision.no_collision_contradiction`.
Same two bullets, same `vtx_eq_iff` bridge, nothing weakened. -/
theorem crossingPairsCoalesce_alpha {α : Type} [DecidableEq α]
    (hK : 0 < K) (S : Fin K → α) (h2L : 2 ≤ L) (hLK : L ≤ K) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) {a b c d : Fin K}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : vtx hK L S a = vtx hK L S b) (hvcd : vtx hK L S c = vtx hK L S d)
    (hI : Interleaved (mkGenome hK S) a b c d) :
    SameExtension K hK S a b c d :=
  crossingPairsCoalesce_of_noCollision hK S h2L hLK hP2 hprim hab hcd hvab hvcd hI
    (fun hab hcd hvab hvcd hI hAC hAD hBC hBD =>
      no_collision_contradiction_alpha hK S h2L hLK hP2 hprim hab hcd hvab hvcd hI
        hAC hAD hBC hBD)

/-- **The `def` itself, inhabited at an arbitrary `[DecidableEq α]`.**

This is the pointer's target: an inhabitant of the **existing** `Prop`
`BBTCrossingCoalesce.CrossingPairsCoalesce` with **no residual assumption on
the alphabet**.  The hypotheses are copied verbatim from that `def`
(`AssemblyP1/BBTCrossingCoalesce.lean:212`) and the conclusion is its own; this
is a restatement of the target, not a weakening or a redefinition of it.

The α-generality rests on `Issue94NoCollisionAlpha`, which shows the `Bin`
restriction of `Issue94NoCollision.lean` was inherited plumbing over an
α-general core rather than a property of the argument. -/
theorem crossingPairsCoalesce_general {α : Type} [DecidableEq α] (L : ℕ) :
    BBTCrossingCoalesce.CrossingPairsCoalesce (α := α) L := by
  intro K hK S h2L hLK hP2 hprim a b c d hab hcd hvab hvcd hI
  exact crossingPairsCoalesce_alpha hK S h2L hLK hP2 hprim hab hcd hvab hvcd hI

end AssemblyP1.Issue94CaseSplit
