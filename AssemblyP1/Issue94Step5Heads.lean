import AssemblyP1.Issue89GapMap
import AssemblyP1.Issue94Step4Prop

/-!
# `Issue94Step5Heads`: `Step5_heads_interleave` is **false as written**

Board issue 94, front A.  `AssemblyP1.Issue89GapMap.Step5_heads_interleave`
(`Issue89GapMap.lean`:483) is the last open input to the §5 reduction of
`AssemblyP1/BBTCrossingCoalesce.lean`.  This module **refutes** it, with a
kernel-checked witness, and states the corrected step 5.

## The refutation

The word is `S = A A B A B` on `K = 5` positions, read at `L = 3` --- the
repository's own `P2RepeatResidual.cexWord`.  It is **primitive**
(`P2RepeatResidual.cex_is_shiftPrimitive`) and it satisfies the repository's
**actual `P2`** at `L = 3` (`P2RepeatResidual.cex_is_p2`).  Both are quoted, not
re-proved: this module adds no new hypothesis of its own.

At `L = 3` the `(L-1)`-mers are the `2`-mers.  The pair `(1, 3)` carries the
common `2`-mer `01` and the pair `(2, 4)` carries the common `2`-mer `10`, and
the four starts interleave (`head_cex_interleaved`).  This is the
already-recorded `P2`-word-with-interleaving-chords instance behind
`P2RepeatResidual.cex_not_NodeCrossing`.

The heads are

* `{maxPairStart 1 3, maxPairStart 3 1} = {1, 3}` --- `01` is preceded by `A`
  at `0` and by `A` at `2`, so the backward chain of `{1, 3}` has length `0`;
* `{maxPairStart 2 4, maxPairStart 4 2} = {1, 3}` --- `10` is preceded by `A`
  at `1` and by `A` at `3`, so the backward chain of `{2, 4}` has length `1`
  and the head is the *same* pair `{1, 3}`.

So the four heads of `Step5_heads_interleave` are the four points `1, 3, 1, 3`,
which are not pairwise distinct, and `Interleaved` is `false` there
(`head_cex_not_interleaved`).

The `maxPairStart` values are obtained by the **computable** restatement
`Issue94OrbitSearch.pairBackC`, bridged to `pairBack` by
`Issue94Step4Prop.pairBackC_eq'`, and then discharged by `decide` at
`K = 5`.  Nothing is searched: each of the four facts is a `decide` on a
closed `Fin 5` term.

## Why this kills the step-5 plan rather than just this instance

`Issue89GapMap.step5_contradiction` shows that under `P2` and primitivity the
head-interleaving conclusion is *unobtainable*: it contradicts
`P2.imp_ExtCrossing`.  Combining the two facts:

* `P2` and primitivity **do not forbid** interleaving chords
  (`head_cex_interleaved` is an instance), and
* `P2` and primitivity **do forbid** the heads of two interleaving chords from
  interleaving (by `step5_contradiction`),

so `Step5_heads_interleave` is false at `L = 3` and there is no way to complete
the §5 step-5 line as written.  **The five-step reduction of `§5` is therefore
blocked not on a hard lemma but on a false one**, in the same way as
`SlidePreservesInterleaved` and `ShiftLeftPersistence` before it.

## The corrected step 5

The mechanism of the failure is that step 5 asks the heads to interleave
*without ever requiring them to be four distinct points*.  The right step-5
statement is a **dichotomy**, whose second disjunct is already refuted:

> either the two unordered head-pairs coincide --- which is
> `SameExtension`, the desired conclusion of `CrossingPairsCoalesce` --- or the
> four heads interleave, which is impossible under `P2` and primitivity.

`head_dichotomy` below states that dichotomy.  In the counterexample the
**left** disjunct holds: the two unordered head-pairs are both `{1, 3}`
(`head_cex_SameExtension`), which is exactly the coalescence conclusion.
`head_dichotomy` is a `Prop` with **no inhabitant** here: the refutation does
not prove it.

What this module *does* prove, beyond the refutation:

* `heads_of_one_chord_ne`: the two extension starts of a single chord are
  distinct, for every primitive word.  So the only way the four heads of
  `Step5_heads_interleave` can fail to be pairwise distinct is a **collision
  between the two chords' head-pairs** --- the object of §5 step 3, which the
  gap map's step-5 statement does not guard against.
* `head_dichotomy_second_is_false`: at `L = K` the second disjunct of
  `head_dichotomy` is `False`.

## Status

Everything in this file is `#print axioms`-clean and kernel-checked.  No
`sorry`, no `admit`, no new `axiom`, no `native_decide`, no `unsafe`, no
`macro`/`elab`/`syntax`, no linter suppression.
-/

namespace AssemblyP1.Issue94Step5Heads

open AssemblyP1
open AssemblyP1.PopulationReduction
open AssemblyP1.SourceFaithfulIs
open AssemblyP1.OrientedRigidity
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.P2RepeatResidual
open AssemblyP1.BBTLadder
open AssemblyP1.BBTCrossingCoalesce
open AssemblyP1.Issue94OrbitSearch
open AssemblyP1.Issue94Step4Prop
open AssemblyP1.Issue89GapMap

set_option maxHeartbeats 800000

/-- `5 > 0`: the witness word is read on five positions. -/
theorem five : 0 < 5 := by norm_num

/-- The witness word, `AABAB` on five positions: the repository's own
`P2RepeatResidual.cexWord`, quoted unchanged. -/
def headWord : Fin 5 → PopulationReduction.Bin := P2RepeatResidual.cexWord

/-- The genome carrying the witness. -/
abbrev headGenome : SourceFaithfulIs.Genome PopulationReduction.Bin :=
  mkGenome (hG := five) (S := headWord)

/-- `maxPairStart` is a `noncomputable` definition, so its values cannot be
reached by `decide` directly.  This is the computable bridge, once: unfold
`maxPairStart` and rewrite the `pairBack` inside it by `pairBackC`. -/
theorem maxPairStart_of_pairBackC {K : ℕ} (hK : 0 < K) (S : Fin K → PopulationReduction.Bin)
    (a b : Fin K) (n : ℕ) (hn : (a.val + K - pairBackC hK S a.val b.val) % K = n)
    (hnlt : n < K) :
    maxPairStart hK S a b = ⟨n, hnlt⟩ := by
  unfold maxPairStart
  have hkey : a.val + K - pairBack hK S a.val b.val
      = a.val + K - pairBackC hK S a.val b.val := by
    rw [pairBackC_eq' hK S a.val b.val]
  apply Fin.ext
  show (a.val + K - pairBack hK S a.val b.val) % K = n
  rw [hkey, hn]

/-- **The witness is primitive.**  Quoted from
`P2RepeatResidual.cex_is_shiftPrimitive`; the word is `cexWord` verbatim. -/
theorem headWord_primitive : RepeatAdapter.IsPrimitive five headWord :=
  P2RepeatResidual.cex_is_shiftPrimitive

/-- **The witness satisfies actual `P2` at `L = 3`.**  Quoted from
`P2RepeatResidual.cex_is_p2`.  So the refutation does not exploit a weakened
`P2`: this is the repository's own instance of a `P2` word that carries
interleaving double-node configurations. -/
theorem headWord_is_p2 : P2 five 3 headWord :=
  P2RepeatResidual.cex_is_p2

/-- **The two `vtx` hypotheses**: `01` is spelled at starts `1` and `3`, and
`10` at starts `2` and `4`, so both pairs are chords at `L = 3`. -/
theorem head_cex_vtx13 : vtx five 3 headWord 1 = vtx five 3 headWord 3 := by decide
theorem head_cex_vtx24 : vtx five 3 headWord 2 = vtx five 3 headWord 4 := by decide

/-- **The two pairs really are pairs of distinct starts.** -/
theorem head_cex_ne13 : (1 : Fin 5) ≠ 3 := by decide
theorem head_cex_ne24 : (2 : Fin 5) ≠ 4 := by decide

/-- **The two chords interleave**: `01` at `{1, 3}` and `10` at `{2, 4}` on the
`5`-cycle. -/
theorem head_cex_interleaved : Interleaved (mkGenome (hG := five) (S := headWord)) (1:Fin 5) (3:Fin 5) (2:Fin 5) (4:Fin 5) := by decide

/-- **The backward chain of `{1, 3}` has length `0`**: `01` is preceded by `A`
at `0` and by `A` at `2`.  Hence the head of `{1, 3}` is `{1, 3}` itself. -/
theorem head_cex_pairBack13 : pairBackC five headWord 1 3 = 0 := by decide
theorem head_cex_pairBack31 : pairBackC five headWord 3 1 = 0 := by decide

/-- **The backward chain of `{2, 4}` has length `1`**: `10` is preceded by `A`
at `1` and by `A` at `3`, and one step further by `A` at `0` against `B` at
`2`.  Hence the head of `{2, 4}` is `{1, 3}` --- **the same pair**. -/
theorem head_cex_pairBack24 : pairBackC five headWord 2 4 = 1 := by decide
theorem head_cex_pairBack42 : pairBackC five headWord 4 2 = 1 := by decide

/-- **The two head-pairs of the first chord.** -/
theorem head_cex_mps13 : maxPairStart five headWord 1 3 = 1 :=
  maxPairStart_of_pairBackC five headWord 1 3 1 (by decide) (by decide)
theorem head_cex_mps31 : maxPairStart five headWord 3 1 = 3 :=
  maxPairStart_of_pairBackC five headWord 3 1 3 (by decide) (by decide)

/-- **The two head-pairs of the second chord** --- equal to the first chord's. -/
theorem head_cex_mps24 : maxPairStart five headWord 2 4 = 1 :=
  maxPairStart_of_pairBackC five headWord 2 4 1 (by decide) (by decide)
theorem head_cex_mps42 : maxPairStart five headWord 4 2 = 3 :=
  maxPairStart_of_pairBackC five headWord 4 2 3 (by decide) (by decide)

/-- **The four heads are `1, 3, 1, 3` and do not interleave**, so the
conclusion of `Step5_heads_interleave` is false at this instance. -/
theorem head_cex_not_interleaved :
    ¬ Interleaved (mkGenome (hG := five) (S := headWord))
      (maxPairStart five headWord (1:Fin 5) (3:Fin 5)) (maxPairStart five headWord (3:Fin 5) (1:Fin 5))
      (maxPairStart five headWord (2:Fin 5) (4:Fin 5)) (maxPairStart five headWord (4:Fin 5) (2:Fin 5)) := by
  intro hI
  have hAC : ¬ (maxPairStart five headWord (1 : Fin 5) (3 : Fin 5)
      = maxPairStart five headWord (2 : Fin 5) (4 : Fin 5)) := hI.1.2.1
  rw [head_cex_mps13, head_cex_mps24] at hAC
  exact hAC rfl

/-- **The refutation, collected.**  Every hypothesis of `Step5_heads_interleave`
holds at `K = 5`, `L = 3`, `S = AABAB`, `(a, b, c, d) = (1, 3, 2, 4)`, and its
conclusion is false. -/
theorem Step5_heads_interleave_cex :
    (2 : ℕ) ≤ 3 ∧ 3 ≤ (5 : ℕ) ∧
    (1 : Fin 5) ≠ 3 ∧ (2 : Fin 5) ≠ 4 ∧
    vtx five 3 headWord 1 = vtx five 3 headWord 3 ∧
    vtx five 3 headWord 2 = vtx five 3 headWord 4 ∧
    Interleaved (mkGenome (hG := five) (S := headWord)) (1:Fin 5) (3:Fin 5) (2:Fin 5) (4:Fin 5) ∧
    ¬ Interleaved (mkGenome (hG := five) (S := headWord))
        (maxPairStart five headWord (1:Fin 5) (3:Fin 5)) (maxPairStart five headWord (3:Fin 5) (1:Fin 5))
        (maxPairStart five headWord (2:Fin 5) (4:Fin 5)) (maxPairStart five headWord (4:Fin 5) (2:Fin 5)) :=
  ⟨by decide, by decide, head_cex_ne13, head_cex_ne24, head_cex_vtx13,
    head_cex_vtx24, head_cex_interleaved, head_cex_not_interleaved⟩

/-- **`Step5_heads_interleave` is false at `L = 3`**: the statement itself is
refuted, at `K = 5`, on the `P2` primitive word `AABAB`.

`P2` and primitivity are carried by the *quotations* `headWord_is_p2` and
`headWord_primitive`, so the refutation is of the statement exactly as the gap
map writes it, hypotheses included. -/
theorem not_Step5_heads_interleave_3 : ¬ (Step5_heads_interleave 3) := by
  intro h
  have hL : (2 : ℕ) ≤ 3 := by decide
  have hLG : 3 ≤ 5 := by decide
  have hres := h 5 five headWord headWord_is_p2 headWord_primitive
    1 3 2 4 hL hLG head_cex_ne13 head_cex_ne24
    head_cex_vtx13 head_cex_vtx24 head_cex_interleaved
  exact head_cex_not_interleaved
    (by simpa only [mkGenome, headWord] using hres)

/-- **The mechanism, made explicit.**  In the counterexample the two chords'
head-pairs *coincide* as unordered pairs --- which is the coalescence
conclusion itself.  What fails is not the coalescence but the claim that the
heads interleave: `P2`'s clause 2 forbids the heads of two interleaving chords
from interleaving (by `Issue89GapMap.step5_contradiction`), and on this `P2`
word the heads coincide instead. -/
theorem head_cex_SameExtension :
    SameExtension 5 five headWord 1 3 2 4 :=
  Or.inl ⟨head_cex_mps13.trans head_cex_mps24.symm,
    head_cex_mps31.trans head_cex_mps42.symm⟩

/-! ## A proved smaller lemma: the two heads of *one* chord are distinct -/

/-- **The two extension starts of a single chord are distinct.**  For every
primitive circular word, every `L` with `2 ≤ L`, and every pair of agreeing
starts `a, b` with `a ≠ b`, the head of the backward list of `{a, b}` is an
unordered pair of *two distinct* starts: `maxPair_isRepeat` exhibits a maximal
repeat at exactly those two starts, and `Genome.IsRepeat` demands they differ.

Consequence for the refutation: in `Step5_heads_interleave` the four heads can
fail to be pairwise distinct **only** by a collision between the two chords'
head-pairs, i.e. by `maxPairStart a b = maxPairStart c d` or
`maxPairStart a b = maxPairStart d c` --- a *cross-chord* collision, which is
the object of §5 step 3 and which the gap map's step-5 statement does not guard
against. -/
theorem heads_of_one_chord_ne {G L : ℕ} (hG : 0 < G)
    (S : Fin G → PopulationReduction.Bin) (hL : 2 ≤ L) (hLG : L ≤ G)
    (hprim : RepeatAdapter.IsPrimitive hG S) {a b : Fin G} (hab : a ≠ b)
    (hag : ∀ d : Fin (L - 1), cyc hG S (a.val + d.val) = cyc hG S (b.val + d.val)) :
    maxPairStart hG S a b ≠ maxPairStart hG S b a := by
  obtain ⟨hR, _hℓ⟩ :=
    maxPair_isRepeat hG S hprim hab (by omega) (by omega) hag
  exact hR.2.2.1

/-! ## The corrected step 5: a dichotomy, not a crossing -/

/-- **The corrected step 5.**  Under `P2` and primitivity, two interleaving
chords either have *coinciding* maximal extensions --- `SameExtension`, the
conclusion of `CrossingPairsCoalesce` --- or their four extension starts
interleave.  The second disjunct is refuted, by
`head_dichotomy_second_is_false` below at `L = K` and by
`not_Step5_heads_interleave_3` at `L = 3`, so the dichotomy is what the §5
reduction should ask for in place of `Step5_heads_interleave`: it no longer
demands a crossing, which is exactly what made the original false.

This is a `Prop` with **no inhabitant** in this module.  The refutation above
does not prove it, and no argument in this file establishes it. -/
def head_dichotomy (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → PopulationReduction.Bin) (_hP2 : P2 hK L S)
    (_hprim : RepeatAdapter.IsPrimitive hK S) (a b c d : Fin K),
    2 ≤ L → L ≤ K → a ≠ b → c ≠ d →
    vtx hK L S a = vtx hK L S b → vtx hK L S c = vtx hK L S d →
    Interleaved (mkGenome hK S) a b c d →
    SameExtension K hK S a b c d ∨
      Interleaved (mkGenome hK S)
        (maxPairStart hK S a b) (maxPairStart hK S b a)
        (maxPairStart hK S c d) (maxPairStart hK S d c)

/-- **The second disjunct of `head_dichotomy` is `False` at `L = K`**, by
`Issue89GapMap.step5_contradiction` --- which is why the dichotomy, once
proved, gives the target outright.  Recorded as a proved implication so that
the dependency is not re-listed as an open input. -/
theorem head_dichotomy_second_is_false {K : ℕ} (hK : 0 < K)
    (S : Fin K → PopulationReduction.Bin) (hL : 2 ≤ K) (hP2 : P2 hK K S)
    (hprim : RepeatAdapter.IsPrimitive hK S) {a b c d : Fin K} (hab : a ≠ b)
    (hcd : c ≠ d) (hvab : vtx hK K S a = vtx hK K S b)
    (hvcd : vtx hK K S c = vtx hK K S d) (hI : Interleaved (mkGenome hK S) a b c d) :
    ¬ Interleaved (mkGenome hK S)
        (maxPairStart hK S a b) (maxPairStart hK S b a)
        (maxPairStart hK S c d) (maxPairStart hK S d c) :=
  Issue89GapMap.step5_contradiction hK S hL (le_refl K) hP2 hprim hab hcd hvab hvcd hI

end AssemblyP1.Issue94Step5Heads
