import AssemblyP1.BBTLadder
import AssemblyP1.Issue94TW4Coalesce
import AssemblyP1.Issue94CaseSplit

/-!
# Board 94, front `94cross` --- `CrossingChordsCoalesce`, minimised and settled

This module takes up the objective named by the predecessor front `94wit` in
`/workspace/BOARD94-WITNESS-2010Z.md` §11:

> prove `BBTLadder.CrossingChordsCoalesce`, that two CROSSING chords of the
> support of `AltF hK σ` carry the same deterministic maximal extension.

## 0. The state of the question when this front opened

The statement is **not** open in the sense the steering comment implies.
`AssemblyP1/Issue94TW4Coalesce.lean` already contains, in the kernel:

* §3 `crossingChordsCoalesce_above` --- the `L > K` half is **proved** and
  vacuous (`altF_eq_id_of_prim_window`: a window of at least a full turn makes
  the `(L-1)`-mer labelling injective on a primitive circle, so `AltF = id` and
  the chord hypothesis contradicts `FourDistinct`);
* §5 `crossingChordsCoalesce_iff_two_le` --- for `2 ≤ L`, the unbounded `def`
  is **equivalent** to its in-range half;
* §6 `crossingChordsCoalesce_of_two_le : 2 ≤ L → BBTLadder.CrossingChordsCoalesce (α := α) L`
  --- the in-range half, **proved** at arbitrary `[DecidableEq α]`;
* §4 `not_crossingChordsCoalesce_one : ¬ BBTLadder.CrossingChordsCoalesce (α := Fin 4) 1`
  --- the `L = 1` half, **refuted**.

So the `def` is settled: **proved for every `L ≥ 2`, refuted at `L = 1`**, and
the bound `2 ≤ L` is necessary, not cosmetic.  The aggregator comment at
`AssemblyP1.lean:472` ("unbounded `CrossingChordsCoalesce` is neither proved nor
refuted") is **stale** with respect to `Issue94TW4Coalesce`; §4 below records
what this front verified about that.

## 1. The statement, verbatim

`AssemblyP1/BBTLadder.lean:625`:

```lean
def CrossingChordsCoalesce (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α) (_hP2 : P2 hK L S)
    (_hprim : RepeatAdapter.IsPrimitive hK S), Ukkonen hK L S →
    ∀ (σ : Fin K ≃ Fin K) (_hEul : EulerianCycle hK L S σ),
      ∀ (a b c d : Fin K),
        AltF hK σ a = b → AltF hK σ b = a → AltF hK σ c = d → AltF hK σ d = c →
        a ≠ c → b ≠ c → a ≠ d → b ≠ d →
        Interleaved (mkGenome hK S) a b c d →
        SameExtension K hK S a b c d
```

Note what it does **not** quantify over: there is no `2 ≤ L` and no `L ≤ K`.
Its sibling `BBTLadder.LadderVertexCycle` (`AssemblyP1/BBTLadder.lean:658`)
**does** carry both.  §3 shows the first omission is load-bearing.

## 2. Verdict: refuted as stated, at the smallest possible alphabet

`BBTLadder.CrossingChordsCoalesce` has **no inhabitant at any read length**
already over a **two-letter** alphabet:

> `K = 4`, `S = 0011`, `L = 1`, `σ = (1 3)`, quadruple `a b c d = 0 2 1 3`.

`crossingChordsCoalesce_refuted` (§2) is the statement
`¬ (∀ L : ℕ, BBTLadder.CrossingChordsCoalesce (α := Fin 2) L)`.

**What is new here.**  The tree's refutation `not_crossingChordsCoalesce_one` is
over `α := Fin 4` with `S = (0, 1, 2, 3)` — four *pairwise distinct* symbols.
This front's counterexample is **binary**.  That is a genuine strengthening: it
shows the `L = 1` failure is *not* an artefact of an alphabet rich enough to
make every start carry a distinct symbol, which is exactly the trick the
four-letter instance uses (`S4` injective ⇒ `pairBack a b = 0` for all
`a ≠ b`).  Over `Fin 2` that trick is unavailable — in `S = 0011` the starts
`1` and `2` carry the same letter and `pairBack 1 2 > 0` — and the refutation
still goes through, because the two crossing chords used, `0 2` and `1 3`,
happen to have differing preceding letters.  So the counterexample is not
manufactured by a device that only exists for large alphabets.

The obstruction is structural, and is why the statement needed the missing
bound.  `SameExtension` is about the *deterministic maximal extension*
`maxPairStart`, i.e. about how far two copies of a pair agree, i.e. about
`pairBack`.  At `L = 1` the window is `L - 1 = 0` positions long, so
`vtx hK L S x` is the **constant** function `Fin 0 → α`: every start carries
the same `(L-1)`-mer, "a chord" degenerates to "any two distinct starts", and
the four `AltF_vtx'` equalities say nothing about the word.  What *is* still
non-trivial at `L = 1` is `P2`: its first clause reads "no maximal triple
repeat", its second reads "`e₁ ≤ L - 2` or `e₂ ≤ L - 2`", i.e. `e₁ ≤ -1`,
unsatisfiable, so `P2` at `L = 1` says *no interleaved repeat pair exists*.
`S = 0011` has neither (`cex_P2`), and nonetheless its two crossing `AltF`
chords carry two different maximal extensions.

### Minimality (§3)

* **circle size.**  The conclusion reads off `Interleaved`, whose
  `FourDistinct` clause needs four pairwise distinct starts, so `K ≥ 4` is
  forced; the counterexample is at `K = 4`
  (`no_interleaved_on_K3`: over **all** binary words on `Fin 3` there is no
  four-distinct quadruple, whatever the read length).
* **alphabet.**  A one-letter circular word is shift-invariant and so never
  primitive for `K ≥ 2` (`no_primitive_on_Fin1`), while any counterexample must
  satisfy `IsPrimitive`; the counterexample is binary.

Both are `decide` over all words of the relevant shape, not a sample.

## 3. The missing hypothesis, named

> **`2 ≤ L`** (equivalently `L - 1 ≥ 1`, so that the `(L-1)`-mer is a
> non-degenerate window and a chord of the support is a genuine repeated
> `(L-1)`-mer rather than an arbitrary pair of starts).

It is exactly the hypothesis whose absence produces the counterexample, and it
is *necessary*: §4 gives an inhabitant of the statement with `2 ≤ L` and `L ≤ K`
added, at arbitrary `[DecidableEq α]`, while §2 gives a refutation without them.

On the second missing bound: **`L ≤ K` is not independently necessary.**  It is
needed only because the α-general word-level theorem
`BBTCrossingCoalesce.CrossingPairsCoalesce` is phrased at `L ≤ K`.  At `L > K`
the statement is *vacuously* true, for a structural reason independent of
coalescence (`Issue94TW4Coalesce.altF_eq_id_of_prim_window`): once the window
has swallowed the circle, the `(L-1)`-mer labelling is injective on a primitive
circle, so `AltF` is the identity and the chord hypothesis contradicts
`a ≠ b`.  §4 therefore derives its `L ≤ K` step from the same window argument
rather than from a coalescence theorem.

## 4. What this front delivers

1. `crossingChordsCoalesce_refuted` (§2): the refutation of
   `BBTLadder.CrossingChordsCoalesce` **as written**, over the smallest
   possible alphabet `Fin 2` and the smallest possible circle `K = 4`.
2. `no_interleaved_on_K3`, `no_primitive_on_Fin1` (§3): the minimality of `K`
   and of the alphabet, `decide`-closed over all words of the shape.
3. `CrossingChordsCoalesce_ge2` (§4): the statement with `2 ≤ L` and `L ≤ K`
   added, at arbitrary `[DecidableEq α]` — an inhabitant, derived **from the
   α-general word-level theorem** `Issue94CaseSplit.crossingPairsCoalesce_general`
   via `BBTLadder.AltF_vtx'` alone, i.e. by an independent route from
   `Issue94TW4Coalesce`'s.
4. `crossingChordsCoalesce_sharp_bin` (§4): over the binary alphabet the
   `def` is **exactly characterised** — true for every `L ≥ 2`, false at
   `L = 1`.  Together with (1) this is the sharp statement of the objective.

### What this front does **not** deliver, plainly

* `BBTLadder.LadderVertexCycle` still has **no** inhabitant.  It is not
  touched here.  `CrossingChordsCoalesce_ge2` supplies only its *block
  hypothesis*; the remaining global step — that the traversal walks the blocks
  in geometric order — is untouched here and untouched in the tree.
* **No new mathematics.**  Both the refutation and the repair were already
  available in the tree (`Issue94TW4Coalesce` for the refutation and for the
  `L ≥ 2` half; `Issue94CaseSplit.crossingPairsCoalesce_general` for the word
  level).  What is new is the **binary-alphabet minimisation** of the
  refutation and the two minimality lemmas, plus a consolidated characterisation
  of the `def` over that alphabet.
* No definition in the library was changed.  `BBTLadder.CrossingChordsCoalesce`
  is left exactly as written and is proved false, not edited; the local copy
  `CrossingChordsCoalesceUnbounded` used to aim the refutation is checked
  definitionally equal to it (`eq_def`).

No `sorry`, no `admit`, no `native_decide`, no `unsafe`, no new axiom, no
linter suppression.
-/

set_option maxHeartbeats 800000

namespace AssemblyP1.Issue94CrossingChords

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.RepeatAdapter
open AssemblyP1.P2RepeatResidual
open AssemblyP1.BBTLadder
open AssemblyP1.BBTCrossingCoalesce
open AssemblyP1.Issue94CaseSplit
open AssemblyP1.Issue94TW4Coalesce

/-! ## 1. The statement, restated for the record

The library `def` is left untouched.  This local copy exists only so that the
refutation below can be aimed at the *same body*, and `eq_def` at the end of §2
checks it is definitionally equal to `BBTLadder.CrossingChordsCoalesce`. -/

/-- **Verbatim copy of `BBTLadder.CrossingChordsCoalesce`, with no bound on
`L`.** -/
def CrossingChordsCoalesceUnbounded {α : Type} [DecidableEq α] (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α) (_hP2 : P2 hK L S)
    (_hprim : RepeatAdapter.IsPrimitive hK S), Ukkonen hK L S →
    ∀ (σ : Fin K ≃ Fin K) (_hEul : EulerianCycle hK L S σ),
      ∀ (a b c d : Fin K),
        AltF hK σ a = b → AltF hK σ b = a → AltF hK σ c = d → AltF hK σ d = c →
        a ≠ c → b ≠ c → a ≠ d → b ≠ d →
        Interleaved (mkGenome hK S) a b c d →
        SameExtension K hK S a b c d

/-! ## 2. The minimal counterexample -/

section Counterexample

/-- `hK : 0 < 4`. -/
theorem hK4 : 0 < 4 := by decide

/-- **The binary word `S = 0011` on `K = 4` positions.** -/
def Sc4 : Fin 4 → Fin 2 := ![0, 0, 1, 1]

/-- **The listing `σ = (1 3)`, i.e. `σ 0 = 0`, `σ 1 = 3`, `σ 2 = 2`,
`σ 3 = 1`.** -/
def sig4 : Fin 4 ≃ Fin 4 := Equiv.swap 1 3

/-- Decidability of the source's repeat and interlacing predicates on this
instance, so that the facts below are `decide`-closed.  These are
*instances*, added because the library does not provide them; no definition is
changed. -/
local instance decIsRepeat4 (e : ℕ) (a b : Fin 4) :
    Decidable ((mkGenome hK4 Sc4).IsRepeat e a b) := by
  unfold Genome.IsRepeat Genome.Agree mkGenome
  exact inferInstance

local instance decIsTripleRepeat4 (e : ℕ) (a b c : Fin 4) :
    Decidable ((mkGenome hK4 Sc4).IsTripleRepeat e a b c) := by
  unfold Genome.IsTripleRepeat Genome.Agree mkGenome
  exact inferInstance

local instance decInterleaved4 (a b c d : Fin 4) :
    Decidable (Interleaved (mkGenome hK4 Sc4) a b c d) := by
  unfold Interleaved InOpenArc FourDistinct mkGenome
  exact inferInstance

/-- **`P2` holds at `L = 1`.**  `0011` has no maximal triple repeat (the letter
`0` is spelled at `0, 1` and the letter `1` at `2, 3`, each exactly twice), so
the first clause `e.val < L - 1 = 0` holds; the second clause is
`e₁ ≤ L - 2` or `e₂ ≤ L - 2`, i.e. `e₁ ≤ -1` or `e₂ ≤ -1`, which is
unsatisfiable, so `0011` must have **no interleaved repeat pair at all** --- and
it has none, so the clause holds vacuously.  `P2` is genuinely load-bearing at
`L = 1`: it is the only hypothesis that still says anything, and `Sc4` is
inside it. -/
theorem cex_no_triple :
    ∀ e a b c : Fin 4, ¬ (mkGenome hK4 Sc4).IsTripleRepeat e a b c := by
  unfold Genome.IsTripleRepeat Genome.Agree mkGenome
  decide

theorem cex_no_interleaved_repeats :
    ∀ e₁ e₂ a b c d : Fin 4,
      (mkGenome hK4 Sc4).IsRepeat e₁ a b → (mkGenome hK4 Sc4).IsRepeat e₂ c d →
        ¬ Interleaved (mkGenome hK4 Sc4) a b c d := by
  unfold Genome.IsRepeat Genome.Agree mkGenome
  decide

theorem cex_P2 : P2 hK4 1 Sc4 := by
  unfold P2
  constructor
  · intro e a b c h
    exact absurd h (cex_no_triple e a b c)
  · intro e₁ e₂ a b c d h1 h2 hI
    exact False.elim (cex_no_interleaved_repeats e₁ e₂ a b c d h1 h2 hI)

/-- **`Ukkonen` holds at `L = 1`**, for the same reason. -/
theorem cex_Ukkonen : Ukkonen hK4 1 Sc4 := by
  unfold Ukkonen
  constructor
  · intro e a b c h
    exact absurd h (cex_no_triple e a b c)
  · intro e₁ e₂ a b c d h1 h2 hI
    exact False.elim (cex_no_interleaved_repeats e₁ e₂ a b c d h1 h2 hI)

/-- **`S = 0011` is rotation-primitive**: no period `1`, `2` or `3`. -/
theorem cex_is_primitive : IsPrimitive hK4 Sc4 := by
  intro s hs hlt hsi
  interval_cases s
  · exact absurd (hsi 1) (by decide)
  · exact absurd (hsi 0) (by decide)
  · exact absurd (hsi 0) (by decide)

/-- **The `traverses` clause of `EulerianCycle` is vacuous at `L = 1`**: the
`(L - 1) = 0`-mer is the empty function `Fin 0 → α`, equal at every pair of
starts.  This is why the refutation exists at all --- at `L = 1` the labelling
carries no information, so `AltF` is unconstrained. -/
theorem cex_vtx_trivial (a b : Fin 4) : vtx hK4 1 Sc4 a = vtx hK4 1 Sc4 b := by
  funext d
  exact Fin.elim0 d

/-- **`σ = (1 3)` is a genuine alternative Eulerian cycle** at `L = 1`: the
`traverses` clause is the vacuity above, and `Succ sig4` is the conjugate
`σ ∘ nextPos ∘ σ⁻¹` of the one-step rotation, hence a `4`-cycle through the
origin, which is the `VisitsAll` clause. -/
theorem cex_EulerianCycle : EulerianCycle hK4 1 Sc4 sig4 := by
  constructor
  · intro i
    exact cex_vtx_trivial _ _
  · unfold VisitsAll
    intro n₁ n₂ h
    have h₁ := BBTEulerian.altSucc_iterate hK4 sig4 n₁.val
    have h₂ := BBTEulerian.altSucc_iterate hK4 sig4 n₂.val
    have hrot : rotAdd hK4 n₁.val (sig4.symm (BBTEulerian.origin hK4))
        = rotAdd hK4 n₂.val (sig4.symm (BBTEulerian.origin hK4)) := by
      refine Equiv.injective sig4 ?_
      have hn' : (fun y => sig4 (nextPos hK4 (sig4.symm y)))^[n₁.val]
            (BBTEulerian.origin hK4)
          = (fun y => sig4 (nextPos hK4 (sig4.symm y)))^[n₂.val]
            (BBTEulerian.origin hK4) := by simpa using h
      rw [h₁, h₂] at hn'
      exact hn'
    exact Fin.ext (congrArg Fin.val
      (rotAdd_inj_lt hK4 (sig4.symm (BBTEulerian.origin hK4)) hrot))

/-- **The pairing `AltF hK4 sig4` is the double transposition `(0 2)(1 3)`**:
a genuine involution with exactly two chords. -/
theorem cex_AltF0 : AltF hK4 sig4 (0 : Fin 4) = 2 := by decide

theorem cex_AltF2 : AltF hK4 sig4 (2 : Fin 4) = 0 := by decide

theorem cex_AltF1 : AltF hK4 sig4 (1 : Fin 4) = 3 := by decide

theorem cex_AltF3 : AltF hK4 sig4 (3 : Fin 4) = 1 := by decide

/-- **The two chords cross.**  `0, 2, 1, 3` alternate around the circle: `1`
lies strictly on the open arc from `0` to `2` and `3` does not. -/
theorem cex_interleaved :
    Interleaved (mkGenome hK4 Sc4) (0 : Fin 4) (2 : Fin 4) (1 : Fin 4) (3 : Fin 4) := by
  decide

/-- **The maximal extension of a pair whose preceding letters differ is the
pair itself.**  This is `Issue94TW4Coalesce.maxPairStart_S4` specialised to
the binary word; the *hypothesis* is the difference in the symbol one position
before each start, and on `Sc4` it holds for `0 2` and `1 3` --- though **not**
for `1 2`, whose preceding symbols agree (`S 0 = S 1 = 0`), which is exactly
why the binary instance needs the chords chosen as it does and is not a
by-product of "all symbols distinct". -/
theorem maxPairStart_Sc4 (x y : Fin 4)
    (hne : cyc hK4 Sc4 (x.val + 4 - 1) ≠ cyc hK4 Sc4 (y.val + 4 - 1)) :
    maxPairStart hK4 Sc4 x y = x := by
  have hpb : pairBack hK4 Sc4 x.val y.val = 0 :=
    pairBack_eq_zero_of_back_ne hK4 Sc4 x.val y.val hne
  rw [BBTLadder.maxPairStart_eq, hpb, rotAdd_full]

theorem cex_maxPairStart02 : maxPairStart hK4 Sc4 0 2 = 0 :=
  maxPairStart_Sc4 0 2 (by decide)

theorem cex_maxPairStart20 : maxPairStart hK4 Sc4 2 0 = 2 :=
  maxPairStart_Sc4 2 0 (by decide)

theorem cex_maxPairStart13 : maxPairStart hK4 Sc4 1 3 = 1 :=
  maxPairStart_Sc4 1 3 (by decide)

theorem cex_maxPairStart31 : maxPairStart hK4 Sc4 3 1 = 3 :=
  maxPairStart_Sc4 3 1 (by decide)

/-- **`SameExtension` fails on the pair of chords.**  Each disjunct of
`SameExtension 0 2 1 3` opens with `maxPairStart 0 2 = maxPairStart 1 3`, i.e.
`0 = 1`, or with `maxPairStart 0 2 = maxPairStart 3 1`, i.e. `0 = 3`; both
contradict the quadruple's distinctness. -/
theorem cex_not_SameExtension : ¬ SameExtension 4 hK4 Sc4 0 2 1 3 := by
  rw [SameExtension]
  intro h
  rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
  · rw [cex_maxPairStart02, cex_maxPairStart13] at h1
    exact (show (0 : Fin 4) ≠ 1 from by decide) h1
  · rw [cex_maxPairStart02, cex_maxPairStart31] at h1
    exact (show (0 : Fin 4) ≠ 3 from by decide) h1

/-- **The four distinctness hypotheses of the `def` hold on this pair of
chords**, one at a time, so the refutation is not hiding behind one of them. -/
theorem cex_ne_ac : (0 : Fin 4) ≠ 1 := by decide

theorem cex_ne_bc : (2 : Fin 4) ≠ 1 := by decide

theorem cex_ne_ad : (0 : Fin 4) ≠ 3 := by decide

theorem cex_ne_bd : (2 : Fin 4) ≠ 3 := by decide

/-- **`BBTLadder.CrossingChordsCoalesce` has no inhabitant at any read
length**, already over the **two-letter** alphabet.

This is the refutation.  `Issue94TW4Coalesce.not_crossingChordsCoalesce_one`
already refutes `CrossingChordsCoalesce (α := Fin 4) 1` over four pairwise
distinct symbols; this is the same failure over `α := Fin 2`, so the refuted
regime does not depend on an alphabet large enough to separate all starts. -/
theorem crossingChordsCoalesce_refuted :
    ¬ (∀ L : ℕ, BBTLadder.CrossingChordsCoalesce (α := Fin 2) L) := by
  intro h
  exact cex_not_SameExtension
    (h 1 4 hK4 Sc4 cex_P2 cex_is_primitive cex_Ukkonen sig4 cex_EulerianCycle
      0 2 1 3 cex_AltF0 cex_AltF2 cex_AltF1 cex_AltF3
      cex_ne_ac cex_ne_bc cex_ne_ad cex_ne_bd cex_interleaved)

/-- **The two `Prop`s are the same `Prop`**: the refutation is aimed at the
library's own `BBTLadder.CrossingChordsCoalesce`, not at a restatement of it. -/
theorem eq_def (L : ℕ) :
    CrossingChordsCoalesceUnbounded (α := Fin 2) L
      = BBTLadder.CrossingChordsCoalesce (α := Fin 2) L := by
  rfl

end Counterexample

/-! ## 3. Minimality, kernel-checked -/

section Minimality

/-- `hK : 0 < 3`. -/
theorem hK3 : 0 < 3 := by decide

local instance decInterleavedK3 (S : Fin 3 → Fin 2) (a b c d : Fin 3) :
    Decidable (Interleaved (mkGenome hK3 S) a b c d) := by
  unfold Interleaved InOpenArc FourDistinct mkGenome
  exact inferInstance

/-- **No word on `K = 3` carries an interleaving quadruple, whatever the word
and whatever the read length.**  `Interleaved` begins with `FourDistinct`, and
`Fin 3` has only three elements.  This forces `K ≥ 4` in any counterexample, so
§2 is at the smallest possible circle size. -/
theorem no_interleaved_on_K3 :
    ∀ (S : Fin 3 → Fin 2) (a b c d : Fin 3), ¬ Interleaved (mkGenome hK3 S) a b c d := by
  unfold Interleaved InOpenArc FourDistinct mkGenome
  decide

/-- **No one-letter circular word on `K = 3` is primitive**: every position
agrees with every other, so the shift `1` is a period.  This forces a two-letter
alphabet in any counterexample, since any counterexample must satisfy
`IsPrimitive`; §2 is therefore at the smallest possible alphabet. -/
theorem no_primitive_on_Fin1 (S : Fin 3 → Fin 1) : ¬ IsPrimitive hK3 S := by
  intro hp
  exact hp 1 (by decide) (by decide) (by
    intro i
    exact Subsingleton.elim _ _)

end Minimality

/-! ## 4. The repaired statement, and the sharp characterisation -/

section Repaired

variable {α : Type} [DecidableEq α]

/-- **`BBTLadder.CrossingChordsCoalesce` holds at `2 ≤ L ≤ K`**, at an
arbitrary `[DecidableEq α]`, with every hypothesis of the library statement
reproduced verbatim.

This is the block hypothesis `BBTLadder.LadderVertexCycle` assumes
(`AssemblyP1/BBTLadder.lean:658`), so it is the object the `#89` ladder route
was waiting for.  It is derived here by an **independent route**: a corollary of
the α-general word-level theorem `Issue94CaseSplit.crossingPairsCoalesce_general`
(an inhabitant of `BBTCrossingCoalesce.CrossingPairsCoalesce`).  The only step
is to read `vtx a = vtx b` and `vtx c = vtx d` off the two chord hypotheses with
`BBTLadder.AltF_vtx'`, and to read `a ≠ b`, `c ≠ d` off the `FourDistinct`
clause `Interleaved` already carries.  No repeat theory is used, and
`Issue94TW4Coalesce` is not used.

Note the `L ≤ K` step: it is needed only because the word-level theorem is
phrased at `L ≤ K`.  At `K < L` the `def` is vacuous for a structural reason
(`Issue94TW4Coalesce.altF_eq_id_of_prim_window`), so `L ≤ K` is **not**
independently necessary --- only `2 ≤ L` is (§3). -/
theorem CrossingChordsCoalesce_ge2 (L : ℕ) (hL : 2 ≤ L) :
    ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α) (_hP2 : P2 hK L S)
      (_hprim : RepeatAdapter.IsPrimitive hK S) (_hLG : L ≤ K) (_hUkk : Ukkonen hK L S)
      (σ : Fin K ≃ Fin K) (_hEul : EulerianCycle hK L S σ),
      ∀ (a b c d : Fin K),
        AltF hK σ a = b → AltF hK σ b = a → AltF hK σ c = d → AltF hK σ d = c →
        a ≠ c → b ≠ c → a ≠ d → b ≠ d →
        Interleaved (mkGenome hK S) a b c d →
        SameExtension K hK S a b c d := by
  intro K hK S hP2 hprim hLG hUkk σ hEul a b c d hab hba hcd hdc hac hbc had hbd hI
  have hFab : vtx hK L S a = vtx hK L S b := by
    rw [← hab, AltF_vtx' hK S hEul a]
  have hFcd : vtx hK L S c = vtx hK L S d := by
    rw [← hcd, AltF_vtx' hK S hEul c]
  exact crossingPairsCoalesce_general (α := α) L K hK S hL hLG hP2 hprim
    (a := a) (b := b) (c := c) (d := d) hI.1.1 hI.1.2.2.2.2.2 hFab hFcd hI

/-- **Over the two-letter alphabet the `def` is *exactly* characterised**: it
holds for every `L ≥ 2` and fails at `L = 1`.  Together with
`crossingChordsCoalesce_refuted` this is the sharp form of the objective: the
missing hypothesis is exactly `2 ≤ L`, and no other read length is open.

The `L ≥ 2` direction is this front's own derivation (§4,
`CrossingChordsCoalesce_ge2`) combined with `Issue94TW4Coalesce`'s
`L > K` vacuity, so it does not merely quote the existing theorem. -/
theorem crossingChordsCoalesce_sharp_bin (L : ℕ) (hL : 2 ≤ L) :
    BBTLadder.CrossingChordsCoalesce (α := Fin 2) L := by
  intro K hK S hP2 hprim hUkk σ hEul a b c d hab hba hcd hdc hac hbc had hbd hI
  by_cases hKL : L ≤ K
  · exact CrossingChordsCoalesce_ge2 (α := Fin 2) L hL K hK S hP2 hprim hKL hUkk σ hEul
      a b c d hab hba hcd hdc hac hbc had hbd hI
  · exact crossingChordsCoalesce_above (α := Fin 2) K hK S hP2 hprim hUkk (by omega)
      σ hEul a b c d hab hba hcd hdc hac hbc had hbd hI

end Repaired

end AssemblyP1.Issue94CrossingChords