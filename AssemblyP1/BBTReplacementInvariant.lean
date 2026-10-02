import AssemblyP1.BBTSupportInvariant

/-!
# Audit of the `S = 001011`, `L = 3` candidate for the replacement invariant (issue #89)

## Status of this module: an audit, not an invariant

This file previously asserted `p2_hG6_S6_L3 : P2 hG6 3 S6` and built a
refutation of the bad-`θ` variant of `SelectedInterleaved_obstruction` on it.
**That `P2` hypothesis is false**, and is refuted below, kernel-checked.  The
refutation asserted by the earlier version of this file was therefore never
established; the file had never compiled, for this reason and not for a memory
reason (see `docs/bbt-replacement-invariant-host-constraint.md` for the
correction).

What survives at `S = 001011` is recorded faithfully here.  What does *not*
survive is stated as not surviving.  In particular:

- the candidate replacement invariant

  ```text
  bad θ  ⟹  SelectedInterleaved θ  ⟹  LongObstruction
  ```

  is **not** refuted by this instance, because `LongObstruction` holds here
  (`longObstruction_S6_L3`).  Its status is unchanged from front 9412's
  `selectedInterleaved_obstruction_false_00101`: open.

## Why the instance is self-refuting

`S = 001011` has two doubled `(L-1) = 2`-mers whose starts interleave:

```text
01 repeats at starts 1, 3
10 repeats at starts 2, 5
```

The four starts `1 < 2 < 3 < 5` alternate around the circle, and both
constituents have length `2 > L - 2 = 1`.  This is precisely the second
clause of `P2`, and precisely what `SelectedInterleaved` asks for.  The module's
own witness `T6` needs `SelectedInterleaved`, so at `L = 3` the mechanism that
would certify the counterexample is the very mechanism that disqualifies the
genome from being `P2`.  `001011` is exactly the shape of genome that
`AssemblyP1.InterleavingNeededCounterexample` exists to talk about.

## Cost notes (measured on this host, 2026-10-02)

Every `decide` here is over a *fixed* witness or a *fixed* vertex.  The
`6^6 = 46 656`-fold enumeration is not reintroduced anywhere: `SelectedTriple`
is `∃ v, 3 ≤ (fibre v).card ∧ Selects θ v`, so `no_triple_mult_001011` takes the
witness and splits over the four `(L-1) = 2`-tuples.  Whole-file elaboration
via `lake env lean` measures 3.4 s and well under 1 GiB.
-/

namespace AssemblyP1.BBTReplacement

open SourceFaithfulIs
open AssemblyP1
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTEulerianSearch
open AssemblyP1.BBTSupport

set_option linter.unusedSectionVars false

/-- `0 < 6`, so that the numerals of the instance fix the length. -/
theorem hG6 : 0 < 6 := by decide

/-- **The candidate word `S = 001011`.** -/
def S6 : Fin 6 → Fin 2 := ![0, 0, 1, 0, 1, 1]

/-- **The candidate successor map** `θ = [3,5,1,4,2,0]` on `Fin 6`.
Its orbit from the origin is `0, 3, 4, 2, 1, 5`, a single six-cycle. -/
def T6 : Fin 6 → Fin 6 := ![3, 5, 1, 4, 2, 0]

instance : NeZero (mkGenome hG6 S6).len := ⟨by norm_num [mkGenome]⟩

/-! ## 1. The refutation of the `P2` hypothesis, kernel-checked -/

/-- **The witness that kills the instance.** `01` is a maximal repeat of length
`2` at starts `1` and `3`; `10` is a maximal repeat of length `2` at starts `2`
and `5`; the four starts interleave around the circle. -/
theorem interleaved_pair_001011 :
    (mkGenome hG6 S6).IsRepeat 2 1 3 ∧
      (mkGenome hG6 S6).IsRepeat 2 2 5 ∧
      Interleaved (mkGenome hG6 S6) 1 3 2 5 := by
  unfold mkGenome Genome.IsRepeat Genome.Agree Genome.window Genome.Preceding
    Genome.Following Interleaved FourDistinct InOpenArc Genome.cycl
  decide

/-- **`S = 001011` does NOT satisfy `P2` at `L = 3`, kernel-checked.**
The first clause (no maximal triple repeat of length `≥ L - 1 = 2`) is fine; the
second fails, witnessed by `interleaved_pair_001011`: both constituents have
length `2`, and `¬ (2 ≤ L - 2 = 1)`.

This is the refutation of `p2_hG6_S6_L3` as previously asserted in this file. -/
theorem not_P2_001011_L3 : ¬ P2 hG6 3 S6 := by
  rintro ⟨-, h2⟩
  obtain ⟨h1, h2', h3⟩ := interleaved_pair_001011
  exact absurd (h2 2 2 1 3 2 5 h1 h2' h3) (by decide)

/-- **The positive form of the same fact: `S = 001011` HAS a long obstruction
at `L = 3`**, with the interleaved pair above as the explicit witness.

Consequence: `¬ LongObstruction hG6 3 S6` is **false** here.  Any refutation of
a conditional that concludes in `LongObstruction` needs `¬ LongObstruction` at
its witness genome, so this instance cannot serve as that witness. -/
theorem longObstruction_001011 : LongObstruction hG6 3 S6 := by
  obtain ⟨h1, h2, h3⟩ := interleaved_pair_001011
  exact Or.inr ⟨2, 2, 1, 3, 2, 5, h1, h2, h3, by decide, by decide⟩

/-! ## 2. What survives at this instance -/

/-- **`θ = T6` is a bijective, fibre-preserving, one-cycle successor map, and
it is BAD**: its spelled vertex cycle `00, 01, 11, 10, 01, 10` is not a cyclic
shift of the truth's `00, 01, 10, 01, 11, 10`.

This is the clause that `BBTSupportInvariant.harmless_selected_crossing_00101`
lacks: there the crossing `θ` was *good*, so `SupportDichotomy` never applied to
it.  Here `θ` is genuinely bad, so it *is* in the scope of `SupportDichotomy`. -/
theorem bad_001011 :
    Function.Bijective T6 ∧
      FibrePreserving (hG := hG6) (L := 3) S6 T6 ∧
      OneCycle hG6 T6 ∧
      ¬ OrbitVertexEq (hG := hG6) (L := 3) S6 T6 := by
  decide

/-- **`T6` is a *selected* interleaving**: the interleaved pair
`01 ↦ {1,3}`, `10 ↦ {2,5}` is rematched. -/
theorem selectedInterleaved_T6 :
    SelectedInterleaved (hG := hG6) (L := 3) S6 T6 := by
  decide

/-- **No `(L-1)`-mer of `S = 001011` at `L = 3` has multiplicity `≥ 3`.**
The fibres are `00 ↦ {0}`, `01 ↦ {1,3}`, `10 ↦ {2,5}`, `11 ↦ {4}`, so the
`(T)` clause of `SupportDichotomy` is vacuous at this instance for every `θ`.

**Proof note.**  This was originally closed by `decide` over all `6^6`
candidate `θ`, which is a pathological elaboration (measured at 13.84 GiB and
SIGKILLed).  Since `SelectedTriple` is an `∃ v, 3 ≤ (fibre v).card ∧ Selects θ v`,
we instead introduce the existential witness and discharge each of the four
`(L-1) = 2`-tuples by `fin_cases` plus a small `decide` on the fibre
cardinality.  This is a four-fold case split, not a `6^6` enumeration. -/
theorem no_triple_mult_001011 :
    ∀ θ : Fin 6 → Fin 6, ¬ SelectedTriple (hG := hG6) (L := 3) S6 θ := by
  intro θ
  rintro ⟨v, hcard, _⟩
  fin_cases v <;> exact absurd hcard (by decide)

/-- **The support dichotomy itself holds at this instance**, witnessed by the
bad `θ = T6`: the `(T)` disjunct is unavailable for all `θ`, and `(I)` holds at
`T6`. -/
theorem supportDichotomy_T6 :
    SelectedTriple (hG := hG6) (L := 3) S6 T6 ∨
      SelectedInterleaved (hG := hG6) (L := 3) S6 T6 :=
  Or.inr selectedInterleaved_T6

/-- **Anti-vacuity of the surviving facts, and their limit.** `UniqueAt` at this
instance is **false**: `S = 001011` admits a bijective, fibre-preserving,
one-cycle `θ` whose spelled vertex cycle is not the truth's.  Via
`AssemblyP1.BBTEulerianSearch.uniqueAt_iff_orbit` (an `Iff`).

This is stated so that no reader can mistake the surviving facts for evidence
against `thm:BBT`, and it is exactly why they are *not* evidence for `#89`
either.  `BBTCompleteSpectrumUniqueness` is a statement about the complete
`L`-spectrum; `UniqueAt` quantifies over all one-cycle fibre-preserving
permutations of the *starts*, a strictly larger class.  The genome here also
has a `LongObstruction` (`longObstruction_001011`), so it is outside
`thm:BBT`'s hypothesis by construction. -/
theorem not_uniqueAt_001011 : ¬ UniqueAt hG6 3 S6 := by
  rw [uniqueAt_iff_orbit]
  intro h
  obtain ⟨hbi, hfp, hoc, hbad⟩ := bad_001011
  exact hbad (h T6 hbi hfp hoc)

/-! ## 3. What a genuine refutation of the candidate would need

Stated as a `Prop`, deliberately **not** proved and **not** claimed.  This is
the shape of witness a future refutation has to exhibit: a `P2` genome at which
a *bad* `θ` is a selected interleaving.  Front 9412 supplied the good-`θ`
version on `00101`; this file's earlier version tried to supply the bad-`θ`
version on `001011`, which is not `P2` and so does not.

Note the hypothesis `¬ LongObstruction` is redundant but kept explicit, since
`P2` gives it (`AssemblyP1.BBTEulerian.not_longObstruction_of_P2`) only via the
`2 ≤ L` side condition, and stating it keeps the intended use visible. -/
def BadSelectedInterleavingWitness : Prop :=
  ∃ (G : ℕ) (L : ℕ) (S : Fin G → Fin 2) (hG : 0 < G) (θ : Fin G → Fin G),
    P2 hG L S ∧ ¬ LongObstruction hG L S ∧
      Function.Bijective θ ∧ FibrePreserving (hG := hG) (L := L) S θ ∧
      OneCycle hG θ ∧ ¬ OrbitVertexEq (hG := hG) (L := L) S θ ∧
      SelectedInterleaved (hG := hG) (L := L) S θ

end AssemblyP1.BBTReplacement
