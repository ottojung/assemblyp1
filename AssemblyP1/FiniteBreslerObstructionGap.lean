import Mathlib
import AssemblyP1.FiniteBayesianSideInformation
import AssemblyP1.FiniteReadStringIsVsUnambiguous
import AssemblyP1.FiniteReadOnlyDecoderCertainty
import AssemblyP1.HistoricalCovers
import AssemblyP1.SourceFaithfulIs

/-!
# The Bresler--Bresler--Tse all-unbridged obstruction is **not** the exact
# necessary-and-sufficient condition for finite read-only recovery (#272, target 5)

This module makes one bounded increment on the remaining open axis of issue #272:
the relationship between the **original information-theoretic repeat-bridging
obstruction** and the exact necessary-and-sufficient condition for finite
Bayesian recovery.

## The source obstruction (attributed, not proved here)

Bresler--Bresler--Tse (2013), Theorem 1 states: *given a DNA sequence `s` and a
set of reads, if there is a pair of interleaved repeats or a triple repeat
whose copies are all unbridged, then there is another sequence `s'` of the same
length under which the likelihood of observing the reads is the same.*  This is a
**necessary** condition for unique reconstruction: the obstruction must be
absent.  It is the source of the "all-unbridged" phrasing that the merged
`I_s` adapter strengthens to "all-bridged" (the MultiBridging/Not-So-Greedy
sufficiency condition).

## The determination

The source obstruction is **necessary but not sufficient** for read-only
decoder certainty on the literal read-string model, and therefore is **not** the
exact necessary-and-sufficient condition.

* **Necessity** (`sourceObstruction_necessary_of_bresler`) is proved from the
  attributed Bresler--Bresler--Tse premise: if the truth genome carries an
  all-unbridged interleaved pair or triple repeat, then there is a same-length
  competitor with the same read likelihood, hence a competitor realizing the
  observed read-string set in a different rotation orbit, so the read-only
  posterior is not one.  The premise is a hypothesis, not an axiom; the
  external theorem is not formalized.
* **Non-sufficiency** (`sourceObstruction_not_sufficient_for_readOnly_certainty`)
  is an unconditional kernel-checked counterexample: the length-`4` binary
  circle `AABB` at read length `L = 2` with sampled starts `R = {0,1}` has
  **no** interleaved pair and **no** triple repeat, so the obstruction is
  absent (`not_sourceObstruction_aabb`), yet the read-realizable support of
  `Y = {AA, AB}` is not a single rotation class (`not_unambiguous_aabb`), so no
  read-only decoder is certain there.  Hence the exact condition is strictly
  stronger than the source obstruction.

The counterexample is deliberately the *same finite read-string model* the merged
adapter uses (length-`4`, two-symbol, read length `2`), so nothing is smuggled
in through a change of convention: same orientation (cyclic rotation), same
genome length, same alphabet, same read-realizable support likelihood.

## Relation to merged #272 objects

* `I_s` (`isPromiseReadString`) is the merged **sufficient** condition; its
  sufficiency is the external Not-So-Greedy premise
  (`FiniteSideInformationReadStringAdapter.sufficient_readStringIS_of_fibreUnique`),
  not proved here.
* `FiniteIsNotNecessaryCertainty` (PR #384) showed `I_s` is **not necessary**
  for read-only certainty.  The present module is the complementary fact about
  the *source obstruction*: it is necessary (attributed) but not sufficient, so
  neither `I_s` nor the all-unbridged obstruction is the exact condition.
* No merged object is redefined, reproved, or duplicated.  `Sp4`, `toGenome4`,
  `orbit`, `Realizable`, `π`, `p` are reused unchanged from
  `AssemblyP1.FiniteReadStringIsVsUnambiguous`; `MatchStarts`, `IsRepeat`,
  `IsTripleRepeat`, `IsTripleRepeatAllBridged`, `Interleaved`, and
  `IsInterleavedPairBridged` are reused unchanged from
  `AssemblyP1.HistoricalCovers` / `AssemblyP1.SourceFaithfulIs`.

No `axiom`, `sorry`, or `admit` is introduced; the axiom audit is
`AssemblyP1/FiniteBreslerObstructionGapAudit.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AssemblyP1.FiniteBreslerObstructionGap

open AssemblyP1.FiniteBayesianSideInformation
open AssemblyP1.FiniteReadStringIsVsUnambiguous
open AssemblyP1.HistoricalCovers
open AssemblyP1.SourceFaithfulIs

variable {α : Type*} [DecidableEq α]

/-! ## 1. The literal Bresler--Bresler--Tse obstruction predicate

The two clauses of Bresler--Bresler--Tse (2013) Theorem 1, transcribed on the
merged repeat/bridging layer: a triple repeat whose three selected copies are
all unbridged, or an interleaved pair of repeats with no bridged copy.  The
quantified repeat lengths range over `Fin S.len`, since `IsRepeat` /
`IsTripleRepeat` already impose `e < S.len`. -/

/-- **All-unbridged triple repeat**: some triple repeat of `S` (at the saturated
match starts of the observed read-string set `Y`) has every selected copy
unbridged. -/
def AllUnbridgedTriple (S : Genome α) (L : ℕ) (Y : Finset (Fin L → α)) : Prop :=
  ∃ (e : Fin S.len) (a b c : Fin S.len),
    S.IsTripleRepeat e.val a b c ∧
      ¬ IsTripleRepeatAllBridged S L (MatchStarts S L Y) e.val a b c

/-- **All-unbridged interleaved pair**: some pair of interleaved repeats of `S`
(at the saturated match starts of `Y`) has no bridged copy. -/
def AllUnbridgedInterleaved (S : Genome α) (L : ℕ)
    (Y : Finset (Fin L → α)) : Prop :=
  ∃ (e₁ e₂ : Fin S.len) (a b c d : Fin S.len),
    S.IsRepeat e₁.val a b ∧ S.IsRepeat e₂.val c d ∧ Interleaved S a b c d ∧
      ¬ IsInterleavedPairBridged S L (MatchStarts S L Y) e₁.val e₂.val a b c d

/-- **The source obstruction** (Bresler--Bresler--Tse 2013, Theorem 1): an
all-unbridged triple repeat or an all-unbridged interleaved pair.  Its absence is
the source's necessary condition for unique reconstruction. -/
def SourceObstruction (S : Genome α) (L : ℕ) (Y : Finset (Fin L → α)) : Prop :=
  AllUnbridgedTriple S L Y ∨ AllUnbridgedInterleaved S L Y

/-! ## 2. Necessity (attributed external premise)

The external Bresler--Bresler--Tse theorem is supplied as the hypothesis
`hBBT`: whenever the truth genome `w` carries the obstruction at `Y`, there is a
same-length competitor `w'` realizing `Y` in a different rotation orbit.  Under
that premise the obstruction is necessary for read-only decoder certainty. -/

/-- **The source obstruction is necessary for read-only certainty** (given the
attributed Bresler--Bresler--Tse equal-likelihood premise).  If some read-only
decoder is certain at `Y` (the supported truth-fibre of `Y` is a single orbit
class), then no realizer of `Y` carries the obstruction. -/
theorem sourceObstruction_necessary_of_bresler (hBBT : ∀ w : Sp4, ∀ Y : Obs2,
    SourceObstruction (toGenome4 w) 2 Y →
      ∃ w' : Sp4, Realizable w' Y ∧ orbit w' ≠ orbit w) :
    ∀ Y : Obs2, Unambiguous π p orbit Y →
      ∀ w : Sp4, Realizable w Y → ¬ SourceObstruction (toGenome4 w) 2 Y := by
  intro Y hU w hw hObs
  obtain ⟨w', hw'real, hw'orb⟩ := hBBT w Y hObs
  have hπw : 0 < π w := by norm_num [π]
  have hπw' : 0 < π w' := by norm_num [π]
  have hpw : 0 < p w Y := (p_pos_iff w Y).mpr hw
  have hpw' : 0 < p w' Y := (p_pos_iff w' Y).mpr hw'real
  exact hw'orb (hU w w' hπw hpw hπw' hpw')

/-! ## 3. The counterexample: `AABB`, `L = 2`, `R = {0, 1}`

The candidate universe is the merged `Sp4` (length-`4` circular spellings over
the two-symbol alphabet `Bit`), the observation is the distinct read-string set
`Obs2`, and the rotation class is the merged canonical code `orbit`.  The
read-realizable support likelihood is the merged `p` (support indicator of any
faithful read likelihood at read length `2`), and the prior is the merged
uniform `π ≡ 1`. -/

/-- The two-block spelling `AABB` (`A = 0`, `B = 1`). -/
def spellAABB : Sp4 := ![0, 0, 1, 1]

/-- The rotation `AAAB` of the triple-`A` spelling. -/
def spellAAAB : Sp4 := ![0, 0, 0, 1]

/-- The witness observation `Y = {AA, AB}`, the read-string set induced by
`AABB` at the starts `{0, 1}`. -/
def Yaabb : Obs2 :=
  observedTypes_ofFinset (toGenome4 spellAABB) 2 ({0, 1} : Finset (Fin 4))

/-- `AABB` realizes `Y = {AA, AB}` via the start set `{0, 1}`. -/
theorem realizable_aabb : Realizable spellAABB Yaabb := ⟨{0, 1}, rfl⟩

/-- The competitor `AAAB` also realizes `Y = {AA, AB}` via the start set
`{0, 2}`: its length-`2` windows are `AA, AA, AB, BA`. -/
theorem realizable_aaab : Realizable spellAAAB Yaabb := ⟨{0, 2}, by decide⟩

/-- `AABB` has **no** triple repeat and **no** interleaved pair at read length
`2`, so the source obstruction is absent: it is not an all-unbridged obstruction
witness. -/
theorem not_sourceObstruction_aabb :
    ¬ SourceObstruction (toGenome4 spellAABB) 2 Yaabb := by
  unfold SourceObstruction AllUnbridgedTriple AllUnbridgedInterleaved
  decide

/-- The canonical rotation codes of `AAAB` and `AABB` differ, so they lie in
different rotation classes. -/
theorem orbit_aaab_ne_aabb : orbit spellAAAB ≠ orbit spellAABB := by
  decide

/-- **`Y = {AA, AB}` is not `Unambiguous`**: both `AABB` and `AAAB` realize it
with positive prior and positive read-realizable likelihood, and they lie in
different rotation classes.  Hence no read-only decoder is certain at `Y`. -/
theorem not_unambiguous_aabb : ¬ Unambiguous π p orbit Yaabb := by
  intro h
  have hπ : ∀ w : Sp4, 0 < π w := fun w => by norm_num [π]
  have := h spellAABB spellAAAB (hπ _) ((p_pos_iff spellAABB Yaabb).mpr realizable_aabb)
    (hπ _) ((p_pos_iff spellAAAB Yaabb).mpr realizable_aaab)
  exact orbit_aaab_ne_aabb this

/-- **The source obstruction is not sufficient for read-only decoder
certainty.**  At the positive-predictive observation `Yaabb = {AA, AB}` the
truth `AABB` carries no all-unbridged triple repeat and no all-unbridged
interleaved pair, yet `Yaabb` is not `Unambiguous`, so no read-only decoder is
certain there.  The exact necessary-and-sufficient condition is therefore
strictly stronger than the source obstruction. -/
theorem sourceObstruction_not_sufficient_for_readOnly_certainty :
    ∃ w : Sp4, ∃ Y : Obs2,
      ¬ SourceObstruction (toGenome4 w) 2 Y ∧ ¬ Unambiguous π p orbit Y :=
  ⟨spellAABB, Yaabb, not_sourceObstruction_aabb, not_unambiguous_aabb⟩

/-- The full counterexample bundle: the observation has positive predictive
mass, the truth realizes it, the truth carries no obstruction, and the
observation is nevertheless ambiguous. -/
theorem counterexample :
    Realizable spellAABB Yaabb ∧
      ¬ SourceObstruction (toGenome4 spellAABB) 2 Yaabb ∧
      ¬ Unambiguous π p orbit Yaabb ∧
      0 < predictiveMass π p (fun _ _ => True) Yaabb :=
  ⟨realizable_aabb, not_sourceObstruction_aabb, not_unambiguous_aabb,
    predictive_pos_of_realizable Yaabb spellAABB realizable_aabb⟩

/-- **Non-sufficiency bundle (attributed necessity + unconditional gap).**  Given
the external premise, the source obstruction is necessary for read-only
certainty, yet the concrete witness above shows it is not sufficient; hence it is
not the exact necessary-and-sufficient condition. -/
theorem sourceObstruction_not_exact_condition (hBBT : ∀ w : Sp4, ∀ Y : Obs2,
    SourceObstruction (toGenome4 w) 2 Y →
      ∃ w' : Sp4, Realizable w' Y ∧ orbit w' ≠ orbit w) :
    (∀ Y : Obs2, Unambiguous π p orbit Y →
      ∀ w : Sp4, Realizable w Y → ¬ SourceObstruction (toGenome4 w) 2 Y) ∧
      ∃ w : Sp4, ∃ Y : Obs2,
        ¬ SourceObstruction (toGenome4 w) 2 Y ∧ ¬ Unambiguous π p orbit Y :=
  ⟨sourceObstruction_necessary_of_bresler hBBT,
    sourceObstruction_not_sufficient_for_readOnly_certainty⟩

end AssemblyP1.FiniteBreslerObstructionGap
