import Mathlib
import AssemblyP1.FiniteBayesianSideInformation
import AssemblyP1.HistoricalCovers
import AssemblyP1.FiniteSideInformationReadStringAdapter
import AssemblyP1.FiniteReadOnlyDecoderCertainty
import AssemblyP1.FiniteReadStringIsVsUnambiguous

/-!
# `I_s` is **not** necessary for read-only decoder certainty (#272, subclaim 1)

This module settles the explicitly-OPEN subclaim (1) of issue #272:

> Is the Shomorony--Kim--Courtade--Tse (2016) information-feasibility condition
> `I_s` **necessary** for decoder-level certainty, or only sufficient?

## Determination

`I_s` is **sufficient but not necessary**.  The prior order results
(`AssemblyP1.FiniteReadStringIsVsUnambiguous`, PR #356) show `I_s` is sufficient
and incomparable with the read-only promise `Unambiguous`; they do **not** address
necessity.  This module supplies the missing direction with a kernel-checked
counterexample: a positive-predictive read-string observation at which a read-only
decoder is **certain** (target 3), produced by a truth genome that **fails** `I_s`.

The counterexample is the length-`4` binary circle `AAAB` with read length `L = 3`
and sampled starts `R = {0, 2}`:

* the induced read-string set is `Y = {AAA, ABA}`;
* **coverage holds** (`HistoricalCovers`), yet the maximal triple repeat `A` at
  starts `{0, 1, 2}` has only its middle copy bridged, so the all-bridged-triple
  clause of `I_s` fails: `¬ isPromiseReadString (toGenome4 AAAB) 3 Y`;
* the read-realizable support of `Y` is **exactly the four rotations of `AAAB`**,
  a single orbit class, so by the merged target-3 characterization
  (`exists_readOnly_decoder_certain_iff_support_singleton`) some read-only decoder
  reaches posterior one at `Y`.

Hence `I_s` cannot be necessary for the existence of a certain read-only decoder.
The failure is on the **triple-bridging** clause, not on coverage; it is exactly
the gap between Bresler--Bresler--Tse (2013) Theorem 1 (which forces ambiguity
only when *all* copies of a triple repeat are unbridged) and the stronger
*all-bridged* requirement of `I_s`.

## Scope and trust boundary

* **Information-theoretic level (this module).**  "Decoder-level certainty" is the
  exact target-3 notion: some read-only decoder reaches posterior one at the read
  string.  At this level the determination is definitive: `I_s` is not necessary.
* **Specific Not-So-Greedy algorithm.**  The 2016 algorithm is **not** formalized
  here (it remains the attributed external premise in
  `AssemblyP1.ConditionalIdentifiability`).  Whether the *particular* Not-So-Greedy
  decoder is correct on such non-`I_s` inputs is an algorithmic question outside
  the kernel boundary and stays OPEN; this module asserts nothing about it.
* Nothing here duplicates or re-verifies merged #266/#269/#271, PR #345
  (`FiniteReadOnlyDecoderCertainty`) or PR #356 (`FiniteReadStringIsVsUnambiguous`):
  those results are imported and reused unchanged.

No `axiom`, `sorry`, or `admit` is introduced; the axiom audit is
`AssemblyP1/FiniteIsNotNecessaryCertaintyAudit.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AssemblyP1.FiniteIsNotNecessaryCertainty

open AssemblyP1.FiniteBayesianSideInformation
open AssemblyP1.HistoricalCovers
open AssemblyP1.FiniteSideInformationReadStringAdapter
open AssemblyP1.FiniteReadOnlyDecoderCertainty
open AssemblyP1.FiniteReadStringIsVsUnambiguous
open AssemblyP1.SourceFaithfulIs

/-! ## 1. The concrete length-`4`, read-length-`3` read-realizable model

The candidate universe is the merged `Sp4 = Fin 4 → Bit` (length-`4` circular
spellings over the two-symbol alphabet `Bit`), the observation is the distinct
read-string set `Finset (Fin 3 → Bit)`, and the rotation class is the merged
canonical rotation code `orbit`.  The read-realizable support likelihood is the
support indicator of any faithful read likelihood at read length `3`. -/

/-- The read-string observation space at read length `3`. -/
abbrev Obs3 := Finset (Fin 3 → Bit)

/-- **Read-realizable support at read length `3`**: the spelling `w` can produce
the observed read-string set `Y` iff some start set induces exactly `Y`. -/
def Realizable3 (w : Sp4) (Y : Obs3) : Prop :=
  ∃ R : Finset (Fin 4), observedTypes_ofFinset (toGenome4 w) 3 R = Y

/-- Uniform (unnormalized) prior on spellings. -/
noncomputable def π3 : Sp4 → ℝ := fun _ => 1

/-- **Read-realizable support likelihood at read length `3`**: `1` when `w` can
produce `Y`, `0` otherwise. -/
noncomputable def p3 : Sp4 → Obs3 → ℝ := by
  classical
  exact fun w Y => if Realizable3 w Y then 1 else 0

theorem π3_nonneg : ∀ g : Sp4, 0 ≤ π3 g := fun _ => by norm_num [π3]

theorem p3_nonneg : ∀ g : Sp4, ∀ Y : Obs3, 0 ≤ p3 g Y := by
  classical
  intro g Y
  unfold p3
  by_cases h : Realizable3 g Y <;> simp [h]

/-- Positivity of the read-realizable likelihood is exactly realizability. -/
theorem p3_pos_iff (w : Sp4) (Y : Obs3) : 0 < p3 w Y ↔ Realizable3 w Y := by
  classical
  unfold p3
  by_cases h : Realizable3 w Y <;> simp [h]

/-- The merged canonical rotation code `orbit` takes values in `{0,…,15}`: it is
the minimum of the four length-`4` base-`2` rotation codes. -/
theorem orbit_le_toNat (g : Sp4) : orbit g ≤ toNat g := by
  simp only [orbit]
  exact min_le_left _ _

theorem toNat_lt_sixteen (g : Sp4) : toNat g < 16 := by
  unfold FiniteReadStringIsVsUnambiguous.toNat
  have h0 := (g 0).isLt
  have h1 := (g 1).isLt
  have h2 := (g 2).isLt
  have h3 := (g 3).isLt
  omega

theorem orbit_lt_sixteen (g : Sp4) : orbit g < 16 :=
  lt_of_le_of_lt (orbit_le_toNat g) (toNat_lt_sixteen g)

/-- The canonical rotation code, as a finite codomain `Fin 16` so that the merged
posterior machinery (which needs a finite orbit type) applies. -/
def orbitFin (g : Sp4) : Fin 16 := ⟨orbit g, orbit_lt_sixteen g⟩

/-! ## 2. The witness: `AAAB`, `L = 3`, `R = {0, 2}` -/

/-- The spelling `AAAB` (`A = 0`, `B = 1`). -/
def spellAAAB : Sp4 := ![0, 0, 0, 1]

/-- The witness observation `Y = {AAA, ABA}`, the read-string set induced by
`AAAB` at the starts `{0, 2}`. -/
def Yaaab : Obs3 :=
  observedTypes_ofFinset (toGenome4 spellAAAB) 3 ({0, 2} : Finset (Fin 4))

/-- `AAAB` realizes `Yaaab = {AAA, ABA}` via the start set `{0, 2}`. -/
theorem realizable_aaab : Realizable3 spellAAAB Yaaab := ⟨{0, 2}, rfl⟩

/-- **Historical coverage holds** at `(AAAB, 3, {0,2})`: every position lies
within `L - 1 = 2` of a match start of the observed read set `{AAA, ABA}`.  So the
`I_s` failure below is **not** a coverage failure. -/
theorem coverage_holds :
    HistoricalCovers (toGenome4 spellAAAB) 3
      (observedTypes_ofFinset (toGenome4 spellAAAB) 3 ({0, 2} : Finset (Fin 4))) := by
  decide

/-- The length-`1` word `A` occurs at the three distinct starts `0, 1, 2`: a
literal three-occurrence repeat, indeed a maximal triple repeat (`AAAB` has
preceding symbols `B, A, A` and following symbols `A, A, B`, neither constant). -/
theorem triple_occurrence : IsTripleOccurrence (toGenome4 spellAAAB) 1 0 1 2 := by
  decide

/-- The triple occurrence `A` at `{0,1,2}` is **not** all-bridged at read length
`3`: a length-`3` read bridges a length-`1` copy only from the immediately
preceding start, and among the match starts `{0, 2}` only start `0` (bridging the
middle copy at `1`) qualifies. -/
theorem triple_not_allBridged :
    ¬ IsTripleRepeatAllBridged (toGenome4 spellAAAB) 3
      (MatchStarts (toGenome4 spellAAAB) 3 Yaaab) 1 0 1 2 := by
  decide

/-- **`I_s` fails at `(AAAB, 3, {0,2})`.**  Historical coverage holds and the
literal/maximal triple occurrence `A` at `{0,1,2}` is not all-bridged, so the
literal historical information-feasibility predicate fails: the read-string
adapter promise `isPromiseReadString` is false. -/
theorem not_isPromise_aaab :
    ¬ isPromiseReadString (toGenome4 spellAAAB) 3 Yaaab := by
  unfold isPromiseReadString
  decide

/-! ## 3. The observation `Yaaab` is read-only certain: one orbit class -/

/-- **Every read-realizer of `Yaaab = {AAA, ABA}` is a rotation of `AAAB`.**  A
length-`4` binary circle with both `AAA` and `ABA` as length-`3` windows has
exactly one `B`, forced to sit so that the circle is `AAAB` up to rotation. -/
theorem realizable_orbit :
    ∀ w : Sp4, Realizable3 w Yaaab → orbit w = orbit spellAAAB := by
  unfold Realizable3
  decide

/-- The `Fin 16` form of `realizable_orbit`. -/
theorem realizable_orbitFin (w : Sp4) (hw : Realizable3 w Yaaab) :
    orbitFin w = orbitFin spellAAAB :=
  Fin.ext (realizable_orbit w hw)

/-- **`Yaaab` is `Unambiguous`.**  Every positive-likelihood candidate at `Yaaab`
is a rotation of `AAAB`, so the read-realizable support is a single rotation
class. -/
theorem unambiguous_yaaab : Unambiguous π3 p3 orbitFin Yaaab := by
  intro g h _ hpg _ hph
  rw [realizable_orbitFin g ((p3_pos_iff g Yaaab).mp hpg),
    realizable_orbitFin h ((p3_pos_iff h Yaaab).mp hph)]

/-- `Yaaab` has positive predictive probability. -/
theorem predictive_pos_yaaab :
    0 < predictiveMass π3 p3 (fun _ _ => True) Yaaab := by
  have hjoint : 0 < jointMass π3 p3 (fun _ _ => True) spellAAAB Yaaab :=
    (jointMass_pos_iff π3 p3 (fun _ _ => True) π3_nonneg p3_nonneg spellAAAB Yaaab).mpr
      ⟨by norm_num [π3], (p3_pos_iff spellAAAB Yaaab).mpr realizable_aaab, trivial⟩
  unfold predictiveMass
  exact lt_of_lt_of_le hjoint
    (Finset.single_le_sum
      (fun h _ => jointMass_nonneg π3 p3 (fun _ _ => True) π3_nonneg p3_nonneg h Yaaab)
      (Finset.mem_univ spellAAAB))

/-- **Some read-only decoder is certain at `Yaaab`.**  This is the merged target-3
characterization applied to the single-orbit observation `Yaaab`: the support is
nonempty (`AAAB` realizes it with positive prior and likelihood) and lies in one
orbit class (`unambiguous_yaaab`). -/
theorem some_readOnly_decoder_certain :
    ∃ A : Obs3 → Sp4,
      posteriorMass π3 p3 (fun _ _ => True) orbitFin Yaaab (orbitFin (A Yaaab)) = 1 :=
  (exists_readOnly_decoder_certain_iff_support_singleton π3 p3 orbitFin
      π3_nonneg p3_nonneg Yaaab).mpr
    ⟨unambiguous_yaaab, spellAAAB, by norm_num [π3],
      (p3_pos_iff spellAAAB Yaaab).mpr realizable_aaab⟩

/-! ## 4. The determination: `I_s` is not necessary for read-only certainty -/

/-- The `I_s` promise as a truth-dependent promise on the concrete model. -/
def IsPromiseIS3 (w : Sp4) (Y : Obs3) : Prop := isPromiseReadString (toGenome4 w) 3 Y

/-- **`I_s` is necessary for read-only decoder certainty** when every observation
at which some read-only decoder is certain is promised by *every* candidate that
realizes it.  This is the exact formal reading of "necessary for the
decoder-level certainty guarantee". -/
def NecessaryForReadOnlyCertainty (E : Sp4 → Obs3 → Prop) : Prop :=
  ∀ Y, (∃ A : Obs3 → Sp4,
        posteriorMass π3 p3 (fun _ _ => True) orbitFin Y (orbitFin (A Y)) = 1) →
    ∀ w, Realizable3 w Y → E w Y

/-- **The counterexample bundle.**  At the positive-predictive observation
`Yaaab`: some read-only decoder is certain, the truth `AAAB` realizes it, yet
`AAAB` fails `I_s`.  Every conjunct is kernel-checked. -/
theorem counterexample :
    (∃ A : Obs3 → Sp4,
        posteriorMass π3 p3 (fun _ _ => True) orbitFin Yaaab (orbitFin (A Yaaab)) = 1) ∧
      Realizable3 spellAAAB Yaaab ∧
      ¬ IsPromiseIS3 spellAAAB Yaaab ∧
      0 < predictiveMass π3 p3 (fun _ _ => True) Yaaab :=
  ⟨some_readOnly_decoder_certain, realizable_aaab,
    not_isPromise_aaab, predictive_pos_yaaab⟩

/-- **`I_s` is not necessary for read-only decoder certainty.**  There is a
positive-predictive read-string observation at which some read-only decoder is
certain, and a candidate realizing it that is not `I_s`-promising.  Hence no
theorem of the form "read-only certainty implies `I_s`" can hold on this model,
so `I_s` is a sufficient but not necessary structural certificate. -/
theorem is_not_necessary_for_readOnly_certainty :
    ¬ NecessaryForReadOnlyCertainty IsPromiseIS3 := by
  intro h
  exact not_isPromise_aaab (h Yaaab some_readOnly_decoder_certain spellAAAB realizable_aaab)

end AssemblyP1.FiniteIsNotNecessaryCertainty
