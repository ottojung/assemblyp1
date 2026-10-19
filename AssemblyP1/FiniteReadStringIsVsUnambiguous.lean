import Mathlib
import AssemblyP1.FiniteBayesianSideInformation
import AssemblyP1.FiniteSideInformationOrder
import AssemblyP1.FiniteSideInformationReadStringAdapter

/-!
# The ordering of the literal read-string `I_s` adapter against `Unambiguous` (#272)

This module settles, on the **merged literal read-string adapter**
(`AssemblyP1.FiniteSideInformationReadStringAdapter.isPromiseReadString`,
PR #297) the ordering question left OPEN by
`docs/issue272-is-vs-unambiguous-ordering.md`:

> Is the read-dependent source-faithful information-feasibility promise
> `isPromiseReadString` ordered against the read-only promise `Unambiguous`:
> does `I_s ⇒ Unambiguous`, does `Unambiguous ⇒ I_s`, or neither?

## The answer: neither, now kernel-checked on the adapter

The verdict is **neither** (incomparable), and the reason is made precise by a
concrete finite read-realizable model rather than by the earlier structural
"different promise families" argument alone.  The two promises constrain
**different fibres**:

* `Unambiguous π p orbit Y` is a condition on the **read-realizable support**
  of `Y`: every candidate `g` that can produce the observed read-string set `Y`
  (i.e. `p g Y > 0`) lies in a single rotation class.  We take the likelihood
  `p g Y = 1` iff some start set on `g` induces exactly `Y`, `0` otherwise — the
  *support* of any faithful read likelihood.
* `isPromiseReadString S L Y` is a condition on the **`I_s`-feasible fibre** of
  `Y`: some placement `R` on `S` induces `Y` **and** satisfies the literal
  historical `I_s` (`HistoricalInformationFeasibleLiteral`).

A candidate can be read-realizable without being `I_s`-feasible, so the two
fibres differ, and each direction of the implication fails:

1. **`I_s` does not imply `Unambiguous`** (`isPromiseRS_not_imp_unambiguous`).
   On the length-`4`, read-length-`2` model, `g = ABAB` is `I_s`-feasible with
   the start set `{0,1}` and observation `Y = {AB, BA}`
   (`isPromiseRS_abab_yabba`), but `Y` is realized by `14` genomes spanning
   `4` rotation classes (`ABAB` and `AABB` are two of them, in different
   orbits).  Hence `¬ Unambiguous π p orbit Y` even though `I_s` holds.
   Equivalently: the literal historical `I_s` is **not** sufficient for
   orbit-pinning in the read-realizable model.
2. **`Unambiguous` does not imply `I_s`**
   (`unambiguous_not_imp_isPromiseRS`).  For the observation `Y = {AA, BB}`
   the read-realizable support is *exactly* the four rotations of `AABB`
   (`realizable_yaabb_orbit`), a single rotation class, so `Unambiguous` holds
   (`unambiguous_yaabb`); but the realizer `BBAA` is not `I_s`-feasible
   (`not_isPromiseRS_bbaa_yaabb`: its only placement `{0,2}` fails historical
   coverage).

## Reconciliation with the external Not-So-Greedy premise

This refutation does **not** contradict the external Shomorony--Kim--Courtade--Tse
(2016) guarantee, because that guarantee constrains the **`I_s`-feasible** fibre
(`AssemblyP1.ConditionalIdentifiability.feasible_fibre_unique`), not the
read-realizable fibre.  In the direction-1 witness the different-orbit
competitor `AABB` is read-realizable but **not** `I_s`-feasible
(`not_isPromiseRS_aabb_yabba`), so no feasible-fibre uniqueness is violated.
The external guarantee remains an attributed premise; nothing here asserts it,
and no `axiom`, `sorry`, `admit`, or `native_decide` is introduced.  The axiom
audit is `AssemblyP1/FiniteReadStringIsVsUnambiguousAudit.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AssemblyP1.FiniteReadStringIsVsUnambiguous

open AssemblyP1.FiniteBayesianSideInformation
open AssemblyP1.FiniteSideInformationReadStringAdapter
open AssemblyP1.HistoricalCovers
open AssemblyP1.SourceFaithfulIs

/-! ## 1. The concrete length-`4`, two-symbol read-string model

A candidate is a length-`4` circular spelling over the two-symbol alphabet
`Bit = Fin 2`; the observation is the set of distinct length-`2` read strings,
`Finset (Fin 2 → Bit)`. -/

/-- The two-symbol read alphabet. -/
abbrev Bit := Fin 2

/-- A length-`4` circular candidate, represented by its spelling. -/
abbrev Sp4 := Fin 4 → Bit

/-- The read-string observation space: sets of distinct length-`2` read strings. -/
abbrev Obs2 := Finset (Fin 2 → Bit)

/-- The circular genome carried by a length-`4` spelling. -/
abbrev toGenome4 (w : Sp4) : Genome Bit where
  len := 4
  len_pos := by norm_num
  sym := w

/-- **The merged literal read-string adapter** at the concrete length-`4`,
read-length-`2` spelling model: the adapter promise of
`AssemblyP1.FiniteSideInformationReadStringAdapter`. -/
def isPromiseRS (w : Sp4) (Y : Obs2) : Prop := isPromiseReadString (toGenome4 w) 2 Y

/-- The merged spelling-level adapter, definitionally equal to `isPromiseRS`. -/
theorem isPromiseRS_iff_spelling (w : Sp4) (Y : Obs2) :
    isPromiseRS w Y ↔ isPromiseReadStringSpelling 4 2 (by norm_num) w Y :=
  Iff.rfl

/-! ### Rotation orbit

`orbit` is the **canonical rotation code**: the minimum of the base-`2`
encoding `toNat` over the four rotations of a spelling.  It is a complete
rotation-class invariant (`orbit_rot` records invariance; the minimum over the
whole class is what makes it complete), so `orbit g = orbit h` expresses "`g`
and `h` are circular rotations of each other". -/

/-- Base-`2` encoding of a length-`4` spelling (values in `{0,…,15}`). -/
def toNat (g : Sp4) : ℕ :=
  (g 0).val + 2 * (g 1).val + 4 * (g 2).val + 8 * (g 3).val

/-- Rotate a length-`4` spelling by `j` positions. -/
def rot (g : Sp4) (j : Fin 4) : Sp4 := fun i => g (i + j)

/-- Canonical rotation code: the minimum `toNat` over the four rotations. -/
def orbit (g : Sp4) : ℕ :=
  min (toNat g) (min (toNat (rot g 1)) (min (toNat (rot g 2)) (toNat (rot g 3))))

/-- **Rotation invariance of the canonical code.**  Rotating a spelling does
not change its orbit code. -/
theorem orbit_rot : ∀ g : Sp4, ∀ j : Fin 4, orbit (rot g j) = orbit g := by decide

/-! ### Read-realizable support, prior and likelihood -/

/-- **Read-realizable support**: the candidate `w` can produce the observed
read-string set `Y` iff some start set induces exactly `Y`. -/
abbrev Realizable (w : Sp4) (Y : Obs2) : Prop :=
  ∃ R : Finset (Fin 4), observedTypes_ofFinset (toGenome4 w) 2 R = Y

/-- Uniform (unnormalized) prior on spellings. -/
noncomputable def π : Sp4 → ℝ := fun _ => 1

/-- **Read-realizable support likelihood**: `1` when `w` can produce `Y`, `0`
otherwise.  This is the support indicator of any faithful read likelihood; only
its positivity matters for `Unambiguous`. -/
noncomputable def p : Sp4 → Obs2 → ℝ := fun w Y => if Realizable w Y then 1 else 0

theorem π_nonneg : ∀ g : Sp4, 0 ≤ π g := fun _ => by norm_num [π]

theorem p_nonneg : ∀ g : Sp4, ∀ Y : Obs2, 0 ≤ p g Y := by
  intro g Y
  by_cases h : Realizable g Y <;> simp [p, h]

/-- Positivity of the read-realizable likelihood is exactly realizability. -/
theorem p_pos_iff (w : Sp4) (Y : Obs2) : 0 < p w Y ↔ Realizable w Y := by
  unfold p
  by_cases h : Realizable w Y <;> simp [h]

/-- The observation `Y` has **positive predictive probability** as soon as some
candidate can realize it.  This is the domain on which the ordering question is
asked ("all positive-probability read-string observations"). -/
theorem predictive_pos_of_realizable (Y : Obs2) (g : Sp4) (hg : Realizable g Y) :
    0 < predictiveMass π p (fun _ _ => True) Y := by
  have hjoint : 0 < jointMass π p (fun _ _ => True) g Y :=
    (jointMass_pos_iff π p (fun _ _ => True) π_nonneg p_nonneg g Y).mpr
      ⟨by norm_num [π], (p_pos_iff g Y).mpr hg, trivial⟩
  unfold predictiveMass
  exact lt_of_lt_of_le hjoint
    (Finset.single_le_sum
      (fun h _ => jointMass_nonneg π p (fun _ _ => True) π_nonneg p_nonneg h Y)
      (Finset.mem_univ g))

/-! ## 2. The two observations and the two witness candidates -/

/-- The period-`2` spelling `ABAB` (`A = 0`, `B = 1`). -/
def spellABAB : Sp4 := ![0, 1, 0, 1]

/-- The two-block spelling `AABB`. -/
def spellAABB : Sp4 := ![0, 0, 1, 1]

/-- The rotation `BBAA` of `AABB`. -/
def spellBBAA : Sp4 := ![1, 1, 0, 0]

/-- `Y = {AB, BA}`, the read-string set induced by `ABAB` at starts `{0,1}`. -/
def Yabba : Obs2 := observedTypes_ofFinset (toGenome4 spellABAB) 2 ({0, 1} : Finset (Fin 4))

/-- `Y = {AA, BB}`, the read-string set induced by `BBAA` at starts `{0,2}`. -/
def Yaabb : Obs2 := observedTypes_ofFinset (toGenome4 spellBBAA) 2 ({0, 2} : Finset (Fin 4))

/-! ## 3. Direction 1: `I_s` does not imply `Unambiguous` -/

/-- `ABAB` realizes `Yabba = {AB, BA}` via the start set `{0,1}`. -/
theorem realizable_abab_yabba : Realizable spellABAB Yabba := ⟨{0, 1}, by decide⟩

/-- `AABB` realizes `Yabba = {AB, BA}` via the start set `{1,3}`. -/
theorem realizable_aabb_yabba : Realizable spellAABB Yabba := ⟨{1, 3}, by decide⟩

/-- The two realizers `ABAB` and `AABB` lie in different rotation classes. -/
theorem orbit_aabb_ne_abab : orbit spellAABB ≠ orbit spellABAB := by decide

/-- **`ABAB` is `I_s`-promising at `Yabba`.**  The start set `{0,1}` induces
`{AB, BA}` and satisfies the literal historical `I_s` (`ABAB` has period `2`,
so it carries no maximal repeat and no triple occurrence, while historical
coverage is saturated). -/
theorem isPromiseRS_abab_yabba : isPromiseRS spellABAB Yabba := by
  unfold isPromiseRS isPromiseReadString
  exact ⟨{0, 1}, rfl, by decide⟩

/-- **General two-orbit refutation of `Unambiguous`.**  If a single observation
is realized by two candidates in different rotation classes, then it is not
`Unambiguous`. -/
theorem not_unambiguous_of_two_orbit_realizers (g h : Sp4) (Y : Obs2)
    (hg : Realizable g Y) (hh : Realizable h Y) (hne : orbit g ≠ orbit h) :
    ¬ Unambiguous π p orbit Y := by
  intro hu
  exact hne (hu g h (by norm_num [π]) ((p_pos_iff g Y).mpr hg)
    (by norm_num [π]) ((p_pos_iff h Y).mpr hh)).symm

/-- **Direction 1, refuted.**  `I_s` holds at `(ABAB, Yabba)` while
`Unambiguous` fails at `Yabba`: the literal read-string `I_s` promise does not
imply the read-only `Unambiguous` promise. -/
theorem isPromiseRS_not_imp_unambiguous :
    isPromiseRS spellABAB Yabba ∧ ¬ Unambiguous π p orbit Yabba :=
  ⟨isPromiseRS_abab_yabba,
    not_unambiguous_of_two_orbit_realizers spellABAB spellAABB Yabba
      realizable_abab_yabba realizable_aabb_yabba orbit_aabb_ne_abab.symm⟩

/-- **Reconciliation with the Not-So-Greedy premise.**  The direction-1
competitor `AABB` is read-realizable at `Yabba` but **not** `I_s`-feasible
(its only placement `{1,3}` fails historical coverage), so the refutation does
not violate feasible-fibre uniqueness; it separates the read-realizable fibre
from the `I_s`-feasible fibre. -/
theorem not_isPromiseRS_aabb_yabba : ¬ isPromiseRS spellAABB Yabba := by
  unfold isPromiseRS isPromiseReadString
  decide

/-- `Yabba` has positive predictive probability. -/
theorem predictive_pos_yabba :
    0 < predictiveMass π p (fun _ _ => True) Yabba :=
  predictive_pos_of_realizable Yabba spellABAB realizable_abab_yabba

/-! ## 4. Direction 2: `Unambiguous` does not imply `I_s` -/

/-- The local support condition "`g` has an adjacent `00` pair". -/
abbrev ex0 (g : Sp4) : Prop := ∃ r : Fin 4, g r = 0 ∧ g (r + 1) = 0

/-- The local support condition "`g` has an adjacent `11` pair". -/
abbrev ex1 (g : Sp4) : Prop := ∃ s : Fin 4, g s = 1 ∧ g (s + 1) = 1

/-- **Combinatorial core of direction 2.**  A length-`4` binary circle with an
adjacent `00` pair and an adjacent `11` pair is a rotation of `AABB`. -/
theorem orbit_of_adj : ∀ g : Sp4, ex0 g → ex1 g → orbit g = orbit spellAABB := by
  decide

/-- The `d = 0` coordinate of the length-`2` window at `r` is `g r`. -/
theorem window_zero (g : Sp4) (r : Fin 4) : (toGenome4 g).window 2 r 0 = g r := by
  simp [toGenome4, Genome.window, Genome.cycl, Nat.mod_eq_of_lt]

/-- The `d = 1` coordinate of the length-`2` window at `r` is `g (r+1)`. -/
theorem window_one (g : Sp4) (r : Fin 4) : (toGenome4 g).window 2 r 1 = g (r + 1) := by
  simp only [toGenome4, Genome.window, Genome.cycl]
  congr 1

/-- **Every read-realizer of `Yaabb = {AA, BB}` is a rotation of `AABB`.**
Realizing both `AA` and `BB` forces an adjacent `00` pair and an adjacent `11`
pair, and `orbit_of_adj` pins the rotation class. -/
theorem realizable_yaabb_orbit (g : Sp4) (hg : Realizable g Yaabb) :
    orbit g = orbit spellAABB := by
  unfold Realizable at hg
  obtain ⟨R, hR⟩ := hg
  have hAA : (fun _ : Fin 2 => (0 : Bit)) ∈ Yaabb := by decide
  have hBB : (fun _ : Fin 2 => (1 : Bit)) ∈ Yaabb := by decide
  have hAA' : (fun _ : Fin 2 => (0 : Bit)) ∈ observedTypes_ofFinset (toGenome4 g) 2 R := by
    rw [hR]; exact hAA
  have hBB' : (fun _ : Fin 2 => (1 : Bit)) ∈ observedTypes_ofFinset (toGenome4 g) 2 R := by
    rw [hR]; exact hBB
  obtain ⟨r, _, hrw⟩ := (observedTypes_ofFinset_mem_iff).mp hAA'
  obtain ⟨s, _, hsw⟩ := (observedTypes_ofFinset_mem_iff).mp hBB'
  refine orbit_of_adj g ⟨r, ?_, ?_⟩ ⟨s, ?_, ?_⟩
  · have h := congrFun hrw 0; rw [window_zero] at h; exact h.symm
  · have h := congrFun hrw 1; rw [window_one] at h; exact h.symm
  · have h := congrFun hsw 0; rw [window_zero] at h; exact h.symm
  · have h := congrFun hsw 1; rw [window_one] at h; exact h.symm

/-- **`Yaabb` is `Unambiguous`.**  Every positive-likelihood candidate at
`{AA, BB}` is a rotation of `AABB`, so the read-realizable support is a single
rotation class. -/
theorem unambiguous_yaabb : Unambiguous π p orbit Yaabb := by
  intro g h _ hpg _ hph
  rw [realizable_yaabb_orbit g ((p_pos_iff g Yaabb).mp hpg),
    realizable_yaabb_orbit h ((p_pos_iff h Yaabb).mp hph)]

/-- **`BBAA` is not `I_s`-promising at `Yaabb`.**  The only start set inducing
`{AA, BB}` on `BBAA` is `{0,2}`, at which historical coverage fails (position
`1` is not within `L-1 = 1` of a matching start). -/
theorem not_isPromiseRS_bbaa_yaabb : ¬ isPromiseRS spellBBAA Yaabb := by
  unfold isPromiseRS isPromiseReadString
  decide

/-- **Direction 2, refuted.**  `Unambiguous` holds at `Yaabb` while the
read-realizer `BBAA` is not `I_s`-promising at `Yaabb`: the read-only
`Unambiguous` promise does not imply the read-dependent `I_s` promise. -/
theorem unambiguous_not_imp_isPromiseRS :
    Unambiguous π p orbit Yaabb ∧ ¬ isPromiseRS spellBBAA Yaabb :=
  ⟨unambiguous_yaabb, not_isPromiseRS_bbaa_yaabb⟩

/-- `Yaabb` has positive predictive probability. -/
theorem predictive_pos_yaabb :
    0 < predictiveMass π p (fun _ _ => True) Yaabb :=
  predictive_pos_of_realizable Yaabb spellBBAA ⟨{0, 2}, by decide⟩

/-! ## 5. The ordering verdict: neither (incomparable) -/

/-- **The read-string `I_s` adapter and `Unambiguous` are incomparable on the
merged literal read-string adapter.**  Direction 1 (`isPromiseRS` at `(ABAB,
Yabba)` without `Unambiguous`) and direction 2 (`Unambiguous` at `Yaabb`
without `isPromiseRS` at `(BBAA, Yaabb)`) both fail, on positive-probability
observations, in one finite read-realizable model.  Hence the ordering is
**neither** `I_s ⇒ Unambiguous` nor `Unambiguous ⇒ I_s`. -/
theorem isPromiseRS_unambiguous_incomparable :
    (isPromiseRS spellABAB Yabba ∧ ¬ Unambiguous π p orbit Yabba) ∧
      (Unambiguous π p orbit Yaabb ∧ ¬ isPromiseRS spellBBAA Yaabb) ∧
      (0 < predictiveMass π p (fun _ _ => True) Yabba) ∧
      (0 < predictiveMass π p (fun _ _ => True) Yaabb) :=
  ⟨isPromiseRS_not_imp_unambiguous, unambiguous_not_imp_isPromiseRS,
    predictive_pos_yabba, predictive_pos_yaabb⟩

end AssemblyP1.FiniteReadStringIsVsUnambiguous
