import AssemblyP1.PopulationUniqueness
import AssemblyP1.P2GcdOne

/-!
# The primitive-`P2` population uniqueness endpoint, driven by the integrated
# gcd one (issue #89, board 94 front `94-primitive-p2pop`)

Paper source: `paper/sections/05-population.tex`, `thm:population` with its
proof chain `def:population` → `lem:gibbs` → `lem:scaling` → `thm:BBT`.

## What this module does

`AssemblyP1.P2GcdOne.gcd_one_of_primitive_P2` proves, from the paper's own
primitivity and the actual `def:P1P2` predicate `P2` alone, that a primitive
`P2` truth has a **gcd-one** `L`-spectrum in the admissible range
`2 ≤ L ≤ G`.  This module *drives the population reduction through that fact*,
reaching as far as `P2` + primitivity + `lem:gibbs` can go, and then isolates
the single remaining deep input — `BBTUniqueAt` / `EulerianCycleObstruction`,
i.e. *equal complete spectrum forces rotation* — as an explicitly named
postcondition.  That postcondition is the target of the complementary
BBT/replacement front; it is **not** proved or assumed away here.

The three exported theorems are, in increasing strength:

1. `popTie_primitiveP2_equal_spectra` — a population tie between two primitive
   `P2` genomes forces equal lengths and equal complete `L`-spectra, with **no**
   BBT, Ukkonen or condensed-graph hypothesis.  Both gcd-one obligations are
   discharged by the integrated `gcd_one_of_primitive_P2`, and the
   proportional-cancellation is `PopulationReduction.population_uniqueness_of_spectra`.
   This is the sharpest statement of how far the reduction reaches from `P2`
   alone.

2. `population_tie_primitiveP2_rotation_of_bbtUniqueAt` — the full tie-to-
   rotation endpoint, composing (1) with the single `BBTUniqueAt` postcondition.
   gcd one is discharged internally; the postcondition is used **once**, only for
   the final "equal spectra ⟹ `RotEquiv`" step.

3. `population_unique_ML_up_to_rotation_of_obstruction_range` — `thm:population`
   (both halves: maximizer and uniqueness) in the admissible range `2 ≤ L ≤ G`,
   carrying the Eulerian-cycle Theorem-3 obstruction as the postcondition, which
   `bbtUniqueAt_of_obstruction` turns into the `BBTUniqueAt` that (2) consumes.
   This is the exact route by which the BBT front closes issue #89 in this
   range.

## Range

The gcd-one multiplicity cap `imp_nodeCount_le_two_of_powerPrimitive` needs
`2 ≤ L ≤ G` (read length not exceeding genome length), so these theorems carry
`hLG : L ≤ G` and `hLK : L ≤ K` explicitly.  The unrestricted-`1 < L` version,
which discharges gcd one through the BBT-dependent
`PopulationReduction.gcd_one_of_primitive_P2_words` route instead, remains
`AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation`.

## Naming note

`AssemblyP1.P2GcdOne` imports, transitively, the List-flavored
`AssemblyP1.IsPrimitive` (from `AssemblyP1/AmpBmpPrimitivity.lean`), which
shadows the circular-word primitivity this module relies on.  Every use below is
therefore written `PopulationReduction.IsPrimitive` (the `Fin G → α` one), never
bare `IsPrimitive`.

All results depend only on `propext`, `Classical.choice` and `Quot.sound`.
No `axiom`, `sorry`, `admit`, `native_decide`, `unsafe` or `partial` appears.
-/

namespace AssemblyP1.P2PopulationEndpoint

open AssemblyP1.PopulationReduction
open AssemblyP1.PopulationGibbs
open AssemblyP1.OrientedRigidity
open AssemblyP1.P2
open AssemblyP1.BBTEulerian
open AssemblyP1.PopulationUniqueness

variable {α : Type} [DecidableEq α] [Fintype α]
variable {G : ℕ}

/-! ## 1. The BBT-free primitive-`P2` spectra endpoint -/

/-- **The primitive-`P2` population reduction reaches equal complete spectra
from a population tie, with no BBT premise and no Ukkonen hypothesis.**  In the
admissible range `2 ≤ L ≤ G`, `2 ≤ L ≤ K`, a population tie between a primitive
`P2` truth `S` and a primitive `P2` candidate `W` forces equal genome lengths and
equal complete `L`-spectra.

Chain: `lem:gibbs` tie ⟹ equal read distributions ⟹ proportional (`normalized`)
spectrum equality (`population_tie_implies_normalized`) ⟹
`PopulationReduction.population_uniqueness_of_spectra` fed by
`AssemblyP1.P2GcdOne.gcd_one_of_primitive_P2` on both genomes (via
`PopulationUniqueness.population_uniqueness_of_primitive_P2`).  Nothing touches
`BBTUniqueAt`, `EulerianCycleObstruction`, `Ukkonen` or condensed-graph
uniqueness: gcd one from `P2`'s triple clause + primitivity is the entire `P2`
content of the reduction. -/
theorem popTie_primitiveP2_equal_spectra
    (L : ℕ) {K : ℕ} (hG : 0 < G) (hK : 0 < K) (hL : 2 ≤ L)
    (hLG : L ≤ G) (hLK : L ≤ K)
    (S : Fin G → α) (W : Fin K → α)
    (hPrimS : PopulationReduction.IsPrimitive S)
    (hPrimW : PopulationReduction.IsPrimitive W)
    (hP2S : P2 hG L S) (hP2W : P2 hK L W)
    (hWTie : PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
      = PopLogLik (popSpectrum L hG S) (popSpectrum L hG S)) :
    G = K ∧ specCount (L := L) hG S = specCount (L := L) hK W :=
  AssemblyP1.P2GcdOne.population_uniqueness_of_primitive_P2
    hG hK S W hL hLG hLK hPrimS hPrimW hP2S hP2W
    (population_tie_implies_normalized L hG hK S W hWTie)

/-! ## 2. The full tie-to-rotation endpoint, with the deep input isolated -/

/-- **The full primitive-`P2` tie-to-rotation endpoint, with the deep BBT input
isolated as the single `BBTUniqueAt` postcondition.**  In the admissible range
`2 ≤ L ≤ G`, `2 ≤ L ≤ K`, a population tie forces the candidate `W` to be a
cyclic shift of the truth `S`, given one inhabitant of `BBTUniqueAt` (equal
complete spectrum determines a `Ukkonen` word up to rotation).

gcd one is discharged internally by `popTie_primitiveP2_equal_spectra`; the
postcondition is used **once**, only for the last step (equal complete spectra
⟹ `RotEquiv`).  This is the exact primitive-`P2` uniqueness endpoint with the
graph-theoretic crux exposed and nothing else assumed. -/
theorem population_tie_primitiveP2_rotation_of_bbtUniqueAt
    (L : ℕ) {K : ℕ} (hG : 0 < G) (hK : 0 < K) (hL : 2 ≤ L)
    (hLG : L ≤ G) (hLK : L ≤ K)
    (S : Fin G → α) (W : Fin K → α)
    (hPrimS : PopulationReduction.IsPrimitive S)
    (hPrimW : PopulationReduction.IsPrimitive W)
    (hP2S : P2 hG L S) (hP2W : P2 hK L W)
    (hBBT : BBTUniqueAt (α := α) L)
    (hWTie : PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
      = PopLogLik (popSpectrum L hG S) (popSpectrum L hG S)) :
    ∃ hGK : G = K, RotEquiv hG (hGK ▸ W) S := by
  obtain ⟨hGK, hSpec⟩ :=
    popTie_primitiveP2_equal_spectra L hG hK hL hLG hLK S W
      hPrimS hPrimW hP2S hP2W hWTie
  subst hGK
  exact ⟨rfl, (hBBT G hG S) W (P2.imp_Ukkonen (by omega) hP2S) hSpec⟩

/-! ## 3. `thm:population` for primitive `P2`, in the admissible range -/

/-- **`thm:population` (issue #89) for primitive `P2`, in the admissible range
`2 ≤ L ≤ G`, with the graph-theoretic crux carried as the single
`EulerianCycleObstruction` postcondition.**  The maximizer half is `lem:gibbs`
(no structural hypothesis); the tie-to-rotation half is
`population_tie_primitiveP2_rotation_of_bbtUniqueAt` supplied with
`bbtUniqueAt_of_obstruction`.

Compared with `PopulationUniqueness.population_unique_ML_up_to_rotation`
(unrestricted `1 < L`, gcd one discharged via the BBT-dependent
`gcd_one_of_primitive_P2_words`), this theorem discharges gcd one through the
integrated pure-`P2` route, so `EulerianCycleObstruction` is consumed **once**,
only for the final rotation step.  It is the exact route by which the BBT front's
proof of `EulerianCycleObstruction` closes issue #89 in this range. -/
theorem population_unique_ML_up_to_rotation_of_obstruction_range
    (L : ℕ) (hG : 0 < G) (hL : 2 ≤ L) (hLG : L ≤ G)
    (S : Fin G → α)
    (hPrimS : PopulationReduction.IsPrimitive S) (hP2S : P2 hG L S)
    (hObs : EulerianCycleObstruction (α := α) L) :
    ((∀ (K : ℕ) (hK : 0 < K) (_hLK : L ≤ K) (W : Fin K → α), AdmClass L hK W →
        PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
          ≤ PopLogLik (popSpectrum L hG S) (popSpectrum L hG S)) ∧
      (∀ (K : ℕ) (hK : 0 < K) (_hLK : L ≤ K) (W : Fin K → α), AdmClass L hK W →
        PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
          = PopLogLik (popSpectrum L hG S) (popSpectrum L hG S) →
        ∃ hGK : G = K, RotEquiv hG (hGK ▸ W) S)) := by
  have hBBT : BBTUniqueAt (α := α) L := bbtUniqueAt_of_obstruction (by omega) hObs
  refine ⟨fun _ hK _ W _ =>
    popLogLik_le_self' (popSpectrum_isProb L hG S) (popSpectrum_isProb L hK W), ?_⟩
  intro K hK _ W hW hWTie
  obtain ⟨hPrimW, hP2W⟩ := hW
  exact population_tie_primitiveP2_rotation_of_bbtUniqueAt
    L hG hK (by omega) hLG (by omega) S W hPrimS hPrimW hP2S hP2W hBBT hWTie

end AssemblyP1.P2PopulationEndpoint
