import AssemblyP1.TwoWalkRigidity

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Routing witnesses for the two-walk criterion (issue #257)

This file discharges the single graph-theoretic hypothesis of
`AssemblyP1.TwoWalkRigidity.rigid_iff_no_two_nonneg_circ` — the routing
property `Routable`: every nonnegative integer flow can be completed to a
nonnegative circulation by adding a nonnegative flow (the transshipment
consequence of strong connectivity). §22 discharges it by closed form on
two concrete supports (`AssemblyP1/TwoWalkRoutable.lean`, kernel-checked):

* **2-cycle** (`atatat_routable`): `h 0 = max (p 1 - p 0) 0`,
  `h 1 = max (p 0 - p 1) 0`, so both sides reach `max (p 0) (p 1)`.
* **Figure-eight** (`figureEight_routable`): the same pairing applied
  independently to each lobe (`{0, 1}` and `{2, 3}`); the shared vertex
  balances as the sum of two balanced lobes. The routing flow satisfies
  `h e ≤ max surplus`, hence the produced two-walk certificate has linear
  size in `‖δ‖₁` — the criterion is checkable by bounded integer search.

Unconditional corollaries (no routing hypothesis, no throughput cap):

* `atatat_rigid`: `S = ATATAT`, `L = 3` (a directed `2`-cycle with uniform
  multiplicity `3`) is rigid despite triple `(L-1)`-mer repeats.
* `figureEight_rigid`: the figure-eight support at uniform multiplicity `1`
  is rigid — the same support that is non-rigid at `A = (2, 2, 1, 1)`
  (`TwoWalkRigidity.figureEight_two_walk_witness`). Rigidity is a
  multiplicity property, not a support-topology property.
-/

namespace AssemblyP1.TwoWalkRoutable

open Finset BigOperators
open AssemblyP1.GraverRigidity
open AssemblyP1.TwoWalkRigidity

section RoutableInstances

/-- Explicit routing flow for the `ATATAT` `2`-cycle: credit only the
lighter edge so both sides reach `max (p 0) (p 1)`. -/
def route2 (p : Fin 2 → ℤ) : Fin 2 → ℤ :=
  fun e => if e = 0 then (if p 1 ≤ p 0 then 0 else p 1 - p 0)
           else (if p 0 ≤ p 1 then 0 else p 0 - p 1)

/-- The `if e = 0` guard reduces definitionally on literals. -/
theorem route2_zero (p : Fin 2 → ℤ) :
    route2 p 0 = (if p 1 ≤ p 0 then 0 else p 1 - p 0) := rfl

theorem route2_one (p : Fin 2 → ℤ) :
    route2 p 1 = (if p 0 ≤ p 1 then 0 else p 0 - p 1) := rfl

theorem route2_nonneg (p : Fin 2 → ℤ) (e : Fin 2) : 0 ≤ route2 p e := by
  have hv : e = 0 ∨ e = 1 := by fin_cases e <;> decide
  rcases hv with rfl | rfl
  · rw [route2_zero]; split <;> omega
  · rw [route2_one]; split <;> omega

theorem route2_bal0 (p : Fin 2 → ℤ) :
    p 0 + route2 p 0 = p 1 + route2 p 1 := by
  rw [route2_zero, route2_one]; split <;> split <;> omega

/-- The `ATATAT` `2`-cycle support is routable. -/
theorem atatat_routable : Routable atatatTail atatatHead := by
  intro p hp
  refine ⟨route2 p, fun e => route2_nonneg p e, ?_⟩
  have hb := route2_bal0 p
  intro v
  have hv : v = 0 ∨ v = 1 := by fin_cases v <;> decide
  rcases hv with rfl | rfl
  · have hout : (Finset.univ.filter (fun e : Fin 2 => atatatTail e = 0))
        = {0} := by decide
    have hin : (Finset.univ.filter (fun e : Fin 2 => atatatHead e = 0))
        = {1} := by decide
    rw [hout, hin, Finset.sum_singleton, Finset.sum_singleton, Pi.add_apply,
      Pi.add_apply]
    omega
  · have hout : (Finset.univ.filter (fun e : Fin 2 => atatatTail e = 1))
        = {1} := by decide
    have hin : (Finset.univ.filter (fun e : Fin 2 => atatatHead e = 1))
        = {0} := by decide
    rw [hout, hin, Finset.sum_singleton, Finset.sum_singleton, Pi.add_apply,
      Pi.add_apply]
    omega

/-- Explicit routing flow for the figure-eight: independent `2`-cycle
routing on each lobe (`{0, 1}` and `{2, 3}`). -/
def routeFig8 (p : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun e => if e = 0 then (if p 1 ≤ p 0 then 0 else p 1 - p 0)
       else if e = 1 then (if p 0 ≤ p 1 then 0 else p 0 - p 1)
       else if e = 2 then (if p 3 ≤ p 2 then 0 else p 3 - p 2)
       else (if p 2 ≤ p 3 then 0 else p 2 - p 3)

theorem routeFig8_zero (p : Fin 4 → ℤ) :
    routeFig8 p 0 = (if p 1 ≤ p 0 then 0 else p 1 - p 0) := rfl

theorem routeFig8_one (p : Fin 4 → ℤ) :
    routeFig8 p 1 = (if p 0 ≤ p 1 then 0 else p 0 - p 1) := rfl

theorem routeFig8_two (p : Fin 4 → ℤ) :
    routeFig8 p 2 = (if p 3 ≤ p 2 then 0 else p 3 - p 2) := rfl

theorem routeFig8_three (p : Fin 4 → ℤ) :
    routeFig8 p 3 = (if p 2 ≤ p 3 then 0 else p 2 - p 3) := rfl

theorem routeFig8_nonneg (p : Fin 4 → ℤ) (e : Fin 4) : 0 ≤ routeFig8 p e := by
  have hv : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by fin_cases e <;> decide
  rcases hv with rfl | rfl | rfl | rfl
  · rw [routeFig8_zero]; split <;> omega
  · rw [routeFig8_one]; split <;> omega
  · rw [routeFig8_two]; split <;> omega
  · rw [routeFig8_three]; split <;> omega

theorem routeFig8_lobeA (p : Fin 4 → ℤ) :
    p 0 + routeFig8 p 0 = p 1 + routeFig8 p 1 := by
  rw [routeFig8_zero, routeFig8_one]; split <;> split <;> omega

theorem routeFig8_lobeB (p : Fin 4 → ℤ) :
    p 2 + routeFig8 p 2 = p 3 + routeFig8 p 3 := by
  rw [routeFig8_two, routeFig8_three]; split <;> split <;> omega

/-- The figure-eight support is routable. Edge layout: `0 : 0 → 1`,
`1 : 1 → 0`, `2 : 0 → 2`, `3 : 2 → 0`. -/
theorem figureEight_routable : Routable figureEightTail figureEightHead := by
  intro p hp
  refine ⟨routeFig8 p, fun e => routeFig8_nonneg p e, ?_⟩
  have hA := routeFig8_lobeA p
  have hB := routeFig8_lobeB p
  intro v
  have hv : v = 0 ∨ v = 1 ∨ v = 2 := by fin_cases v <;> decide
  rcases hv with rfl | rfl | rfl
  · have hout : (Finset.univ.filter (fun e : Fin 4 => figureEightTail e = 0))
        = {0, 2} := by decide
    have hin : (Finset.univ.filter (fun e : Fin 4 => figureEightHead e = 0))
        = {1, 3} := by decide
    rw [hout, hin,
      Finset.sum_insert (by decide : (0 : Fin 4) ∉ ({2} : Finset (Fin 4))),
      Finset.sum_insert (by decide : (1 : Fin 4) ∉ ({3} : Finset (Fin 4))),
      Finset.sum_singleton, Finset.sum_singleton, Pi.add_apply, Pi.add_apply,
      Pi.add_apply, Pi.add_apply]
    omega
  · have hout : (Finset.univ.filter (fun e : Fin 4 => figureEightTail e = 1))
        = {1} := by decide
    have hin : (Finset.univ.filter (fun e : Fin 4 => figureEightHead e = 1))
        = {0} := by decide
    rw [hout, hin, Finset.sum_singleton, Finset.sum_singleton, Pi.add_apply,
      Pi.add_apply]
    omega
  · have hout : (Finset.univ.filter (fun e : Fin 4 => figureEightTail e = 2))
        = {3} := by decide
    have hin : (Finset.univ.filter (fun e : Fin 4 => figureEightHead e = 2))
        = {2} := by decide
    rw [hout, hin, Finset.sum_singleton, Finset.sum_singleton, Pi.add_apply,
      Pi.add_apply]
    omega

end RoutableInstances

section UnconditionalRigidity

/-- `ATATAT` at uniform multiplicity `3` is feasible for total `6`. -/
theorem atatat_feasible :
    Feasible atatatTail atatatHead (Finset.univ : Finset (Fin 2)) 6 atatatA := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    have hv : e = 0 ∨ e = 1 := by fin_cases e <;> decide
    rcases hv with rfl | rfl <;> decide
  · intro v _
    fin_cases v <;> decide
  · decide

/-- **Unconditional rigidity of `S = ATATAT`, `L = 3`.** No routing
hypothesis: `atatat_routable` discharges it. A triple `(L-1)`-mer repeat
that is rigid — repeat bounds are not necessary. -/
theorem atatat_rigid :
    Rigid atatatTail atatatHead (Finset.univ : Finset (Fin 2)) atatatA 6 :=
  (rigid_iff_no_two_nonneg_circ _ _ _ _ atatat_routable atatat_feasible).mpr
    atatat_no_two_nonneg_circ

/-- At uniform multiplicity `1` the figure-eight admits no two-closed-walk
certificate: every nonnegative circulation is `(a, a, b, b)`, the box
`f - g ≥ 1 - A = 0` forces `f ≥ g`, and equal totals then force `f = g`. -/
theorem figureEight_no_two_nonneg_circ :
    ¬ ∃ f g : Fin 4 → ℤ,
      TwoNonnegCirc figureEightTail figureEightHead (fun _ => 1) f g := by
  rintro ⟨f, g, hfnn, hgnn, hfb, hgb, hsum, hne, hbox⟩
  have hf10 : f 1 = f 0 := by
    have h1 := hfb 1
    rw [show (Finset.univ.filter (fun e : Fin 4 => figureEightTail e = 1))
        = {1} from by decide,
      show (Finset.univ.filter (fun e : Fin 4 => figureEightHead e = 1))
        = {0} from by decide,
      Finset.sum_singleton, Finset.sum_singleton] at h1
    exact h1
  have hf32 : f 3 = f 2 := by
    have h2 := hfb 2
    rw [show (Finset.univ.filter (fun e : Fin 4 => figureEightTail e = 2))
        = {3} from by decide,
      show (Finset.univ.filter (fun e : Fin 4 => figureEightHead e = 2))
        = {2} from by decide,
      Finset.sum_singleton, Finset.sum_singleton] at h2
    exact h2
  have hg10 : g 1 = g 0 := by
    have h1 := hgb 1
    rw [show (Finset.univ.filter (fun e : Fin 4 => figureEightTail e = 1))
        = {1} from by decide,
      show (Finset.univ.filter (fun e : Fin 4 => figureEightHead e = 1))
        = {0} from by decide,
      Finset.sum_singleton, Finset.sum_singleton] at h1
    exact h1
  have hg32 : g 3 = g 2 := by
    have h2 := hgb 2
    rw [show (Finset.univ.filter (fun e : Fin 4 => figureEightTail e = 2))
        = {3} from by decide,
      show (Finset.univ.filter (fun e : Fin 4 => figureEightHead e = 2))
        = {2} from by decide,
      Finset.sum_singleton, Finset.sum_singleton] at h2
    exact h2
  have hle : ∀ e : Fin 4, g e ≤ f e := by
    intro e
    have h := hbox e
    simp only [Pi.sub_apply] at h
    omega
  have hle0 : g 0 ≤ f 0 := hle 0
  have hle1 : g 1 ≤ f 1 := hle 1
  have hle2 : g 2 ≤ f 2 := hle 2
  have hle3 : g 3 ≤ f 3 := hle 3
  have hsum' : f 0 + f 1 + f 2 + f 3 = g 0 + g 1 + g 2 + g 3 := by
    have h := hsum
    simp only [Fin.sum_univ_four] at h
    exact h
  have e0 : f 0 = g 0 := by omega
  have e1 : f 1 = g 1 := by omega
  have e2 : f 2 = g 2 := by omega
  have e3 : f 3 = g 3 := by omega
  exact hne (by funext e; fin_cases e <;> assumption)

/-- The figure-eight at uniform multiplicity `1` is feasible for total `4`. -/
theorem figureEight_feasible :
    Feasible figureEightTail figureEightHead (Finset.univ : Finset (Fin 3)) 4
      (fun _ => 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    have hv : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by fin_cases e <;> decide
    rcases hv with rfl | rfl | rfl | rfl <;> decide
  · intro v _
    fin_cases v <;> decide
  · decide

/-- **Unconditional rigidity of the figure-eight at `A = (1, 1, 1, 1)`.**
Same support as the non-rigid `A = (2, 2, 1, 1)` instance: rigidity is a
multiplicity property, not a support-topology property. -/
theorem figureEight_rigid :
    Rigid figureEightTail figureEightHead (Finset.univ : Finset (Fin 3))
      (fun _ => 1) 4 :=
  (rigid_iff_no_two_nonneg_circ _ _ _ _ figureEight_routable
    figureEight_feasible).mpr figureEight_no_two_nonneg_circ

end UnconditionalRigidity

end AssemblyP1.TwoWalkRoutable
