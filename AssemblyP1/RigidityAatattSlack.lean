import AssemblyP1.FiniteRigidityDecider

open Finset BigOperators
open AssemblyP1.GraverRigidity
open AssemblyP1.FiniteRigidityDecider

namespace AssemblyP1.AatattSlack

/-!
# Exact per-support rigidity characterization (issue #257)

The running `AATATT`/`AATT` support (vertices `0 = A`, `1 = T`; ordered edges
`AA, AT, TA, TT`) is small enough to solve *parametrically*: balance collapses
to the single equation `AT = TA`, and rigidity is decided by total mass alone.

> For every feasible circulation `A` of total `G` on this support,
> `Rigid A G ↔ G = 4`.

The forward direction is the general unit-slack fact (`G = |E|` forces the
all-ones vector); the backward direction exhibits, for every `G > 4`, an
explicit distinct feasible circulation, by case split on where the slack sits:

* asymmetric loops (`A 0 ≠ A 3`): swap the two loop values;
* symmetric loops with `AT = TA ≥ 2`: shift `+1` onto the loops, `-1` off the
  arcs (the `δ = (1,-1,-1,1)` direction);
* symmetric loops with `AT = TA = 1` (hence loops `≥ 2` since `G > 4`): shift
  the other way.

Together with `aatatt_nonrigid` / `aatt_rigid` (kernel-checked instances) this
gives the complete rigidity table for this genome-realizable support, and a
template for per-support exact criteria beyond repeat bounds.
-/

/-- **General unit-slack lemma.** If the total mass equals the number of support
edges, every feasible circulation is the all-ones vector, hence rigid. -/
theorem rigid_of_total_eq_card {V E : Type} [DecidableEq V] [DecidableEq E]
    [Fintype E] (tail head : E → V) (nodes : Finset V)
    (A : E → ℤ) (G : ℕ) (hG : G = Fintype.card E)
    (hA : Feasible tail head nodes G A) :
    Rigid tail head nodes A G := by
  have key : ∀ f : E → ℤ, Pos f → (∑ e ∈ Finset.univ, f e = (G : ℤ)) →
      f = fun _ => 1 := by
    intro f hpos hsum
    have h1 : (∑ _e ∈ (Finset.univ : Finset E), (1:ℤ))
        = ((Fintype.card E : ℕ) : ℤ) := by simp
    have hsub : ∑ e ∈ (Finset.univ : Finset E), (f e - 1) = 0 := by
      rw [Finset.sum_sub_distrib, hsum, h1, hG, sub_self]
    have hnn : ∀ i ∈ (Finset.univ : Finset E), (0 : ℤ) ≤ f i - 1 := by
      intro i _
      have := hpos i
      omega
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsub
    funext e
    have he := hall e (Finset.mem_univ e)
    have := hpos e
    omega
  intro B hBpos _ hBsum
  rw [key A hA.1 hA.2.2, key B hBpos hBsum]

/-- Filter computations on the `AATATT` support. -/
private theorem filt_out0 :
    (Finset.univ.filter (fun e : Fin 4 => aatattTail e = 0)) = {0, 1} := by
  decide

private theorem filt_in0 :
    (Finset.univ.filter (fun e : Fin 4 => aatattHead e = 0)) = {0, 2} := by
  decide

private theorem filt_out1 :
    (Finset.univ.filter (fun e : Fin 4 => aatattTail e = 1)) = {2, 3} := by
  decide

private theorem filt_in1 :
    (Finset.univ.filter (fun e : Fin 4 => aatattHead e = 1)) = {1, 3} := by
  decide

private theorem univ_fin4 : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by
  decide

/-- Balance on this support is exactly `AT = TA` (edges `1` and `2`). -/
theorem aatatt_balanced_iff (f : Fin 4 → ℤ) :
    BalancedZ aatattTail aatattHead (Finset.univ : Finset (Fin 2)) f ↔
      f 1 = f 2 := by
  constructor
  · intro h
    have h0 := h 0 (Finset.mem_univ 0)
    -- `outF`/`inF` are private; transport along definitional unfolding
    have c0 : (∑ e ∈ Finset.univ.filter (fun e : Fin 4 => aatattTail e = 0), f e)
        = (∑ e ∈ Finset.univ.filter (fun e : Fin 4 => aatattHead e = 0), f e) := h0
    -- specialize the out/in filters via the computed sets
    have e0 : ∑ e ∈ Finset.univ.filter (fun e : Fin 4 => aatattTail e = 0), f e
        = f 0 + f 1 := by
      rw [filt_out0]
      simp only [Finset.sum_insert (by decide : (0 : Fin 4) ∉ ({1} : Finset (Fin 4))),
        Finset.sum_singleton]
    have e1 : ∑ e ∈ Finset.univ.filter (fun e : Fin 4 => aatattHead e = 0), f e
        = f 0 + f 2 := by
      rw [filt_in0]
      simp only [Finset.sum_insert (by decide : (0 : Fin 4) ∉ ({2} : Finset (Fin 4))),
        Finset.sum_singleton]
    rw [e0, e1] at c0
    omega
  · intro h
    unfold BalancedZ
    intro v _
    -- both vertex equations reduce to f 1 = f 2 after filter computation
    have e0 : ∑ e ∈ Finset.univ.filter (fun e : Fin 4 => aatattTail e = 0), f e
        = f 0 + f 1 := by
      rw [filt_out0]
      simp only [Finset.sum_insert (by decide : (0 : Fin 4) ∉ ({1} : Finset (Fin 4))),
        Finset.sum_singleton]
    have e1 : ∑ e ∈ Finset.univ.filter (fun e : Fin 4 => aatattHead e = 0), f e
        = f 0 + f 2 := by
      rw [filt_in0]
      simp only [Finset.sum_insert (by decide : (0 : Fin 4) ∉ ({2} : Finset (Fin 4))),
        Finset.sum_singleton]
    have e2 : ∑ e ∈ Finset.univ.filter (fun e : Fin 4 => aatattTail e = 1), f e
        = f 2 + f 3 := by
      rw [filt_out1]
      simp only [Finset.sum_insert (by decide : (2 : Fin 4) ∉ ({3} : Finset (Fin 4))),
        Finset.sum_singleton]
    have e3 : ∑ e ∈ Finset.univ.filter (fun e : Fin 4 => aatattHead e = 1), f e
        = f 1 + f 3 := by
      rw [filt_in1]
      simp only [Finset.sum_insert (by decide : (1 : Fin 4) ∉ ({3} : Finset (Fin 4))),
        Finset.sum_singleton]
    -- `v` is `0` or `1`
    have hv : v = 0 ∨ v = 1 := by fin_cases v <;> decide
    rcases hv with rfl | rfl
    · change (∑ e ∈ Finset.univ.filter (fun e : Fin 4 => aatattTail e = 0), f e)
        = (∑ e ∈ Finset.univ.filter (fun e : Fin 4 => aatattHead e = 0), f e)
      rw [e0, e1, h]
    · change (∑ e ∈ Finset.univ.filter (fun e : Fin 4 => aatattTail e = 1), f e)
        = (∑ e ∈ Finset.univ.filter (fun e : Fin 4 => aatattHead e = 1), f e)
      rw [e2, e3, h]

/-- Total mass on this support, expanded. -/
theorem aatatt_sum (f : Fin 4 → ℤ) :
    ∑ e ∈ (Finset.univ : Finset (Fin 4)), f e = f 0 + f 1 + f 2 + f 3 := by
  rw [univ_fin4]
  simp only [Finset.sum_insert (by decide : (0 : Fin 4) ∉ ({1, 2, 3} : Finset (Fin 4))),
    Finset.sum_insert (by decide : (1 : Fin 4) ∉ ({2, 3} : Finset (Fin 4))),
    Finset.sum_insert (by decide : (2 : Fin 4) ∉ ({3} : Finset (Fin 4))),
    Finset.sum_singleton]
  omega

/-- Every feasible circulation here has `AT = TA`. -/
theorem aatatt_arc_eq (A : Fin 4 → ℤ) (G : ℕ)
    (hA : Feasible aatattTail aatattHead (Finset.univ : Finset (Fin 2)) G A) :
    A 1 = A 2 :=
  (aatatt_balanced_iff A).mp hA.2.1

/-- Lower mass bound: four positive edges force `G ≥ 4`. -/
theorem aatatt_ge_four (A : Fin 4 → ℤ) (G : ℕ)
    (hA : Feasible aatattTail aatattHead (Finset.univ : Finset (Fin 2)) G A) :
    4 ≤ G := by
  have hsum := hA.2.2
  rw [aatatt_sum] at hsum
  have h0 := hA.1 0
  have h1 := hA.1 1
  have h2 := hA.1 2
  have h3 := hA.1 3
  omega

/-- Loop-swap witness: asymmetric loops are never rigid. -/
theorem aatatt_loop_swap_nonrigid (A : Fin 4 → ℤ) (G : ℕ)
    (hA : Feasible aatattTail aatattHead (Finset.univ : Finset (Fin 2)) G A)
    (hne : A 0 ≠ A 3) :
    ¬ Rigid aatattTail aatattHead (Finset.univ : Finset (Fin 2)) A G := by
  intro hR
  let B : Fin 4 → ℤ := fun e => if e = 0 then A 3 else if e = 3 then A 0 else A e
  have n10 : (1 : Fin 4) ≠ 0 := by decide
  have n13 : (1 : Fin 4) ≠ 3 := by decide
  have n20 : (2 : Fin 4) ≠ 0 := by decide
  have n21 : (2 : Fin 4) ≠ 1 := by decide
  have n23 : (2 : Fin 4) ≠ 3 := by decide
  have n30 : (3 : Fin 4) ≠ 0 := by decide
  have hB0 : B 0 = A 3 := by simp [B]
  have hB1 : B 1 = A 1 := by simp [B, n10, n13]
  have hB2 : B 2 = A 2 := by simp [B, n20, n23]
  have hB3 : B 3 = A 0 := by simp [B, n30]
  have hpos : Pos B := by
    intro e
    have h0 := hA.1 0
    have h1 := hA.1 1
    have h2 := hA.1 2
    have h3 := hA.1 3
    have he : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by fin_cases e <;> decide
    rcases he with rfl | rfl | rfl | rfl <;> simp [B] <;> omega
  have hbal : BalancedZ aatattTail aatattHead (Finset.univ : Finset (Fin 2)) B := by
    rw [aatatt_balanced_iff]
    rw [hB1, hB2]
    exact aatatt_arc_eq A G hA
  have hsum : ∑ e ∈ (Finset.univ : Finset (Fin 4)), B e = (G : ℤ) := by
    have hAsum := hA.2.2
    rw [aatatt_sum] at hAsum ⊢
    rw [hB0, hB1, hB2, hB3]
    omega
  have hEq := hR B hpos hbal hsum
  have h0 : B 0 = A 0 := congrFun hEq 0
  rw [hB0] at h0
  exact hne h0.symm

/-- Slack-shift witness (`δ = (1,-1,-1,1)` direction): arcs `≥ 2` are never rigid. -/
theorem aatatt_shift_nonrigid (A : Fin 4 → ℤ) (G : ℕ)
    (hA : Feasible aatattTail aatattHead (Finset.univ : Finset (Fin 2)) G A)
    (ht : 2 ≤ A 1) :
    ¬ Rigid aatattTail aatattHead (Finset.univ : Finset (Fin 2)) A G := by
  intro hR
  have harc := aatatt_arc_eq A G hA
  let B : Fin 4 → ℤ := fun e =>
    if e = 0 then A 0 + 1 else if e = 3 then A 3 + 1
    else if e = 1 then A 1 - 1 else A 2 - 1
  have n10 : (1 : Fin 4) ≠ 0 := by decide
  have n13 : (1 : Fin 4) ≠ 3 := by decide
  have n20 : (2 : Fin 4) ≠ 0 := by decide
  have n21 : (2 : Fin 4) ≠ 1 := by decide
  have n23 : (2 : Fin 4) ≠ 3 := by decide
  have n30 : (3 : Fin 4) ≠ 0 := by decide
  have hB0 : B 0 = A 0 + 1 := by simp [B]
  have hB1 : B 1 = A 1 - 1 := by simp [B, n10, n13]
  have hB2 : B 2 = A 2 - 1 := by simp [B, n20, n23, n21]
  have hB3 : B 3 = A 3 + 1 := by simp [B, n30]
  have hpos : Pos B := by
    intro e
    have h0 := hA.1 0
    have h1 := hA.1 1
    have h2 := hA.1 2
    have h3 := hA.1 3
    have he : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by fin_cases e <;> decide
    rcases he with rfl | rfl | rfl | rfl <;> simp [B] <;> omega
  have hbal : BalancedZ aatattTail aatattHead (Finset.univ : Finset (Fin 2)) B := by
    rw [aatatt_balanced_iff]
    rw [hB1, hB2, harc]
  have hsum : ∑ e ∈ (Finset.univ : Finset (Fin 4)), B e = (G : ℤ) := by
    have hAsum := hA.2.2
    rw [aatatt_sum] at hAsum ⊢
    rw [hB0, hB1, hB2, hB3]
    omega
  have hEq := hR B hpos hbal hsum
  have h0 : B 0 = A 0 := congrFun hEq 0
  rw [hB0] at h0
  omega

/-- Reverse slack-shift (`δ = (-1,1,1,-1)` direction): loops `≥ 2` are never rigid. -/
theorem aatatt_shift_rev_nonrigid (A : Fin 4 → ℤ) (G : ℕ)
    (hA : Feasible aatattTail aatattHead (Finset.univ : Finset (Fin 2)) G A)
    (h0 : 2 ≤ A 0) (h3 : 2 ≤ A 3) :
    ¬ Rigid aatattTail aatattHead (Finset.univ : Finset (Fin 2)) A G := by
  intro hR
  have harc := aatatt_arc_eq A G hA
  let B : Fin 4 → ℤ := fun e =>
    if e = 0 then A 0 - 1 else if e = 3 then A 3 - 1
    else if e = 1 then A 1 + 1 else A 2 + 1
  have n10 : (1 : Fin 4) ≠ 0 := by decide
  have n13 : (1 : Fin 4) ≠ 3 := by decide
  have n20 : (2 : Fin 4) ≠ 0 := by decide
  have n21 : (2 : Fin 4) ≠ 1 := by decide
  have n23 : (2 : Fin 4) ≠ 3 := by decide
  have n30 : (3 : Fin 4) ≠ 0 := by decide
  have hB0 : B 0 = A 0 - 1 := by simp [B]
  have hB1 : B 1 = A 1 + 1 := by simp [B, n10, n13]
  have hB2 : B 2 = A 2 + 1 := by simp [B, n20, n23, n21]
  have hB3 : B 3 = A 3 - 1 := by simp [B, n30]
  have hpos : Pos B := by
    intro e
    have ha0 := hA.1 0
    have ha1 := hA.1 1
    have ha2 := hA.1 2
    have ha3 := hA.1 3
    have he : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by fin_cases e <;> decide
    rcases he with rfl | rfl | rfl | rfl <;> simp [B] <;> omega
  have hbal : BalancedZ aatattTail aatattHead (Finset.univ : Finset (Fin 2)) B := by
    rw [aatatt_balanced_iff]
    rw [hB1, hB2, harc]
  have hsum : ∑ e ∈ (Finset.univ : Finset (Fin 4)), B e = (G : ℤ) := by
    have hAsum := hA.2.2
    rw [aatatt_sum] at hAsum ⊢
    rw [hB0, hB1, hB2, hB3]
    omega
  have hEq := hR B hpos hbal hsum
  have h00 : B 0 = A 0 := congrFun hEq 0
  rw [hB0] at h00
  omega

/-- **Exact per-support criterion.** On the `AA, AT, TA, TT` support, a feasible
circulation of total `G` is rigid if and only if `G = 4` (equivalently, it is
the unit circulation). -/
theorem aatatt_rigid_iff (A : Fin 4 → ℤ) (G : ℕ)
    (hA : Feasible aatattTail aatattHead (Finset.univ : Finset (Fin 2)) G A) :
    Rigid aatattTail aatattHead (Finset.univ : Finset (Fin 2)) A G ↔ G = 4 := by
  constructor
  · intro hR
    have hge := aatatt_ge_four A G hA
    by_contra hne
    have hgt : 4 < G := by omega
    have harc := aatatt_arc_eq A G hA
    have hsum := hA.2.2
    rw [aatatt_sum] at hsum
    have h0 := hA.1 0
    have h1 := hA.1 1
    have h2 := hA.1 2
    have h3 := hA.1 3
    by_cases hloop : A 0 = A 3
    · -- symmetric loops: slack sits in arcs or in loops
      by_cases ht : 2 ≤ A 1
      · exact aatatt_shift_nonrigid A G hA ht hR
      · have h2le : 2 ≤ A 0 := by omega
        have h3le : 2 ≤ A 3 := by omega
        exact aatatt_shift_rev_nonrigid A G hA h2le h3le hR
    · exact aatatt_loop_swap_nonrigid A G hA hloop hR
  · intro hG
    have hcard : Fintype.card (Fin 4) = 4 := by decide
    exact rigid_of_total_eq_card aatattTail aatattHead _ A G (by omega) hA

end AssemblyP1.AatattSlack
