import AssemblyP1.GraverThroughputBridge

set_option autoImplicit false

/-!
# A concrete throughput sign clash (#263)

Four distinct loop edges on two vertices give two conformal balance-plus-total
kernel moves whose naive throughput lifts have opposite signs at vertex zero.
This finite calculation illustrates the obstruction; it asserts no general
T-sign-compatible decomposition theorem.
-/

namespace AssemblyP1.ThroughputSignClash263

open Finset BigOperators
open AssemblyP1.GraverThroughputBridge

abbrev V := Fin 2
abbrev E := Fin 4

def tail : E → V := fun e => if e.val = 0 ∨ e.val = 1 then 0 else 1
def head : E → V := tail

def g₁ : E → ℤ := fun e =>
  if e.val = 0 then 1 else if e.val = 2 then -1 else 0

def g₂ : E → ℤ := fun e =>
  if e.val = 1 then -1 else if e.val = 3 then 1 else 0

def δ : E → ℤ := g₁ + g₂

/-- The source-oriented outgoing throughput of a signed edge vector. -/
def throughput (f : E → ℤ) (v : V) : ℤ :=
  ∑ e : E, if tail e = v then f e else 0

private theorem g₁_kernel : flowLin tail head g₁ = 0 := by
  funext r
  rcases r with v | u
  · fin_cases v <;> decide
  · cases u
    decide

private theorem g₂_kernel : flowLin tail head g₂ = 0 := by
  funext r
  rcases r with v | u
  · fin_cases v <;> decide
  · cases u
    decide

private theorem delta_kernel : flowLin tail head δ = 0 := by
  rw [δ, flowLin_add, g₁_kernel, g₂_kernel, zero_add]

/-- Both pieces and their sum are in the balance-plus-fixed-total kernel. -/
theorem kernel_decomposition :
    flowLin tail head g₁ = 0 ∧ flowLin tail head g₂ = 0 ∧
    flowLin tail head δ = 0 ∧ δ = g₁ + g₂ := by
  exact ⟨g₁_kernel, g₂_kernel, delta_kernel, rfl⟩

/-- The two edge moves are coordinatewise conformal to their sum. -/
theorem edge_conformal :
    (∀ e : E, g₁ e = 0 ∨ δ e = 0 ∨ 0 < g₁ e * δ e) ∧
    (∀ e : E, g₂ e = 0 ∨ δ e = 0 ∨ 0 < g₂ e * δ e) := by
  constructor <;> intro e <;> fin_cases e <;>
    norm_num [g₁, g₂, δ]

/-- The conformal edge decomposition has opposite lifted signs at vertex zero. -/
theorem naive_lift_throughput_sign_clash :
    throughput g₁ 0 = 1 ∧ throughput g₂ 0 = -1 ∧ throughput δ 0 = 0 := by
  decide

/-- For the box `0 ≤ w_e ≤ 2`, the base point and displaced point are feasible;
the displacement preserves total and vertex balance. -/
theorem bounded_feasible_pair :
    (∀ _e : E, (0 : ℤ) ≤ (1 : ℤ) ∧ (1 : ℤ) ≤ 2) ∧
    (∀ e : E, (0 : ℤ) ≤ 1 + δ e ∧ 1 + δ e ≤ 2) ∧
    flowLin tail head (fun _ => (1 : ℤ)) = flowLin tail head (fun e : E => 1 + δ e) ∧
    (∑ _e : E, (1 : ℤ)) = 4 ∧ (∑ e : E, ((1 : ℤ) + (δ e))) = 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide
  · intro e
    fin_cases e <;> decide
  · have hfun : (fun e : E => 1 + δ e) = (fun _ => (1 : ℤ)) + δ := by
      funext e
      rfl
    rw [hfun, flowLin_add, delta_kernel, add_zero]
  · decide
  · decide

end AssemblyP1.ThroughputSignClash263
