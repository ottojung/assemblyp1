import AssemblyP1.FiniteRigidityDecider

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Directed-cycle sufficiency and the AATT boundary (issue #257, §22)

This module proves a new small Lean-checked rigidity lemma for a restricted
family (§8.1 progress on a bounded-topology front) and a kernel-checked rigid
repetitive boundary example. It imports — and does not duplicate — the exact
criterion (`ExactRigidityCriterion`), the Graver criterion (`GraverRigidity`)
and the finite decider (`FiniteRigidityDecider`).

## Main results

* `cycle2_rigid`: a directed `2`-cycle support (`0 → 1 → 0`) with uniform
  multiplicity `k` and total `G = 2 * k` is **rigid** — for *every* `k`.
  This is the parametric form of the `ATATAT`/`L = 3` rigidity fact: the
  `ATATAT` read graph *is* this `2`-cycle (`atatat_of_cycle2`), so the
  canonical "rigid despite triple `(L-1)`-mer repeats" example follows from
  the general lemma rather than from a single `by decide`.
* `aatt_rigid`: the `S = AATT`, `L = 2` read graph (vertices `A, T`; edges
  `AA : A → A`, `AT : A → T`, `TT : T → T`, `TA : T → A`, all of multiplicity
  `1`, total `G = 4`) is **rigid** (`by decide`). This support is *not* a
  single directed cycle (cycle rank `|E| - |V| + c = 3`, zero-sum rank `r = 2`),
  so "single directed cycle" is
  sufficient but **not necessary** — a kernel-checked boundary case.
* `aatt_search_space`: the `AATT` decider ranges over exactly `5 ^ 4 = 625`
  candidates — the §8.2 complexity record `(G+1)^|E|` at a concrete point.

## Failed simpler hypotheses (recorded)

"Single directed cycle ⟺ rigid" is **false** as an iff: `aatt_rigid` is a
rigid support with two vertices and four edges. The forward direction
(single directed cycle ⟹ rigid for uniform multiplicities) is `cycle2_rigid`
for `2`-cycles; the general `n`-cycle case is strictly analogous and remains
open in Lean (the arithmetic core is identical: balance forces constancy on a
directed cycle, and the total then pins the constant).
-/

namespace AssemblyP1.RigiditySimpleCycle

open Finset BigOperators
open AssemblyP1.GraverRigidity
open AssemblyP1.FiniteRigidityDecider

set_option maxRecDepth 100000

/-- The directed `2`-cycle support: edge `0 : 0 → 1`, edge `1 : 1 → 0`.
This is exactly the `ATATAT`/`L = 3` read graph
(`FiniteRigidityDecider.atatatTail`/`atatatHead`). -/
def cycle2Tail : Fin 2 → Fin 2 := fun e => e
def cycle2Head : Fin 2 → Fin 2 := fun e => if e = 0 then 1 else 0

/-- Balance on the directed `2`-cycle forces constancy: both coordinates are
equal. Vertex `0` has out-edge `{0}` and in-edge `{1}`. The hypothesis is
stated with explicit `Finset.filter`s (definitionally the `BalancedZ`
condition, cf. `admissible_iff`) so the singleton sets are computable. -/
theorem cycle2_balanced_const (B : Fin 2 → ℤ)
    (hbal : ∀ v ∈ (Finset.univ : Finset (Fin 2)),
      ∑ e ∈ Finset.univ.filter (fun e => cycle2Tail e = v), B e =
      ∑ e ∈ Finset.univ.filter (fun e => cycle2Head e = v), B e) :
    B 0 = B 1 := by
  have h0 := hbal (0 : Fin 2) (Finset.mem_univ _)
  have hout : Finset.univ.filter (fun e : Fin 2 => cycle2Tail e = 0) = {0} := by
    decide
  have hin : Finset.univ.filter (fun e : Fin 2 => cycle2Head e = 0) = {1} := by
    decide
  rw [hout, hin] at h0
  simpa using h0

/-- **Directed-2-cycle sufficiency (parametric).** The directed `2`-cycle with
uniform multiplicity `k` (`G = 2 * k`) is rigid. -/
theorem cycle2_rigid (k : ℕ) :
    Rigid cycle2Tail cycle2Head (Finset.univ : Finset (Fin 2))
      (fun _ => (k : ℤ)) (2 * k) := by
  intro B hpos hbal htot
  have hconst := cycle2_balanced_const B hbal
  -- Total: B 0 + B 1 = 2 * k.
  have hsum : B 0 + B 1 = 2 * (k : ℤ) := by
    have hU : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
    rw [hU] at htot
    simp [Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1)] at htot
    linarith
  have hk' : B 0 = (k : ℤ) := by linarith
  funext e
  fin_cases e <;> simp_all

/-- The `ATATAT`/`L = 3` read graph is the directed `2`-cycle. -/
theorem cycle2_is_atatat_tail : cycle2Tail = atatatTail := by decide

theorem cycle2_is_atatat_head : cycle2Head = atatatHead := by decide

/-- `S = ATATAT`, `L = 3` is rigid at *every* uniform multiplicity `k`
(total `2 * k`) — the parametric form of
`FiniteRigidityDecider.atatat_rigid` (which is the case `k = 3`). -/
theorem atatat_of_cycle2 (k : ℕ) :
    Rigid atatatTail atatatHead (Finset.univ : Finset (Fin 2))
      (fun _ => (k : ℤ)) (2 * k) := by
  rw [← cycle2_is_atatat_tail, ← cycle2_is_atatat_head]
  exact cycle2_rigid k

/-! ## The AATT boundary: rigid but not a single directed cycle -/

/-- The `S = AATT`, `L = 2` read graph: vertices `A = 0`, `T = 1`; edges
`0 : AA : A → A`, `1 : AT : A → T`, `2 : TT : T → T`, `3 : TA : T → A`.
Cycle rank `|E| - |V| + c = 3` (zero-sum rank `r = 2`): two loops plus the
`2`-cycle — not a single directed cycle. -/
def aattTail : Fin 4 → Fin 2 :=
  fun e => if e = 2 then 1 else if e = 3 then 1 else 0
def aattHead : Fin 4 → Fin 2 :=
  fun e => if e = 1 then 1 else if e = 2 then 1 else 0

/-- `S = AATT`, `L = 2` is **rigid** at `A = (1,1,1,1)` (`G = 4`): balance at
`A` forces `B(AT) = B(TA)`, and the total `B(AA) + B(TT) + 2 * B(AT) = 4`
with `B ≥ 1` forces `B = 1` everywhere. Kernel-checked by the finite
decider. -/
theorem aatt_rigid :
    Rigid aattTail aattHead (Finset.univ : Finset (Fin 2)) (fun _ => 1) 4 :=
  (rigid_iff_decider aattTail aattHead (Finset.univ : Finset (Fin 2))
    (fun _ => 1) 4).mpr (by decide)

/-- The `AATT` decider search space has exactly `(4+1)^4 = 625` candidates
(the §8.2 `(G+1)^|E|` record at this support). -/
theorem aatt_search_space :
    Fintype.card (Fin 4 → Fin (4 + 1)) = 625 := by decide

end AssemblyP1.RigiditySimpleCycle
