import AssemblyP1.GraverRigidity

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Finite rigidity decider (issue #257)

This file lands the **checkable** half of the exact circulation criterion of
`docs/source-notes/issue-257-rigid-read-graphs.md`: the missing *finite
decision procedure* announced on the issue board (2026-10-13), on top of the
already-merged algebraic criterion
`AssemblyP1.ExactRigidityCriterion.nonrigid_iff_exists_delta` and the Graver
criterion `AssemblyP1.GraverRigidity.rigid_iff_forall_graver_not_feasible`.

## The unblock

Let `E` be the finite support edge type, `A : E → ℤ` a positive balanced
circulation of total `G`, and let `F = {B : E → ℤ | B ≥ 1, M B = 0, ∑ B = G}`
be the candidate set (`Feasible`). Every `B ∈ F` satisfies, coordinatewise,

```
1 ≤ B e ≤ G          (indeed B e ≤ G - (|E| - 1)).
```

The lower bound is positivity; the upper bound follows because every other
coordinate is `≥ 0`, so `B e ≤ ∑_{e'} B e' = G`. Hence **every candidate is
already a function `E → Fin (G + 1)`**, and the candidate set is the image of
the finite type `E → Fin (G + 1)` under the natural coercion. Therefore

> `A` is rigid **iff** every `B : E → Fin (G + 1)` with `Admissible B`
> (positive, balanced, total `G`) agrees with `A` coordinatewise.

This is a terminating decision procedure: enumerate the finite set
`(E → Fin (G + 1))`, keep the admissible ones, and compare. Its search space
has exactly `(G + 1) ^ |E|` elements (`card_candidates`), so it runs in
`O((G + 1)^|E| · poly(|V| + |E|))` — *pseudopolynomial*, exponential in the
support size, and explicitly **not** a claim of polynomial time in the bit
length of `G`. This matches the issue's request for a genuine finite
certificate rather than only a logical iff, and it avoids the (still open)
question of a sharp Graver-basis cardinality bound.

## Main results

* `le_total_of_feasible`: the coordinate bound `B e ≤ G`.
* `admissible_iff`: the enumerated predicate is the `BalancedZ`/`Pos` form.
* `rigid_iff_forall_admissible`: the exact finite criterion as a proposition.
* `decider` / `rigid_iff_decider`: an executable Boolean decider together with
  its correctness theorem.
* `card_candidates`: the `(G + 1) ^ |E|` search-space count.
* Kernel-checked worked instances: `atatat_rigid` (rigid *despite* triple
  `(L-1)`-mer repeats — the canonical refutation of the "no triple repeat" iff),
  `aaaab_nonrigid` (a non-rigid genome), and the figure-eight rigid/non-rigid
  pair `figureEight_rigid` / `figureEight_nonrigid` showing rigidity is a
  multiplicity, not a topology, property.

## Failed simpler hypotheses (recorded, not claimed as iff)

The decider confirms, in the kernel, the counterexamples already recorded in
§5–§6 of the source note:

* "no `(L-1)`-mer occurs `≥ 3` times" is **sufficient but not necessary**
  (`atatat_rigid`: `AT` and `TA` each occur `3` times).
* "the support is a single directed cycle" is **sufficient but not necessary**
  (`figureEight_rigid`: two independent cycles, still rigid).
* "`A` is determined by the support topology" is **false**
  (`figureEight_nonrigid`: same graph as `figureEight_rigid`, different `A`).

The two-cycle certificate is *not necessary* (source note §4, verified in
`scratch257/`); the finite decider here is the exact replacement.
-/

namespace AssemblyP1.FiniteRigidityDecider

open Finset BigOperators
open AssemblyP1.GraverRigidity

section Decider

variable {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype E]

/-- An enumerated candidate on the finite support: a function into `Fin (G + 1)`
that is positive, balanced, and of total mass `G` after coercion to `ℤ`.

The balance condition is written out with explicit `Finset.filter`s (rather than
via `BalancedZ`) so that it is *reducible* and therefore computably decidable;
`admissible_iff` proves it is the same predicate. -/
abbrev Admissible (tail head : E → V) (nodes : Finset V) (G : ℕ)
    (B : E → Fin (G + 1)) : Prop :=
  (∀ e, (1 : ℤ) ≤ (B e : ℤ)) ∧
    (∀ v ∈ nodes,
      ∑ e ∈ (Finset.univ.filter (fun e => tail e = v)), (B e : ℤ)
      = ∑ e ∈ (Finset.univ.filter (fun e => head e = v)), (B e : ℤ)) ∧
    (∑ e, (B e : ℤ)) = (G : ℤ)

/-- The enumerated predicate is exactly `Pos` together with `BalancedZ` and the
fixed total mass. -/
theorem admissible_iff (tail head : E → V) (nodes : Finset V) (G : ℕ)
    (B : E → Fin (G + 1)) :
    Admissible tail head nodes G B ↔
      (∀ e, (1 : ℤ) ≤ (B e : ℤ)) ∧
        BalancedZ tail head nodes (fun e => (B e : ℤ)) ∧
        (∑ e, (B e : ℤ)) = (G : ℤ) := by
  unfold BalancedZ
  rfl

/-- **Coordinate bound.** Every feasible circulation of total `G` has each
coordinate at most `G`: all other coordinates are nonnegative, so
`B e ≤ ∑ B = G`. -/
theorem le_total_of_feasible {tail head : E → V} {nodes : Finset V} {G : ℕ}
    {B : E → ℤ} (hB : Feasible tail head nodes G B) (e : E) :
    B e ≤ (G : ℤ) := by
  have hsum : (∑ e, B e) = (G : ℤ) := hB.2.2
  calc B e ≤ ∑ e' ∈ (Finset.univ : Finset E), B e' := by
        exact Finset.single_le_sum (fun i _ => by have := hB.1 i; omega)
          (Finset.mem_univ e)
    _ = (G : ℤ) := by rw [hsum]

/-- **Exact finite criterion.** `A` is rigid iff every admissible
`Fin (G + 1)`-valued candidate agrees with `A` coordinatewise. Both directions
are constructive; the backward direction encodes an arbitrary feasible integer
circulation into `Fin (G + 1)` using `le_total_of_feasible`. -/
theorem rigid_iff_forall_admissible (tail head : E → V) (nodes : Finset V)
    (A : E → ℤ) (G : ℕ) :
    Rigid tail head nodes A G ↔
      ∀ B : E → Fin (G + 1), Admissible tail head nodes G B → ∀ e, (B e : ℤ) = A e := by
  constructor
  · intro hRig B hB e
    obtain ⟨hpos, hbal, hsum⟩ := (admissible_iff tail head nodes G B).mp hB
    have hfeas : Feasible tail head nodes G (fun e => (B e : ℤ)) := ⟨hpos, hbal, hsum⟩
    have hEq : (fun e => (B e : ℤ)) = A :=
      hRig (fun e => (B e : ℤ)) hfeas.1 hfeas.2.1 hfeas.2.2
    exact congrFun hEq e
  · intro h B hBpos hBbal hBtot
    have hfeas : Feasible tail head nodes G B := ⟨hBpos, hBbal, hBtot⟩
    have hle : ∀ e, B e ≤ (G : ℤ) := fun e => le_total_of_feasible hfeas e
    have h0 : ∀ e, (0 : ℤ) ≤ B e := fun e => by have := hBpos e; omega
    let B' : E → Fin (G + 1) := fun e =>
      ⟨(B e).toNat, by
        have hc : ((B e).toNat : ℤ) = B e := Int.toNat_of_nonneg (h0 e)
        have := hle e
        omega⟩
    have hfun : (fun e => (B' e : ℤ)) = B := by
      funext e
      show ((B e).toNat : ℤ) = B e
      exact Int.toNat_of_nonneg (h0 e)
    have hAdm : Admissible tail head nodes G B' := by
      refine (admissible_iff tail head nodes G B').mpr ⟨?_, ?_, ?_⟩
      · intro e
        show (1 : ℤ) ≤ ((B e).toNat : ℤ)
        rw [Int.toNat_of_nonneg (h0 e)]
        exact hBpos e
      · rw [hfun]; exact hBbal
      · rw [hfun]; exact hBtot
    have he := h B' hAdm
    funext e
    have := he e
    rw [show (B' e : ℤ) = B e from congrFun hfun e] at this
    exact this

/-- **Executable decider.** The decision procedure of
`rigid_iff_forall_admissible` as a Boolean: `decide` of the finite universal
statement over `E → Fin (G + 1)` (the instance
`Fintype.decidableForallFintype` enumerates the finite function type). Returns
`true` exactly when `A` is rigid. -/
def decider (tail head : E → V) (nodes : Finset V) (A : E → ℤ) (G : ℕ) : Bool :=
  decide (∀ B : E → Fin (G + 1), Admissible tail head nodes G B → ∀ e, (B e : ℤ) = A e)

/-- **Decider correctness.** The Boolean decider returns `true` exactly when
`A` is rigid. -/
theorem rigid_iff_decider (tail head : E → V) (nodes : Finset V)
    (A : E → ℤ) (G : ℕ) :
    Rigid tail head nodes A G ↔ decider tail head nodes A G = true := by
  unfold decider
  rw [rigid_iff_forall_admissible]
  exact decide_eq_true_iff.symm

/-- **Search-space size.** The decider ranges over exactly `(G + 1) ^ |E|`
candidate functions. -/
theorem card_candidates (G : ℕ) :
    Fintype.card (E → Fin (G + 1)) = (G + 1) ^ Fintype.card E := by
  rw [Fintype.card_fun, Fintype.card_fin]

end Decider

/-! ## Kernel-checked worked instances -/

section Examples

set_option maxRecDepth 100000

/-- The `ATATAT`, `L = 3` read graph: two nodes `AT`, `TA`; two edges
`ATA : AT → TA`, `TAT : TA → AT`; a single directed `2`-cycle. -/
def atatatTail : Fin 2 → Fin 2 := fun e => if e = 0 then 0 else 1
def atatatHead : Fin 2 → Fin 2 := fun e => if e = 0 then 1 else 0
def atatatA : Fin 2 → ℤ := fun _ => 3

/-- `S = ATATAT`, `L = 3` is **rigid** even though the `(L-1)`-mers `AT` and
`TA` each occur `3` times: the only positive circulation of total `6` is
`A = (3, 3)`. This is the canonical witness that "no `(L-1)`-mer occurs `≥ 3`
times" is sufficient but **not necessary**. -/
theorem atatat_rigid :
    Rigid atatatTail atatatHead (Finset.univ : Finset (Fin 2)) atatatA 6 :=
  (rigid_iff_decider atatatTail atatatHead (Finset.univ : Finset (Fin 2)) atatatA 6).mpr
    (by decide)

/-- The `AAAAB`, `L = 2` read graph: nodes `A`, `B`; edges `AA : A → A`,
`AB : A → B`, `BA : B → A`; spectrum `AA : 3, AB : 1, BA : 1`. -/
def aaaabTail : Fin 3 → Fin 2 := fun e => if e = 2 then 1 else 0
def aaaabHead : Fin 3 → Fin 2 := fun e => if e = 1 then 1 else 0
def aaaabA : Fin 3 → ℤ := fun e => if e = 0 then 3 else 1

/-- `S = AAAAB`, `L = 2` is **not** rigid: `A = (3, 1, 1)` and the alternative
`B = (1, 2, 2)` both carry `G = 5`. -/
theorem aaaab_nonrigid :
    ¬ Rigid aaaabTail aaaabHead (Finset.univ : Finset (Fin 2)) aaaabA 5 := by
  intro h
  have h' := (rigid_iff_decider aaaabTail aaaabHead (Finset.univ : Finset (Fin 2))
    aaaabA 5).mp h
  revert h'
  decide

/-- The figure-eight support `0 → 1 → 0`, `0 → 2 → 0` with
`A = (1, 1, 1, 1)` (`G = 4`). -/
def figureEightTail : Fin 4 → Fin 3 :=
  fun e => if e = 0 then 0 else if e = 1 then 1 else if e = 2 then 0 else 2
def figureEightHead : Fin 4 → Fin 3 :=
  fun e => if e = 0 then 1 else if e = 1 then 0 else if e = 2 then 2 else 0
def figureEightA : Fin 4 → ℤ := fun _ => 1

/-- The figure-eight is **rigid** at `A = (1, 1, 1, 1)`: the two independent
cycles carry no slack, so "the support is a single directed cycle" is
sufficient but not necessary. -/
theorem figureEight_rigid :
    Rigid figureEightTail figureEightHead (Finset.univ : Finset (Fin 3)) figureEightA 4 :=
  (rigid_iff_decider figureEightTail figureEightHead (Finset.univ : Finset (Fin 3))
    figureEightA 4).mpr (by decide)

/-- The *same* figure-eight support with `A = (2, 2, 1, 1)` (`G = 6`) is **not**
rigid: `B = (1, 1, 2, 2)` is the alternative. So rigidity is a multiplicity
property, not determined by the support topology. -/
theorem figureEight_nonrigid :
    ¬ Rigid figureEightTail figureEightHead (Finset.univ : Finset (Fin 3))
        (fun e => if e = 0 then 2 else if e = 1 then 2 else 1) 6 := by
  intro h
  have h' := (rigid_iff_decider figureEightTail figureEightHead (Finset.univ : Finset (Fin 3))
    (fun e => if e = 0 then 2 else if e = 1 then 2 else 1) 6).mp h
  revert h'
  decide

end Examples

end AssemblyP1.FiniteRigidityDecider
