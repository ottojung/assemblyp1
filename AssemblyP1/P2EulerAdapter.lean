import Mathlib
import AssemblyP1.P2RepeatResidual

/-!
# (R3): from the corrected `P2` genome facts to the exact combinatorial residual

`AssemblyP1.P2RepeatResidual` proves the corrected genome side of the #89
residual: actual `P2` plus primitivity gives **node multiplicity `≤ 2`**
(`AssemblyP1.P2.imp_nodeCount_le_two`) and the non-interleaving of the *maximal
extensions* of interleaving repeated `(L-1)`-mers
(`AssemblyP1.P2.imp_ExtCrossing`), and it *refutes* the two un-extended
formulations (`cex_not_NodeCrossing`, `cex_not_maximalRepeat_at_same_starts`).
What is left of the residual is the (R3) multigraph/chord combinatorics.

This module replaces the multigraph layer of that residual by a purely
genome-side statement, proves the transfer to it in the kernel, and pins down
exactly which hypothesis that statement still needs.

## 1. The transfer: equal spectrum ⟹ same `(L-1)`-mer traversal

The classical route matches the two traversals of the `(L-1)`-de Bruijn
multigraph start by start and needs a *bijection* of the starts.  That is
avoidable, and avoiding it matters here: the transfer below needs only a
*choice*, so no injectivity/surjectivity argument is needed anywhere.

| theorem | content |
| --- | --- |
| `exists_startChoice` | equal complete `L`-spectra give `τ : Fin G → Fin G` with `window S (τ j) = window E j` for every `j` (a choice of truth occurrences of the candidate's read types) |
| `NodeStep` | `τ` walks the truth's `(L-1)`-mer multigraph: `nodeWindow S (τ j + 1) = nodeWindow S (τ (j + 1))` |
| `nodeStep_of_choice` | **`NodeStep` is automatic for a start-by-start choice**: the candidate's node at `j + 1` and the truth's node at `τ j + 1` are both the `L-1`-suffix of the same length-`L` read type |
| `symbol_of_choice` | `E j = S (τ j)`: the candidate is the truth read through `τ` |

So the *only* remaining content of the spectrum-to-traversal transfer is
`NodeStep`+`symbol_of_choice`, both proved here with no premise.

## 2. The exact combinatorial residual, and the reduction to it

```text
NodeStepUnique hG L S :=
  ∀ τ : Fin G → Fin G, NodeStep hG L S τ →
    ∃ k, ∀ j, S (τ (j + k)) = S j
```

`p2_of_nodeStepUnique` : equal complete `L`-spectrum + `NodeStepUnique` ⟹
`RotEquiv hG E S`.  So `NodeStepUnique` **replaces** the
`hUnique : UniqueEulerCircuit …` premise of
`AssemblyP1.P2SpectrumUniqueness.p2_spectrum_unique_up_to_rotation` by a
statement that mentions only the truth's `nodeWindow`, the starts `Fin G` and
the successor map — **no** `EulerCircuit`, no `TrailEquiv`, no multigraph, no
`UniqueEulerCircuit`, no `specCount`, and no BBT/Ukkonen premise.  The residual
is a single decidable combinatorial statement about the truth alone.

Also proved here: `exists_rotAdd_of_comm_nextStart`, i.e. a map of the starts
commuting with the successor is a rotation — the closure property that
`P1` uses to force `NodeStep` maps to be rotations.

## 3. Kernel-checked: node multiplicity `≤ 2` is not enough; clause 2 is the
load-bearing ingredient

`S = 0 0 1 0 1 1` at `G = 6`, `L = 3`:

* every length-`2` word occurs at most twice (`cex_nodeCount_le_two`), so the
  multigraph hypothesis of the search route is satisfied;
* `S` and `E = 0 0 1 1 0 1` have the **same complete length-`3` spectrum**
  (`cex_spec`) and `E` is **not** a cyclic shift of `S` (`cex_not_rotEquiv`);
* the only two maximal repeats of length `≥ L - 1 = 2` are at the starts
  `1, 3` and `2, 5`, and those two pairs interleave
  (`cex_interleaved_long_repeats`), so `S` is **not** `P2` at `L = 3`
  (`cex_not_p2`).

So `nodeCount ≤ 2` and primitivity do **not** give `NodeStepUnique`; the two
traversals are separated by exactly one interleaved pair of maximal repeats of
length `≥ L - 1`, which is clause 2 of `P2`.  `noInterleavedLongRepeat` is that
clause in the form the (R3) argument needs: it ranges over
`SourceFaithfulIs.Genome.IsRepeat` — maximal repeats, maximal on *both* sides —
and **not** over the un-extended node pairs, which
`AssemblyP1.P2RepeatResidual.cex_not_NodeCrossing` shows is false for `P2`.
`ExtCrossing`, the correction proved in `AssemblyP1.P2RepeatResidual`, is a
*consequence* of the same clause but is stated on the (shifted) starts of
`maxPair_isRepeat`, so it is the maximal-repeat form above, not `ExtCrossing`
itself, that the (R3) combinatorics consumes.

## 4. What is *not* proved here

`NodeStepUnique` is **not** proved for a `P2` truth.  The remaining step is the
(R3) combinatorial theorem: for a primitive `P2` truth whose `(L-1)`-mers each
occur at most twice, every map of the starts satisfying `NodeStep` spells the
truth up to cyclic shift.  §3 shows this is a genuine statement (it is false for
`nodeCount ≤ 2` alone) and identifies the hypothesis it must use.  It is the
laminar-chord / block-coherence argument described in
`docs/issue89-spectrum-uniqueness.md` §3(R3) and `docs/bbt-chord-rematch-89.md`
§4, and it is **not** attempted here.

No `axiom`, `sorry` or `admit` occurs in this file, no definition in the
library was changed to make a theorem provable, and the statement of any
existing theorem is unchanged.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

namespace AssemblyP1.P2EulerAdapter

open AssemblyP1.P2SpectrumUniqueness
open AssemblyP1.PopulationReduction
open AssemblyP1.SourceFaithfulIs
open AssemblyP1.OrientedRigidity

variable {α : Type} [DecidableEq α] {G L : ℕ}

/-- The starts of `W` spelling the read type `w`. -/
private abbrev fibre (hG : 0 < G) (W : Fin G → α) (w : Fin L → α) : Finset (Fin G) :=
  Finset.univ.filter (fun r => window (L := L) hG W r = w)

private theorem card_fibre (hG : 0 < G) (W : Fin G → α) (w : Fin L → α) :
    (fibre hG W w).card = specCount (L := L) hG W w := rfl

theorem mem_fibre (hG : 0 < G) (W : Fin G → α) (w : Fin L → α) (r : Fin G)
    (h : window (L := L) hG W r = w) : r ∈ fibre hG W w :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩

/-- **Equal complete spectra give a start-by-start choice of truth
occurrences.**  For every start `j` of `E` there is a start `τ j` of `S`
carrying the *same complete length-`L` read type*; `τ` need not be a bijection
and none is needed downstream. -/
theorem exists_startChoice (hG : 0 < G) (hL : 0 < L) (S E : Fin G → α)
    (hspec : specCount (L := L) hG S = specCount (L := L) hG E) :
    ∃ τ : Fin G → Fin G, ∀ j : Fin G, window (L := L) hG S (τ j)
      = window (L := L) hG E j := by
  classical
  have hmem : ∀ j : Fin G, ∃ r : Fin G,
      window (L := L) hG S r = window (L := L) hG E j := by
    intro j
    have hne : (fibre hG E (window (L := L) hG E j)).Nonempty :=
      ⟨j, mem_fibre hG E _ j rfl⟩
    have hE : 0 < specCount (L := L) hG E (window (L := L) hG E j) := by
      rw [← card_fibre]
      exact Finset.card_pos.mpr hne
    have hS : 0 < specCount (L := L) hG S (window (L := L) hG E j) := by
      rw [hspec]
      exact hE
    have hSc : 0 < (fibre hG S (window (L := L) hG E j)).card := by
      rw [card_fibre]; exact hS
    obtain ⟨r, hr⟩ := Finset.card_pos.mp hSc
    exact ⟨r, (Finset.mem_filter.mp hr).2⟩
  choose τ hτ using hmem
  exact ⟨τ, hτ⟩

/-- **The node-step condition.**  `τ` walks the truth's `(L-1)`-mer
multigraph if the node it lands on at each start is the node the truth has one
step later.  Equivalently: the candidate's node sequence is the truth's node
sequence read through `τ`. -/
def NodeStep (hG : 0 < G) (L : ℕ) (S : Fin G → α) (τ : Fin G → Fin G) : Prop :=
  ∀ j : Fin G, nodeWindow (L := L) hG S (nextStart hG (τ j))
    = nodeWindow (L := L) hG S (τ (nextStart hG j))

/-- **The node-step condition is automatic for a start-by-start choice.**  If
`window S (τ j) = window E j` for all `j`, then the candidate's node at `j + 1`
is the truth's node at `τ j + 1`, because both are the `L-1`-suffix of the same
length-`L` read type.  This is the whole transfer from "equal complete
spectrum" to "same `(L-1)`-mer traversal", and it needs no bijectivity. -/
theorem nodeStep_of_choice (hG : 0 < G) (S E : Fin G → α) (τ : Fin G → Fin G)
    (hτ : ∀ j : Fin G, window (L := L) hG S (τ j) = window (L := L) hG E j) :
    NodeStep hG L S τ := by
  intro j
  calc nodeWindow (L := L) hG S (nextStart hG (τ j))
      = winSuffix (window (L := L) hG S (τ j)) :=
        (nodeWindow_next' hG S (τ j))
    _ = winSuffix (window (L := L) hG E j) := congrArg winSuffix (hτ j)
    _ = nodeWindow (L := L) hG E (nextStart hG j) := (nodeWindow_next' hG E j).symm
    _ = winPrefix (window (L := L) hG E (nextStart hG j)) := (winPrefix_window' hG E _).symm
    _ = winPrefix (window (L := L) hG S (τ (nextStart hG j))) :=
      congrArg winPrefix ((hτ (nextStart hG j)).symm)
    _ = nodeWindow (L := L) hG S (τ (nextStart hG j)) := winPrefix_window' hG S _

/-- The start chosen for a read type carries the same symbol, so the candidate
is the truth read through `τ`. -/
theorem symbol_of_choice (hG : 0 < G) {hL : 0 < L} (S E : Fin G → α) (τ : Fin G → Fin G)
    (hτ : ∀ j : Fin G, window (L := L) hG S (τ j) = window (L := L) hG E j)
    (j : Fin G) : E j = S (τ j) := by
  have h1 : cyc hG S (τ j).val = cyc hG E j.val := by
    have hh := congrFun (hτ j) ⟨0, hL⟩
    simpa only [window, cyc, Nat.add_zero] using hh
  have hS : cyc hG S (τ j).val = S (τ j) := by
    unfold cyc
    exact congrArg S (Fin.ext (Nat.mod_eq_of_lt (τ j).isLt))
  have hE : cyc hG E j.val = E j := by
    unfold cyc
    exact congrArg E (Fin.ext (Nat.mod_eq_of_lt j.isLt))
  exact hE.symm.trans (h1.symm.trans hS)


/-! ## The exact combinatorial residual, and the reduction to it -/

section Combinatorics

variable (hG : 0 < G)

/-- Forward rotation of the circle of starts by `s`. -/
def rotAdd (hG : 0 < G) (s : ℕ) (x : Fin G) : Fin G :=
  ⟨(x.val + s) % G, Nat.mod_lt _ hG⟩

/-- A map commuting with the successor is a rotation. -/
theorem exists_rotAdd_of_comm_nextStart {τ : Fin G → Fin G}
    (hτ : ∀ j : Fin G, τ (nextStart hG j) = nextStart hG (τ j)) :
    ∃ c : Fin G, ∀ j : Fin G, τ j = rotAdd hG c.val j := by
  set c : Fin G := τ (⟨0, hG⟩ : Fin G) with hcdef
  have hiter : ∀ (n : ℕ) (j : Fin G),
      τ ((nextStart hG)^[n] j) = (nextStart hG)^[n] (τ j) := by
    intro n
    induction n with
    | zero => intro j; simp only [Function.iterate_zero, id_eq]
    | succ m ih =>
        intro j
        have e1 : (nextStart hG)^[Nat.succ m] j = nextStart hG ((nextStart hG)^[m] j) :=
          Function.iterate_succ_apply' (f := nextStart hG) (n := m) j
        have e2 : (nextStart hG)^[Nat.succ m] (τ j) = nextStart hG ((nextStart hG)^[m] (τ j)) :=
          Function.iterate_succ_apply' (f := nextStart hG) (n := m) (τ j)
        have h3 : τ ((nextStart hG)^[m] j) = (nextStart hG)^[m] (τ j) := ih j
        calc τ ((nextStart hG)^[Nat.succ m] j) = τ (nextStart hG ((nextStart hG)^[m] j)) :=
            congrArg τ e1
          _ = nextStart hG (τ ((nextStart hG)^[m] j)) := hτ _
          _ = nextStart hG ((nextStart hG)^[m] (τ j)) := congrArg (nextStart hG) h3
          _ = (nextStart hG)^[Nat.succ m] (τ j) := e2.symm
  refine ⟨c, ?_⟩
  intro j
  have h0 : ((nextStart hG)^[j.val] (⟨0, hG⟩ : Fin G)) = j := by
    apply Fin.ext
    rw [nextIter_val]
    simpa using (Nat.mod_eq_of_lt j.isLt)
  have hv := hiter j.val (⟨0, hG⟩ : Fin G)
  rw [h0, ← hcdef] at hv
  refine hv.trans ?_
  apply Fin.ext
  rw [nextIter_val, Nat.add_comm]
  show (j.val + c.val) % G = (j.val + c.val) % G
  rfl

/-- **The exact combinatorial residual of `thm:BBT` at `K = L - 1`.**  Every
map of the starts that walks the truth's `(L-1)`-mer multigraph (`NodeStep`)
spells the truth up to cyclic shift.

This statement mentions only the truth's `nodeWindow`, the starts `Fin G`, and
the successor map.  It contains **no** multigraph, no `EulerCircuit`, no
`TrailEquiv`, no `specCount`, no `UniqueEulerCircuit` and no BBT/Ukkonen
premise: it is the (R3) combinatorial content of the residual, isolated on the
genome side. -/
def NodeStepUnique (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  ∀ τ : Fin G → Fin G, NodeStep hG L S τ →
    ∃ k : ℕ, ∀ j : Fin G, S (τ ⟨(j.val + k) % G, Nat.mod_lt _ hG⟩) = S j

/-- **Equal complete `L`-spectrum plus `NodeStepUnique` gives rotation
equivalence.**  This replaces `hUnique : UniqueEulerCircuit …` of
`AssemblyP1.P2SpectrumUniqueness.p2_spectrum_unique_up_to_rotation` by a
statement about the genome's own `(L-1)`-windows.

The proof is short because the transfer is automatic: a start-by-start choice
`τ` of truth occurrences of the candidate's read types is a `NodeStep` map for
free, and the candidate is the truth read through `τ`. -/
theorem p2_of_nodeStepUnique (hG : 0 < G) (hL : 0 < L) (S E : Fin G → α)
    (hUni : NodeStepUnique hG L S)
    (hSpec : specCount (L := L) hG S = specCount (L := L) hG E) :
    RotEquiv hG E S := by
  obtain ⟨τ, hτ⟩ := exists_startChoice hG hL S E hSpec
  have hstep : NodeStep hG L S τ := nodeStep_of_choice hG S E τ hτ
  obtain ⟨k, hk⟩ := hUni τ hstep
  refine ⟨k, ?_⟩
  intro i
  exact (symbol_of_choice (hL := hL) hG S E τ hτ _).trans (hk i)
/-- **Clause 2 of the canonical `AssemblyP1.P2` forbids interleaved maximal
repeats of length `≥ L - 1`.**  This is the form of the non-interleaving
obstruction that the (R3) combinatorial argument consumes: it ranges over
`Genome.IsRepeat` (a maximal repeat, maximal on *both* sides), not over the
un-extended node pairs — which is exactly the correction forced by
`AssemblyP1.P2RepeatResidual.cex_not_NodeCrossing`. -/
theorem noInterleavedLongRepeat (hL : 2 ≤ L) (S : Fin G → α)
    (hP2 : P2 hG L S) {e₁ e₂ : Fin G} {a b c d : Fin G}
    (he₁ : L - 1 ≤ e₁.val) (he₂ : L - 1 ≤ e₂.val)
    (hR₁ : (mkGenome hG S).IsRepeat e₁.val a b)
    (hR₂ : (mkGenome hG S).IsRepeat e₂.val c d)
    (hI : Interleaved (mkGenome hG S) a b c d) : False := by
  have h := hP2.2 e₁ e₂ a b c d hR₁ hR₂ hI
  rcases h with h | h <;> omega

/-! ## 3. Kernel-checked: node multiplicity `≤ 2` is *not* enough; clause 2 is
the load-bearing ingredient

The search route for the (R3) combinatorics wants to conclude `NodeStepUnique`
from "every `(L-1)`-mer occurs at most twice" together with primitivity, and to
use **clause 2 of `P2`** to rule out the remaining alternatives.  The instance
below shows that the multiplicity bound alone is *not* sufficient, and that the
two alternative traversals it exhibits are separated by exactly one interleaved
pair of maximal repeats of length `≥ L - 1` — i.e. by clause 2, and by nothing
else.  This pins the residual precisely: any proof of `NodeStepUnique` for a
`P2` truth must use clause 2 in this form (interleaved **maximal repeats**,
not the un-extended node pairs, which `cex_not_NodeCrossing` shows is false). -/

section LoadBearing

variable (hG : 0 < G)

/-- `S = 0 0 1 0 1 1`, the truth of the separating instance. -/
def cexW : Fin 6 → Fin 2 := ![0, 0, 1, 0, 1, 1]

/-- `E = 0 0 1 1 0 1`, an alternative traversal of the same `(L-1)`-mer
multigraph. -/
def cexE : Fin 6 → Fin 2 := ![0, 0, 1, 1, 0, 1]

theorem cexG : 0 < 6 := by decide

/-- **The complete length-`3` spectra of `cexW` and `cexE` agree.**  Both words
have the six distinct length-`3` words `001`, `011`, `110`, `101`, `010`,
`100`, each exactly once. -/
theorem cex_spec : specCount (L := 3) (hG := cexG) cexW
    = specCount (L := 3) (hG := cexG) cexE := by
  unfold specCount
  decide +kernel

/-- **`cexE` is not a cyclic shift of `cexW`.** -/
theorem cex_not_rotEquiv :
    ¬ RotEquiv (hG := cexG) cexE cexW := by
  rintro ⟨k, hk⟩
  have hnot : ∀ j : ℕ, j < 6 →
      ¬ (∀ i : Fin 6, cexE ⟨(i.val + j) % 6, Nat.mod_lt _ cexG⟩ = cexW i) := by
    intro j hj
    interval_cases j <;> decide
  exact hnot (k % 6) (Nat.mod_lt _ cexG) (by simpa [Nat.add_mod, Nat.mod_mod] using hk)

/-- **Every length-`2` word of `cexW` occurs at most twice**, so the
`(L-1)`-de Bruijn multigraph of `cexW` has node multiplicity `≤ 2` and
`AssemblyP1.P2.imp_nodeCount_le_two`'s conclusion holds. -/
theorem cex_nodeCount_le_two : ∀ k : Fin 2 → Fin 2,
    nodeCount (L := 3) (hG := cexG) cexW k ≤ 2 := by
  decide +kernel

/-- **The two maximal repeats of length `2 = L - 1` in `cexW`, at the starts
`1, 3` and `2, 5`.**  Both are `Genome.IsRepeat` (equal length-`2` windows,
different preceding *and* following symbols), and their selected starts
interleave. -/
theorem cex_interleaved_long_repeats :
    (mkGenome (hG := cexG) (S := cexW)).IsRepeat 2 ⟨1, by decide⟩ ⟨3, by decide⟩
      ∧ (mkGenome (hG := cexG) (S := cexW)).IsRepeat 2 ⟨2, by decide⟩
          ⟨5, by decide⟩
      ∧ Interleaved (mkGenome (hG := cexG) (S := cexW)) ⟨1, by decide⟩ ⟨3, by decide⟩
          ⟨2, by decide⟩ ⟨5, by decide⟩ := by
  decide +kernel

/-- **So `cexW` is *not* `P2` at `L = 3`:** the interleaved-pair clause fails on
the pair of maximal repeats of length `2 > L - 2 = 1`.  This is the exact
obstruction that separates the two traversals of §3, and
`noInterleavedLongRepeat` above is the form of clause 2 that rules it
out. -/
theorem cex_not_p2 : ¬ P2 (hG := cexG) (L := 3) (S := cexW) := by
  intro hP2
  exact noInterleavedLongRepeat cexG (by decide) cexW hP2
    (e₁ := ⟨2, by decide⟩) (e₂ := ⟨2, by decide⟩)
    (a := ⟨1, by decide⟩) (b := ⟨3, by decide⟩)
    (c := ⟨2, by decide⟩) (d := ⟨5, by decide⟩)
    (by decide) (by decide) cex_interleaved_long_repeats.1
    cex_interleaved_long_repeats.2.1 cex_interleaved_long_repeats.2.2

end LoadBearing

end Combinatorics

end AssemblyP1.P2EulerAdapter

