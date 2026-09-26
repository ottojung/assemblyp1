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

This module replaces the multigraph layer of that residual by a purely
genome-side statement, proves the transfer to it in the kernel, and pins down
exactly which hypothesis that statement still needs.

## 0. Two statements that look right and are **false** (both refuted below)

The residual of `thm:BBT` at `K = L - 1` is a statement about maps of the
starts that walk the truth's `(L-1)`-mer multigraph (`NodeStep`).  Two
quantifications over such maps are *both* wrong, and both are refuted in the
kernel here, because the two defects are independent of the repeat theory:

* **`NodeStepUniqueArbitrary`** — every map `τ : Fin G → Fin G` satisfying
  `NodeStep` spells the truth up to cyclic shift — is **false**.
  `NodeStep` is satisfied by every *constant* map `τ j = r` at any start `r`
  whose `(L-1)`-window equals the window at `r + 1`, i.e. as soon as the truth
  contains a run of `L` equal symbols; the conclusion then forces the truth to
  be constant.  Kernel-checked: `cexConst_not_NodeStepUnique` on
  `S = A A A B`, `G = 4`, `L = 3` (primitive, `P2`).
* **`NodeStepPermUnique`** — every *bijection* `σ` satisfying `NodeStep` is
  itself a cyclic shift — is **false** as well, and for a subtler reason: a
  switch of two copies of a repeated `(L-1)`-mer that swaps *equal symbols*
  changes the traversal without changing the genome.  Kernel-checked:
  `cexPerm_not_NodeStepPermUnique` on `S = A A B A B`, `G = 5`, `L = 3`
  (primitive, `P2`).

Neither defect is a property of repeats; both are defects of the *statement*,
and the second one is invisible to any argument that only looks at the map
`σ`.  The correct residual therefore has to be stated **about the word that the
map spells**:

```text
NodeStepRot hG L S :=
  ∀ σ : Fin G ≃ Fin G, NodeStep hG L S σ → RotEquiv hG (fun j => S (σ j)) S
```

i.e. every *bijection* of the starts that walks the multigraph spells the truth
up to cyclic shift.  This is `NodeStepUnique` with the two corrections: the map
must be a bijection (defect 1) and the conclusion is about `S ∘ σ`, not about
`σ` (defect 2).  `p2_of_NodeStepRot` below shows it is exactly as strong as the
old `hUnique` premise, and no stronger.

## 1. The transfer: equal spectrum ⟹ same `(L-1)`-mer traversal

The classical route matches the two traversals of the `(L-1)`-de Bruijn
multigraph start by start and needs a *bijection* of the starts.  The transfer
below produces such a bijection, fibre by fibre: equal complete spectra mean
that for every read type `w` the number of starts of `S` spelling `w` equals
the number of starts of `E` spelling `w`, so each pair of fibres admits an
equivalence, and these assemble into a bijection of the starts.

| theorem | content |
| --- | --- |
| `startsOf`, `card_startsOf` | the read-type fibre; `card_startsOf` is `rfl`-equal to `specCount` |
| `Matching` | a bijection `τ` of the starts with `window S (τ j) = window E j` for every `j` |
| `exists_matching` | **equal complete `L`-spectra give a `Matching`, i.e. an `Equiv`, not a mere choice** |
| `NodeStep` | `τ` walks the truth's `(L-1)`-mer multigraph |
| `nodeStep_of_choice` | **`NodeStep` is automatic for such a matching**: the candidate's node at `j + 1` and the truth's node at `τ j + 1` are both the `L-1`-suffix of the same length-`L` read type |
| `symbol_of_choice` | `E j = S (τ j)`: the candidate is the truth read through `τ` |

So the *only* remaining content of the spectrum-to-traversal transfer is
`NodeStep` + `symbol_of_choice`, both automatic.

## 2. The exact combinatorial residual, and the reduction to it

`p2_of_NodeStepRot` : equal complete `L`-spectrum + `NodeStepRot` ⟹
`RotEquiv hG E S`.  So `NodeStepRot` **replaces** the
`hUnique : UniqueEulerCircuit …` premise of
`AssemblyP1.P2SpectrumUniqueness.p2_spectrum_unique_up_to_rotation` by a
statement that mentions only the truth's `nodeWindow`, the starts `Fin G` and
the successor map — **no** `EulerCircuit`, no `TrailEquiv`, no multigraph, no
`UniqueEulerCircuit`, no `specCount`, and no BBT/Ukkonen premise.

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

So `nodeCount ≤ 2` and primitivity do **not** give `NodeStepRot`; the two
traversals are separated by exactly one interleaved pair of maximal repeats of
length `≥ L - 1`, which is clause 2 of `P2`.  `noInterleavedLongRepeat` is that
clause in the form the (R3) argument needs: it ranges over
`SourceFaithfulIs.Genome.IsRepeat` (a maximal repeat, maximal on *both*
sides), and **not** over the un-extended node pairs, which
`AssemblyP1.P2RepeatResidual.cex_not_NodeCrossing` shows is false for `P2`.

## 4. What is *not* proved here

`NodeStepRot` is **not** proved for a `P2` truth.  See
`AssemblyP1.P2LongObstruction` for the exact remaining combinatorial statement
(`LemmaT`, the first-divergence / two-switch lemma) and for the kernel-checked
intermediates that do *not* settle it.
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

/-! ## 1. Equal complete spectra give a *bijection* of the starts -/

/-- The starts of `W` spelling the read type `w`.  This is the fibre used by
`specCount`; it is a definition, not a new predicate. -/
def startsOf (hG : 0 < G) (W : Fin G → α) (w : Fin L → α) : Finset (Fin G) :=
  Finset.univ.filter (fun r : Fin G => window (L := L) hG W r = w)

theorem card_startsOf (hG : 0 < G) (W : Fin G → α) (w : Fin L → α) :
    (startsOf hG W w).card = specCount (L := L) hG W w := rfl

/-- **A matching of the two traversals.**  `τ` pairs each start of the
candidate with a start of the truth carrying the *same complete length-`L` read
type*, and is a **bijection** of the starts.  Such a matching exists exactly
when the complete spectra agree, and it is unique up to the choices inside a
read-type fibre. -/
def Matching (hG : 0 < G) (L : ℕ) (S E : Fin G → α) (τ : Fin G → Fin G) : Prop :=
  Function.Bijective τ ∧ ∀ j : Fin G, window (L := L) hG S (τ j)
    = window (L := L) hG E j

/-- Two nonempty finite sets of the same cardinality are in bijection. -/
private theorem finset_equiv_of_card_eq {β : Type} (s t : Finset β)
    (h : s.card = t.card) (hs : 0 < s.card) : Nonempty (↥s ≃ ↥t) := by
  have e1 : Nonempty (↥s ≃ Fin s.card) := by
    have h1 := Fintype.equivFin ↥s
    rw [Fintype.card_coe] at h1
    exact ⟨h1⟩
  have e2 : Nonempty (Fin t.card ≃ ↥t) := by
    have h2 := Fintype.equivFin ↥t
    rw [Fintype.card_coe] at h2
    exact ⟨h2.symm⟩
  have e3 : Nonempty (Fin s.card ≃ Fin t.card) := by
    rw [h]
    exact ⟨Equiv.refl _⟩
  exact ⟨e1.some.trans e3.some |>.trans e2.some⟩

/-- **Equal complete spectra give a matching**: a *bijection* `τ` of the starts
with `window hG S (τ j) = window hG E j` for every `j`.

The construction is fibre by fibre: the two spectra agree, so the starts of `S`
spelling `w` and the starts of `E` spelling `w` have the same cardinality for
every read type `w`, hence are in bijection; these fibre bijections assemble
into a bijection of all the starts.  This is the Eulerian-traversal
correspondence in the only form the reduction needs, and it is an `Equiv`, not
a choice: a non-injective map of the starts satisfies `NodeStep` far too
easily (`cexConst_not_NodeStepUnique` below). -/
theorem exists_matching (hG : 0 < G) (S E : Fin G → α)
    (hspec : specCount (L := L) hG S = specCount (L := L) hG E) :
    ∃ τ : Fin G ≃ Fin G, Matching hG L S E (τ : Fin G → Fin G) := by
  classical
  set A : (Fin L → α) → Finset (Fin G) := fun w => startsOf hG E w with hAdef
  set B : (Fin L → α) → Finset (Fin G) := fun w => startsOf hG S w with hBdef
  have hcard : ∀ w : Fin L → α, (A w).card = (B w).card := by
    intro w
    rw [hAdef, hBdef]
    have e := congrArg (fun f : (Fin L → α) → ℕ => f w) hspec
    simpa only [card_startsOf] using e.symm
  have hmemA : ∀ r : Fin G, r ∈ A (window (L := L) hG E r) := by
    intro r
    simp only [hAdef, startsOf, Finset.mem_filter, Finset.mem_univ, true_and]
  have hmemB : ∀ s : Fin G, s ∈ B (window (L := L) hG S s) := by
    intro s
    simp only [hBdef, startsOf, Finset.mem_filter, Finset.mem_univ, true_and]
  -- the fibre bijections, chosen simultaneously
  have hne : ∀ w : Fin L → α, Nonempty (↥(A w) ≃ ↥(B w)) := by
    intro w
    by_cases hw : 0 < (A w).card
    · exact finset_equiv_of_card_eq _ _ (hcard w) hw
    · have hb : (A w).card = 0 := by omega
      have hAe : A w = ∅ := Finset.card_eq_zero.mp hb
      have hb' : (B w).card = 0 := by rw [← hcard w, hb]
      have hBe : B w = ∅ := Finset.card_eq_zero.mp hb'
      rw [hAe, hBe]
      exact ⟨Equiv.refl _⟩
  letI : Nonempty (∀ w : Fin L → α, Nonempty (↥(A w) ≃ ↥(B w))) :=
    ⟨fun w => hne w⟩
  set φ : ∀ w : Fin L → α, ↥(A w) ≃ ↥(B w) :=
    fun w => Classical.choice (inferInstanceAs (Nonempty (↥(A w) ≃ ↥(B w)))) with hφdef
  have hφinj : ∀ (w : Fin L → α), Function.Injective (fun y : ↥(A w) => (φ w y).val) :=
    fun w a b hab => (φ w).injective (Subtype.ext hab)
  have memA : ∀ (w : Fin L → α) (r : Fin G), window (L := L) hG E r = w → r ∈ A w := by
    intro w r hr
    have : window (L := L) hG E r = w := hr
    simp only [hAdef, startsOf, Finset.mem_filter, Finset.mem_univ, true_and, this]
  set V : (Fin L → α) → Fin G → Fin G := fun w r =>
    if h : window (L := L) hG E r = w then (φ w ⟨r, memA w r h⟩).val else r with hVdef
  set σ : Fin G → Fin G := fun r => V (window (L := L) hG E r) r with hσdef
  have hmatch : ∀ r : Fin G, window (L := L) hG E r = window (L := L) hG S (σ r) := by
    intro r
    have h1 : (φ (window (L := L) hG E r) ⟨r, memA _ r rfl⟩).val
        ∈ B (window (L := L) hG E r) := (φ _ _).property
    simp only [hBdef, startsOf, Finset.mem_filter, Finset.mem_univ, true_and] at h1
    calc window (L := L) hG E r
        = window (L := L) hG S ((φ (window (L := L) hG E r) ⟨r, memA _ r rfl⟩).val) :=
          h1.symm
      _ = window (L := L) hG S (σ r) := by
        simp only [hσdef, hVdef]
        rw [dif_pos (by simp)]
  -- injectivity, fibre by fibre: equal images force equal read types, so both
  -- ends are computed by the *same* fibre equivalence `φ w`, whose injectivity
  -- then gives `r = r'`.
  have hinj : Function.Injective σ := by
    intro r r' heq
    have hw : window (L := L) hG E r = window (L := L) hG E r' := by
      have h1 : window (L := L) hG E r = window (L := L) hG S (σ r) := hmatch r
      have h2 : window (L := L) hG E r' = window (L := L) hG S (σ r') := hmatch r'
      rw [h1, h2, heq]
    set w : Fin L → α := window (L := L) hG E r with hwdef
    have hleft : σ r = (φ w ⟨r, memA w r rfl⟩).val := by
      simp only [hσdef, hVdef]
      rw [dif_pos (by simp)]
    have hright : σ r' = (φ w ⟨r', memA w r' hw.symm⟩).val := by
      have e : σ r' = V w r' := by
        simp only [hσdef, ← hw, hwdef]
      simp only [e, hVdef]
      rw [dif_pos (show window (L := L) hG E r' = w from hw.symm)]
    have hval : (φ w ⟨r, memA w r rfl⟩).val
        = (φ w ⟨r', memA w r' hw.symm⟩).val := by
      rw [← hleft, ← hright]
      exact heq
    have hsub : (⟨r, memA w r rfl⟩ : ↥(A w)) = ⟨r', memA w r' hw.symm⟩ := hφinj w hval
    exact congrArg Subtype.val hsub
  -- `Fin G` is finite, so the injective endomap `σ` is surjective: the
  -- surjectivity needs no separate fibre construction at all.
  have hsurj : Function.Surjective σ :=
    (Finite.injective_iff_surjective).mp hinj
  refine ⟨Equiv.ofBijective σ ⟨hinj, hsurj⟩, (Equiv.ofBijective σ ⟨hinj, hsurj⟩).bijective, ?_⟩
  intro j
  exact (hmatch j).symm

/-- **The node-step condition.**  `τ` walks the truth's `(L-1)`-mer
multigraph if the node it lands on at each start is the node the truth has one
step later.  Equivalently: the candidate's node sequence is the truth's node
sequence read through `τ`. -/
def NodeStep (hG : 0 < G) (L : ℕ) (S : Fin G → α) (τ : Fin G → Fin G) : Prop :=
  ∀ j : Fin G, nodeWindow (L := L) hG S (nextStart hG (τ j))
    = nodeWindow (L := L) hG S (τ (nextStart hG j))

/-- **The node-step condition is automatic for a matching.**  If
`window S (τ j) = window E j` for all `j`, then the candidate's node at `j + 1`
is the truth's node at `τ j + 1`, because both are the `L-1`-suffix of the same
length-`L` read type.  This is the whole transfer from "equal complete
spectrum" to "same `(L-1)`-mer traversal". -/
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

/-- The start matched for a read type carries the same symbol, so the candidate
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

/-- The matching of `exists_matching` is a `NodeStep` map. -/
theorem nodeStep_of_matching (hG : 0 < G) (S E : Fin G → α) (τ : Fin G → Fin G)
    (hτ : Matching hG L S E τ) : NodeStep hG L S τ :=
  nodeStep_of_choice hG S E τ hτ.2

/-! ## 2. The exact combinatorial residual, and the reduction to it -/

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

/-- **A rotation of the starts is a `NodeStep` map**, so the conclusion of
`NodeStepRot` is attained by every rotation: the residual is not vacuous. -/
theorem nodeStep_rotAdd (hG : 0 < G) (L : ℕ) (S : Fin G → α) (c : Fin G) :
    NodeStep hG L S (rotAdd hG c.val) := by
  intro j
  congr 1
  apply Fin.ext
  simp only [rotAdd, nextStart]
  rw [Nat.mod_add_mod, Nat.mod_add_mod,
    show j.val + c.val + 1 = j.val + 1 + c.val from by omega]

/-- A rotation of the starts spells a rotation of the genome. -/
theorem rotEquiv_rotAdd (hG : 0 < G) (S : Fin G → α) (c : Fin G) :
    RotEquiv hG (fun j => S (rotAdd hG c.val j)) S := by
  refine ⟨G - c.val, ?_⟩
  intro i
  refine congrArg S (Fin.ext ?_)
  simp only [rotAdd]
  rw [Nat.mod_add_mod]
  rw [show i.val + (G - c.val) + c.val = i.val + G from by omega]
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

/-! ### 2.1 The two false statements, and the corrected residual -/

/-- **REFUTED: the arbitrary-map version of the residual.**

Every map `τ : Fin G → Fin G` satisfying `NodeStep` spells the truth up to
cyclic shift.  This is `false`: `NodeStep` is satisfied by every constant map
`τ j = r` at a start `r` with `nodeWindow r = nodeWindow (r + 1)`, and the
conclusion would then force the truth to be constant.  See
`cexConst_not_NodeStepUnique` for a kernel-checked instance.

The definition is kept, under a name that says it is refuted, so that the
regression cannot return silently.  It is **not** used in any theorem. -/
def NodeStepUniqueArbitrary (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  ∀ τ : Fin G → Fin G, NodeStep hG L S τ →
    ∃ k : ℕ, ∀ j : Fin G, S (τ ⟨(j.val + k) % G, Nat.mod_lt _ hG⟩) = S j

/-- **REFUTED: the permutation version of the residual, stated about the map.**

Every bijection `σ` satisfying `NodeStep` is itself a cyclic shift of the
starts.  This is `false` as well, and for a subtler reason than the
arbitrary-map version: switching the two copies of a repeated `(L-1)`-mer that
swaps *equal symbols* changes the traversal of the multigraph without changing
the genome.  See `cexPerm_not_NodeStepPermUnique` for a kernel-checked
instance on a primitive `P2` word.

The definition is kept, under a name that says it is refuted, so that the
regression cannot return silently.  It is **not** used in any theorem. -/
def NodeStepPermUnique (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  ∀ σ : Fin G ≃ Fin G, NodeStep hG L S (σ : Fin G → Fin G) →
    ∃ c : Fin G, ∀ j : Fin G, σ j = rotAdd hG c.val j

/-- **The corrected exact combinatorial residual of `thm:BBT` at `K = L - 1`.**

Every **bijection** of the starts that walks the truth's `(L-1)`-mer multigraph
(`NodeStep`) spells the truth up to cyclic shift.

Two corrections relative to the two refuted statements above, both forced by
kernel-checked counterexamples:

* the map must be a **bijection** — a mere map satisfies `NodeStep` far too
  easily (`cexConst_not_NodeStepUnique`);
* the conclusion is about the **genome the map spells**, `S ∘ σ`, and not
  about the map `σ` itself — switching two copies of a repeated `(L-1)`-mer can
  change the map without changing the genome (`cexPerm_not_NodeStepPermUnique`).

The statement mentions only the truth's `nodeWindow`, the starts `Fin G` and
the successor map.  It contains **no** multigraph, no `EulerCircuit`, no
`TrailEquiv`, no `specCount`, no `UniqueEulerCircuit` and no BBT/Ukkonen
premise: it is the (R3) combinatorial content of the residual, isolated on the
genome side. -/
def NodeStepRot (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  ∀ σ : Fin G ≃ Fin G, NodeStep hG L S (σ : Fin G → Fin G) →
    RotEquiv hG (fun j => S (σ j)) S

/-- **Every rotation of the starts satisfies `NodeStepRot`'s conclusion**, so the
residual is a statement about the alternatives to the rotations, not a
vacuous one. -/
theorem NodeStepRot.rotations (hG : 0 < G) (L : ℕ) (S : Fin G → α) (c : Fin G) :
    RotEquiv hG (fun j => S (rotAdd hG c.val j)) S :=
  rotEquiv_rotAdd hG S c

/-- **Equal complete `L`-spectrum plus `NodeStepRot` gives rotation
equivalence.**  This replaces `hUnique : UniqueEulerCircuit …` of
`AssemblyP1.P2SpectrumUniqueness.p2_spectrum_unique_up_to_rotation` by a
statement about the genome's own `(L-1)`-windows.

The proof is short because the transfer is automatic: equal spectra give a
bijection `σ` of the starts (`exists_matching`) carrying the read types, that
bijection is a `NodeStep` map for free, and the candidate is the truth read
through `σ`. -/
theorem p2_of_NodeStepRot (hG : 0 < G) (hL : 0 < L) (S E : Fin G → α)
    (hUni : NodeStepRot hG L S)
    (hSpec : specCount (L := L) hG S = specCount (L := L) hG E) :
    RotEquiv hG E S := by
  obtain ⟨σ, hσ⟩ := exists_matching hG S E hSpec
  have hstep : NodeStep hG L S (σ : Fin G → Fin G) := nodeStep_of_matching hG S E _ hσ
  obtain ⟨k, hk⟩ := hUni σ hstep
  refine ⟨k, ?_⟩
  intro i
  calc E ⟨(i.val + k) % G, Nat.mod_lt _ hG⟩
      = S (σ ⟨(i.val + k) % G, Nat.mod_lt _ hG⟩) :=
        symbol_of_choice (hL := hL) hG S E _ hσ.2 _
    _ = S i := hk i

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

The search route for the (R3) combinatorics wants to conclude `NodeStepRot`
from "every `(L-1)`-mer occurs at most twice" together with primitivity, and to
use **clause 2 of `P2`** to rule out the remaining alternatives.  The instances
below show that the multiplicity bound alone is *not* sufficient, and that the
two alternative traversals it exhibits are separated by exactly one interleaved
pair of maximal repeats of length `≥ L - 1` — i.e. by clause 2, and by nothing
else.  This pins the residual precisely: any proof of `NodeStepRot` for a `P2`
truth must use clause 2 in this form (interleaved **maximal repeats**, not the
un-extended node pairs, which `cex_not_NodeCrossing` shows is false). -/

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

/-! ## 3b. Kernel-checked: the two quantifications of §0, refuted

`cexConst_*` refutes the arbitrary-map version of the residual and
`cexPerm_*` refutes the permutation version stated about the map.  Both
instances are *primitive* and satisfy the repository's actual `P2` at the stated
`L`, so the refutations are not about degenerate words. -/

section Refutations

/-- `S = A A A B`, the truth refuting the arbitrary-map version: it is
primitive and `P2` at `L = 3`, and its `(L-1)`-mers at the starts `0` and `1`
are equal, so a constant start map is a `NodeStep` map. -/
def cexConstW : Fin 4 → PopulationReduction.Bin := ![Bin.A, Bin.A, Bin.A, Bin.B]

theorem cexConstG : 0 < 4 := by decide

/-- The constant start map at the start `0`. -/
def cexConst : Fin 4 → Fin 4 := fun _ => ⟨0, by decide⟩

/-- **`cexConstW` is primitive.** -/
theorem cexConst_primitive :
    RepeatAdapter.IsPrimitive (hG := cexConstG) (S := cexConstW) := by
  intro s hs0 hsG
  have hcases : s = 1 ∨ s = 2 ∨ s = 3 := by omega
  rcases hcases with rfl | rfl | rfl
  · intro hcon
    exact absurd (hcon 2) (by decide)
  · intro hcon
    exact absurd (hcon 1) (by decide)
  · intro hcon
    exact absurd (hcon 0) (by decide)

/-- **`cexConstW` satisfies the repository's actual `P2` at `L = 3`.**  Its
`2`-mers are `AA` (twice), `AB`, `BA`, and `AAA`; there is no maximal triple
repeat of length `≥ 2`, and the only maximal repeat pair, `(2, 0, 1)`, is
vacuous for clause 2. -/
theorem cexConst_clause1 : ∀ (e a b c : Fin 4),
    (mkGenome (hG := cexConstG) (S := cexConstW)).IsTripleRepeat e a b c → e.val < 2 := by
  unfold mkGenome
  decide

theorem cexConst_clause2 : ∀ (e₁ e₂ a b c d : Fin 4),
    (mkGenome (hG := cexConstG) (S := cexConstW)).IsRepeat e₁ a b →
    (mkGenome (hG := cexConstG) (S := cexConstW)).IsRepeat e₂ c d →
    Interleaved (mkGenome (hG := cexConstG) (S := cexConstW)) a b c d →
      e₁.val ≤ 1 ∨ e₂.val ≤ 1 := by
  unfold mkGenome
  decide

theorem cexConst_p2 : P2 (hG := cexConstG) (L := 3) (S := cexConstW) := by
  refine ⟨?_, ?_⟩
  · intro e a b c h
    exact cexConst_clause1 e a b c h
  · intro e₁ e₂ a b c d h₁ h₂ hI
    have h₁4 : e₁ < (mkGenome (hG := cexConstG) (S := cexConstW)).len := h₁.2.1
    have h₂4 : e₂ < (mkGenome (hG := cexConstG) (S := cexConstW)).len := h₂.2.1
    exact cexConst_clause2 ⟨e₁, h₁4⟩ ⟨e₂, h₂4⟩ a b c d h₁ h₂ hI

/-- **The constant start map is a `NodeStep` map of `cexConstW`.**  The
`(L-1)`-mers at the starts `0` and `1` are both `AA`, so
`nodeWindow 1 = nodeWindow 0` and the `NodeStep` condition at the only `j`
that constrains the constant map's node holds. -/
theorem cexConst_nodeStep : NodeStep cexConstG 3 cexConstW cexConst := by
  intro j
  fin_cases j <;> decide

/-- **REFUTES the arbitrary-map version of the residual.**  `cexConstW` is
primitive and `P2` at `L = 3`, and `cexConst` is a `NodeStep` map of it, but
`cexConst` spells the constant word `AAAA`, which is not a cyclic shift of
`AAAB`.  The premise of this refutation is a `NodeStep` map, so
`NodeStepUniqueArbitrary` cannot be restored by any later refinement of the
repeat theory. -/
theorem cexConst_not_NodeStepUnique :
    ¬ NodeStepUniqueArbitrary cexConstG 3 cexConstW := by
  intro h
  obtain ⟨k, hk⟩ := h cexConst cexConst_nodeStep
  have h3 := hk ⟨3, by decide⟩
  simp [cexConst, cexConstW] at h3

/-- `S = A A B A B`, the truth refuting the permutation version stated about
the map: it is primitive and `P2` at `L = 3`, and it has a `NodeStep`
bijection of the starts that is not a rotation, while spelling `S` itself. -/
def cexPermW : Fin 5 → PopulationReduction.Bin := ![Bin.A, Bin.A, Bin.B, Bin.A, Bin.B]

theorem cexPermG : 0 < 5 := by decide

/-- The non-rotational `NodeStep` bijection `0, 3, 2, 1, 4` of the starts of
`cexPermW`.  It swaps the two copies `0, 2` of the repeated `2`-mer `AB`
against the two copies `1, 4` of `AA`… in the order the traversal visits them;
the point is that it is not a rotation. -/
def cexPerm : Fin 5 ≃ Fin 5 where
  toFun := ![⟨0, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩, ⟨4, by decide⟩]
  invFun := ![⟨0, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩, ⟨4, by decide⟩]
  left_inv := by decide
  right_inv := by decide

/-- **`cexPermW` is primitive.** -/
theorem cexPerm_primitive :
    RepeatAdapter.IsPrimitive (hG := cexPermG) (S := cexPermW) := by
  have h1 := P2RepeatResidual.cex_is_shiftPrimitive
  unfold RepeatAdapter.IsPrimitive at *
  intro s hs0 hsG
  have hcases : s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · intro hcon
    exact absurd (hcon 1) (by decide)
  · intro hcon
    exact absurd (hcon 0) (by decide)
  · intro hcon
    exact absurd (hcon 1) (by decide)
  · intro hcon
    exact absurd (hcon 0) (by decide)

/-- **`cexPermW` satisfies the repository's actual `P2` at `L = 3`.**  This is
the same word as `AssemblyP1.P2RepeatResidual.cexWord`, and
`AssemblyP1.P2RepeatResidual.cex_is_p2` already establishes it; it is re-proved
here so that this section is self-contained. -/
theorem cexPerm_p2 : P2 (hG := cexPermG) (L := 3) (S := cexPermW) := by
  have h := P2RepeatResidual.cex_is_p2
  exact h

/-- **`cexPerm` is a `NodeStep` bijection of the starts of `cexPermW`.** -/
theorem cexPerm_nodeStep : NodeStep cexPermG 3 cexPermW (cexPerm : Fin 5 → Fin 5) := by
  intro j
  fin_cases j <;> decide

/-- **REFUTES the permutation version of the residual stated about the map.**
`cexPermW` is primitive and `P2` at `L = 3`, `cexPerm` is a `NodeStep`
bijection of its starts, and it is not a rotation of them.  So the conclusion
of the residual has to be about the genome the map spells, not about the map:
`cexPerm` spells `cexPermW` itself, which is the point of the instance. -/
theorem cexPerm_not_NodeStepPermUnique :
    ¬ NodeStepPermUnique cexPermG 3 cexPermW := by
  intro h
  obtain ⟨c, hc⟩ := h cexPerm cexPerm_nodeStep
  have h0 := hc ⟨0, by decide⟩
  have h1 := hc ⟨1, by decide⟩
  simp [cexPerm, rotAdd] at h0 h1
  fin_cases c <;> simp at h0 h1

end Refutations

end Combinatorics

end AssemblyP1.P2EulerAdapter
