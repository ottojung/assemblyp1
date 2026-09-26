import Mathlib
import AssemblyP1.P2EulerAdapter

/-!
# The `LongObstruction` statement of #89, and the proved part of (R3)

`AssemblyP1.P2EulerAdapter` corrects the surface of the #89 residual: equal
complete `L`-spectra give a **bijection** `σ` of the starts carrying the read
types (`exists_matching`), that bijection is a `NodeStep` map, and the residual
`NodeStepRot` says that every such map spells the truth up to cyclic shift.

Two things are *not* admissible in the residual any more, both because they are
refuted in the kernel by primitive `P2` instances:

* quantifying over **arbitrary** maps satisfying `NodeStep`
  (`cexConst_not_NodeStepUnique`); and
* stating the conclusion about the **map** rather than about the genome it
  spells (`cexPerm_not_NodeStepPermUnique`).

So the residual is stated at the **spectrum level**, which is what the
brute-force probe of `docs/issue89-spectrum-uniqueness.md` §4 actually tested, and
which is the shape of `thm:BBT`'s input:

```text
spectrum_ambiguity_gives_longObstruction :
  IsPrimitive S → specCount S = specCount E → ¬ RotEquiv hG E S →
    LongObstruction hG L S
```

No `NodeStep`, no `NodeStepUnique`, no `NodeStepPermUnique`, no
`UniqueEulerCircuit`, no `EulerianCycle`, no `BBTUniqueAt` and no BBT/Ukkonen
premise appears in it.  The exhaustive probe over binary circular words up to
rotation with `G ≤ 10` and `L ≤ G` found 631 ambiguous `(S, E, L)` configurations
(equal complete `L`-spectrum, `E` not a cyclic shift of `S`) and **zero** of them
without a long obstruction on `S`.

## 1. What *is* proved here

The obstruction is the `P2`-shaped statement: a long maximal triple repeat, or
two interleaved maximal repeats each of length `≥ L - 1`.  This module proves

| name | content |
| --- | --- |
| `LongRepeat`, `LongObstruction`, `LongInterleavedRepeat` | the two clauses, verbatim the clauses of `def:P1P2` |
| `P2.imp_noLongObstruction` | actual `P2` ⟹ no long obstruction (clause 1 and clause 2 separately) |
| `NodeMultiplicity`, `P2.imp_NodeMultiplicity` | actual `P2` + primitivity ⟹ every node has multiplicity `≤ 2` |
| `nodeWindow_E_of_matching`, `nodeCount_E_of_matching` | **the alternative traversal runs on the truth's `(L-1)`-mer multigraph**: for a `Matching` `τ`, `nodeWindow E j = nodeWindow S (τ j)` and `nodeCount E v = nodeCount S v` |
| `longRepeat_of_agree_pair` | two distinct starts carrying a common `(L-1)`-window extend to a `LongRepeat` (via `P2RepeatResidual.maxPair_isRepeat`) |
| `nodeCount_ge_two_of_switch` | a switch of a `NodeStep` map lands twice on one node |
| `switch_longRepeat` | **every switch of the matched traversal produces a long maximal repeat on the truth** |
| `switch_doubleNode_inj_or_pair` | **two-switch lemma**: two switches at the same node are the same switch, or are paired by `τ(·+1) = (τ ·)+1` at the other site; the switch sites form a double cover of the switched nodes |
| `exists_rotAdd_of_noSwitch`, `rotEquiv_of_noSwitch` | a `NodeStep` map with no switch at all *is* a rotation of the starts and spells a rotation of the genome |

`rotEquiv_of_noSwitch` and `switch_longRepeat` together are the proved part of
(R3): the residual is confined to the switched case, and in that case the truth
carries a long maximal repeat.  What is **not** proved is that there are *two*
interleaved ones (clause 2), or a long triple repeat (clause 1).

## 2. What is *not* proved here

`spectrum_ambiguity_gives_longObstruction` is **not** proved in this module; it is
*stated*, as `SpectrumLongObstruction`, and `p2_spectrum_ambiguity` derives the
complete-spectrum uniqueness conclusion from it.  §1 isolates the exact
remaining step: given a matched traversal with at least one switch, show that
the switched nodes yield *two* interleaved maximal repeats of length
`≥ L - 1`, or a maximal triple repeat of length `≥ L - 1`.  The two-switch
double cover `switch_doubleNode_inj_or_pair` is the structural input; the
geometry of its chords is not formalized.

No `axiom`, `sorry` or `admit` occurs in this file, and no definition in the
library was changed to make a theorem provable.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

namespace AssemblyP1.P2LongObstruction

open AssemblyP1.P2EulerAdapter
open AssemblyP1.P2RepeatResidual
open AssemblyP1.P2SpectrumUniqueness
open AssemblyP1.PopulationReduction
open AssemblyP1.SourceFaithfulIs
open AssemblyP1.OrientedRigidity
open AssemblyP1.RepeatAdapter

variable {α : Type} [DecidableEq α] {G L : ℕ}
variable (hG : 0 < G)

/-! ## 1. The obstruction -/

/-- A **long** maximal repeat of `S`: a `Genome.IsRepeat` of length `≥ L - 1`.
This is exactly the shape the second clause of `def:P1P2` ranges over. -/
def LongRepeat (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  ∃ (e : Fin G) (a b : Fin G), L - 1 ≤ e.val ∧ (mkGenome hG S).IsRepeat e.val a b

/-- Two **long** maximal repeats of `S` with interleaving selected starts: the
second clause of `def:P1P2` as a positive statement. -/
def LongInterleavedRepeat (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  ∃ (e₁ e₂ : Fin G) (a b c d : Fin G),
    L - 1 ≤ e₁.val ∧ L - 1 ≤ e₂.val ∧
    (mkGenome hG S).IsRepeat e₁.val a b ∧
    (mkGenome hG S).IsRepeat e₂.val c d ∧
    Interleaved (mkGenome hG S) a b c d

/-- **`LongObstruction`**: the obstruction of `thm:BBT` at `K = L - 1`, spelled
out on the truth alone.  Either a maximal triple repeat of length `≥ L - 1`
(clause 1 of `def:P1P2`) or two interleaved maximal repeats each of length
`≥ L - 1` (clause 2). -/
def LongObstruction (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  (∃ (e : Fin G) (a b c : Fin G), L - 1 ≤ e.val ∧
    (mkGenome hG S).IsTripleRepeat e.val a b c) ∨
  LongInterleavedRepeat hG L S

/-- **Actual `P2` rules out the obstruction**, clause by clause.  This is the
form of the hypothesis the (R3) argument consumes: it ranges over
`Genome.IsTripleRepeat` and `Genome.IsRepeat` (maximal on *both* sides), and
**not** over the un-extended node pairs, which
`AssemblyP1.P2RepeatResidual.cex_not_NodeCrossing` shows is false for `P2`. -/
theorem P2.imp_noLongObstruction (hL : 2 ≤ L) (S : Fin G → α) (hP2 : P2 hG L S) :
    ¬ LongObstruction hG L S := by
  rintro (⟨e, a, b, c, he, hR⟩ | ⟨e₁, e₂, a, b, c, d, he₁, he₂, hR₁, hR₂, hI⟩)
  · exact absurd (hP2.1 e a b c hR) (by omega)
  · rcases hP2.2 e₁ e₂ a b c d hR₁ hR₂ hI with h | h <;> omega

/-- The `(L-1)`-mer multigraph of `S`, spelled on the truth: every node is
spelled at most twice. -/
def NodeMultiplicity (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  ∀ v : Fin (L - 1) → α, nodeCount (L := L) hG S v ≤ 2

/-- Actual `P2` plus primitivity gives `NodeMultiplicity`. -/
theorem P2.imp_NodeMultiplicity (hG : 0 < G) (hL : 2 ≤ L) (hLG : L ≤ G) (S : Fin G → α)
    (hprim : IsPrimitive hG S) (hP2 : P2 hG L S) : NodeMultiplicity hG L S :=
  fun v => P2.imp_nodeCount_le_two hG hL hLG S hprim hP2 v

/-! ## 2. The alternative traversal has the truth's multigraph -/

/-- **A matched traversal runs on the truth's `(L-1)`-mer multigraph.**  If
`τ` matches the read types of `S` and `E`, then the node of `E` at `j` is the
node of `S` at `τ j`.  This is the genome-side form of "the two words are two
Eulerian circuits of the same multigraph", and it is what transfers the truth's
node multiplicity bound (clause 1 of `P2`, via `P2.imp_NodeMultiplicity`) to the
competitor. -/
theorem nodeWindow_E_of_matching (hG : 0 < G) {hL : 0 < L} (S E : Fin G → α)
    (τ : Fin G → Fin G) (hτ : Matching hG L S E τ) (j : Fin G) :
    nodeWindow (L := L) hG E j = nodeWindow (L := L) hG S (τ j) := by
  rw [(winPrefix_window' hG E j).symm, ← hτ.2 j, (winPrefix_window' hG S (τ j)).symm]

/-- **The two words have the same node multiplicities.** -/
theorem nodeCount_E_of_matching (hG : 0 < G) {hL : 0 < L} (S E : Fin G → α)
    (τ : Fin G → Fin G) (hτ : Matching hG L S E τ) (v : Fin (L - 1) → α) :
    nodeCount (L := L) hG E v = nodeCount (L := L) hG S v := by
  set σ : Fin G ≃ Fin G := Equiv.ofBijective τ hτ.1 with hσdef
  have hτj : ∀ j : Fin G, σ j = τ j := fun _ => rfl
  have h2 : (Finset.univ.filter (fun j : Fin G => nodeWindow (L := L) hG E j = v))
      = (Finset.univ.filter (fun r : Fin G => nodeWindow (L := L) hG S r = v)).image
        σ.symm := by
    refine Finset.ext fun j => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.mem_image]
    constructor
    · intro hj
      have hn := nodeWindow_E_of_matching (hL := hL) hG S E τ hτ j
      have hn' : nodeWindow (L := L) hG S (σ j) = nodeWindow (L := L) hG E j := by
        rw [hτj]
        exact hn.symm
      exact ⟨σ j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn'.trans hj⟩,
        Equiv.left_inv σ j⟩
    · rintro ⟨s, hs, hjs⟩
      subst hjs
      have hmem : nodeWindow (L := L) hG S s = v := (Finset.mem_filter.mp hs).2
      have hn := nodeWindow_E_of_matching (hL := hL) hG S E τ hτ (σ.symm s)
      have hlt : τ (σ.symm s) = s := by
        rw [← hτj]
        exact Equiv.apply_symm_apply σ s
      exact hn.trans (congrArg (nodeWindow (L := L) hG S) hlt) |>.trans hmem
  unfold nodeCount
  rw [h2, Finset.card_image_of_injective _
    (fun (a b : Fin G) (hab : σ.symm a = σ.symm b) => by
      simpa only [Equiv.apply_symm_apply] using congrArg (fun x : Fin G => σ x) hab)]

/-! ## 3. A switch of the matched traversal yields a long maximal repeat -/

/-- Two distinct starts carrying a common `ℓ`-window, on a **primitive** circular
word, extend to a `Genome.IsRepeat` of length `≥ ℓ` — this is (R1) at `n = 2` as
proved in `AssemblyP1.P2RepeatResidual.maxPair_isRepeat`.  The repeat sits at the
*shifted* starts; that is forced, and the un-shifted version is refuted there. -/
theorem longRepeat_of_agree_pair (hG : 0 < G) (hL : 2 ≤ L) (hLG : L ≤ G)
    (S : Fin G → α) (hprim : IsPrimitive hG S) {a b : Fin G} (hab : a ≠ b)
    (hag : ∀ d : Fin (L - 1), cyc hG S (a.val + d.val) = cyc hG S (b.val + d.val)) :
    LongRepeat hG L S := by
  obtain ⟨hR, hle⟩ := maxPair_isRepeat hG S hprim hab (ℓ := L - 1) (by omega)
    (by omega) hag
  exact ⟨⟨maxPairLen hG S a b, hR.2.1⟩, maxPairStart hG S a b, maxPairStart hG S b a,
    hle, hR⟩

/-- A **switch** at `j` of a `NodeStep` map `τ` is a start `j` where the map does
*not* respect the successor, `τ (·+1) ≠ (τ ·)+1` there.  At such a start the
`NodeStep` condition forces both `τ j + 1` and `τ (j + 1)` onto the same node,
and injectivity of `τ` forces them to be two *distinct* starts, so the node is
spelled at least twice. -/
theorem nodeCount_ge_two_of_switch (hG : 0 < G) (S : Fin G → α) (τ : Fin G → Fin G)
    (htau : Function.Injective τ) (hstep : NodeStep hG L S τ) (j : Fin G)
    (hj : nextStart hG (τ j) ≠ τ (nextStart hG j)) :
    2 ≤ nodeCount (L := L) hG S (nodeWindow (L := L) hG S (nextStart hG (τ j))) := by
  refine nodeCount_ge_two hG S (by intro hcon; exact hj hcon) (hstep j)

/-- **Every switch of the matched traversal produces a long maximal repeat on
the truth.**

The two starts a switch lands on are distinct and carry the same
`(L-1)`-window, so they extend to a `LongRepeat` by
`longRepeat_of_agree_pair`.  Primitivity of the truth is the only extra input,
and it is exactly what makes the extension a *maximal* repeat of length `< G`. -/
theorem switch_longRepeat (hG : 0 < G) (hL : 2 ≤ L) (hLG : L ≤ G) (S : Fin G → α)
    (hprim : IsPrimitive hG S) (τ : Fin G → Fin G) (htau : Function.Injective τ)
    (hstep : NodeStep hG L S τ) (j : Fin G)
    (hj : nextStart hG (τ j) ≠ τ (nextStart hG j)) : LongRepeat hG L S := by
  have hn : nodeWindow (L := L) hG S (nextStart hG (τ j))
      = nodeWindow (L := L) hG S (τ (nextStart hG j)) := hstep j
  exact longRepeat_of_agree_pair hG hL hLG S hprim (by intro hcon; exact hj hcon)
    (fun d => congrFun hn d)

/-- The successor map on the circle of starts is injective. -/
theorem nextStart_injective (hG : 0 < G) {a b : Fin G}
    (h : nextStart hG a = nextStart hG b) : a = b := by
  have ha : a.val < G := a.isLt
  have hb : b.val < G := b.isLt
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [nextStart, Fin.val_mk] at hv
  have ha1 : a.val + 1 ≤ G := by omega
  have hb1 : b.val + 1 ≤ G := by omega
  by_cases hla : a.val + 1 < G
  · by_cases hlb : b.val + 1 < G
    · rw [Nat.mod_eq_of_lt hla, Nat.mod_eq_of_lt hlb] at hv
      omega
    · have hbe : b.val + 1 = G := by omega
      rw [Nat.mod_eq_of_lt hla, hbe, Nat.mod_self G] at hv
      omega
  · have hae : a.val + 1 = G := by omega
    by_cases hlb : b.val + 1 < G
    · rw [hae, Nat.mod_self G, Nat.mod_eq_of_lt hlb] at hv
      omega
    · have hbe : b.val + 1 = G := by omega
      omega

/-! ## 4. The two-switch lemma: switched nodes form a double cover -/

/-- **Two switches at the same node are the same switch, or are paired.**

Let `τ` be an injective `NodeStep` map whose nodes all have multiplicity `≤ 2`,
and let `j`, `j'` be two switches landing on the same node `v`.  Then either
`j = j'`, or the two switches are the two "directions" of the same node:
`τ (j + 1) = τ j' + 1`.

This is the structural input of the chord argument: the switch sites are
*paired* over each switched node, so a switched node accounts for at most two
switches, and the two of them are mutually determined.  The remaining step — that
the two paired switches produce two **interleaved** maximal repeats, or a long
triple repeat — is not formalized. -/
theorem switch_doubleNode_inj_or_pair (hG : 0 < G) (S : Fin G → α) (τ : Fin G → Fin G)
    (htau : Function.Injective τ) (hstep : NodeStep hG L S τ)
    (hn : NodeMultiplicity hG L S) {j j' : Fin G}
    (hj : nextStart hG (τ j) ≠ τ (nextStart hG j))
    (hj' : nextStart hG (τ j') ≠ τ (nextStart hG j'))
    (hv : nodeWindow (L := L) hG S (nextStart hG (τ j))
      = nodeWindow (L := L) hG S (nextStart hG (τ j'))) :
    j = j' ∨ τ (nextStart hG j) = nextStart hG (τ j') := by
  set v : Fin (L - 1) → α := nodeWindow (L := L) hG S (nextStart hG (τ j)) with hvdef
  have hv' : nodeWindow (L := L) hG S (nextStart hG (τ j')) = v := by
    rw [hv]
  have hv2 : nodeWindow (L := L) hG S (τ (nextStart hG j)) = v := by
    rw [hvdef]
    exact (hstep j).symm
  have hv3 : nodeWindow (L := L) hG S (τ (nextStart hG j')) = v := by
    rw [← hv']
    exact (hstep j').symm
  by_cases hcase : nextStart hG (τ j) = nextStart hG (τ j')
  · left
    apply htau
    exact nextStart_injective hG hcase
  · right
    by_contra hcon
    -- the fibre of `v` holds at most two starts, and it would have to hold the
    -- three pairwise distinct starts `τ j + 1`, `τ j' + 1` and `τ (j + 1)'`
    have hFmem1 : nextStart hG (τ j)
        ∈ Finset.univ.filter (fun r : Fin G => nodeWindow (L := L) hG S r = v) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvdef⟩
    have hFmem3 : nextStart hG (τ j')
        ∈ Finset.univ.filter (fun r : Fin G => nodeWindow (L := L) hG S r = v) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv'⟩
    have hFmem2 : τ (nextStart hG j)
        ∈ Finset.univ.filter (fun r : Fin G => nodeWindow (L := L) hG S r = v) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv2⟩
    have h2 : nextStart hG (τ j') ≠ τ (nextStart hG j') := hj'
    have hcase' : nextStart hG (τ j') ≠ nextStart hG (τ j) := fun h => hcase h.symm
    have hle : (Finset.univ.filter (fun r : Fin G => nodeWindow (L := L) hG S r = v)).card
        ≤ 2 := by
      have hcard := hn v
      unfold nodeCount at hcard
      exact hcard
    have hsub : insert (τ (nextStart hG j)) (insert (nextStart hG (τ j'))
        (insert (nextStart hG (τ j)) (∅ : Finset (Fin G))))
        ⊆ Finset.univ.filter (fun r : Fin G => nodeWindow (L := L) hG S r = v) := by
      intro r hr
      rw [Finset.mem_insert] at hr
      rcases hr with hr | hr
      · rw [hr]
        exact hFmem2
      · rw [Finset.mem_insert] at hr
        rcases hr with hr | hr
        · rw [hr]
          exact hFmem3
        · rw [Finset.mem_insert] at hr
          rcases hr with hr | hr
          · rw [hr]
            exact hFmem1
          · simp at hr
    set T : Finset (Fin G) := insert (τ (nextStart hG j))
      (insert (nextStart hG (τ j')) (insert (nextStart hG (τ j))
        (∅ : Finset (Fin G)))) with hTdef
    have hTle : T.card ≤ 2 := by
      refine le_trans (Finset.card_le_card ?_) hle
      rwa [hTdef]
    have hn1 : nextStart hG (τ j)
        ∉ insert (nextStart hG (τ j')) (∅ : Finset (Fin G)) := by
      simp [hcase]
    have hn2 : nextStart hG (τ j')
        ∉ insert (nextStart hG (τ j)) (∅ : Finset (Fin G)) := by
      simp [hcase']
    have hn3 : τ (nextStart hG j)
        ∉ insert (nextStart hG (τ j')) (insert (nextStart hG (τ j))
          (∅ : Finset (Fin G))) := by
      intro hmem
      rcases Finset.mem_insert.mp hmem with h1 | h1
      · exact hcon h1
      · rcases Finset.mem_insert.mp h1 with h2' | h2'
        · exact hj h2'.symm
        · exact absurd h2' (by simp)
    have hTcard : T.card = 3 := by
      have hA : Finset.card (insert (nextStart hG (τ j)) (∅ : Finset (Fin G))) = 1 := by
        rw [Finset.card_insert_of_notMem (by simp), Finset.card_empty]
      have hB : Finset.card (insert (nextStart hG (τ j'))
          (insert (nextStart hG (τ j)) (∅ : Finset (Fin G)))) = 2 := by
        rw [Finset.card_insert_of_notMem hn2, hA]
      have hC : Finset.card (insert (τ (nextStart hG j))
          (insert (nextStart hG (τ j')) (insert (nextStart hG (τ j))
            (∅ : Finset (Fin G))))) = 3 := by
        rw [Finset.card_insert_of_notMem hn3, hB]
      rwa [hTdef]
    rw [hTcard] at hTle
    omega

/-! ## 5. The switch-free half: a `NodeStep` map with no switch is a rotation -/

/-- **A `NodeStep` map with no switch commutes with the successor, hence is a
rotation of the starts.**  This is the switch-free half of (R3): if the matched
traversal respects the successor everywhere, it is the truth's own traversal,
started somewhere else, and it spells a rotation of the genome. -/
theorem exists_rotAdd_of_noSwitch (hG : 0 < G) (S : Fin G → α) (τ : Fin G → Fin G)
    (_hstep : NodeStep hG L S τ)
    (hnoswitch : ∀ j : Fin G, nextStart hG (τ j) = τ (nextStart hG j)) :
    ∃ c : Fin G, ∀ j : Fin G, τ j = rotAdd hG c.val j :=
  exists_rotAdd_of_comm_nextStart (hG := hG) (fun _ => (hnoswitch _).symm)

/-- **…and a `NodeStep` map with no switch spells a rotation of the genome.**
So the residual of `thm:BBT` is confined to the switched case. -/
theorem rotEquiv_of_noSwitch (hG : 0 < G) (S : Fin G → α) (τ : Fin G → Fin G)
    (_hstep : NodeStep hG L S τ)
    (hnoswitch : ∀ j : Fin G, nextStart hG (τ j) = τ (nextStart hG j)) :
    ∃ c : Fin G, RotEquiv hG (fun j => S (τ j)) S := by
  obtain ⟨c, hc⟩ := exists_rotAdd_of_comm_nextStart (hG := hG) (fun _ => (hnoswitch _).symm)
  have heq : (fun j : Fin G => S (τ j)) = fun j => S (rotAdd hG c.val j) := by
    funext j
    exact congrArg S (hc j)
  exact ⟨c, heq ▸ rotEquiv_rotAdd hG S c⟩

/-! ## 6. The exact residual: spectrum ambiguity forces a long obstruction -/

/-- **The exact remaining combinatorial statement of #89**, in the
spectrum-level shape that the brute-force probe of
`docs/issue89-spectrum-uniqueness.md` §4 tested and that the clauses of `P2`
are stated against:

> a primitive circular genome `S` of length `G`, a competitor `E` of the same
> length with the **same complete `L`-spectrum** and **not** a cyclic shift of
> `S`, forces a long obstruction on `S`.

It mentions `specCount`, `RotEquiv` and the truth's own repeats; it mentions no
multigraph, no `NodeStep`, no `EulerCircuit`, no `UniqueEulerCircuit`, no
`BBTUniqueAt` and no BBT/Ukkonen premise. -/
def SpectrumLongObstruction (hG : 0 < G) (L : ℕ) (S E : Fin G → α) : Prop :=
  IsPrimitive hG S →
  specCount (L := L) hG S = specCount (L := L) hG E →
  ¬ RotEquiv hG E S →
  LongObstruction hG L S

/-- **The residual lemma, stated exactly.**  It is *not* proved in this module;
see the header.  The conclusion is the one the (R3) argument needs, and it is
identical to `LongObstruction` on the truth alone. -/
theorem spectrum_ambiguity_gives_longObstruction (hG : 0 < G) (L : ℕ) (S E : Fin G → α)
    (hprim : IsPrimitive hG S) (hSpec : specCount (L := L) hG S = specCount (L := L) hG E)
    (hnot : ¬ RotEquiv hG E S) (hRes : SpectrumLongObstruction hG L S E) :
    LongObstruction hG L S :=
  hRes hprim hSpec hnot

/-- **The `P2` complete-spectrum uniqueness theorem, modulo the residual.**

Equal complete `L`-spectrum between a primitive `P2` truth and a candidate of
the same length forces the candidate to be a cyclic shift.  This is the shape of
`AssemblyP1.PopulationUniqueness`'s `hBBTS` premise, so it plugs straight into
`population_tie_implies_rotation` / `population_unique_ML_up_to_rotation` with
`AdmP2 := fun {K} S => P2 hG K S`: taking `E` to be the candidate, `hprim` to be
`hPrimS`, `hP2` to be `hP2S` and `hSpec` to be the spectrum equality delivered by
`hGibbs`, the conclusion is exactly that theorem's `RotEquiv hG D S`. -/
theorem p2_spectrum_ambiguity (hG : 0 < G) (hL : 2 ≤ L) (hLG : L ≤ G)
    (S E : Fin G → α) (hprim : IsPrimitive hG S) (hP2 : P2 hG L S)
    (hRes : SpectrumLongObstruction hG L S E)
    (hSpec : specCount (L := L) hG S = specCount (L := L) hG E) :
    RotEquiv hG E S := by
  by_contra hnot
  exact (P2.imp_noLongObstruction hG hL S hP2) (hRes hprim hSpec hnot)

end AssemblyP1.P2LongObstruction
