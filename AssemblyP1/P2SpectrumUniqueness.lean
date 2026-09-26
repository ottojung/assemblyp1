import Mathlib
import AssemblyP1.PopulationReduction
import AssemblyP1.OrientedFinalRigidity
import AssemblyP1.SourceFaithfulIs

/-!
# P2 / Ukkonen complete-spectrum uniqueness: the proved part, and the exact
  residual (issue #89)

This module works on the **current `main`** state of the library, where
`AssemblyP1.PopulationUniqueness` still takes the whole of the
Bresler--Bresler--Tse uniqueness implication as a caller-supplied premise
(`hBBTS`, `hBBTD`).  This file attacks exactly that premise.

## Proved here

1. **The actual conditions.** `mkGenome`, `P2` and `Ukkonen` are transcribed
   from `paper/sections/05-population.tex` `def:P1P2` and `thm:BBT`, on top of
   the source-faithful predicates of `AssemblyP1.SourceFaithfulIs`
   (`IsRepeat`, `IsTripleRepeat`, `Interleaved`).  `P2.imp_Ukkonen`
   kernel-checks the paper's alignment sentence "setting `K = L - 1` aligns
   the theorem's condition exactly with P2".

2. **The word / Eulerian-circuit bridge.**  `thm:BBT` is phrased in terms of
   the `K`-mer graph having a *unique Eulerian cycle*.  `EulerCircuit` and
   `TrailEquiv` make that concrete (cyclic closed trails of length-`L` words
   with prescribed edge multiplicities), `window_isEulerCircuit` proves that a
   circular word gives such a circuit, and `rotEquiv_of_trailEquiv` proves that
   a shift of trails gives rotation-equivalent genomes.  So the paper's
   statement is reduced, in the kernel, to a statement about a multigraph.

3. **`p1_spectrum_unique_up_to_rotation`: a premise-free complete-spectrum
   uniqueness theorem.**  For circular genomes of the same length, if the
   truth has no repeated length-`(L-1)` word (P1 of `def:P1P2`) and the
   complete oriented length-`L` spectra are equal, then the two words are
   cyclic shifts.  This is the "no repeat of length `≥ K`" case of the
   Bresler uniqueness theorem at `K = L - 1`, and **no BBT, Ukkonen or
   uniqueness premise occurs in its statement**.

4. **The residual, stated on the multigraph.**  `UniqueEulerCircuit` says the
   multigraph of a multiplicity function `c` has a single Eulerian circuit up
   to cyclic shift.  It mentions neither `specCount`, nor `RotEquiv`, nor any
   repeat predicate, so it is not a restatement of the genome statement.
   `p2_spectrum_unique_up_to_rotation` proves, in the kernel, that
   `UniqueEulerCircuit` yields the conclusion of `thm:BBT` at `K = L - 1` for
   a primitive P2 truth.

## Not proved here

`UniqueEulerCircuit` for the P2 hypothesis.  Its three missing ingredients are
stated exactly, with the reduction that would use them, in
`docs/issue89-spectrum-uniqueness.md`; briefly:

* the simultaneous maximal-extension lemma (two or three agreeing starts on a
  primitive circle extend to a maximal repeat / maximal triple repeat), which
  is what turns clause 1 of P2 into "every `(L-1)`-mer occurs at most twice"
  and clause 2 into the non-crossing condition `NodeCrossing`;
* the multigraph combinatorics: with all node degrees `≤ 2` and the double
  nodes' occurrence pairs pairwise non-interleaved, the Eulerian circuit is
  unique up to shift.

No `axiom`, `sorry` or `admit` occurs in this file.  Nothing in the library was
weakened to make a theorem provable, and the P1 theorem is a proved sub-case
rather than a replacement of the P2 statement.
-/

set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace AssemblyP1.P2SpectrumUniqueness

open AssemblyP1.SourceFaithfulIs
open AssemblyP1.OrientedRigidity
open AssemblyP1.PopulationReduction

variable {α : Type} [DecidableEq α] {G L : ℕ}

/-! ## 1. The actual conditions of `def:P1P2` and `thm:BBT` -/

/-- The `Fin G → α` word read as a source-faithful circular genome, so that
`window`, `Preceding`, `Following`, `IsRepeat`, `IsTripleRepeat` and
`Interleaved` are the issue-#85/#90 predicates on the same symbols. -/
def mkGenome (hG : 0 < G) (S : Fin G → α) : SourceFaithfulIs.Genome α :=
  ⟨G, hG, S⟩

/-- **P2 of `def:P1P2`** at read length `L`: no maximal triple repeat of
length `≥ L - 1`, and every interleaved maximal repeat pair has a constituent
of length `≤ L - 2`. -/
def P2 (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  (∀ e a b c : Fin G, (mkGenome hG S).IsTripleRepeat e a b c → e.val < L - 1) ∧
    (∀ (e₁ e₂ : Fin G) (a b c d : Fin G), (mkGenome hG S).IsRepeat e₁ a b →
      (mkGenome hG S).IsRepeat e₂ c d →
      Interleaved (mkGenome hG S) a b c d →
      e₁.val ≤ L - 2 ∨ e₂.val ≤ L - 2)

/-- **Ukkonen's condition at `K = L - 1`**, the hypothesis of `thm:BBT` as
stated in `paper/sections/05-population.tex`. -/
def Ukkonen (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  (∀ e a b c : Fin G, (mkGenome hG S).IsTripleRepeat e a b c → e.val < L - 1) ∧
    (∀ (e₁ e₂ : Fin G) (a b c d : Fin G), (mkGenome hG S).IsRepeat e₁ a b →
      (mkGenome hG S).IsRepeat e₂ c d →
      Interleaved (mkGenome hG S) a b c d →
      e₁.val < L - 1 ∨ e₂.val < L - 1)

/-- **The paper's alignment claim, kernel-checked.** -/
theorem P2.imp_Ukkonen {hG : 0 < G} {L : ℕ} {S : Fin G → α} (hL : 2 ≤ L)
    (h : P2 hG L S) :
    Ukkonen hG L S := by
  refine ⟨h.1, ?_⟩
  intro e₁ e₂ a b c d hR₁ hR₂ hI
  rcases h.2 e₁ e₂ a b c d hR₁ hR₂ hI with h1 | h2
  · refine Or.inl (lt_of_le_of_lt h1 (by omega))
  · refine Or.inr (lt_of_le_of_lt h2 (by omega))

/-! ## 2. The word / Eulerian-circuit bridge

`thm:BBT` speaks about the `K`-mer graph having a *unique Eulerian cycle*.
The objects below make that phrase a concrete statement, and prove in the
kernel that it is equivalent to the statement about genomes that the rest of
the library wants.  The `(L-1)`-de Bruijn graph is
`head = winSuffix`/`tail = winPrefix` on length-`L` words, i.e. exactly the
transition structure `AssemblyP1.OrientedRigidity` uses, and the edge
multiplicity of a length-`L` word is its `L`-spectrum count. -/

/-- **A cyclic closed trail in the `(L-1)`-de Bruijn graph with prescribed
edge multiplicities**: a `G`-indexed sequence of length-`L` words whose
consecutive windows overlap in `L - 1` symbols (cyclically, last to first),
using each length-`L` word `w` exactly `c w` times.

This is the object `thm:BBT` is about: a closed trail in the `K`-mer graph
built from the complete `(K+1)`-spectrum, the multiplicity of the edge `w`
being the count of `w` in the `(K+1)`-spectrum. -/
def EulerCircuit (hG : 0 < G) (c : (Fin L → α) → ℕ)
    (T : Fin G → Fin L → α) : Prop :=
  (∀ j : Fin G, winSuffix (T j) = winPrefix (T ⟨(j.val + 1) % G, Nat.mod_lt _ hG⟩))
    ∧ (∀ w : Fin L → α,
      (Finset.univ.filter (fun j : Fin G => T j = w)).card = c w)

/-- **Cyclic shift of a trail**: `T` is `U` read from a different start. -/
def TrailEquiv (hG : 0 < G) (T U : Fin G → Fin L → α) : Prop :=
  ∃ k : ℕ, ∀ j : Fin G, T ⟨(j.val + k) % G, Nat.mod_lt _ hG⟩ = U j

/-- Cyclic adjacency of two consecutive window starts. -/
theorem winSuffix_window_next (hG : 0 < G) (S : Fin G → α) (r : Fin G) :
    winSuffix (window (L := L) hG S r)
      = winPrefix (window (L := L) hG S ⟨(r.val + 1) % G, Nat.mod_lt _ hG⟩) := by
  funext d
  show cyc hG S (r.val + (d.val + 1)) = cyc hG S (((r.val + 1) % G) + d.val)
  unfold cyc
  apply congrArg S
  apply Fin.ext
  show (r.val + (d.val + 1)) % G = (((r.val + 1) % G) + d.val) % G
  rw [show r.val + (d.val + 1) = (r.val + 1) + d.val from by omega]
  exact (Nat.mod_add_mod _ _ _).symm

/-- **The windows of a circular word form an Eulerian circuit of its
`L`-spectrum.**  This is the whole of the "genome ⟹ Eulerian cycle" direction,
kernel-checked. -/
theorem window_isEulerCircuit (hG : 0 < G) (S : Fin G → α) :
    EulerCircuit hG (specCount (L := L) hG S) (window (L := L) hG S) :=
  ⟨fun j => winSuffix_window_next hG S j, fun _ => rfl⟩

/-- The word trail of `S` is a shift of any circuit with the same
multiplicities that `E`'s own window trail is: this is the only use made of
`EulerCircuit`. -/
theorem EulerCircuit_spell {hG : 0 < G} {hL : 0 < L} (S E : Fin G → α)
    {c : (Fin L → α) → ℕ} {T : Fin G → Fin L → α}
    (_hT : EulerCircuit hG c T)
    (_hc : c = specCount (L := L) hG S)
    (hE : ∀ j : Fin G, window (L := L) hG E j = T j)
    (hTE : TrailEquiv hG T (window (L := L) hG S)) :
    RotEquiv hG E S := by
  obtain ⟨k, hk⟩ := hTE
  refine ⟨k, fun i => ?_⟩
  have hz1 := congrFun (hE ⟨(i.val + k) % G, Nat.mod_lt _ hG⟩).symm ⟨0, hL⟩
  have hz2 := congrFun (hk i) ⟨0, hL⟩
  simp only [window, cyc] at hz1 hz2
  have hAm : ((i.val + k) % G + 0) % G = (i.val + k) % G := by
    rw [Nat.add_zero, Nat.mod_mod]
  have hA : E ⟨(i.val + k) % G, Nat.mod_lt _ hG⟩
      = E ⟨((i.val + k) % G + 0) % G, Nat.mod_lt _ hG⟩ := congrArg E (Fin.ext hAm.symm)
  have hBm : (i.val + 0) % G = i.val := by
    rw [Nat.add_zero, Nat.mod_eq_of_lt i.isLt]
  have hB : S ⟨(i.val + 0) % G, Nat.mod_lt _ hG⟩ = S i := congrArg S (Fin.ext hBm)
  calc E ⟨(i.val + k) % G, Nat.mod_lt _ hG⟩
      = E ⟨((i.val + k) % G + 0) % G, Nat.mod_lt _ hG⟩ := hA
    _ = S ⟨(i.val + 0) % G, Nat.mod_lt _ hG⟩ := hz1.symm.trans hz2
    _ = S i := hB

/-- Rotation of circular words is rotation of their window trails. -/
theorem trailEquiv_of_rot (hG : 0 < G) {S E : Fin G → α}
    (h : RotEquiv hG E S) :
    TrailEquiv hG (window (L := L) hG E) (window (L := L) hG S) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, fun j => ?_⟩
  funext d
  have hjd : (j.val + d.val) % G < G := Nat.mod_lt _ hG
  have h1 := hk ⟨(j.val + d.val) % G, hjd⟩
  have harg : (((j.val + k) % G) + d.val) % G = (((j.val + d.val) % G) + k) % G := by
    rw [Nat.mod_add_mod, Nat.mod_add_mod]
    congr 1
    omega
  show cyc hG E (((j.val + k) % G) + d.val) = cyc hG S (j.val + d.val)
  unfold cyc
  have hL : (⟨(((j.val + k) % G) + d.val) % G, Nat.mod_lt _ hG⟩ : Fin G)
      = ⟨(((j.val + d.val) % G) + k) % G, Nat.mod_lt _ hG⟩ := Fin.ext harg
  rw [hL]
  exact h1

/-! ## 3. `P1`: the complete `L`-spectrum determines the genome up to rotation

`P1` (`def:P1P2`): no length-`(L-1)` word occurs more than once.  Under `P1`
every de Bruijn node of the `(L-1)`-graph occurs at most once, hence has
out-degree one, the Eulerian cycle is forced, and the complete `L`-spectrum
determines the circular word up to cyclic rotation.  **This theorem carries no
BBT and no Ukkonen premise**: it is proved here, from `P1` and spectrum
equality alone. -/

/-- `winPrefix (window hG S r)` is the de Bruijn node (the `(L-1)`-window) at
`r`. -/
theorem winPrefix_window' (hG : 0 < G) (S : Fin G → α) (r : Fin G) :
    winPrefix (window (L := L) hG S r) = nodeWindow (L := L) hG S r := by
  funext d
  rfl

/-- **P1 of `def:P1P2`**: no length-`(L-1)` word occurs more than once. -/
def P1 (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  ∀ v : Fin (L - 1) → α, nodeCount (L := L) hG S v ≤ 1

/-- `P1` says the node map of `S` is injective: no two starts carry the same
`(L-1)`-window. -/
theorem P1.node_injective (hG : 0 < G) (S : Fin G → α) (hP1 : P1 hG L S)
    {r s : Fin G} (h : nodeWindow (L := L) hG S r = nodeWindow (L := L) hG S s) :
    r = s := by
  by_contra hne
  have hsub : (insert r ({s} : Finset (Fin G))) ⊆ Finset.univ.filter
      (fun j : Fin G => nodeWindow (L := L) hG S j = nodeWindow (L := L) hG S r) := by
    intro j hj
    rcases Finset.mem_insert.mp hj with hj | hj
    · rw [hj]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    · have hjs : j = s := Finset.mem_singleton.mp hj
      rw [hjs, h]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hcard := Finset.card_le_card hsub
  have hc : (insert r ({s} : Finset (Fin G))).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton, Nat.add_comm]
  have h3 := hP1 (nodeWindow (L := L) hG S r)
  unfold nodeCount at h3
  omega

/-- Successor start on the circle. -/
def nextStart (hG : 0 < G) (r : Fin G) : Fin G :=
  ⟨(r.val + 1) % G, Nat.mod_lt _ hG⟩

/-- Iterating `nextStart` adds `t` modulo `G`. -/
theorem nextIter_val (hG : 0 < G) (r : Fin G) (t : ℕ) :
    ((nextStart hG)^[t] r).val = (r.val + t) % G := by
  induction t with
  | zero =>
      simp [Function.iterate_zero, id_eq, Nat.mod_eq_of_lt r.isLt]
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      show (((nextStart hG)^[n] r).val + 1) % G = (r.val + (n + 1)) % G
      rw [ih, Nat.mod_add_mod, show r.val + n + 1 = r.val + (n + 1) from by omega]

/-- `winSuffix (window hG S r) = winPrefix (window hG S (nextStart hG r))`. -/
theorem winSuffix_window_next' (hG : 0 < G) (S : Fin G → α) (r : Fin G) :
    winSuffix (window (L := L) hG S r)
      = winPrefix (window (L := L) hG S (nextStart hG r)) := by
  funext d
  show cyc hG S (r.val + (d.val + 1)) = cyc hG S (((r.val + 1) % G) + d.val)
  unfold cyc
  apply congrArg S
  apply Fin.ext
  show (r.val + (d.val + 1)) % G = (((r.val + 1) % G) + d.val) % G
  rw [show r.val + (d.val + 1) = (r.val + 1) + d.val from by omega]
  exact (Nat.mod_add_mod _ _ _).symm

/-- The length-`L` windows at two consecutive starts agree on their first
`L - 1` coordinates: the window at the successor start is the window at `r`
shifted by one. -/
theorem window_next' (hG : 0 < G) (S : Fin G → α) (r : Fin G) (d : Fin (L - 1)) :
    window (L := L) hG S (nextStart hG r) ⟨d.val, by have := d.isLt; omega⟩
      = window (L := L) hG S r ⟨d.val + 1, by have := d.isLt; omega⟩ := by
  show cyc hG S (((r.val + 1) % G) + d.val) = cyc hG S (r.val + (d.val + 1))
  unfold cyc
  apply congrArg S
  apply Fin.ext
  show (((r.val + 1) % G) + d.val) % G = (r.val + (d.val + 1)) % G
  have h1 : r.val + (d.val + 1) = (r.val + 1) + d.val := by omega
  have h2 : (((r.val + 1) % G) + d.val) % G = ((r.val + 1) + d.val) % G :=
    Nat.mod_add_mod _ _ _
  rw [h1, h2]

/-- The node at the successor start is the suffix of the window at `r`. -/
theorem nodeWindow_next' (hG : 0 < G) (S : Fin G → α) (r : Fin G) :
    nodeWindow (L := L) hG S (nextStart hG r) = winSuffix (window (L := L) hG S r) := by
  funext d
  show cyc hG S (((r.val + 1) % G) + d.val) = cyc hG S (r.val + (d.val + 1))
  unfold cyc
  apply congrArg S
  apply Fin.ext
  show (((r.val + 1) % G) + d.val) % G = (r.val + (d.val + 1)) % G
  have h1 : r.val + (d.val + 1) = (r.val + 1) + d.val := by omega
  have h2 : (((r.val + 1) % G) + d.val) % G = ((r.val + 1) + d.val) % G :=
    Nat.mod_add_mod _ _ _
  rw [h1, h2]

/-- Rotation of window trails is rotation of the words. -/
theorem rotEquiv_of_trailEquiv (hG : 0 < G) (hL : 0 < L) {S E : Fin G → α}
    (h : TrailEquiv hG (window (L := L) hG E) (window (L := L) hG S)) :
    RotEquiv hG E S := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, fun i => ?_⟩
  have hz1 := congrFun (hk i) ⟨0, hL⟩
  simp only [window, cyc] at hz1
  have hAm : ((i.val + k) % G + 0) % G = (i.val + k) % G := by
    rw [Nat.add_zero, Nat.mod_mod]
  have hBm : (i.val + 0) % G = i.val := by
    rw [Nat.add_zero, Nat.mod_eq_of_lt i.isLt]
  calc E ⟨(i.val + k) % G, Nat.mod_lt _ hG⟩
      = E ⟨((i.val + k) % G + 0) % G, Nat.mod_lt _ hG⟩ := congrArg E (Fin.ext hAm.symm)
    _ = S ⟨(i.val + 0) % G, Nat.mod_lt _ hG⟩ := hz1
    _ = S i := congrArg S (Fin.ext hBm)

/-- **The `P1` reconstruction theorem: the complete `L`-spectrum of a `P1`
genome determines it up to cyclic rotation, with no external premise.**

Every node of the `(L-1)`-de Bruijn graph of `S` occurs at most once, so the
node map of `S` is injective; hence any length-`L` window of `E`, which occurs
in `E` and therefore in `S`, sits at a unique start of `S`; and the start map
is forced to commute with the successor map, hence is a cyclic shift, so `E`
is a cyclic shift of `S`.  This is the "no repeat of length `≥ K`" case of
the Bresler--Bresler--Tse uniqueness input, at `K = L - 1`, proved here. -/
theorem p1_spectrum_unique_up_to_rotation (hG : 0 < G) (hL : 0 < L)
    (S E : Fin G → α) (hP1 : P1 hG L S)
    (hSpec : specCount (L := L) hG S = specCount (L := L) hG E) :
    RotEquiv hG E S := by
  letI : NeZero G := ⟨Nat.pos_iff_ne_zero.mp hG⟩
  have hpos : ∀ (W : Fin G → α) (j : Fin G),
      0 < specCount (L := L) hG W (window (L := L) hG W j) := by
    intro W j
    have hne : (Finset.univ.filter
        (fun r : Fin G => window (L := L) hG W r = window (L := L) hG W j)).Nonempty :=
      ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    have hc : 0 < (Finset.univ.filter
        (fun r : Fin G => window (L := L) hG W r = window (L := L) hG W j)).card :=
      Finset.card_pos.mpr hne
    simpa [specCount] using hc
  -- any length-`L` word occurring in `E` occurs in `S`
  have hocc : ∀ w : Fin L → α, 0 < specCount (L := L) hG E w → ∃ r : Fin G,
      window (L := L) hG S r = w := by
    intro w hw
    have hposS : 0 < specCount (L := L) hG S w := by rw [hSpec]; exact hw
    have hmem : w ∈ support (L := L) hG S := (mem_support_iff hG S w).mpr hposS
    obtain ⟨r, -, hr⟩ := Finset.mem_image.mp hmem
    exact ⟨r, hr⟩
  -- the start of `S` realizing the window of `E` at a given start is unique
  have hexu : ∀ j : Fin G, ∃! j' : Fin G,
      window (L := L) hG E j = window (L := L) hG S j' := by
    intro j
    obtain ⟨i, hi⟩ := hocc _ (hpos E j)
    refine ⟨i, hi.symm, fun i' hi' => ?_⟩
    have hnv : nodeWindow (L := L) hG S i = nodeWindow (L := L) hG S i' := by
      rw [← winPrefix_window' hG S i, ← winPrefix_window' hG S i', ← hi.symm, hi']
    exact P1.node_injective (hG := hG) (S := S) hP1 hnv.symm
  set φ : Fin G → Fin G := fun j => Classical.choose (hexu j) with hφdef
  have hφspec : ∀ j : Fin G, window (L := L) hG E j = window (L := L) hG S (φ j) :=
    fun j => (Classical.choose_spec (hexu j)).1
  have hφuniq : ∀ (j j' : Fin G),
      window (L := L) hG E j = window (L := L) hG S j' → j' = φ j :=
    fun j j' h => ExistsUnique.unique (hexu j) h (hφspec j)
  -- the start map commutes with the successor map, hence is a cyclic shift
  -- the node sequence of `E` is the node sequence of `S` read through `φ`
  have hnode : ∀ r : Fin G, nodeWindow (L := L) hG E r
      = nodeWindow (L := L) hG S (φ r) := by
    intro r
    calc nodeWindow (L := L) hG E r
        = winPrefix (window (L := L) hG E r) := (winPrefix_window' hG E r).symm
      _ = winPrefix (window (L := L) hG S (φ r)) := by rw [hφspec r]
      _ = nodeWindow (L := L) hG S (φ r) := winPrefix_window' hG S (φ r)
  have hsucc : ∀ j : Fin G, φ (nextStart hG j) = nextStart hG (φ j) := by
    intro j
    have hnv : nodeWindow (L := L) hG S (φ (nextStart hG j))
        = nodeWindow (L := L) hG S (nextStart hG (φ j)) := by
      calc nodeWindow (L := L) hG S (φ (nextStart hG j))
          = nodeWindow (L := L) hG E (nextStart hG j) := (hnode (nextStart hG j)).symm
        _ = winSuffix (window (L := L) hG E j) := nodeWindow_next' hG E j
        _ = winSuffix (window (L := L) hG S (φ j)) := by rw [hφspec j]
        _ = nodeWindow (L := L) hG S (nextStart hG (φ j)) :=
          (winSuffix_window_next' hG S (φ j)).trans
            (winPrefix_window' hG S (nextStart hG (φ j)))
    exact P1.node_injective (hG := hG) (S := S) hP1 hnv
  have hcomm : ∀ (n : ℕ) (j : Fin G),
      (nextStart hG)^[n] (φ j) = φ ((nextStart hG)^[n] j) := by
    intro n
    induction n with
    | zero => intro j; simp only [Function.iterate_zero, id_eq]
    | succ m ih =>
        intro j
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
          hsucc ((nextStart hG)^[m] j)]
  have hphiIter : ∀ j : Fin G, φ j = (nextStart hG)^[j.val] (φ (0 : Fin G)) := by
    intro j
    have hk := hcomm j.val (0 : Fin G)
    have hv := nextIter_val hG (0 : Fin G) j.val
    have h0 : ((nextStart hG)^[j.val] (0 : Fin G)) = j := by
      apply Fin.ext
      rw [hv]
      simpa using (Nat.mod_eq_of_lt j.is_lt : j.val % G = j.val)
    rw [h0] at hk
    exact hk.symm
  have hiter : ∀ j : Fin G, window (L := L) hG E j
      = window (L := L) hG S ((nextStart hG)^[j.val] (φ (0 : Fin G))) := by
    intro j
    rw [hφspec j, hphiIter j]
  -- read off the rotation
  set r₀ : Fin G := φ (0 : Fin G) with hr₀def
  set k : ℕ := (G - r₀.val) % G with hkdef
  have hkey : (r₀.val + k) % G = 0 := by
    have h1 : (r₀.val + k) % G = ((r₀.val + (G - r₀.val)) % G) % G := by
      rw [hkdef, Nat.add_mod_mod, Nat.mod_mod]
    rw [h1]
    have h2 : (r₀.val + (G - r₀.val)) % G = 0 := by
      have hlt : r₀.val < G := r₀.is_lt
      rw [show r₀.val + (G - r₀.val) = G by omega]
      exact Nat.mod_self G
    rw [h2, Nat.zero_mod]
  refine rotEquiv_of_trailEquiv hG hL ?_
  refine ⟨k, fun j => ?_⟩
  have hj := hiter ⟨(j.val + k) % G, Nat.mod_lt _ hG⟩
  rw [hr₀def] at hj
  rw [hj]
  have hjv : (r₀.val + ((j.val + k) % G)) % G = j.val := by
    have h1 : (r₀.val + ((j.val + k) % G)) % G
        = ((r₀.val + (j.val + k)) % G) % G := by
      rw [Nat.add_mod_mod, Nat.mod_mod]
    have h2 : (r₀.val + (j.val + k)) % G = ((r₀.val + k) % G + j.val) % G := by
      have hx : r₀.val + (j.val + k) = (r₀.val + k) + j.val := by omega
      rw [hx]
      exact (Nat.mod_add_mod _ _ _).symm
    rw [h1, h2, hkey, Nat.zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt j.is_lt
  have hval : ((nextStart hG)^[((j.val + k) % G)] (φ 0)).val = j.val := by
    rw [nextIter_val]
    exact hjv
  exact congrArg (fun x : Fin G => window (L := L) hG S x) (Fin.ext hval)

/-! ## 5. The residual: Eulerian-circuit uniqueness for the `(L-1)`-de Bruijn
multigraph under Ukkonen's condition

`thm:BBT` says: build the `K`-mer graph from the complete `(K+1)`-spectrum;
if the genome satisfies Ukkonen's condition at `K`, the graph has a *unique
Eulerian cycle*, which spells the genome up to cyclic rotation.  Sections 2
and 4 above turned both halves of that sentence into concrete objects
(`EulerCircuit`, `TrailEquiv`) and proved the translation to `RotEquiv`.

What remains is the uniqueness half.  It is stated here on the multigraph, not
on genomes. -/

/-- **Unique Eulerian circuit of the multigraph of `c`.**  A closed trail with
edge multiplicities `c` exists, and every such trail is a cyclic shift of it.

This is a statement purely about the integer-valued multiplicity function `c`
(the `(K+1)`-spectrum) and the de Bruijn transition structure
`winPrefix`/`winSuffix` on length-`L` words; it does not mention
`specCount`, `RotEquiv`, primitivity, or any repeat predicate. -/
def UniqueEulerCircuit (hG : 0 < G) (c : (Fin L → α) → ℕ)
    (T : Fin G → Fin L → α) : Prop :=
  EulerCircuit hG c T ∧ ∀ U, EulerCircuit hG c U → TrailEquiv hG U T

/-- **The non-crossing condition on doubly-occurring `(L-1)`-mers.**  If two
`(L-1)`-mers each occur exactly twice, at starts `a, b` and `c, d`, then the
four starts do not alternate around the circle.

This is the concrete content of the second clause of P2 that the combinatorial
argument consumes, and it is a decidable statement about `S` alone. -/
def NodeCrossing (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  ∀ (u v : Fin (L - 1) → α) (a b c d : Fin G),
    nodeCount (L := L) hG S u = 2 → nodeCount (L := L) hG S v = 2 →
    (∀ x : Fin G, nodeWindow (L := L) hG S x = u → x = a ∨ x = b) →
    (∀ x : Fin G, nodeWindow (L := L) hG S x = v → x = c ∨ x = d) →
    ¬ Interleaved (mkGenome hG S) a b c d

/-! ### 5.1 What is proved: the translation

Everything from the multigraph statement to the conclusion about genomes is
proved below.  `p2_spectrum_unique_up_to_rotation` is therefore exactly as
strong as `thm:BBT` and no stronger. -/

/-- **`thm:BBT` at `K = L - 1`, modulo the Eulerian-circuit uniqueness input.**
A primitive genome satisfying P2 at read length `L`, whose `(L-1)`-de Bruijn
multigraph has a unique Eulerian circuit, is determined up to cyclic rotation
by its complete `L`-spectrum among all circular candidates of the same length.

The `Ukkonen` premise is *not* assumed: `P2.imp_Ukkonen` derives it. -/
theorem p2_spectrum_unique_up_to_rotation
    (hG : 0 < G) (hL : 2 ≤ L) (hLG : L ≤ G)
    (S E : Fin G → α)
    (_hPrimS : IsPrimitive S)
    (hP2S : P2 hG L S)
    (hUnique : UniqueEulerCircuit hG (specCount (L := L) hG S) (window (L := L) hG S))
    (hSpec : specCount (L := L) hG S = specCount (L := L) hG E) :
    RotEquiv hG E S := by
  -- the windows of `E` are an Eulerian circuit of the same multiplicities
  have hEc : EulerCircuit hG (specCount (L := L) hG E) (window (L := L) hG E) :=
    window_isEulerCircuit hG E
  have hEc' : EulerCircuit hG (specCount (L := L) hG S) (window (L := L) hG E) :=
    ⟨hEc.1, fun w => by rw [hEc.2 w, hSpec]⟩
  -- hence the two window trails are cyclic shifts
  have hTE : TrailEquiv hG (window (L := L) hG E) (window (L := L) hG S) :=
    hUnique.2 _ hEc'
  exact rotEquiv_of_trailEquiv hG (by omega) hTE

section Concrete

variable (hG : 0 < G)

/-- A concrete `P1` instance, so that the hypothesis of
`p1_spectrum_unique_up_to_rotation` is visibly inhabited: the circular word
`AAB` at read length `3` has the three `2`-mers `AA`, `AB`, `BA`, each exactly
once. -/
theorem aab_p1 : P1 (hG := by norm_num) (L := 3)
    (S := ![Bin.A, Bin.A, Bin.B]) := by
  unfold P1
  decide

/-- `AAB` at read length `3` is not `P1`-degenerate: it does have a repeated
`2`-mer once the word is `AABA`, which is why the `P1` hypothesis of
`p1_spectrum_unique_up_to_rotation` is not vacuous on this model. -/
theorem aaba_not_p1 : ¬ P1 (hG := by norm_num) (L := 3)
    (S := ![Bin.A, Bin.A, Bin.B, Bin.A]) := by
  unfold P1
  decide

end Concrete

end AssemblyP1.P2SpectrumUniqueness
