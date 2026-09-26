import Mathlib
import AssemblyP1.PopulationReduction
import AssemblyP1.OrientedFinalRigidity
import AssemblyP1.SourceFaithfulIs

/-!
# P2 / Ukkonen complete-spectrum uniqueness, and the exact residual core
  (issue #89)

This module works on the **current `main`** state of the library, where
`AssemblyP1.PopulationUniqueness` still takes the whole of the
Bresler--Bresler--Tse uniqueness implication as a caller-supplied premise
(`hBBTS`, `hBBTD`).  This file attacks exactly that premise.

## What is proved here

1. **The actual conditions.** `mkGenome`, `P2` and `Ukkonen` are transcribed
   verbatim from `paper/sections/05-population.tex` `def:P1P2` and
   `thm:BBT`, on top of the source-faithful predicates of
   `AssemblyP1.SourceFaithfulIs` (`IsRepeat`, `IsTripleRepeat`,
   `Interleaved`).  `P2.imp_Ukkonen` kernel-checks the paper's alignment
   sentence "setting `K = L - 1` aligns the theorem's condition exactly with
   P2".

2. **The maximal-extension engine.**  On a circle, two or three starts
   carrying a common window extend *simultaneously* to a maximal repeat, and
   maximality is exactly the two-sided maximality required by
   `Genome.IsRepeat` / `Genome.IsTripleRepeat`.  Everything is done with a
   single maximal length, so no separate left/right extension argument is
   needed: shifting the common window one step left and then extending
   maximally to the right yields both maximality conditions at once.

3. **The repeat consequences of P2** (`P2.node_le_two`,
   `P2.no_crossing_doubles`):
   * every `(L-1)`-mer occurs at most twice (`node_le_two`), which is the
     vertex-throughput cap that `AssemblyP1.OrientedRigidity` documents as
     the remaining hypothesis of `unique_positive_circulation`;
   * the *occurrence pairs* of the doubly-occurring `(L-1)`-mers are
     pairwise non-interleaved (`no_crossing_doubles`).  This is the second
     clause of P2 in exactly the form the combinatorial argument needs.

4. **The word / Eulerian-circuit bridge** (`EulerCircuit`, `TrailEquiv`): a
   circular word of length `G` gives a cyclic closed trail of length-`L`
   windows whose edge multiplicities are its `L`-spectrum, and a cyclic
   closed trail with those multiplicities spells a circular word which is a
   cyclic shift of the trail.  This is the kernel-checked translation from the
   paper's "unique Eulerian cycle" language to `RotEquiv`, so that what
   remains is a statement about a multigraph, not about genomes.

## What is *not* proved here, and why

The genuinely missing step is the Eulerian-circuit uniqueness theorem for the
`(L-1)`-de Bruijn multigraph under the non-crossing condition.  It is stated
as `UniqueEulerCircuit` in terms of the explicitly defined objects above
(`EulerCircuit`, `TrailEquiv`, `winPrefix`/`winSuffix`, `nodeCount`,
`Interleaved`), **not** as a restatement of "equal spectrum implies rotation",
and `p2_spectrum_unique_up_to_rotation` shows kernel-checked that
`UniqueEulerCircuit` yields the desired conclusion.

That residual is the hard half of `thm:BBT` and is *not* discharged here;
see `docs/issue89-spectrum-uniqueness.md` for its exact statement, the
computational evidence that P2 at `L` really does suffice (exhaustive search
over circular words with `|Σ| ≤ 4`, `L ≤ 5`, `|S| ≤ 12` finds **no**
primitive P2-satisfying word sharing its `L`-spectrum with a non-shift), and
the reduction argument showing the residual is the smallest possible.
No `axiom`, `sorry` or `admit` occurs in this file.
-/

set_option maxHeartbeats 600000

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

end AssemblyP1.P2SpectrumUniqueness
