import AssemblyP1.BBTLadder

/-!
# Board 94, front 94transpose: the one-step transposition lemma for
# `VertexCycleEq`, and the sharpness of its hypothesis

The question assigned to this front was: *if the current Eulerian listing `σ`
is `VertexCycleEq` to the truth and a directed transposition is performed at two
branch vertices interlaced in the current tour, can the resulting listing be
shown `VertexCycleEq`?*  The suggested route was to transport the four
occurrences of the two chords through the rotation witness, re-apply
`CrossingPairsCoalesce_general` / `SameExtension` in truth coordinates, and
compare the swapped arc labels with `ladder_of_coalescing` + `ladder_arc_eq`.

**The suggested route is unnecessary, and the statement it was meant to prove is
`TRUE`, but only because of a hypothesis it never mentions.**  What is delivered:

* §1 `vertexCycleEq_transposition`: the one-step lemma.  A transposition of two
  starts spelling the **same `(L-1)`-mer** is vertex-invisible — the new
  listing spells, *pointwise at every listing position*, exactly the same
  vertex as the old one — hence it preserves `VertexCycleEq` with the *same*
  rotation witness `k`.  This is why no transport through the rotation witness
  is needed: `VertexCycleEq` with witness `k` is preserved by any permutation of
  the listing that is pointwise `vtx`-invisible, and swapping two equal-mers
  starts is exactly that.
* §2 two corollaries in the vocabulary of the ladder packet: the two ends of a
  chord of `f = AltF hK σ` (`AltF_vtx'`) and the two occurrences of a branch
  object (`DoubledPair`) satisfy the hypothesis automatically, so the lemma
  applies to a transposition at the two ends of any support chord, interlaced or
  not.
* §3 closure under any finite sequence of such transpositions.
* §4 **the refutation**: interlacement alone is NOT enough.  At the smallest
  possible circle with a non-degenerate window, `K = 3`, `L = 3`,
  `S = 001`, `σ = Equiv.refl`, transposing the interlaced pair `{0, 1}` breaks
  `VertexCycleEq`.  So the equal-`(L-1)`-mer hypothesis of §1 is exactly the
  load-bearing one, and the "raw final-support interlacement" formulation the
  front was warned about is refuted.

**What this does NOT do.**  It does not produce an inhabitant of
`BBTLadder.LadderVertexCycle`, and it does not touch
`CrossingChordsCoalesce`.  In particular `LadderVertexCycle`'s real content is
not this step: §1 applies to *any* listing whose entries are starts of the
circle, and never uses `EulerianCycle`, `P2`, `Ukkonen`, primitivity,
`Interleaved`, `SameExtension` or `AltF = id`.  The remaining obstruction named
by `BOARD94-LADDERCYCLE-0851Z.md` (that the traversal must walk the laminar
blocks in geometric order) is untouched by this module.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace AssemblyP1.BBTTranspose

open AssemblyP1
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTLadder
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTChords
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.OrientedRigidity

variable {α : Type} [DecidableEq α] {K : ℕ} (hK : 0 < K) (L : ℕ) (S : Fin K → α)

/-- The size of the smallest instance of §4. -/
theorem hK3 : (0 : ℕ) < 3 := by omega

/-! ## 1. `VertexCycleEq` sees only the pointwise vertex reading -/

/-- **A listing is determined, for `VertexCycleEq`, by what it reads at each
position.**  Two listings spelling the same `(L-1)`-mer at every listing
position are `VertexCycleEq` at shift `0`.

This is the whole reason §2 below is cheap: `VertexCycleEq` with witness `k` is
a *pointwise* statement `∀ i, vtx (σ i) = vtx (rotAdd k i)`, so any
rearrangement of the listing that preserves the pointwise reading preserves it,
with the same witness. -/
theorem vertexCycleEq_of_pointwise_vtx {σ τ : Fin K ≃ Fin K}
    (h : ∀ i : Fin K, vtx hK L S (σ i) = vtx hK L S (τ i)) :
    VertexCycleEq hK L S σ τ := by
  refine ⟨origin hK, ?_⟩
  intro i
  simpa only [Equiv.refl_apply, rotAdd_zero, origin_val] using h i

/-- **One-step lemma: a transposition at two branch vertices is
vertex-invisible.**  Let `a` and `b` be two starts spelling the same
`(L-1)`-mer — i.e. the two occurrences of one branch object of the condensed
graph — and let `σ` be a listing that is `VertexCycleEq` to the truth.  The
transposed listing `(a b) ∘ σ` (in Lean, `σ.trans (Equiv.swap a b)`, since
`f.trans g = g ∘ f`; this exchanges the two *listing positions* at which the
branch vertices `a` and `b` occur) is again `VertexCycleEq` to the truth, with
the same rotation witness.

No interlacement hypothesis is used, no `AltF`, no `SameExtension`, no
`EulerianCycle`, no `P2`/`Ukkonen`, no primitivity, and no `AltF = id`. -/
theorem vertexCycleEq_transposition {σ : Fin K ≃ Fin K} {a b : Fin K}
    (hvb : vtx hK L S a = vtx hK L S b)
    (hv : VertexCycleEq hK L S σ (Equiv.refl (α := Fin K))) :
    VertexCycleEq hK L S (σ.trans (Equiv.swap a b)) (Equiv.refl (α := Fin K)) := by
  obtain ⟨k, hk⟩ := hv
  refine ⟨k, ?_⟩
  intro i
  simp only [Equiv.trans_apply, Equiv.refl_apply]
  by_cases hia : σ i = a
  · rw [hia, Equiv.swap_apply_left, hvb.symm]
    have h := hk i
    rw [hia] at h
    exact h
  by_cases hib : σ i = b
  · rw [hib, Equiv.swap_apply_right, hvb]
    have h := hk i
    rw [hib] at h
    exact h
  rw [Equiv.swap_apply_of_ne_of_ne hia hib]
  exact hk i

/-! ## 2. The two ends of a support chord satisfy the hypothesis -/

/-- **The one-step lemma in the genuine-Eulerian vocabulary.**  A transposition
at the two ends of a chord of `f = AltF hK σ` — `AltF hK σ a = b` — preserves
`VertexCycleEq`.  The equal-`(L-1)`-mer hypothesis is discharged by
`BBTLadder.AltF_vtx'`, i.e. by the `traverses` clause alone; `P2`, primitivity,
`L ≤ K` and `AltF_sq` are not needed for *this* step. -/
theorem vertexCycleEq_transposition_AltF {σ : Fin K ≃ Fin K} {a b : Fin K}
    (hEul : EulerianCycle hK L S σ) (hfb : AltF hK σ a = b)
    (hv : VertexCycleEq hK L S σ (Equiv.refl (α := Fin K))) :
    VertexCycleEq hK L S (σ.trans (Equiv.swap a b)) (Equiv.refl (α := Fin K)) := by
  have hb : vtx hK L S b = vtx hK L S a := by
    rw [← hfb]
    exact AltF_vtx' hK S hEul a
  exact vertexCycleEq_transposition hK L S hb.symm hv

/-- **The same, for the two occurrences of one branch object.**  `DoubledPair`
is the branch object of the condensed graph together with its two realisations,
so a transposition of those two realisations preserves `VertexCycleEq`. -/
theorem vertexCycleEq_transposition_DoubledPair {σ : Fin K ≃ Fin K} {a b : Fin K}
    (hd : DoubledPair (L := L) hK S a b)
    (hv : VertexCycleEq hK L S σ (Equiv.refl (α := Fin K))) :
    VertexCycleEq hK L S (σ.trans (Equiv.swap a b)) (Equiv.refl (α := Fin K)) :=
  vertexCycleEq_transposition hK L S hd.2.2.symm hv

/-! ## 3. Closure under any finite sequence of such transpositions -/

/-- **A finite sequence of branch-vertex transpositions preserves
`VertexCycleEq`.**  The hypothesis is on the *starts* `p`, not on the listing,
and the hypothesis of §1 is likewise on the starts, so the steps compose
without any bookkeeping. -/
theorem vertexCycleEq_transpositionList {σ : Fin K ≃ Fin K}
    {ps : List (Fin K × Fin K)}
    (hps : ∀ p ∈ ps, vtx hK L S p.1 = vtx hK L S p.2)
    (hv : VertexCycleEq hK L S σ (Equiv.refl (α := Fin K))) :
    VertexCycleEq hK L S
      (ps.foldl (fun τ p => τ.trans (Equiv.swap p.1 p.2)) σ)
      (Equiv.refl (α := Fin K)) := by
  induction ps generalizing σ with
  | nil => exact hv
  | cons p ps ih =>
      have hp : vtx hK L S p.1 = vtx hK L S p.2 := hps p List.mem_cons_self
      have hps' : ∀ q ∈ ps, vtx hK L S q.1 = vtx hK L S q.2 := by
        intro q hq
        exact hps q (List.mem_cons_of_mem _ hq)
      exact ih (hps := hps')
        (vertexCycleEq_transposition hK L S hp hv)

end AssemblyP1.BBTTranspose

namespace AssemblyP1.BBTTranspose

open AssemblyP1
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTLadder
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTChords
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.OrientedRigidity

end AssemblyP1.BBTTranspose

namespace AssemblyP1.BBTTranspose

open AssemblyP1
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTLadder
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTChords
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.OrientedRigidity

/-! ## 4. Anti-vacuity: a real chord of a real `AltF` -/

/-- On `S = 0101`, `G = 4`, `L = 3`, the alternative traversal `tau4` sends
`0` to `1`: it genuinely re-pairs there, so `0`, `1` are the two ends of a
support chord. -/
theorem altF_tau4_0 : AltF hG4 tau4 0 = 2 := by decide

/-- The lemma of §2 applied to that chord: transposing the two listing positions
of the chord ends `0`, `2` keeps `VertexCycleEq`. -/
theorem transposition_at_chord_S4 :
    VertexCycleEq hG4 3 S4 (tau4.trans (Equiv.swap 0 2))
      (Equiv.refl (α := Fin 4)) :=
  vertexCycleEq_transposition_AltF hG4 3 S4 eulerianCycle_S4 altF_tau4_0
    trivial_vertexCycleEq_S4

/-- ... and the transposed listing is *not* the identity listing, so the
statement is about a genuinely different listing. -/
theorem transposition_at_chord_S4_ne :
    tau4.trans (Equiv.swap 0 2) ≠ Equiv.refl (α := Fin 4) := by decide

/-! ## 5. Interlacement alone is not enough: the refutation -/

/-- `001` on a circle of three positions, read at window length `3`. -/
def S3t : Fin 3 → Fin 2 := ![0, 0, 1]

/-- The identity listing of `S3t`. -/
def sigma3 : Fin 3 ≃ Fin 3 := Equiv.refl (α := Fin 3)

/-- The identity listing is a vertex cycle of the truth: witness `k = 0`. -/
theorem vertexCycleEq_sigma3 :
    VertexCycleEq hK3 3 S3t sigma3 (Equiv.refl (α := Fin 3)) :=
  vertexCycleEq_of_pointwise_vtx _ _ _ (fun _ => rfl)

/-- The refuted instance.  The two transposition points are `0` and `1`; they
are distinct, and on a circle of three positions *every* pair of distinct points
alternates, so any formulation whose only condition on the two transposition
points is interlacement / crossing in the tour admits this instance.  (At
`K ≥ 4` the four-point `BBTCondense.Interleaved` is the non-vacuous reading of
"crossing"; the equal-`(L-1)`-mer hypothesis of §1 is what makes the lemma true
there, and §4 shows it cannot be dropped.) -/
theorem not_vertexCycleEq_sigma3_swap01 :
    ¬ VertexCycleEq hK3 3 S3t (sigma3.trans (Equiv.swap 0 1))
      (Equiv.refl (α := Fin 3)) := by
  decide

/-- **The refuted formulation**, in general form: *any* transposition of two
distinct points of a listing preserves `VertexCycleEq`.  This is what an
interlacement-only / raw-final-support reading of the one-step lemma gives ---
distinctness of the two transposition points is all such a reading has, and on a
circle of at most three positions every pair of distinct points alternates, so
interlacement adds nothing there. -/
def AnyTranspositionPreserves {K : ℕ} (hK : 0 < K) (L : ℕ) (S : Fin K → Fin 2)
    (σ : Fin K ≃ Fin K) : Prop :=
  ∀ a b : Fin K, a ≠ b →
    VertexCycleEq hK L S σ (Equiv.refl (α := Fin K)) →
    VertexCycleEq hK L S (σ.trans (Equiv.swap a b)) (Equiv.refl (α := Fin K))

/-- **`AnyTranspositionPreserves` is false**, already at `K = 3`, `L = 3`. -/
theorem interlaceAlone_insufficient :
    ¬ AnyTranspositionPreserves (K := 3) hK3 3 S3t sigma3 := by
  intro h
  exact absurd (h (0 : Fin 3) 1 (by decide) vertexCycleEq_sigma3)
    not_vertexCycleEq_sigma3_swap01

/-! ## 6. Axiom audit -/

#print axioms AssemblyP1.BBTTranspose.vertexCycleEq_of_pointwise_vtx
#print axioms AssemblyP1.BBTTranspose.vertexCycleEq_transposition
#print axioms AssemblyP1.BBTTranspose.vertexCycleEq_transposition_AltF
#print axioms AssemblyP1.BBTTranspose.vertexCycleEq_transposition_DoubledPair
#print axioms AssemblyP1.BBTTranspose.vertexCycleEq_transpositionList
#print axioms AssemblyP1.BBTTranspose.altF_tau4_0
#print axioms AssemblyP1.BBTTranspose.transposition_at_chord_S4
#print axioms AssemblyP1.BBTTranspose.transposition_at_chord_S4_ne
#print axioms AssemblyP1.BBTTranspose.vertexCycleEq_sigma3
#print axioms AssemblyP1.BBTTranspose.not_vertexCycleEq_sigma3_swap01
#print axioms AssemblyP1.BBTTranspose.AnyTranspositionPreserves
#print axioms AssemblyP1.BBTTranspose.interlaceAlone_insufficient

end AssemblyP1.BBTTranspose