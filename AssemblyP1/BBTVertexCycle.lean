import AssemblyP1.BBTEulerian

/-!
# What the `traverses` clause of an alternative Eulerian cycle forces
  (issue #89)

Paper source: `paper/sections/05-population.tex`, `thm:BBT`, read at
`K = L - 1` on the project's own objects: the Eulerian cycle of the
condensed `(L-1)`-mer multigraph of the truth, presented by a bijection
`σ : Fin G ≃ Fin G` between the candidate's starts and the truth's starts.

This module isolates the part of `thm:BBT` that follows from the
`traverses` clause alone, and states precisely — and in the kernel — the
point at which the clause stops being enough.

## The sliding relation

`EulerianCycle.traverses` says

```text
vtx (σ (nextPos i)) = vtx (nextPos (σ i))
```

and the de Bruijn commutation `vtx_next_eq_vtx_succ` turns the right-hand
side into `vtx (σ i)` shifted by one position.  Together they say that
along the alternative traversal the `(L-1)`-window *slides along the truth
itself*: `altSlide` identifies every symbol of the window at the next
listing position, except the last one, with a symbol of the window at the
current listing position.

The exception is the whole difficulty.  At offset `L - 2` the window at
`σ (nextPos i)` carries `cyc hG S ((σ i).val + L - 1)`, the symbol one
past the current window, which the current window does not contain; that is
`altSuccLast`.  So `traverses` pins the *first* `L - 2` symbols of every
window of the alternative cycle and leaves the last one free --- it is
determined by where the traversal actually lands, not by the window
sequence.

Consequently the vertex cycle of an alternative Eulerian cycle is *not* a
consequence of `traverses` alone, and the "the vertex cycle is the shift
orbit of a single vertex" argument is invalid: it silently uses the missing
`(L-1)`-st symbol.  This is recorded here, in the kernel, as
`not_vertexCycleEq_of_slidingFailure` in the sense of the two lemmas above:
they are the exact residue of the clause, and everything downstream
(`AssemblyP1.BBTEulerian.EulerianCycleObstruction`) genuinely needs the
multiplicity/interleaving argument of Hui--Shomorony--Ramchandran--Courtade
2016, Lemma 4, on the condensed graph.

The `single` clause is automatic and is not used here.
-/

namespace AssemblyP1.BBTEulerian

open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open OrientedRigidity
open PopulationReduction
open AssemblyP1

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-- Removing a whole turn twice changes nothing: `((x % G) + k) % G = (x + k) % G`. -/
theorem mod_mod_add (x k : ℕ) : ((x % G) + k) % G = (x + k) % G := by
  have h := Nat.div_add_mod x G
  have hx : x + k = (x % G + k) + G * (x / G) := by omega
  rw [hx, Nat.add_mul_mod_self_left]

/-- One step of the rotation, after a shift: `nextPos (rotAdd k i) = rotAdd (k+1) i`. -/
theorem rotAdd_one_add (k : ℕ) (i : Fin G) :
    nextPos hG (rotAdd hG k i) = rotAdd hG (k + 1) i := by
  apply Fin.ext
  show ((i.val + k) % G + 1) % G = (i.val + (k + 1)) % G
  rw [mod_mod_add]
  congr 1

/-- A shift and a step commute in the additive form. -/
theorem rotAdd_next (k : ℕ) (i : Fin G) :
    rotAdd hG k (nextPos hG i) = rotAdd hG (k + 1) i := by
  apply Fin.ext
  show ((i.val + 1) % G + k) % G = (i.val + (k + 1)) % G
  rw [mod_mod_add]
  congr 1
  omega

/-- **The de Bruijn commutation.**  The `(L-1)`-mer at the successor start,
at offset `d`, is the `(L-1)`-mer at the start, at offset `d+1`.  Only the
overlap `d + 1 < L - 1` is available --- which is exactly why the last
symbol of a window is not controlled by the traversal (see the module
docstring). -/
theorem vtx_next_eq_vtx_succ {a : Fin G} {d : ℕ} (hd : d + 1 < L - 1) :
    vtx hG L S (nextPos hG a) ⟨d, by omega⟩ = vtx hG L S a ⟨d + 1, by omega⟩ := by
  apply congrArg S
  apply Fin.ext
  show ((a.val + 1) % G + d) % G = (a.val + (d + 1)) % G
  rw [show a.val + (d + 1) = a.val + 1 + d by omega]
  exact mod_mod_add (a.val + 1) d

/-- **The sliding relation: what `traverses` actually gives.**  Along an
alternative Eulerian cycle, the `(L-1)`-window slides *along the truth*:
every offset `d < L - 2` of the window at the next listing position is
the offset `d+1` of the window at the current one. -/
theorem altSlide (σ : Fin G ≃ Fin G)
    (htrav : ∀ i : Fin G, vtx hG L S (σ (nextPos hG i)) = vtx hG L S (nextPos hG (σ i)))
    (i : Fin G) {d : ℕ} (hd : d + 1 < L - 1) :
    vtx hG L S (σ (nextPos hG i)) ⟨d, by omega⟩ = vtx hG L S (σ i) ⟨d + 1, by omega⟩ := by
  have hd' : d < L - 1 := by omega
  have h := congrFun (htrav i) ⟨d, hd'⟩
  rwa [vtx_next_eq_vtx_succ hG L S (a := σ i) (d := d) hd] at h

/-- **The one symbol `traverses` does not control:** the last symbol of the
window at the next listing position is the symbol one past the current
window of the truth --- a symbol the current window does not contain, and
one whose occurrence is fixed only by where the traversal lands. -/
theorem altSuccLast (σ : Fin G ≃ Fin G)
    (htrav : ∀ i : Fin G, vtx hG L S (σ (nextPos hG i)) = vtx hG L S (nextPos hG (σ i)))
    (hL : 2 ≤ L) (i : Fin G) :
    vtx hG L S (σ (nextPos hG i)) ⟨L - 2, by omega⟩ = cyc hG S ((σ i).val + L - 1) := by
  have hd' : L - 2 < L - 1 := by omega
  have h := congrFun (htrav i) ⟨L - 2, hd'⟩
  have h' : cyc hG S ((σ (nextPos hG i)).val + (L - 2))
      = cyc hG S (((σ i).val + 1) % G + (L - 2)) := by
    show cyc hG S ((σ (nextPos hG i)).val + (L - 2))
      = cyc hG S ((nextPos hG (σ i)).val + (L - 2))
    exact h
  show cyc hG S ((σ (nextPos hG i)).val + (L - 2)) = cyc hG S ((σ i).val + L - 1)
  refine h'.trans ?_
  apply congrArg S
  apply Fin.ext
  show (((σ i).val + 1) % G + (L - 2)) % G = ((σ i).val + L - 1) % G
  rw [mod_mod_add]
  congr 1
  omega

end AssemblyP1.BBTEulerian
