import AssemblyP1.BBTVertexCycleReduction
import AssemblyP1.Issue94TW7AltF

/-!
# Board 94: two presentations with the same `AltF` have the same vertex cycle

This module is the correct purely combinatorial replacement for the refuted
obligation of front tw7 (`AssemblyP1/Issue94TW7AltF.lean`).  That front showed
that "`Ukkonen` plus label-preservation implies `AltF = id`" is **false**, and
that the object `EulerianCycleObstruction` (`BBTEulerian.lean:415-418`) actually
quantifies over is `VertexCycleEq`, not `AltF = id` — and it left open whether
even `VertexCycleEq` follows from that combination.

Here it does, for the exact hypothesis pair tw7 identified as the real content:

```lean
hAlt : ∀ x : Fin G, AltF hG σ x = AltF hG τ x          -- same alternative traversal
hLP  : ∀ x : Fin G, vtx hG L S (τ x) = vtx hG L S x    -- τ is label-preserving
```

and the conclusion is exactly the board's target,
`VertexCycleEq hG L S σ (Equiv.refl _)` — the listing of `σ` is the truth's own
vertex listing, modulo the choice of the starting position.

## Why it works

The two presentations induce the *same* successor map `AltF`, so the listings
are conjugate by `τ`, and the conjugating element `q = τ⁻¹ ∘ σ` commutes with the
one-step rotation:

```text
   τ (q (nextPos i)) = σ (nextPos i)                                  (definition of q)
                     = AltF hG σ (nextPos (σ i))                     (BBTVertexCycle.listing_step)
                     = AltF hG τ (nextPos (τ (q i)))                 (hAlt)
                     = τ (nextPos (q i))                              (BBTVertexCycle.listing_step)
```

Note what is **not** used: no `EulerianCycle` hypothesis, no `Ukkonen`, no
`P2`, no primitivity, no repeat theory, no `VisitsAll`.  Only
`BBTVertexCycle.listing_step` (a permutation-form rewriting of
`Succ σ (σ i) = σ (nextPos i)`, hence of the definition of `BBTUniqueEulerian.AltF`),
the hypothesis `hAlt`, and `Issue94TW7AltF.comm_nextPos_isRotation`.

`comm_nextPos_isRotation` then upgrades the commutation to "`q` is a rotation of
the circle", `q i = rotAdd hG s i`, and `hLP` converts `vtx (τ x)` into `vtx x`.
So the listing of `σ` is the truth's vertex listing shifted by `s`, which is
`VertexCycleEq hG L S σ (Equiv.refl _)` with witness `⟨s % G, _⟩`.

## Status

* **Proved:** `sameAltF_comm_nextPos` and `sameAltF_vertexCycleEq` (§1, §2),
  both unconditional with respect to `EulerianCycle`.
* **Not claimed:** this does **not** discharge
  `BBTEulerian.EulerianCycleObstruction`, i.e. `hPevzner`
  (`AssemblyP1/PopulationUniqueness.lean:164`, `:217`, `:247`) — it does not
  touch `BBTEulerian.UniqueEulerianCycle`, `BBTLadder.LadderVertexCycle`, or
  `BBTUniqueEulerian` Lemma 2.  `BBT` remains a hypothesis.
* No `sorry`, no `admit`, no `native_decide`, no `axiom`, no definition
  changed, no theorem statement weakened.
-/

set_option linter.unusedVariables false

namespace AssemblyP1.Issue94SameAltF

open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian

/-! ## 1. The re-indexing between two presentations with the same `AltF`
commutes with the one-step rotation -/

/-- **Two presentations with the same `AltF` re-index each other by a
rotation.**

If `AltF hG σ x = AltF hG τ x` for every `x`, then the re-indexing
`q = τ.symm ∘ σ` commutes with `nextPos hG`:

```lean
   q (nextPos hG y) = nextPos hG (q y)
```

**No `EulerianCycle` hypothesis is used** — only
`BBTVertexCycle.listing_step`, the hypothesis, and
`BBTUniqueEulerian.AltF`.  This is the step that is missing from the
point-level chain flagged in `Issue94TW7AltF.lean:558-583`: there the pull-back
was a single presentation `σ`, whose deviation from a rotation is the open
content of `thm:BBT`; here two presentations are assumed to *agree on
`AltF`*, which is precisely what pins the deviation to zero. -/
theorem sameAltF_comm_nextPos {G : ℕ} (hG : 0 < G) (σ τ : Fin G ≃ Fin G)
    (hAlt : ∀ x : Fin G,
      BBTUniqueEulerian.AltF hG σ x = BBTUniqueEulerian.AltF hG τ x) :
    ∀ y : Fin G, τ.symm (σ (nextPos hG y)) = nextPos hG (τ.symm (σ y)) := by
  intro y
  have hτ : τ (τ.symm (σ (nextPos hG y))) = τ (nextPos hG (τ.symm (σ y))) := by
    calc τ (τ.symm (σ (nextPos hG y))) = σ (nextPos hG y) :=
          Equiv.apply_symm_apply τ _
      _ = BBTUniqueEulerian.AltF hG σ (nextPos hG (σ y)) := by
          apply BBTVertexCycle.listing_step
      _ = BBTUniqueEulerian.AltF hG τ (nextPos hG (τ (τ.symm (σ y)))) := by
          rw [Equiv.apply_symm_apply]
          exact hAlt _
      _ = τ (nextPos hG (τ.symm (σ y))) := by
          exact (BBTVertexCycle.listing_step (σ := τ) hG (τ.symm (σ y))).symm
  exact Equiv.injective τ hτ

/-! ## 2. The board target: the listing is the truth's vertex listing

`VertexCycleEq hG L S σ (Equiv.refl _)` is the target of
`BBTEulerian.EulerianCycleObstruction` and of
`BBTLadder.LadderVertexCycle`, i.e. exactly the statement the tw7 front
identified as the right one in place of the false `AltF = id`. -/

/-- **Same `AltF` + label-preserving `τ` ⟹ the listing of `σ` is the truth's
vertex listing, up to rotation.**

More precisely: `AltF hG σ = AltF hG τ` and
`∀ x, vtx hG L S (τ x) = vtx hG L S x` give `VertexCycleEq hG L S σ (Equiv.refl _)`.

The proof is `sameAltF_comm_nextPos` followed by
`Issue94TW7AltF.comm_nextPos_isRotation` (the re-indexing is a rotation of the
circle) and then `hLP` (a rotation of the circle does not change a `(L-1)`-mer).

**No `EulerianCycle` hypothesis is used.**  What is *not* claimed: that
`hAlt` holds for the presentations one actually obtains from the repeat theory,
i.e. that `EulerianCycleObstruction` (`hPevzner`) follows.  `BBT` remains a
hypothesis. -/
theorem sameAltF_vertexCycleEq {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G)
    (S : Fin G → α) (σ τ : Fin G ≃ Fin G)
    (hAlt : ∀ x : Fin G,
      BBTUniqueEulerian.AltF hG σ x = BBTUniqueEulerian.AltF hG τ x)
    (hLP : ∀ x : Fin G, vtx hG L S (τ x) = vtx hG L S x) :
    VertexCycleEq hG L S σ (Equiv.refl (α := Fin G)) := by
  obtain ⟨s, hs⟩ :=
    Issue94TW7AltF.comm_nextPos_isRotation hG (fun y => τ.symm (σ y))
      (sameAltF_comm_nextPos hG σ τ hAlt)
  refine ⟨⟨s % G, Nat.mod_lt s hG⟩, ?_⟩
  intro i
  have hshift : τ.symm (σ i) = rotAdd hG s i := hs i
  have hkey : vtx hG L S (σ i) = vtx hG L S (rotAdd hG s i) := by
    calc vtx hG L S (σ i) = vtx hG L S (τ (τ.symm (σ i))) := by
          rw [Equiv.apply_symm_apply]
      _ = vtx hG L S (τ.symm (σ i)) := hLP _
      _ = vtx hG L S (rotAdd hG s i) := by rw [hshift]
  calc vtx hG L S (σ i) = vtx hG L S (rotAdd hG s i) := hkey
    _ = vtx hG L S (rotAdd hG (s % G) i) := by rw [rotAdd_mod hG s i]
    _ = vtx hG L S (rotAdd hG (s % G) ((Equiv.refl (α := Fin G)) i)) := by rfl

/-- **Restatement of `sameAltF_vertexCycleEq` as the two facts that are actually
consumed downstream**, so a reader need not re-derive them from the `∃`-form:
the listing is a rotation of the truth's vertex listing. -/
theorem sameAltF_listing_is_rotation {α : Type} [DecidableEq α] {G L : ℕ}
    (hG : 0 < G) (S : Fin G → α) (σ τ : Fin G ≃ Fin G)
    (hAlt : ∀ x : Fin G,
      BBTUniqueEulerian.AltF hG σ x = BBTUniqueEulerian.AltF hG τ x)
    (hLP : ∀ x : Fin G, vtx hG L S (τ x) = vtx hG L S x) :
    ∃ s : ℕ, ∀ i : Fin G,
      vtx hG L S (σ i) = vtx hG L S (rotAdd hG s ((Equiv.refl (α := Fin G)) i)) := by
  obtain ⟨s, hs⟩ :=
    Issue94TW7AltF.comm_nextPos_isRotation hG (fun y => τ.symm (σ y))
      (sameAltF_comm_nextPos hG σ τ hAlt)
  refine ⟨s, fun i => ?_⟩
  have hshift : τ.symm (σ i) = rotAdd hG s ((Equiv.refl (α := Fin G)) i) := hs i
  calc vtx hG L S (σ i) = vtx hG L S (τ (τ.symm (σ i))) := by
        rw [Equiv.apply_symm_apply]
    _ = vtx hG L S (τ.symm (σ i)) := hLP _
    _ = vtx hG L S (rotAdd hG s ((Equiv.refl (α := Fin G)) i)) := by rw [hshift]

end AssemblyP1.Issue94SameAltF
