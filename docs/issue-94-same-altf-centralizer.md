# Board 94 — the same-`AltF` centralizer lemma

Module: `AssemblyP1/Issue94SameAltF.lean` (imports `AssemblyP1.Issue94TW7AltF`).
Branch: `research/94-phoebe-cle2`.

## Claim

Let `ρ = nextPos hG` (one-step rotation of the circle of `G` positions),
`Succ hG σ = σ ρ σ⁻¹` (`BBTUniqueEulerian.lean:656`) and
`AltF hG σ = Succ hG σ ∘ prevPos` (`BBTUniqueEulerian.lean:698`). If

* `hvtx : ∀ q : Fin G, vtx hG L S (τ q) = vtx hG L S q` — `τ` preserves the
  `(L-1)`-mer at every start, and
* `hAlt : ∀ q : Fin G, AltF hG τ q = AltF hG σ q` — the two alternative
  traversals have the same successor at every start,

then

1. `∀ x, τ (nextPos hG (τ.symm x)) = σ (nextPos hG (σ.symm x))`, i.e.
   `τ ρ τ⁻¹ = σ ρ σ⁻¹` — **`succ_eq_of_altF_eq`**;
2. `IsRotation hG (σ⁻¹ ∘ τ)`: the quotient `q := σ⁻¹ ∘ τ` is a **rotation of the
   circle** — **`qfun_isRotation`**, via the existing
   `Issue94TW7AltF.comm_nextPos_isRotation`; consequently
   `τ = σ ∘ rotAdd s` (**`tau_eq_sigma_rot`**) and
   `σ = τ ∘ rotAdd (G - s % G)` (**`sigma_eq_tau_rot`**);
3. `VertexCycleEq hG L S σ (Equiv.refl (α := Fin G))` — **`same_altF_vertexCycleEq`**,
   and the conjunction of 1, 2, 3 is **`same_altF_centralizer`**.

## Proof, in the repository's vocabulary

* Step 1 is one line: `AltF_succ` rewrites the pointwise equality at
  `nextPos hG x` into `Succ hG τ x = Succ hG σ x`, and `Succ` *is* the
  rotation-conjugate (`succ_eq_conj_nextPos`, `rfl` in `Issue94Transposition`).
* Step 2 cancels `σ` on the right and `σ⁻¹` on the left: from
  `τ ρ τ⁻¹ = σ ρ σ⁻¹` one gets `q ρ = ρ q` with `q = σ⁻¹ ∘ τ`. That `q`
  commutes with `ρ` **is** a rotation is exactly tw7's
  `comm_nextPos_isRotation`; no word, no `L`, no `vtx`, no `Ukkonen`.
* Step 3 needs the inverse rotation `rotAdd s ∘ rotAdd (G - s) = id`
  (**`rotAdd_comp_inv`**, pure `Fin G` arithmetic) and then
  `vtx (τ x) = vtx x`.

**The last step deliberately does not use shift-invariance of `vtx`.** That
statement is false and is refuted kernel-side by
`Issue94EulerianTheta.vtx_rotAdd_refuted` (`vtx (rotAdd 1 0) ≠ vtx 0` at
`S = 0101`, `G = 4`, `L = 3`). Routing through the inverse rotation is the only
correct way; a draft that instead shifts `vtx` was not written.

## Status of this front

Proved (pending the validation build): `rotAdd_comp_inv`,
`succ_eq_of_altF_eq`, `qfun_comm_nextPos`, `qfun_isRotation`, `tau_eq_sigma_rot`,
`sigma_eq_tau_rot`, `same_altF_vertexCycleEq`, `same_altF_centralizer`.

Not proved, unchanged: `BBTEulerian.EulerianCycleObstruction` (`hPevzner`),
`BBTEulerian.UniqueEulerianCycle`, `BBTLadder.LadderVertexCycle`,
`BBTLadder.CrossingChordsCoalesce`. This module adds no `BBT`-shaped
hypothesis and inhabits no endpoint `Prop`; no `sorry`, no `admit`, no
`native_decide`, no new axiom, no definition changed.

## Why it matters for the open problem

`VertexCycleEq` is what `EulerianCycleObstruction` asks for. This lemma says the
`AltF` presentation carries *no* information beyond a rotation of the starts, so
the only way an Eulerian cycle of the condensed graph can fail to be
vertex-cycle-trivial is not "the same `AltF` as a rotation", it is "an `AltF`
that is not the one of any rotation". That is the sharpest reduction available
on this object: the residual obstruction is a statement about the *chords* of
`AltF hG σ` (the support analysis of `Issue94Transposition` / `BBTVertexCycle`),
not about the choice of listing position. It does **not** settle #89: the
remaining step is still "chords of a non-rotational `AltF` ⟹ non-trivial vertex
cycle", i.e. `Issue94TW8Contraction` / `BBTLadder` territory.

## Notes for the validation agent

* Proofs are written against signatures read from the sources, not built in this
  worktree (no `.lake` here); nothing was elaborated.
* Signature dependencies: `Succ_apply`, `AltF_succ` (`BBTUniqueEulerian`),
  `rotAdd_mod`, `rotAdd_zero`, `nextPos` (`BBTChords`), `mod_add_shl`,
  `rotAdd_add`, `rotAdd_full` (section `Windows` of `BBTUniqueEulerian`; note
  `S` is dropped from their signatures), `origin`, `VertexCycleEq`
  (`BBTEulerian`), `comm_nextPos_isRotation` (`Issue94TW7AltF`).
* `AssemblyP1.lean` imports the module at the end of the file and lists the
  eight `#print axioms` commands.