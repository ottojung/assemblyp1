import AssemblyP1.Issue94TW7AltF

/-!
# Board 94: two listings with the same `AltF` differ by a rotation, and a
# rotation of the starts is vertex-cycle-trivial

This module proves the **same-`AltF` centralizer lemma**.

## The statement

Let `ρ = nextPos hG` be the one-step rotation of the circle of `G` positions,
`Succ hG σ = σ ρ σ⁻¹` (`BBTUniqueEulerian.lean:656`, `rfl`-checked as
`Issue94Transposition.succ_eq_conj_nextPos`), and

```lean
def AltF {G : ℕ} (hG : 0 < G) (σ : Fin G ≃ Fin G) (q : Fin G) : Fin G :=
  Succ hG σ (prevPos hG q)
```

so `AltF hG σ = Succ hG σ ∘ prevPos`.  If `τ : Fin G ≃ Fin G` **preserves `vtx`
pointwise** (`∀ q, vtx hG L S (τ q) = vtx hG L S q`) and **`AltF hG τ` and
`AltF hG σ` agree pointwise**, then

1. `τ ρ τ⁻¹ = σ ρ σ⁻¹` (`Succ hG τ = Succ hG σ`),
2. `q := σ⁻¹ ∘ τ` commutes with `ρ`, hence `q` is a **rotation of the circle**
   (`IsRotation hG q`, by the already-proved
   `Issue94TW7AltF.comm_nextPos_isRotation`), i.e. `τ = σ ∘ rotAdd s` for some
   `s : ℕ`,
3. `σ = τ ∘ rotAdd (G - s % G)`, i.e. the same statement with `τ` in place of
   `σ` (`sigma_eq_tau_rot`), and
4. `VertexCycleEq hG L S σ (Equiv.refl (α := Fin G))` — the truth's own vertex
   cycle, read from some start.

`same_altF_centralizer` is the conjunction of 1, 2 and 4;
`same_altF_vertexCycleEq` is 4 alone; `sigma_eq_tau_rot` is 3.

## Why this is the right shape, and what it is not

Step 1 is `AltF_succ` plus injectivity of `q ↦ nextPos q`; step 2 is
`Issue94TW7AltF.comm_nextPos_isRotation`, the *same* lemma tw7 used to
characterise `AltF = id`, applied one level up: instead of "one `AltF` equal to
the identity forces the listing to be a rotation", this says "two equal `AltF`s
force the two listings to differ by a rotation".  Step 4 then says the *only*
freedom left in `σ` once `AltF hG σ` is pinned is a rotation of the starts, and a
rotation of the starts is vertex-invisible (`BBTChords.IsRotation` composed with
`Issue94EulerianTheta.vertexCycleEq_of_isRotation` is the same content; here it
is obtained directly, since the witness `k` of `VertexCycleEq` is allowed to be
`origin hG`).

**Step 4 does not need `vtx`-shift-invariance**, and it must not be added:
`Issue94EulerianTheta.vtx_rotAdd_refuted` is a kernel-checked refutation of
`vtx (rotAdd s x) = vtx x`.  The argument therefore routes the hypothesis
`vtx (τ q) = vtx q` through the inverse rotation of step 3, which needs only the
group structure of `rotAdd` on the circle (`rotAdd_comp_inv`).

## What is proved, and what is not

* **Proved (this module, on top of the tree):**
  `rotAdd_comp_inv`, `succ_eq_of_altF_eq`, `qfun_comm_nextPos`,
  `qfun_isRotation`, `tau_eq_sigma_rot`, `sigma_eq_tau_rot`,
  `same_altF_vertexCycleEq`, `same_altF_centralizer`.
* **Not proved, and unchanged:** `BBTEulerian.EulerianCycleObstruction`
  (`hPevzner`), `BBTEulerian.UniqueEulerianCycle`,
  `BBTLadder.LadderVertexCycle`, `BBTLadder.CrossingChordsCoalesce`.  This module
  adds no hypothesis of the `BBT` kind and inhabits no `Prop` of the endpoint;
  it is a structural lemma about `AltF`, `Succ`, `rotAdd` and `vtx`.  No `sorry`,
  no `admit`, no `native_decide`, no new axiom, no definition changed.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AssemblyP1.Issue94SameAltF

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.Issue94TW7AltF

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-! ## 1. The one-step rotation group of the circle: an inverse shift -/

/-- **A rotation of fewer than one full turn has an inverse rotation, and the
inverse is the complementary shift `G - s`.**  Pure `Fin G` arithmetic: the
point-level fact that `rotAdd hG s ∘ rotAdd hG (G - s) = id` on a circle of `G`
positions.  Used below in `sigma_eq_tau_rot`, which needs the inverse rotation
because `vtx` is *not* shift-invariant
(`Issue94EulerianTheta.vtx_rotAdd_refuted`). -/
theorem rotAdd_comp_inv {s : ℕ} (hs : s < G) (x : Fin G) :
    rotAdd hG s (rotAdd hG (G - s) x) = x := by
  unfold rotAdd
  apply Fin.ext
  show (((x.val + (G - s)) % G) + s) % G = x.val
  have hstep := (mod_add_shl (x.val + (G - s)) s).symm
  rw [hstep]
  have h2 : x.val + (G - s) + s = x.val + G := by omega
  rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]

/-! ## 2. Same `AltF` ⟹ same successor permutation ⟹ rotation quotient -/

/-- **Same `AltF` gives same `Succ`.**  `AltF hG σ = Succ hG σ ∘ prevPos` and
`nextPos hG` is a bijection, so equal `AltF`s have equal `Succ`s.  In the
language of the front: `τ ρ τ⁻¹ = σ ρ σ⁻¹`, with `ρ = nextPos hG`. -/
theorem succ_eq_of_altF_eq (σ τ : Fin G ≃ Fin G)
    (h : ∀ q : Fin G, AltF hG τ q = AltF hG σ q) : Succ hG τ = Succ hG σ := by
  funext x
  have e := h (nextPos hG x)
  rwa [AltF_succ, AltF_succ] at e

/-- **The rotation quotient of two listings:** `qfun σ τ = σ⁻¹ ∘ τ`, the start
that `τ` reads where `σ` reads the start `0`.  This is the map the centralizer
lemma constrains. -/
def qfun (σ τ : Fin G ≃ Fin G) : Fin G → Fin G := fun y => σ.symm (τ y)

/-- **`qfun σ τ` commutes with the one-step rotation.**  From
`Succ hG τ = Succ hG σ`, i.e. `τ ρ τ⁻¹ = σ ρ σ⁻¹`: cancelling `σ` on the right
and `σ⁻¹` on the left turns `ρ` into `σ⁻¹ τ ρ (τ⁻¹ σ⁻¹) = qfun σ τ`. -/
theorem qfun_comm_nextPos (σ τ : Fin G ≃ Fin G)
    (h : ∀ x : Fin G, Succ hG τ x = Succ hG σ x) (y : Fin G) :
    qfun σ τ (nextPos hG y) = nextPos hG (qfun σ τ y) := by
  change σ.symm (τ (nextPos hG y)) = nextPos hG (σ.symm (τ y))
  have e : τ (nextPos hG (τ.symm (τ y))) = σ (nextPos hG (σ.symm (τ y))) := h (τ y)
  rw [Equiv.symm_apply_apply] at e
  have e2 := congrArg σ.symm e
  rw [Equiv.symm_apply_apply] at e2
  exact e2

/-- **Same `AltF` makes the rotation quotient a rotation of the circle.**  This
is the tw7 lemma `Issue94TW7AltF.comm_nextPos_isRotation` applied to
`qfun σ τ = σ⁻¹ ∘ τ`: a map commuting with `ρ` is a rotation.  Unconditional: no
`S`, no `L`, no `vtx`, no `Ukkonen`. -/
theorem qfun_isRotation (σ τ : Fin G ≃ Fin G)
    (h : ∀ q : Fin G, AltF hG τ q = AltF hG σ q) : IsRotation hG (qfun σ τ) := by
  refine comm_nextPos_isRotation hG (qfun σ τ) ?_
  intro y
  exact qfun_comm_nextPos hG σ τ (succ_eq_of_altF_eq hG σ τ h) y

/-- **Same `AltF` forces the two listings to differ by a rotation:**
`τ = σ ∘ rotAdd s` for some `s`. -/
theorem tau_eq_sigma_rot (σ τ : Fin G ≃ Fin G)
    (h : ∀ q : Fin G, AltF hG τ q = AltF hG σ q) :
    ∃ s : ℕ, ∀ x : Fin G, τ x = σ (rotAdd hG s x) := by
  obtain ⟨s, hs⟩ := qfun_isRotation hG σ τ h
  refine ⟨s, fun x => ?_⟩
  have e := congrArg σ (hs x)
  rw [qfun, Equiv.symm_apply_apply] at e
  exact e

/-- **... and the other way round: `σ = τ ∘ rotAdd (G - s % G)`**, i.e. the two
listings are rotations of each other.  This is step 3 of the centralizer lemma,
and it is the step that consumes the inverse rotation of `rotAdd_comp_inv`; it
is what lets the vertex-cycle conclusion be drawn without assuming that `vtx` is
shift-invariant (it is not: `Issue94EulerianTheta.vtx_rotAdd_refuted`). -/
theorem sigma_eq_tau_rot (σ τ : Fin G ≃ Fin G)
    (h : ∀ q : Fin G, AltF hG τ q = AltF hG σ q) :
    ∃ s : ℕ, ∀ x : Fin G, σ x = τ (rotAdd hG s x) := by
  obtain ⟨s, hs⟩ := tau_eq_sigma_rot hG σ τ h
  refine ⟨G - s % G, fun x => ?_⟩
  have e := hs (rotAdd hG (G - s % G) x)
  rw [rotAdd_mod hG s] at e
  have hstep : rotAdd hG (s % G) (rotAdd hG (G - s % G) x) = x := by
    have h1 : rotAdd hG (s % G) (rotAdd hG (G - s % G) x)
        = rotAdd hG (s % G + (G - s % G)) x := rotAdd_add hG _ _ _
    have h2 : s % G + (G - s % G) = G := by
      have hslt : s % G < G := Nat.mod_lt _ hG
      omega
    rw [h1, h2, rotAdd_full]
  rw [hstep] at e
  exact e.symm

/-! ## 3. The centralizer lemma and its vertex-cycle consequence -/

/-- **Vertex-cycle consequence of the centralizer lemma.**  If `τ` preserves
`vtx` pointwise and `AltF hG τ = AltF hG σ` pointwise, then `σ` walks the truth's
own vertex cycle --- the object `BBTEulerian.EulerianCycleObstruction`
quantifies over --- read from the start `σ 0`, with witnessing shift `origin hG`.

The proof is `sigma_eq_tau_rot` (i.e. `σ = τ ∘ rotAdd s`) plus
`vtx (τ ·) = vtx (·)`; note that it uses **no** shift-invariance of `vtx`, which
is refuted in `Issue94EulerianTheta.vtx_rotAdd_refuted`. -/
theorem same_altF_vertexCycleEq (τ σ : Fin G ≃ Fin G)
    (hvtx : ∀ q : Fin G, vtx hG L S (τ q) = vtx hG L S q)
    (hAlt : ∀ q : Fin G, AltF hG τ q = AltF hG σ q) :
    VertexCycleEq hG L S σ (Equiv.refl (α := Fin G)) := by
  obtain ⟨s, hs⟩ := sigma_eq_tau_rot hG σ τ hAlt
  refine ⟨origin hG, fun i => ?_⟩
  show vtx hG L S (σ i) = vtx hG L S (rotAdd hG 0 i)
  have hq := hvtx (rotAdd hG s i)
  rw [hs i, hq, rotAdd_zero hG i]

/-- **THE CENTRALIZER LEMMA.**  If `τ` preserves `vtx` pointwise and
`AltF hG τ = AltF hG σ` pointwise, then

* the two rotation-conjugates agree, `τ ρ τ⁻¹ = σ ρ σ⁻¹`;
* the quotient `q = σ⁻¹ ∘ τ` is a **rotation of the circle** (`IsRotation`,
  i.e. a genomic rotation of the starts), so `τ` and `σ` are rotations of each
  other (`sigma_eq_tau_rot`);
* and the truth's own vertex cycle is the vertex cycle of `σ`
  (`same_altF_vertexCycleEq`). -/
theorem same_altF_centralizer (τ σ : Fin G ≃ Fin G)
    (hvtx : ∀ q : Fin G, vtx hG L S (τ q) = vtx hG L S q)
    (hAlt : ∀ q : Fin G, AltF hG τ q = AltF hG σ q) :
    (∀ x : Fin G, τ (nextPos hG (τ.symm x)) = σ (nextPos hG (σ.symm x))) ∧
      IsRotation hG (qfun σ τ) ∧
      VertexCycleEq hG L S σ (Equiv.refl (α := Fin G)) := by
  have h1 : Succ hG τ = Succ hG σ := succ_eq_of_altF_eq hG σ τ hAlt
  refine ⟨fun x => h1 x, qfun_isRotation hG σ τ hAlt,
    same_altF_vertexCycleEq hG L S τ σ hvtx hAlt⟩

end AssemblyP1.Issue94SameAltF

#print axioms AssemblyP1.Issue94SameAltF.rotAdd_comp_inv
#print axioms AssemblyP1.Issue94SameAltF.succ_eq_of_altF_eq
#print axioms AssemblyP1.Issue94SameAltF.qfun_comm_nextPos
#print axioms AssemblyP1.Issue94SameAltF.qfun_isRotation
#print axioms AssemblyP1.Issue94SameAltF.tau_eq_sigma_rot
#print axioms AssemblyP1.Issue94SameAltF.sigma_eq_tau_rot
#print axioms AssemblyP1.Issue94SameAltF.same_altF_centralizer
#print axioms AssemblyP1.Issue94SameAltF.same_altF_vertexCycleEq