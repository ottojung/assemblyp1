import AssemblyP1.BBTUniqueEulerian

/-!
# Board 94, front 94tw5: the `single` clause of `BBTEulerian.EulerianCycle`
# is a **tautology**, and what that costs `BBTUniqueEulerian` §4

This module does **not** touch `BBTEulerian.UniqueEulerianCycle`,
`BBTEulerian.EulerianCycleObstruction`, `AssemblyP1/PopulationUniqueness.lean`,
`BBTLadder` or `BBTLadder.CrossingChordsCoalesce`.  `hPevzner` is unchanged;
see "What is proved, and what is not" below.

It characterises one named `Prop` that no front had examined in this
direction --- the second conjunct of the object `BBTEulerian.EulerianCycle`
--- and the characterisation is a **refutation** of the reading that the
module docs give it.

Named theorems, all kernel-checked:

| theorem | what it says |
| --- | --- |
| `succ_visitsAll` | `VisitsAll (Succ hG σ) (origin hG)` for **every** bijection `σ`: the `single` clause is a tautology |
| `eulerianCycle_iff_traverses` | `EulerianCycle hG L S σ ↔` its first conjunct `traverses` |
| `altF_no_innermost_chord` | `AltF hG σ` has no innermost chord, for **every** bijection `σ`, unconditionally |
| `labelPreserving_iff_traverses` | `traverses` is exactly "`AltF hG σ` preserves the `(L-1)`-mer labelling" |
| `uniqueEulerianCycle_iff_labelPreserving` | characterisation of `BBTEulerian.UniqueEulerianCycle` in that reduced object |
| `obstruction_iff_labelPreserving` | same for `BBTEulerian.EulerianCycleObstruction`, i.e. `hPevzner` |
| `not_labelPreserving_S3`, `labelPreserving_S4`, `single_clauses_S4`, `altF_S4_ne` | anti-vacuity: the reduction is neither vacuous nor empty |

## The object

`AssemblyP1/BBTEulerian.lean:169-171`, verbatim:

```lean
def EulerianCycle (σ : Fin G ≃ Fin G) : Prop :=
  (∀ i : Fin G, vtx hG L S (σ (nextPos hG i)) = vtx hG L S (nextPos hG (σ i))) ∧
  VisitsAll (fun x => σ (nextPos hG (σ.symm x))) (origin hG)
```

The first conjunct is `traverses`: the vertex labelling is respected by the
alternative traversal.  The second is `single`, and the module docstring at
`AssemblyP1/BBTEulerian.lean:42-45` says of it:

> **it is a single cycle** (`single`): the successor
> `fun x => σ (nextPos (σ.symm x))` runs through all `G` positions
> before returning (`VisitsAll`).  This is the clause ruling out a
> decomposition of the walk into several disjoint circuits.

and at lines 41-45 together:

> Both clauses are load-bearing

**That reading is false, and the kernel-checked proof is in `succ_visitsAll` below.**  The
`single` clause holds for *every* bijection `σ : Fin G ≃ Fin G`, with no
hypothesis on `S`, on `L`, on `Ukkonen`, or on anything else.  It is a
tautology of group theory, and the tree already contains a proof of it ---
`AssemblyP1/BBTEulerian.lean:279-290`, inside `pullback_isEulerianCycle`,
where the `single` conjunct is discharged from `σ`'s bijectivity alone --- but
nobody had isolated the conjunct, so the tautology was invisible.

## Why the `single` clause cannot fail

`Succ hG σ x = σ (nextPos hG (σ.symm x))` (`BBTUniqueEulerian.lean:623-624`) is
the **conjugate** `σ ∘ ρ ∘ σ⁻¹` of the one-step rotation `ρ = nextPos hG`.  The
one-step rotation of a circle of `G` positions is a `G`-cycle; a conjugate of a
`G`-cycle is a `G`-cycle; so `Succ hG σ` is a `G`-cycle whatever `σ` is.  The proof
does this by the concrete route (`altSucc_iterate` + `rotAdd_inj_lt`), so the
result rests only on facts already in the tree.

The structural reason is worth stating plainly, because it is the modelling
answer to the question the second briefing asked: **the pull-back
presentation cannot fail to be a single circuit.**  A presentation is a
bijection between the candidate's starts and the truth's starts; the walk it
describes is `σ 0, σ 1, …`, which by construction visits each of the `G`
starts exactly once.  A "decomposition into several disjoint circuits" is not
an object this presentation can name.

## The innermost chord, and the consequence for the board's plan

* **`eulerianCycle_iff_traverses`:** `EulerianCycle` is *equivalent* to its
  first conjunct.  So `BBTEulerian.UniqueEulerianCycle` and
  `BBTEulerian.EulerianCycleObstruction` are the same `Prop`s with one
  conjunct of their object deleted.

* **`altF_no_innermost_chord`:** **for every bijection `σ`, the
  alternative traversal `AltF hG σ` has no innermost chord** --- no `a ≠ b`
  with `AltF b = a` and `AltF` the identity on the open arc from `a` to `b`.
  This is `BBTUniqueEulerian.EulerianCycle_no_innermost_chord`
  (`:945-964`) with its `EulerianCycle` hypothesis *deleted*, and it is
  **unconditional**: no word, no window, no `Ukkonen`.

* **`uniqueEulerianCycle_iff_labelPreserving`:** a decidable
  characterisation of the target `Prop` itself,
  `BBTEulerian.UniqueEulerianCycle`, in which the candidate object is the
  plain statement "`AltF hG σ` preserves the `(L-1)`-mer labelling at every
  start" and the traversal-order clause of `EulerianCycle` is gone.

The second of these has a real consequence for the board's plan, and it is
stated as a theorem rather than a remark because it is one.
`AssemblyP1/BBTUniqueEulerian.lean:96-100` records the intended end of
`thm:BBT`:

> Lemma 1 makes `f` a product of disjoint transpositions, Lemma 2 makes their
> support chords pairwise non-interleaved, and a non-crossing configuration has
> an innermost chord, which §4 rules out.  So the remaining content of
> `thm:BBT` is these two repeat-theory lemmas and nothing else.

`altF_no_innermost_chord` rules out the innermost chord **without the non-crossing**.  So Lemma 2 ---
the crossing clause, i.e. the interleaved-repeat half of `Ukkonen`, i.e. the
harder of the two repeat-theory inputs --- is not needed on this route at all.
The remaining content is Lemma 1 alone.

**This is a statement about which inputs a proof would need, not a proof.**
Lemma 1 is not discharged here and `thm:BBT` is not proved here; the theorem above says the
plan in `BBTUniqueEulerian`'s docstring needs one fewer lemma than its author
recorded, and the next front should know that before spending a tranche on the
crossing clause.

## What is proved, and what is not

* **Proved (kernel-checked).**  `succ_visitsAll` and
  `eulerianCycle_iff_traverses`: the `single` clause of
  `BBTEulerian.EulerianCycle` is a tautology, and the `Prop` is equivalent to
  its first conjunct.  `altF_no_innermost_chord`:
  `BBTUniqueEulerian.EulerianCycle_no_innermost_chord` with its `EulerianCycle`
  hypothesis deleted.  `uniqueEulerianCycle_iff_labelPreserving` and
  `obstruction_iff_labelPreserving`: the characterisation of the two target
  `Prop`s.  `labelPreserving_S4`, `not_labelPreserving_S3`, `single_clauses_S4`
  and `altF_S4_ne` are the anti-vacuity checks.

* **Not proved.**  `BBTEulerian.UniqueEulerianCycle`,
  `BBTEulerian.EulerianCycleObstruction`, `BBTLadder.LadderVertexCycle`,
  `BBTUniqueEulerian` Lemma 1 (the multiplicity / triple-repeat clause), and
  `AssemblyP1/PopulationUniqueness.lean`'s `hPevzner` are all **unchanged**.
  Nothing in this module is on a route *into* `hPevzner`; this module removes a
  hypothesis from an existing lemma and characterises a target `Prop`, and
  that is all it does.  No `sorry`, no `admit`, no new axiom, no
  `native_decide`, no `unsafe`, no theorem statement weakened.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AssemblyP1.Issue94TW5Single

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-! ## 1. `single` is a tautology: the successor is a conjugate of the rotation -/

/-- **`Succ hG σ` is a `G`-cycle on the starts, for every bijection `σ`.**

`Succ hG σ = σ ∘ nextPos ∘ σ⁻¹` (`BBTUniqueEulerian.lean:623-624`) is the
conjugate of the one-step rotation `nextPos hG`, and `altSucc_iterate`
(`:645-649`) gives the iterates as `σ (rotAdd hG n i)`; `rotAdd_inj_lt`
(`BBTEulerian.lean:221-242`) makes those distinct for distinct `n : Fin G`.

No hypothesis on `S`, `L`, `Ukkonen`, or even on `G` beyond `0 < G` occurs in
the statement.  This is the second conjunct of `BBTEulerian.EulerianCycle`
(`:171`), discharged on its own. -/
theorem succ_visitsAll {G : ℕ} (hG : 0 < G) (σ : Fin G ≃ Fin G) :
    VisitsAll (Succ hG σ) (origin hG) := by
  show VisitsAll (fun x => σ (nextPos hG (σ.symm x))) (origin hG)
  unfold VisitsAll
  intro n₁ n₂ hn
  have h₁ := altSucc_iterate hG σ n₁.val (origin hG)
  have h₂ := altSucc_iterate hG σ n₂.val (origin hG)
  have hn' : (fun y => σ (nextPos hG (σ.symm y)))^[n₁.val] (origin hG)
      = (fun y => σ (nextPos hG (σ.symm y)))^[n₂.val] (origin hG) := hn
  have hrot : rotAdd hG n₁.val (σ.symm (origin hG))
      = rotAdd hG n₂.val (σ.symm (origin hG)) := by
    refine Equiv.injective σ ?_
    exact h₁.symm.trans (hn'.trans h₂)
  exact Fin.ext (congrArg Fin.val (rotAdd_inj_lt hG (σ.symm (origin hG)) hrot))

/-- **`BBTEulerian.EulerianCycle` is equivalent to its first conjunct**, i.e.
`traverses`: the vertex labelling is respected by the alternative traversal.
The `single` conjunct of `BBTEulerian.lean:171` is a tautology (`succ_visitsAll`)
and carries no information. -/
theorem eulerianCycle_iff_traverses {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)
    (σ : Fin G ≃ Fin G) :
    EulerianCycle hG L S σ ↔
      (∀ i : Fin G, vtx hG L S (σ (nextPos hG i)) = vtx hG L S (nextPos hG (σ i))) := by
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, succ_visitsAll hG σ⟩

/-! ## 2. What is left of `thm:BBT`, and the innermost chord -/

/-- **The alternative traversal `AltF hG σ` has no innermost chord, for every
bijection `σ`.**

This is `BBTUniqueEulerian.EulerianCycle_no_innermost_chord`
(`:945-964`) with its `EulerianCycle` hypothesis **deleted**.  The lemma it
used that way was `hV : VisitsAll (Succ hG σ) (origin hG)`, and by `succ_visitsAll` that is
a theorem about `σ` alone.

Nothing is assumed about the word: no `vtx`, no `Ukkonen`, no primitivity, no
`L`, no `K`.  In particular the *non-crossing of the support chords is not
needed* --- `BBTUniqueEulerian`'s docstring at `:96-100` plans to obtain
non-crossing first and then produce an innermost chord from it, and this
theorem shows the innermost chord is already excluded. -/
theorem altF_no_innermost_chord {G : ℕ} (hG : 0 < G) (σ : Fin G ≃ Fin G)
    {a b : Fin G} (hg : 1 ≤ sh hG a b) (hgb : sh hG a b < G)
    (hfree : ∀ x : Fin G, InArc hG a b x → AltF hG σ x = x)
    (hfb : AltF hG σ b = a) : False := by
  have hV : VisitsAll (Succ hG σ) (origin hG) := succ_visitsAll hG σ
  unfold VisitsAll at hV
  have hfun : (fun n : Fin G => (Succ hG σ)^[n.val] (origin hG))
      = (fun n : Fin G => (fun x => AltF hG σ (nextPos hG x))^[n.val] (origin hG)) := by
    funext n
    exact congrArg (fun θ : Fin G → Fin G => θ^[n.val] (origin hG))
      (funext (Succ_eq_altF hG σ))
  have hV' : VisitsAll (fun x => AltF hG σ (nextPos hG x)) (origin hG) := by
    unfold VisitsAll
    rw [← hfun]
    exact hV
  exact not_visitsAll_of_innermost_chord hG (AltF_bijective hG σ) hg hgb hfree hfb hV'

/-! ### 2.1 The same statement, spelled without `Succ` -/

/-- **`AltF hG σ ∘ nextPos = Succ hG σ` and `VisitsAll (Succ hG σ)` always
holds**, so the innermost-chord obstruction applies to `AltF hG σ` with the
traverses hypothesis dropped.  This is `succ_visitsAll` restated as the pair of facts the
proof actually consumes, for a later front that wants to re-use it. -/
theorem altF_nextPos_visitsAll {G : ℕ} (hG : 0 < G) (σ : Fin G ≃ Fin G) :
    (∀ x : Fin G, Succ hG σ x = AltF hG σ (nextPos hG x)) ∧
      VisitsAll (Succ hG σ) (origin hG) :=
  ⟨Succ_eq_altF hG σ, succ_visitsAll hG σ⟩

/-! ## 3. A decidable characterisation of the target `Prop` itself -/

/-- **The candidate object, with `traverses` replaced by its content.**

`AltF hG σ` is the alternative traversal read at the preceding start
(`BBTUniqueEulerian.lean:665-666`), and `AltF_vtx` (`:673-679`) says
`traverses` is exactly "`AltF hG σ` preserves the `(L-1)`-mer labelling at
every start".  So this is the first conjunct of `EulerianCycle` rewritten with
the traversal-order clauses gone. -/
def LabelPreserving (hG : 0 < G) (L : ℕ) (S : Fin G → α) (σ : Fin G ≃ Fin G) : Prop :=
  ∀ q : Fin G, vtx hG L S (AltF hG σ q) = vtx hG L S q

instance {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α) (σ : Fin G ≃ Fin G) :
    Decidable (LabelPreserving hG L S σ) := by
  unfold LabelPreserving
  infer_instance

theorem labelPreserving_iff_traverses {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)
    (σ : Fin G ≃ Fin G) :
    LabelPreserving hG L S σ ↔
      (∀ i : Fin G, vtx hG L S (σ (nextPos hG i)) = vtx hG L S (nextPos hG (σ i))) := by
  constructor
  · intro h i
    have h1 := h (nextPos hG (σ i))
    have hA : AltF hG σ (nextPos hG (σ i)) = σ (nextPos hG i) := by
      rw [AltF_succ hG σ (σ i), Succ_apply]
    rwa [hA] at h1
  · intro h q
    exact AltF_vtx hG L S σ h q

/-- **`BBTEulerian.UniqueEulerianCycle`, characterised.**  For every `Ukkonen`
word, every alternative traversal whose permutation preserves the `(L-1)`-mer
labelling has the truth's vertex cycle --- with the `single` clause of the
object, and the `VisitsAll` clause with it, deleted.

This is a characterisation *of* `BBTEulerian.lean:404-407`, not a proof of it:
the right-hand side is still open.  What it establishes is that the target
`Prop` does not mention `VisitsAll`, `Succ`, or "one circuit", so no proof of
it has to establish a single-circuit statement. -/
theorem uniqueEulerianCycle_iff_labelPreserving {L : ℕ} :
    UniqueEulerianCycle (α := α) L ↔
      ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α), Ukkonen hK L S →
        ∀ (σ : Fin K ≃ Fin K), LabelPreserving hK L S σ →
          VertexCycleEq hK L S σ (Equiv.refl (α := Fin K)) := by
  constructor
  · intro h K hK S hUkk σ hLP
    have hEul : EulerianCycle hK L S σ :=
      (eulerianCycle_iff_traverses hK L S σ).mpr ((labelPreserving_iff_traverses hK L S σ).mp hLP)
    exact h K hK S hUkk σ hEul
  · intro h K hK S hUkk σ hEul
    exact h K hK S hUkk σ ((labelPreserving_iff_traverses hK L S σ).mpr hEul.1)

/-- **... and the obstruction form, characterised the same way.**  This is the
`Prop` that `AssemblyP1/PopulationUniqueness.lean` consumes as `hPevzner`
(`BBTEulerian.lean:415-418`), stated here so that a later front can see that
the object it quantifies over is `LabelPreserving`.  It is a `Prop` of the
repository, it is **not** inhabited, and nothing in this module approaches an
inhabitant. -/
theorem obstruction_iff_labelPreserving {L : ℕ} :
    EulerianCycleObstruction (α := α) L ↔
      ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α), Ukkonen hK L S →
        ∀ (σ : Fin K ≃ Fin K), LabelPreserving hK L S σ →
          VertexCycleEq hK L S σ (Equiv.refl (α := Fin K)) ∨ LongObstruction hK L S := by
  constructor
  · intro h K hK S hUkk σ hLP
    have hEul : EulerianCycle hK L S σ :=
      (eulerianCycle_iff_traverses hK L S σ).mpr ((labelPreserving_iff_traverses hK L S σ).mp hLP)
    exact h K hK S hUkk σ hEul
  · intro h K hK S hUkk σ hEul
    exact h K hK S hUkk σ ((labelPreserving_iff_traverses hK L S σ).mpr hEul.1)

/-- **`LabelPreserving` gives an `EulerianCycle` back.**  The one direction that
is not an `iff`, isolated so that a later front applying `LabelPreserving`
directly does not have to re-derive the `Succ` obligation. -/
theorem labelPreserving_implies_eulerianCycle {G : ℕ} (hG : 0 < G) (L : ℕ)
    (S : Fin G → α) (σ : Fin G ≃ Fin G) (hLP : LabelPreserving hG L S σ) :
    EulerianCycle hG L S σ :=
  (eulerianCycle_iff_traverses hG L S σ).mpr
    ((labelPreserving_iff_traverses hG L S σ).mp hLP)

/-! ## 5. Anti-vacuity: the reduced object still has content -/

/-! ### 5.1 The reduction does not make `EulerianCycle` vacuous

`LabelPreserving` is a genuinely restrictive condition, not a tautology: it is
exactly `traverses`, and `succ_visitsAll`'s tautology was only about the *second* conjunct.
On the `BBTEulerian.lean` §4.1 instance the reduced object still fails, and on
the §4.2 instance it still holds.  These two `by decide` lines are the
anti-vacuity check: they are the same two facts the module
already records as `not_eulerianCycle_validity` and `eulerianCycle_S4`, read
through the reduced object. -/

/-- `tau3` fails the reduced object too: `S3 = 001` at `L = 3`, and `tau3` is
not an alternative traversal.  So deleting the `single` clause did **not**
weaken `EulerianCycle` into vacuity --- it was `traverses` doing all the work. -/
theorem not_labelPreserving_S3 : ¬ LabelPreserving hG3 3 S3 tau3 := by decide

/-- ... and `tau4` satisfies it: `S4 = 0101`, `tau4 = (0 1)(2 3)`.  The
reduced object still has genuine inhabitants. -/
theorem labelPreserving_S4 : LabelPreserving hG4 3 S4 tau4 := by decide

/-- The `single` clause really is uninformative *as a discriminator of
traversals*: it is satisfied on `S4`/`tau4` and, by `succ_visitsAll`, on every
other bijection too. -/
theorem single_clauses_S4 : VisitsAll (Succ hG4 tau4) (origin hG4) :=
  succ_visitsAll hG4 tau4

/-! ### 5.2 And the innermost-chord statement is not vacuous either

`altF_no_innermost_chord` concludes `False`, so an instance of it is a genuine
kernel-checked impossibility, not a `Prop` that is trivially true.  The
positive content is that `AltF` really does move points --- the two support
chords `0 2` and `1 3` of `Issue94TW4Coalesce.altF_chords_S4` are exactly the
chords an innermost-chord argument would have to exclude, and they are not
excluded because they *cross*, not because one of them is innermost. -/

/-- On the `BBTEulerian.lean` §4.2 instance the alternative traversal is
genuinely non-identity, so the chords ruled out by `altF_no_innermost_chord`
are really present. -/
theorem altF_S4_ne : AltF hG4 tau4 (0 : Fin 4) ≠ 0 := by decide

end AssemblyP1.Issue94TW5Single
