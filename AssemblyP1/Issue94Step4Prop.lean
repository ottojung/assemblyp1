import AssemblyP1.Issue94OrbitGeneral

/-!
# Board 94, front A: §5 step 4 — an inhabitant of the *guarded* form, and a
# refutation of `Issue89GapMap.Step4_slide_iterates` as it is written

## 1. The unconditional `pairBack` bound: the bridge the previous front missed

Front 94a4 recorded, as its first "not established" item, that the library
`pairBack` bound `pairBack < G` is stated under `IsPrimitive` whereas the
unconditional bound it used is a property of the computable restatement
`pairBackC` only, and that bridging the two is "genuine new work about the word
layer".  That diagnosis was too pessimistic.  Two facts close it, both
unconditional:

* `Issue94OrbitSearch.pairBackC_eq` (`:87`) proves
  `pairBackC hK S a b = pairBack hK S a b` with **no** `IsPrimitive`, no `P2`
  and no primitivity of any kind; so the unconditional `pairBackC ≤ K` of
  `Issue94OrbitGeneral.pairBackC_le_K` transports to `pairBack ≤ K` for free.
* Independently, `P2RepeatResidual.pairBack_spec` (`:426`) already states
  `pairBack hG S a b ≤ G` outright, because `backSet` is a filter of
  `Icc 0 G`.  `pairBack_le_K` below is just that conjunct.

So `pairBack ≤ K` is available with no hypothesis, and the primitivity-
conditional `pairBack_lt_G` is **not** on the critical path.

## 2. The guard shapes are different propositions

`SlideGuards hK a b c d j` (`Issue94IterSlide`:344) is the **conjunction**
`slide j c ≠ a ∧ slide j c ≠ b ∧ slide j d ≠ a ∧ slide j d ≠ b`.
`slide hK n x` is *definitionally* `rotAdd hK (K - n) x` (`Issue94IterSlide`:55),
so in `rotAdd` coordinates the guarded statement wants

```lean
(∀ j : ℕ, j ≤ t → rotAdd hK (K - j) c ≠ a → ... → rotAdd hK (K - j) d ≠ b) →
```

— the four non-equalities as **premises**, i.e. the guard is an *assumption*.

But `Issue89GapMap.Step4_slide_iterates` (`:443`) is written as

```lean
(∀ j : ℕ, j ≤ t → rotAdd hK (K - j) c ≠ a → ... → rotAdd hK (K - j) d ≠ b) →
  Interleaved ...
```

Lean parses this as: the hypothesis is the function
`∀ j ≤ t, A → B → C → D`, i.e. `∀ j ≤ t, (A → B → C → D)`, whose body is the
**implication chain** `A → B → C → D`.  That is a different `Prop` from
`∀ j ≤ t, A ∧ B ∧ C ∧ D`.  It is *weaker* as a hypothesis in the cases that
matter: it is satisfied vacuously whenever `A` or `B` fails, i.e. exactly when
the slid pair `c, d` has collided with `a` or `b` — which is precisely the case
the guard is there to exclude.  In particular it is satisfied by the
colliding configurations themselves.

The two shapes are **not** equivalent, and the difference is not cosmetic: the
guarded form is proved below (`step4_guarded`), and the implication-shaped
form is **false**, with a kernel-checked counterexample
(`not_Step4_slide_iterates_1`).

## 3. What is NOT established here

* I did **not** produce an inhabitant of
  `Issue89GapMap.Step4_slide_iterates` as written.  It is refutable, and I
  refute it in the kernel.  Per the brief's rule 6 this is a result, not a
  failure.
* I did **not** edit `Issue89GapMap.lean` to repair the statement; that file is
  the gap map and another front reads it.  The repair is stated here as a
  separate definition `Step4_slide_iterates_guarded` and proved.
* I did **not** touch `Issue94OrbitSearch.lean`, `Issue94IterSlide.lean` or
  `Issue94OrbitGeneral.lean`.
-/

namespace AssemblyP1.Issue94Step4Prop

open AssemblyP1
open AssemblyP1.PopulationReduction
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.P2RepeatResidual
open AssemblyP1.SourceFaithfulIs
open AssemblyP1.BBTChords
open AssemblyP1.Issue89GapMap
open AssemblyP1.Issue94IterSlide
open AssemblyP1.Issue94OrbitSearch
open AssemblyP1.Issue94OrbitGeneral

variable {K : ℕ}

/-- **The unconditional bound on the library `pairBack`.**  A conjunct of the
library's own `pairBack_spec`; no hypothesis of any kind.  This is the second,
independent route to the bound (the first is `pairBackC_eq` plus
`pairBackC_le_K`) and it is the one used by the guarded inhabitant. -/
theorem pairBack_le_K (hK : 0 < K) (S : Fin K → Bin) (a b : ℕ) :
    pairBack hK S a b ≤ K := (pairBack_spec hK S a b).2

/-- The two objects coincide, unconditionally.  This is the bridge 94a4
believed was missing; it is `Issue94OrbitSearch.pairBackC_eq`. -/
theorem pairBackC_eq' (hK : 0 < K) (S : Fin K → Bin) (a b : ℕ) :
    pairBackC hK S a b = pairBack hK S a b := pairBackC_eq hK S a b

/-- The guard predicate of `Issue94IterSlide` in the `rotAdd` coordinates that
`Issue89GapMap` writes in.  Definitional: `slide hK n x = rotAdd hK (K - n) x`. -/
theorem slideGuards_iff (hK : 0 < K) (a b c d : Fin K) (j : ℕ) :
    SlideGuards hK a b c d j ↔
      rotAdd hK (K - j) c ≠ a ∧ rotAdd hK (K - j) c ≠ b ∧
      rotAdd hK (K - j) d ≠ a ∧ rotAdd hK (K - j) d ≠ b :=
  Iff.rfl

/-- The implication-shaped guard, spelled out.  This is what Lean reads out of
`Issue89GapMap.Step4_slide_iterates` (`:443`), and it is *not* `SlideGuards`. -/
def WeakGuards (hK : 0 < K) (a b c d : Fin K) (t : ℕ) : Prop :=
  ∀ j : ℕ, j ≤ t → rotAdd hK (K - j) c ≠ a → rotAdd hK (K - j) c ≠ b →
    rotAdd hK (K - j) d ≠ a → rotAdd hK (K - j) d ≠ b

/-- The same guard with its index carried as a `Fin (K + 1)`, so that the whole
statement is `Decidable` (a `∀` over `ℕ` with a side condition does not admit a
nested `Decidable` instance; a `Fintype` index does, as in
`Issue94OrbitSearch.IterStep4`). -/
def WeakGuardsB (hK : 0 < K) (a b c d : Fin K) (t : ℕ) : Prop :=
  ∀ j : Fin (K + 1), j.val ≤ t → rotAdd hK (K - j.val) c ≠ a →
    rotAdd hK (K - j.val) c ≠ b → rotAdd hK (K - j.val) d ≠ a →
    rotAdd hK (K - j.val) d ≠ b

/-! ## 4. The guarded statement, and its inhabitant

This is the statement §5 step 4 actually invokes, and the one
`Issue94IterSlide` and `Issue94OrbitGeneral` were built for: the four
non-collisions are *hypotheses* about every intermediate `j ≤ t`. -/

/-- **§5 step 4, in the shape §5 step 4 means**: the pair `c, d` may be slid
`t` steps down its backward list keeping its interleaving with `a, b`, provided
no intermediate position `j ≤ t` collides with `a` or `b`.  Identical to
`Step4_slide_iterates` except that the guard is the conjunction
`SlideGuards` rather than the implication chain `WeakGuards`. -/
def Step4_slide_iterates_guarded (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → Bin) (a b c d : Fin K),
    a ≠ b → c ≠ d →
    vtx hK L S a = vtx hK L S b → vtx hK L S c = vtx hK L S d →
    Interleaved (mkGenome hK S) a b c d →
    ∀ t : ℕ, t ≤ pairBack hK S c.val d.val →
      (∀ j : ℕ, j ≤ t → SlideGuards hK a b c d j) →
      Interleaved (mkGenome hK S) a b (rotAdd hK (K - t) c) (rotAdd hK (K - t) d)

/-- **The inhabitant of the guarded form of §5 step 4.**  For every `L`, for
every circle size, with no primitivity and no `P2` hypothesis.

The proof is `step4_slide_iterates_word` at `t`; the only thing it needs beyond
the interleaving and the guards is `t ≤ K`, which comes from the shift bound
`t ≤ pairBack hK S c.val d.val` together with the unconditional
`pairBack ≤ K` (`pairBack_le_K`).  The two `vtx` hypotheses and the parameters
`L`, `a ≠ b`, `c ≠ d` do not occur in the conclusion and are carried unused:
the result is a statement purely about the circle. -/
theorem step4_guarded (L : ℕ) : Step4_slide_iterates_guarded L :=
  fun K hK S a b c d _hab _hcd _hvab _hvcd hI t ht hg => by
    have _hKne : NeZero K := ⟨hK.ne'⟩
    have htK : t ≤ K := le_trans ht (pairBack_le_K hK S c.val d.val)
    exact step4_slide_iterates_word hK a b c d hI t htK hg

/-- The same, with the guards written out in the `rotAdd` coordinates of
`Issue89GapMap` (as a conjunction, which is the point). -/
theorem step4_guarded_rotAdd (L : ℕ) :
    ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → Bin) (a b c d : Fin K),
      a ≠ b → c ≠ d →
      vtx hK L S a = vtx hK L S b → vtx hK L S c = vtx hK L S d →
      Interleaved (mkGenome hK S) a b c d →
      ∀ t : ℕ, t ≤ pairBack hK S c.val d.val →
        (∀ j : ℕ, j ≤ t →
          rotAdd hK (K - j) c ≠ a ∧ rotAdd hK (K - j) c ≠ b ∧
          rotAdd hK (K - j) d ≠ a ∧ rotAdd hK (K - j) d ≠ b) →
        Interleaved (mkGenome hK S) a b (rotAdd hK (K - t) c) (rotAdd hK (K - t) d) :=
  fun K hK S a b c d hab hcd hvab hvcd hI t ht hg =>
    step4_guarded L K hK S a b c d hab hcd hvab hvcd hI t ht
      (fun j hj => (slideGuards_iff hK a b c d j).mpr (hg j hj))

/-- The same theorem with the shift bound taken against the computable
restatement `pairBackC`, so that the `pairBackC_eq` bridge is *exercised* on
the critical path rather than merely cited. -/
theorem step4_guarded_pairBackC (L : ℕ) :
    ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → Bin) (a b c d : Fin K),
      a ≠ b → c ≠ d →
      vtx hK L S a = vtx hK L S b → vtx hK L S c = vtx hK L S d →
      Interleaved (mkGenome hK S) a b c d →
      ∀ t : ℕ, t ≤ pairBackC hK S c.val d.val →
        (∀ j : ℕ, j ≤ t → SlideGuards hK a b c d j) →
        Interleaved (mkGenome hK S) a b (rotAdd hK (K - t) c) (rotAdd hK (K - t) d) :=
  fun K hK S a b c d hab hcd hvab hvcd hI t ht hg => by
    have _hKne : NeZero K := ⟨hK.ne'⟩
    have ht' : t ≤ pairBack hK S c.val d.val := by
      simpa only [pairBackC_eq'] using ht
    exact step4_guarded L K hK S a b c d hab hcd hvab hvcd hI t ht' hg

/-- At `L = 1` every `vtx` is a function out of `Fin 0` and so all of them are
equal.  This is why dropping the two `vtx` hypotheses from `Step4LitC` loses
nothing at `L = 1`, and hence why the `decide` really does refute the library
`Prop` and not a weakened shadow of it. -/
theorem vtx_eq_vtx (hK : 0 < K) (S : Fin K → Bin) (a b : Fin K) :
    vtx hK 1 S a = vtx hK 1 S b :=
  funext fun i => Fin.elim0 i

/-! ## 5. `Step4_slide_iterates` as written is FALSE

`Step4LitK K` is the literal guard shape of `Issue89GapMap.Step4_slide_iterates`
at a fixed circle size `K`: the guard is the **implication chain**
`WeakGuards`, not the conjunction `SlideGuards`.  The two `vtx` hypotheses of
the library `Prop` are dropped, which makes this statement *stronger*, and the
shift bound is taken against `pairBackC`, which `pairBackC_eq` proves is
`pairBack`.  Shifts and guards are `Fin (K + 1)`-indexed, as in
`Issue94OrbitSearch.IterStep4`, so that the whole statement is decidable. -/

/-- The literal statement of `Issue89GapMap.Step4_slide_iterates` at a fixed
circle size, with the guard taken in the implication-chain form that Lean
actually reads out of `:443`.

It is stated on `InterleavedStarts` rather than on `Interleaved` for
decidability only: `Issue94IterSlide.interleaved_iff` proves the two are
equivalent at every occurrence, so this is the same `Prop` up to that `Iff`. -/
def Step4LitK (K : ℕ) (hK : 0 < K) [NeZero K] : Prop :=
  ∀ (S : Fin K → Bin) (a b c d : Fin K) (t : Fin (K + 1)),
    a ≠ b → c ≠ d →
    InterleavedStarts hK a b c d →
    t.val ≤ pairBackC hK S c.val d.val →
    WeakGuardsB hK a b c d t.val →
    InterleavedStarts hK a b (rotAdd hK (K - t.val) c) (rotAdd hK (K - t.val) d)

instance instStep4LitK (K : ℕ) (hK : 0 < K) [NeZero K] : Decidable (Step4LitK K hK) := by
  unfold Step4LitK WeakGuardsB; infer_instance

/-- A `Fin (K + 1)`-indexed guard of the implication shape is the same guard
indexed by `ℕ`: to go one way, restrict to the range; to go the other, note
that a `Fin (K + 1)` index carries a `Nat`-valued coercion. -/
theorem weakGuards_of_weakGuardsB (hK : 0 < K) (a b c d : Fin K) {t : ℕ}
    (ht : t ≤ K) (h : WeakGuardsB hK a b c d t) : WeakGuards hK a b c d t :=
  fun j hj h1 h2 h3 h4 => h ⟨j, by omega⟩ hj h1 h2 h3 h4

/-- `Step4_slide_iterates 1` implies `Step4LitK K` at every `K`.  This is the
bridge: the library `Prop`, instantiated at this `K`, must produce the
interleaving at every `t ≤ pairBack`, so in particular at every
`t ∈ range (K + 1)` with `t ≤ pairBack = pairBackC`, for every guard shape. -/
theorem step4LitK_of_step4 (h : Step4_slide_iterates 1) (K : ℕ) (hK : 0 < K)
    [NeZero K] : Step4LitK K hK := by
  intro S a b c d t hab hcd hI ht hg
  have hres := h K hK S a b c d hab hcd (vtx_eq_vtx hK S a b) (vtx_eq_vtx hK S c d)
    ((interleaved_iff hK (S := S) a b c d).mp hI) t.val (by rwa [pairBackC_eq'] at ht)
      (weakGuards_of_weakGuardsB hK a b c d (Nat.lt_succ_iff.mp t.isLt) hg)
  exact (interleaved_iff hK (S := S) a b (rotAdd hK (K - t.val) c)
    (rotAdd hK (K - t.val) d)).mp hres

/-- **The library statement `Issue89GapMap.Step4_slide_iterates` is false.**

The implication-shaped guard is *satisfied* by every `j` at which the slid `c`
has landed on `a` or `b`, because then the first antecedent of the chain is
false and the whole implication is vacuous.  So the guard does not exclude the
collisions it exists to exclude --- the colliding configurations are precisely
the ones that satisfy it --- and the slid pair can leave the interleaving.

This is a `decide` at the single fixed circle size `K = 4` (16 genomes, finitely
many quadruples and `5` shifts).  It is a fixed-`K` search, not the `K`-sweep
whose `decide` OOMed on this host at `K = 5`; it elaborates in seconds. -/
theorem not_Step4LitK_4 : ¬ Step4LitK 4 (by norm_num) := by decide

/-- **Hence `Issue89GapMap.Step4_slide_iterates` has no inhabitant**, in the
literal reading of its own guard clause.  The library `Prop` at `L = 1`
implies `Step4LitK 4`, which is refuted. -/
theorem not_Step4_slide_iterates_1 : ¬ Step4_slide_iterates 1 :=
  by
  intro h
  exact not_Step4LitK_4 (step4LitK_of_step4 (K := 4) (hK := by norm_num) h)

end AssemblyP1.Issue94Step4Prop
