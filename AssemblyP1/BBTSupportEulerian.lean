import AssemblyP1.BBTSupportChords

/-!
# `#89`: the support-permutation route, bridged to the real `EulerianCycle`
# object --- a precise interface theorem

`AssemblyP1.BBTSupportChords` proves the support dichotomy for an *abstract*
labelling `W : Fin G → λ` of the circle.  This module bridges it to the
objects of `AssemblyP1.BBTEulerian`, and the bridge is short, because
`AssemblyP1.BBTUniqueEulerian` has already identified the abstract
permutation:

* `AssemblyP1.BBTUniqueEulerian.AltF_vtx`: the `traverses` clause of
  `EulerianCycle hG L S σ` says exactly that `f = AltF hG σ` is a
  **label-preserving** permutation for `W = vtx hG L S`;
* `AssemblyP1.BBTUniqueEulerian.AltF_bijective`: `f` is a permutation;
* `AssemblyP1.BBTUniqueEulerian.Succ_eq_altF`: the successor of the alternative
  traversal is `f ∘ nextPos`, so the `single` clause of `EulerianCycle` is
  `VisitsAll (fun x => f (nextPos hG x)) (origin hG)` --- literally the third
  hypothesis of `support_dichotomy`.

So `support_dichotomy` applies with **no** new word layer, and its two
disjuncts are statements about *real* starts of the truth:

* `(W)` three distinct starts spelling the same `(L-1)`-mer;
* `(X)` two doubled `(L-1)`-mer pairs whose four starts interleave.

## What is proved here

`vertexCycleEq_of_noTriple_noCross` (§2) is the master theorem of the route:

```text
   σ is an Eulerian cycle
   ∧ no `(L-1)`-mer is spelled at three distinct starts
   ∧ no two doubled `(L-1)`-mer pairs interleave
   ⟹ the vertex cycle of σ is a rotation of the truth's.
```

The proof is the short one the earlier packets did not see: the support
dichotomy forces `AltF hG σ = id`; `Succ hG σ = nextPos hG` then forces `σ` to
be a rotation of the circle, by the elementary recursion
`σ (nextPos i) = nextPos (σ i)` (`Succ hG σ = nextPos hG` says that `σ`
*commutes with the one-step rotation*, and a permutation commuting with the
generator of a cyclic group is a power of it); and a rotation of the circle
carries the truth to a rotation of the truth.

`obstruction_of_wordLevel` (§3) packages this as the interface to
`AssemblyP1.BBTEulerian.EulerianCycleObstruction`: with the two *word-level*
hypotheses below, the whole of `thm:BBT` follows.  Those two hypotheses are
local combinatorial statements about a `Ukkonen` word, and neither of them is
a renaming of the goal:

* `NoTripleVertex` --- no `(L-1)`-mer of an `Ukkonen` word is spelled at three
  distinct starts.  This is Lemma 1 of
  `AssemblyP1.BBTUniqueEulerian`; it is the three-copy version of the
  two-sided maximal extension already proved in
  `AssemblyP1.P2RepeatResidual.maximal_extension_of_repeated`, and it is
  **not** proved here.
* `NoCrossedDoubledPairs` --- no two doubled `(L-1)`-mer pairs of an `Ukkonen`
  word interleave.  `AssemblyP1.BBTSupportCrossing` shows by a kernel-checked
  instance that this is **false**: the collapse regime
  (`S = 00101`, `G = 5`, `L = 3`) is an `Ukkonen` --- indeed `P2` --- word with
  a crossing pair.  So this hypothesis cannot be proved, and the route needs a
  *block* statement for the collapse regime instead; see §4.

## What is not proved here

Neither word-level hypothesis, and therefore not
`EulerianCycleObstruction`, and therefore not `thm:BBT`.  The residual is now
stated as the two clauses above, the second of which is known to be false in
the stated form; the open core is the block statement of §4.

No `sorry`, no `admit`, no new axiom.
-/

namespace AssemblyP1.BBTSupportEulerian

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTSupportChords

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-! ## 1. The `single` clause, in the shape `support_dichotomy` wants -/

/-- **The `single` clause of `EulerianCycle`, transported to `AltF`.**  The
successor of the alternative traversal is `f ∘ nextPos` with `f = AltF hG σ`,
so the `single` clause is literally the third hypothesis of
`support_dichotomy` at `W = vtx hG L S`.  This is the step that makes the
abstract dichotomy applicable with no new word layer. -/
theorem visitsAll_altF {σ : Fin G ≃ Fin G} (hEul : EulerianCycle hG L S σ) :
    VisitsAll (fun x => AltF hG σ (nextPos hG x)) (origin hG) := by
  have hV : VisitsAll (Succ hG σ) (origin hG) := hEul.2
  have hfun : (fun x => AltF hG σ (nextPos hG x)) = Succ hG σ :=
    funext (Succ_eq_altF hG σ)
  rw [hfun]
  exact hV

/-! ## 2. The master theorem: no triple, no crossing ⟹ the vertex cycle is a
rotation -/

/-- **The rotation forced by `AltF hG σ = id`.**  If the alternative traversal
induces the identity permutation of the starts, its successor `Succ hG σ`
*is* the one-step rotation, and hence `σ` commutes with the generator of the
cyclic group of starts. -/
theorem succ_eq_nextPos_of_altF_id {σ : Fin G ≃ Fin G}
    (hA : AltF hG σ = fun q => q) (x : Fin G) :
    Succ hG σ x = nextPos hG x := by
  have h1 := Succ_eq_altF hG σ x
  have h2 : AltF hG σ (nextPos hG x) = nextPos hG x := by
    have := congrFun (congrFun hA (nextPos hG x))
    simpa using this.symm
  rw [h1, h2]

/-- **A permutation commuting with the one-step rotation is a rotation of the
circle.**  If `Succ hG σ = nextPos hG`, i.e.
`σ (nextPos i) = nextPos (σ i)` for every `i`, then
`σ i = rotAdd hG (σ (origin hG)).val i`.  This is the one place the length `G`
enters: at the wrap-around step `n = G`, the induction has to return to
`origin`, which is exactly what `rotAdd hG _ G = rotAdd hG _ 0` says. -/
theorem eq_rotAdd_of_comm {σ : Fin G ≃ Fin G}
    (hSucc : ∀ x, Succ hG σ x = nextPos hG x) :
    ∀ i : Fin G, σ i = rotAdd hG (σ (origin hG)).val i := by
  have hrec : ∀ i : Fin G, σ (nextPos hG i) = nextPos hG (σ i) := by
    intro i
    have h1 := Succ_apply hG σ i
    have h2 := hSucc (σ i)
    rw [h1] at h2
    exact h2.symm
  have key : ∀ (n : ℕ) (h : n < G),
      σ ⟨n, h⟩ = rotAdd hG (σ (origin hG)).val ⟨n, h⟩ := by
    intro n
    induction n with
    | zero =>
        intro h
        have ho : (⟨0, h⟩ : Fin G) = origin hG := by
          apply Fin.ext
          rfl
        rw [ho, rotAdd, origin]
        apply Fin.ext
        show (0 + (σ (origin hG)).val) % G = (σ (origin hG)).val
        rw [Nat.zero_add]
        exact Nat.mod_eq_of_lt (σ (origin hG)).isLt
    | succ n ih =>
        intro h
        by_cases hG1 : n + 1 < G
        · have hn : n < G := by omega
          have hrec' := hrec ⟨n, hn⟩
          have hprev : (⟨n + 1, h⟩ : Fin G) = nextPos hG ⟨n, hn⟩ := by
            apply Fin.ext
            show ((n + 1) % G) = ((n % G + 1) % G)
            rw [Nat.add_mod, Nat.mod_eq_of_lt hn]
          rw [hprev] at hrec'
          have hih := ih hn
          rw [hrec', hih, nextPos_rotAdd, rotAdd]
          apply congrArg (fun w : Fin G => w)
          apply Fin.ext
          show (n + (σ (origin hG)).val + 1) % G
              = ((n + 1) + (σ (origin hG)).val) % G
          congr 2
          omega
        · exact absurd h hG1
  intro i
  exact key i.val i.isLt

/-- **The master theorem of the support-permutation route.**  An alternative
Eulerian cycle of the condensed `(L-1)`-mer graph whose induced permutation has
*no* wide label and *no* crossing pair has the same vertex cycle as the truth.

The two hypotheses are read at the real objects: no `(L-1)`-mer of `S` is
spelled at three distinct starts, and no two doubled `(L-1)`-mer pairs of `S`
interleave.  This is `thm:BBT` with those two word-level statements isolated;
§3 turns it into the interface with `EulerianCycleObstruction`. -/
theorem vertexCycleEq_of_noTriple_noCross {σ : Fin G ≃ Fin G}
    (hEul : EulerianCycle hG L S σ)
    (hnot1 : ¬ ∃ a b c : Fin G, TripleClass (vtx hG L S) a b c)
    (hnot2 : ¬ CrossedDoubledPairs hG (vtx hG L S)) :
    VertexCycleEq hG L S σ (Equiv.refl (α := Fin G)) := by
  have hA : AltF hG σ = fun q => q :=
    eq_id_of_noTriple_noCross hG (vtx hG L S) (AltF hG σ)
      (AltF_bijective hG σ) (fun q => AltF_vtx hG L S σ hEul.1 q)
      (visitsAll_altF hEul) hnot1 hnot2
  have hSucc : ∀ x, Succ hG σ x = nextPos hG x := succ_eq_nextPos_of_altF_id hA
  have hrot := eq_rotAdd_of_comm hSucc
  refine ⟨σ (origin hG), ?_⟩
  intro i
  rw [hrot i]

/-! ## 3. The interface with `EulerianCycleObstruction` -/

/-- **No `(L-1)`-mer is spelled at three distinct starts of an `Ukkonen`
word.**  This is Lemma 1 of `AssemblyP1.BBTUniqueEulerian`: the three-copy
version of the two-sided maximal extension of
`AssemblyP1.P2RepeatResidual.maximal_extension_of_repeated`. -/
def NoTripleVertex (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  ¬ ∃ a b c : Fin G, TripleClass (vtx hG L S) a b c

/-- **No two doubled `(L-1)`-mer pairs of an `Ukkonen` word interleave.**
This is the statement `AssemblyP1.BBTSupportCrossing` refutes: `S = 00101`,
`G = 5`, `L = 3` is `P2` and has the crossing pair `{1, 3}`, `{2, 4}`.  It is
stated here because it is the exact residual of the route, and because its
failure is *localized*: the counterexample is the collapse regime, in which the
two crossing pairs lie inside one maximal repeat. -/
def NoCrossedDoubledPairs (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  ¬ CrossedDoubledPairs hG (vtx hG L S)

/-- **The interface theorem.**  `EulerianCycleObstruction` --- the single
hypothesis of `AssemblyP1.PopulationUniqueness` --- follows from the two
word-level statements above, uniformly over all circular words satisfying
`Ukkonen`.  Equivalently: `P2.imp_Ukkonen` plus these two give
`BBTUniqueAt` with no external input.

This is the reduction the earlier packets were reaching for.  The two
hypotheses are *not* renamings of the goal: each is a statement about a single
`(L-1)`-mer (resp. a single pair of them) in a word, with no `EulerianCycle` in
sight, and the first of them is exactly the maximal-extension bridge applied to
a third copy. -/
theorem obstruction_of_wordLevel {L : ℕ}
    (h1 : ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α), Ukkonen hK L S →
      NoTripleVertex hK L S)
    (h2 : ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α), Ukkonen hK L S →
      NoCrossedDoubledPairs hK L S) :
    EulerianCycleObstruction (α := α) L := by
  intro K hK S hUkk σ hEul
  exact Or.inl (vertexCycleEq_of_noTriple_noCross hK L S hEul
    (h1 K hK S hUkk) (h2 K hK S hUkk))

/-- **The same interface at the level of the P2 truth**, so that the exported
theorem of `AssemblyP1.PopulationUniqueness` needs no `Ukkonen` side
condition. -/
theorem obstruction_of_P2_wordLevel {L : ℕ} (hL : 2 ≤ L)
    (h1 : ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α), P2 hK L S →
      NoTripleVertex hK L S)
    (h2 : ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α), P2 hK L S →
      NoCrossedDoubledPairs hK L S) :
    EulerianCycleObstruction (α := α) L := by
  apply obstruction_of_wordLevel
  · intro K hK S h
    exact h1 K hK S (P2.imp_Ukkonen hL h)
  · intro K hK S h
    exact h2 K hK S (P2.imp_Ukkonen hL h)

/-! ## 4. The open core, in one paragraph

The residual of `#89` is now exactly this: prove `NoTripleVertex` for a
`Ukkonen` word, and replace `NoCrossedDoubledPairs` by a statement about the
**blocks** of the support of `f = AltF hG σ` rather than about the pairs.  The
replacement must accommodate the collapse regime of
`AssemblyP1.BBTSupportCrossing`, in which two interlacing doubled pairs lie
inside one maximal repeat and are therefore moved by one block; the local
statement needed is that such a block cut preserves the vertex sequence, which
is what `docs/bbt-chord-rematch-89.md` §5 and
`AssemblyP1.BBTMaximalExtension` reduce to.  Neither is proved here. -/

end AssemblyP1.BBTSupportEulerian
