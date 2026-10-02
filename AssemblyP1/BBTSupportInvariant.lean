import AssemblyP1.BBTEulerianSearch
import AssemblyP1.BBTMaximalExtension

/-!
# The selected-support invariant for the one-cycle route to `thm:BBT`

## What this module is for

`AssemblyP1.BBTEulerianSearch` (commit `ba91723`) rephrases the first clause of
`thm:BBT` as a statement about a **successor map** rather than about a
presentation, and proves the two halves of the equivalence in the kernel
(`uniqueAt_iff_orbit`):

```text
UniqueAt hG L S
  <->  every bijective, FibrePreserving, OneCycle θ has OrbitVertexEq θ
```

So the exact remaining content is

```text
Bijective θ, FibrePreserving θ, OneCycle θ, and NOT OrbitVertexEq θ
    ==>  a violation of `Ukkonen`
```

i.e. a triple repeat or an interleaved pair of maximal repeats of length
`≥ L-1` — the two disjuncts of `BBTEulerian.LongObstruction`.  This module
isolates that content into three named pieces and proves the reduction.

## Why the support, and why *selected*

The earlier attempt at this endgame was the **crossing-pairs lemma**: two
doubled `(L-1)`-mers with four distinct interleaving starts extend to two
interleaved maximal repeats.  That statement is **false**, and the repository
already contains two independent refutations of it:

* `BBTChords.raw_node_crossing_not_maximal` (kernel-checked): on
  `S = 00101`, `L = 3`, the doubled `(L-1)`-mers `01` and `10` sit at the
  interleaving starts `1 < 2 < 3 < 4`, yet `S` satisfies `P2`;
* `docs/audit-p2-direct-proof-maximal-extension-2026-09-21.md`, on
  `S = AABCBCBAB`, where two crossing raw pairs extend to the *same* maximal
  repeat, so they never produce two interleaved ones.

An exhaustive search run for this module (`scripts/verify_support_dichotomy_89.py`,
primitive binary circular words, `G ≤ 8`, `K = L-1 ≤ 3`, enumerating **circuits** rather
than `G!` presentations) found the raw lemma failing in 768 of the 1024 primitive
`(word, K)` pairs that have interleaved doubled `(L-1)`-mers at all.

Crucially, the search also shows the *selected* reading is the right one, and
that it is still not the whole story:

* selecting a crossing can be **harmless**.  On `S = 00101`, `L = 3` the
  rematching `f = (1 3)(2 4)` (fixing `0`) is fibre-preserving and
  `θ = f ∘ nextPos` is the single cycle `0, 3, 2, 1, 4`, whose `(L-1)`-mer
  orbit is exactly the truth's `00, 01, 10, 01, 10`.  So `OrbitVertexEq` holds.
  `SupportDichotomy` is nevertheless *decided* for every `θ` on this word
  (`supportDichotomy_00101` below), i.e. the harmless crossing is correctly
  not a counterexample to the dichotomy;
* what is never harmless is a deviation that changes the spelled vertex cycle.
  `deviation θ` is the set of starts where `θ` does not step forward, and
  `deviation_ne_empty_of_not_orbitVertexEq` proves a bad `θ` has a nonempty
  one.  This is the `Prop`-level content of "the transposition has a
  nontrivial effect", which the `Arratia et al. 1996` descent must carry.

So: **do not** try to prove `f = id`, and **do not** try to prove that the
support has no crossing.  Both are refuted.  The invariant that survives is
`SupportDichotomy` below, and it is the two *moves* of
`Arratia et al. 1996`, Theorem 6 (a three-way repeated `t`-tuple, or two
interleaved repeated `t`-tuple pairs), each of them *selected* by `θ`.

## Status

* **Proved here:** `deviation_eq_empty_iff`, `deviation_ne_empty_of_not_orbitVertexEq`,
  `deviation_is_a_choice_site`, and the reduction theorems
  `orbitVertexEq_of_dichotomy` and `uniqueAt_of_dichotomy`, which show the
  endgame follows from exactly three remaining inputs.
* **Not proved (stated as `Prop`s, no `axiom`/`sorry`/`admit`):**
  `SupportDichotomy`, `SelectedTriple_obstruction`,
  `SelectedInterleaved_obstruction`.  These are the maximal-extension content.
* **Kernel-checked evidence:** `supportDichotomy_00101`, decided for every
  `θ` on `Fin 5`.
-/

namespace AssemblyP1.BBTSupport

open SourceFaithfulIs
open OrientedRigidity
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTEulerianSearch


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000

variable {α : Type} [DecidableEq α] [Fintype α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-! ## 1. The deviation set: nontriviality of a traversal -/

/-- The **deviation set** of `θ`: the starts at which the traversal does *not*
step one place forward.  Writing `f = θ ∘ nextPos⁻¹` for the induced
rematching of the `(L-1)`-mer multigraph, this is the support of `f` shifted
back by one, since `θ x ≠ nextPos x` exactly when `f (nextPos x) ≠ nextPos x`.

This, and not "all repeated `(L-1)`-mers", is the object the endgame needs:
it is the set of places where the traversal genuinely departs from the truth. -/
def deviation (θ : Fin G → Fin G) : Finset (Fin G) :=
  Finset.univ.filter (fun x => θ x ≠ nextPos hG x)

theorem mem_deviation {θ : Fin G → Fin G}{x : Fin G} :
    x ∈ deviation hG θ ↔ θ x ≠ nextPos hG x := by
  simp [deviation]

/-- A deviation-free traversal *is* the truth's own successor. -/
theorem deviation_eq_empty_iff {θ : Fin G → Fin G}:
    deviation hG θ = ∅ ↔ θ = nextPos hG := by
  constructor
  · intro h
    funext x
    by_contra hc
    have hx : x ∈ deviation hG θ := (mem_deviation hG).2 hc
    rw [h] at hx
    simp at hx
  · intro h
    ext x
    simp [deviation, h]

/-- **Nontriviality of a traversal is exactly a nonempty deviation set.**  A
traversal that steps forward everywhere is the truth and spells the truth's
vertex cycle; so a one-cycle that spells something *else* must deviate
somewhere.  This is the propositional content of "the transposition has a
nontrivial effect", which is what the `Arratia et al.` shift-left descent has
to preserve; it is proved here so that the descent has something to carry. -/
theorem deviation_ne_empty_of_not_orbitVertexEq {θ : Fin G → Fin G}
    (hbad : ¬ OrbitVertexEq hG L S θ) : deviation hG θ ≠ ∅ := by
  intro h
  have hEq : θ = nextPos hG := (deviation_eq_empty_iff hG).1 h
  exact hbad (hEq ▸ orbitVertexEq_nextPos hG L S)

/-- A deviation is a genuine choice of continuation: at a deviating start `θ`
and the truth pick out the *same* `(L-1)`-mer, so `θ` is a rematching of the
multigraph and not an unrelated walk. -/
theorem deviation_is_a_choice_site {θ : Fin G → Fin G}
    (hf : FibrePreserving hG L S θ) {x : Fin G} (hx : x ∈ deviation hG θ) :
    vtx hG L S (θ x) = vtx hG L S (nextPos hG x) ∧ θ x ≠ nextPos hG x :=
  ⟨hf x, (mem_deviation hG).1 hx⟩

/-! ## 2. Selected fibre configurations -/

/-- `θ` **selects** the condensed vertex `v`: the rematching uses one of `v`'s
occurrences, so the traversal makes a genuine alternative choice at `v`.  The
word *selected* is load-bearing: it is what separates the harmless `00101`
crossing (on which the rematching is the identity, or a harmless swap) from a
crossing that changes the spelled vertex cycle. -/
def Selects (θ : Fin G → Fin G) (v : Fin (L - 1) → α) : Prop :=
  ∃ x, x ∈ fibre hG L S v ∧ θ x ≠ nextPos hG x

/-- **(T) a selected three-way repeated `(L-1)`-tuple**: some vertex of
multiplicity `≥ 3` is rematched. -/
def SelectedTriple (θ : Fin G → Fin G) : Prop :=
  ∃ v : Fin (L - 1) → α, 3 ≤ (fibre hG L S v).card ∧ Selects hG L S θ v

/-- **(I) two selected interleaved doubled `(L-1)`-mers**: two doubled
`(L-1)`-mers, both rematched, whose four starts interleave.  `FourDistinct`
already carries the pairwise distinctness, so both are genuine doubled pairs.

This is stated with the *heads* `FourDistinct` and `InOpenArc` rather than with
`Interleaved` itself, purely so that typeclass search can find the decidability:
`Interleaved` takes the `Genome` structure in head position, and instance
resolution cannot unify through a structure in the head.  The two are the same
predicate: `interleaved_iff` below is an `Iff` between them, so nothing is
weakened and the source-faithful `Interleaved` is still what this means. -/
def SelectedInterleaved (θ : Fin G → Fin G) : Prop :=
  ∃ a b c d : Fin G,
    ((a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) ∧
      ((InOpenArc (mkGenome hG S) a b c) ↔ ¬ InOpenArc (mkGenome hG S) a b d)) ∧
    vtx hG L S a = vtx hG L S b ∧ vtx hG L S c = vtx hG L S d ∧
    Selects hG L S θ (vtx hG L S a) ∧ Selects hG L S θ (vtx hG L S c)

/-- **The `SelectedInterleaved` clause really is the source-faithful
`Interleaved`**: definitionally, by the definition of `Interleaved`. -/
theorem interleaved_iff (a b c d : Fin G) :
    ((a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) ∧
        ((InOpenArc (mkGenome hG S) a b c) ↔ ¬ InOpenArc (mkGenome hG S) a b d)) ↔
      Interleaved (mkGenome hG S) a b c d := Iff.rfl

/-- **The support dichotomy: the exact statement this endgame needs.**

A bijective, fibre-preserving, one-cycle successor map whose spelled vertex
cycle differs from the truth's must either rematch a vertex of multiplicity
`≥ 3`, or rematch two interleaved doubled `(L-1)`-mers.  These are the two
move types of `Arratia et al. 1996`, Theorem 6, in *selected* form.

Stated as a `Prop` and **not proved**; it is the remaining content.  Note what
is deliberately *not* claimed: neither `θ = nextPos`, nor that `θ`'s support
has no crossing.  Both are refuted (`00101`). -/
def SupportDichotomy (θ : Fin G → Fin G) : Prop :=
  Function.Bijective θ → FibrePreserving hG L S θ → OneCycle hG θ →
    ¬ OrbitVertexEq hG L S θ →
    SelectedTriple hG L S θ ∨ SelectedInterleaved hG L S θ

/-- **Maximal extension of a selected three-way repeat.**  Three occurrences
of one `(L-1)`-mer of multiplicity `≥ 3` extend *simultaneously* to a maximal
triple repeat of length `≥ L-1`.  This is the first disjunct of
`LongObstruction`; the assembly is `BBTMaximalExtension.triple_disjunct`.
Not proved: this needs the simultaneous three-way extension, which the
existing `maximalRepeat_of_branch` provides only for *pairs*. -/
def SelectedTriple_obstruction (θ : Fin G → Fin G) : Prop :=
  SelectedTriple hG L S θ → LongObstruction hG L S

/-- **Maximal extension of two selected interleaved doubled `(L-1)`-mers.**
Two interleaved doubled `(L-1)`-mers, *both rematched*, extend to two
interleaved maximal repeats of length `≥ L-1`.  This is the second disjunct of
`LongObstruction`; the assembly is `BBTMaximalExtension.interleaved_disjunct`.

This is the **selected** form of the crossing-pairs lemma, and it is the
statement that was previously stated wrongly.  The unselected version is
false; here both pairs are rematched, which the search shows is what excludes
the harmless `00101` case.  Not proved. -/
def SelectedInterleaved_obstruction (θ : Fin G → Fin G) : Prop :=
  SelectedInterleaved hG L S θ → LongObstruction hG L S

instance {θ : Fin G → Fin G} {v : Fin (L - 1) → α} : Decidable (Selects hG L S θ v) := by
  unfold Selects; infer_instance

instance {θ : Fin G → Fin G} : Decidable (SelectedTriple hG L S θ) := by
  unfold SelectedTriple; infer_instance

instance {θ : Fin G → Fin G} : Decidable (SelectedInterleaved hG L S θ) := by
  unfold SelectedInterleaved InOpenArc; infer_instance

instance {θ : Fin G → Fin G} : Decidable (SupportDichotomy hG L S θ) := by
  haveI hT : Decidable (SelectedTriple hG L S θ) := inferInstance
  haveI hI : Decidable (SelectedInterleaved hG L S θ) := inferInstance
  haveI hF : Decidable (FibrePreserving hG L S θ) := inferInstance
  haveI hO : Decidable (OneCycle hG θ) := inferInstance
  haveI hV : Decidable (OrbitVertexEq hG L S θ) := inferInstance
  haveI hB : Decidable (Function.Bijective θ) := inferInstance
  unfold SupportDichotomy
  infer_instance

/-! ## 3. The reduction: the endgame follows from exactly three inputs -/

/-- **Everything except `SupportDichotomy` and the two maximal-extension
lemmas is already closed.**  A `Ukkonen` word has no `LongObstruction`, so a
bad `θ` contradicts the dichotomy and the two derivations.

This is proved, so the residual mathematical content of the whole `#89`
Eulerian-cycle gap is precisely the three `Prop`s above. -/
theorem orbitVertexEq_of_dichotomy {θ : Fin G → Fin G}
    (hd : SupportDichotomy hG L S θ)
    (h1 : SelectedTriple_obstruction hG L S θ)
    (h2 : SelectedInterleaved_obstruction hG L S θ)
    (hUkk : Ukkonen hG L S)
    (hb : Function.Bijective θ) (hf : FibrePreserving hG L S θ)
    (ho : OneCycle hG θ) : OrbitVertexEq hG L S θ := by
  by_contra hbad
  have hn := not_longObstruction_of_Ukkonen (S := S) hUkk
  rcases hd hb hf ho hbad with ht | hi
  · exact hn (h1 ht)
  · exact hn (h2 hi)

/-- ... and therefore the first clause of `thm:BBT` itself. -/
theorem uniqueAt_of_dichotomy
    (hd : ∀ θ : Fin G → Fin G, SupportDichotomy hG L S θ)
    (h1 : ∀ θ : Fin G → Fin G, SelectedTriple_obstruction hG L S θ)
    (h2 : ∀ θ : Fin G → Fin G, SelectedInterleaved_obstruction hG L S θ)
    (hUkk : Ukkonen hG L S) : UniqueAt hG L S := by
  rw [uniqueAt_iff_orbit]
  intro θ hb hf ho
  exact orbitVertexEq_of_dichotomy hG L S (hd θ) (h1 θ) (h2 θ) hUkk hb hf ho

/-- **Kernel-checked on `S = 00101`, `L = 3`.**  The dichotomy is decided for
*every* successor map on `Fin 5`, on the very word that refutes the unselected
crossing-pairs lemma.  The harmless crossing of the doubled `(L-1)`-mers `01`
and `10` is correctly not a counterexample, while the dichotomy itself holds
for all `θ`. -/
theorem supportDichotomy_00101 :
    ∀ θ : Fin 5 → Fin 5,
      SupportDichotomy (hG := BBTChords.hG5) (L := 3) BBTChords.S5 θ := by
  decide

/-- **Anti-vacuity: a *selected* interleaving exists on a good `θ`, and is
harmless.**  There is a bijective, fibre-preserving, one-cycle `θ` on
`S = 00101` whose deviation set is an *interleaved pair of doubled
`(L-1)`-mers* --- i.e. `SelectedInterleaved` holds --- and whose spelled
vertex cycle is nevertheless the truth's own.

This is the instance that rules out both tempting strengthenings of the
dichotomy.  It refutes "a good `θ` has no selected crossing"
(`SelectedInterleaved` holds here), and by exhibiting a good `θ` at all it
refutes "`θ = nextPos`".  Concretely, this is the rematching that swaps the
doubled `(L-1)`-mers `01` and `10` at the interleaving starts `1 < 2 < 3 < 4`;
its successor is the single cycle `0, 3, 2, 1, 4`, whose `(L-1)`-mer orbit is
exactly the truth's `00, 01, 10, 01, 10`.

So the invariant of this module has to be about `¬OrbitVertexEq`, not about
crossings, and `SupportDichotomy` is stated accordingly. -/
theorem harmless_selected_crossing_00101 :
    ∃ θ : Fin 5 → Fin 5, Function.Bijective θ ∧
        FibrePreserving (hG := BBTChords.hG5) (L := 3) BBTChords.S5 θ ∧
        OneCycle BBTChords.hG5 θ ∧
        SelectedInterleaved (hG := BBTChords.hG5) (L := 3) BBTChords.S5 θ ∧
        OrbitVertexEq (hG := BBTChords.hG5) (L := 3) BBTChords.S5 θ := by
  decide

/-- **Consequence, kernel-checked: `SelectedInterleaved_obstruction` above is
FALSE at the very instance `harmless_selected_crossing_00101` exhibits.**
The witness `θ` there is selected-interleaved, so the obstruction would force a
`LongObstruction` on `S = 00101` at `L = 3`; but `BBTChords.p2_hG5_S5_L3`
gives `P2`, hence `Ukkonen`, hence `¬ LongObstruction`.  So the `#89` endgame
cannot be closed by demanding `SelectedInterleaved_obstruction` for every `θ`:
the two crossing doubled `(L-1)`-mers at `{1,3}` and `{2,4}` are harmless.  The
residual content is therefore the remaining clause of `SupportDichotomy`, not
the selected-interleaving obstruction. -/
theorem selectedInterleaved_obstruction_false_00101 :
    ¬ (∀ θ : Fin 5 → Fin 5,
        SelectedInterleaved_obstruction BBTChords.hG5 3 BBTChords.S5 θ) := by
  intro hobs
  obtain ⟨θ, _, _, _, hθsi, _⟩ := harmless_selected_crossing_00101
  have hnot : ¬ LongObstruction BBTChords.hG5 3 BBTChords.S5 :=
    not_longObstruction_of_Ukkonen (P2.imp_Ukkonen (by decide) BBTChords.p2_hG5_S5_L3)
  exact hnot (hobs θ hθsi)

end AssemblyP1.BBTSupport
