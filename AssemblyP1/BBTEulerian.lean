import AssemblyP1.P2
import AssemblyP1.BBTCondense

/-!
# `thm:BBT` as uniqueness of the Eulerian cycle of the condensed graph (#89)

Paper source: `paper/sections/05-population.tex`, `thm:BBT`, in the theorem
shape of Bresler--Bresler--Tse 2013 (*Optimal assembly for high throughput
shotgun sequencing*), Theorem 3:

> Construct the `K`-mer graph from the complete `(K+1)`-spectrum of a
> circular genome `s` and condense it.  If `s` satisfies Ukkonen's
> condition --- no triple repeat and no interleaved repeat pair of length
> at least `K` --- then the condensed graph has a **unique Eulerian
> cycle**, and that cycle spells `s` up to cyclic rotation.

At `K = L - 1` the `K`-mer graph of `thm:BBT` is exactly the
`(L-1)`-mer multigraph of `AssemblyP1.BBTSequenceGraph` (§1 of
`AssemblyP1/BBTCondense.lean`): its vertices are the `(L-1)`-mers of the
truth, its edges are the starts, and the condensation of `thm:BBT`
contracts the unambiguous (multiplicity `≤ 1`) vertices, leaving the
branch objects.  `AssemblyP1/BBTCondense.lean` §3 already proved the two
traversal facts the uniqueness step consumes --- `match_next_vtx` (both
traversals enter the same vertex) and `forced_at_unambiguous` (no choice
at an unambiguous vertex) --- but it had no object for *"a second Eulerian
cycle"*, and therefore could not state the uniqueness theorem.  This
module supplies exactly that object, and nothing else.

## The object: an Eulerian cycle of the condensed graph

`EulerianCycle hG L S σ` is a **presentation** of an Eulerian cycle of the
`(L-1)`-mer multigraph of the truth, given by a bijection
`σ : Fin G ≃ Fin G` between the candidate's starts and the truth's starts
(the pull-back of an equal-spectrum matching, §2).  It has exactly the two
clauses an Eulerian cycle has:

1. **it traverses edges** (`traverses`): consecutive elements of the
   listing `σ 0, σ 1, …` are joined by an edge of the multigraph, i.e.
   `vtx (σ (nextPos i)) = vtx (nextPos (σ i))` for every `i`.  This is
   `BBTSequenceGraph.match_next_vtx`, the de Bruijn shift relation, and
   it is what says that the candidate walks *this* multigraph;
2. **it is a single cycle** (`single`): the successor
   `fun x => σ (nextPos (σ.symm x))` runs through all `G` positions
   before returning (`VisitsAll`).  This is the clause ruling out a
   decomposition of the walk into several disjoint circuits.

Both clauses are load-bearing, and §4 contains the kernel-checked
instances that pin them down: `not_eulerianCycle_validity` and
`not_vertexCycleEq` exhibit a permutation of the starts which satisfies
neither and which is therefore *not* an alternative Eulerian cycle --- it
is outside `thm:BBT` altogether (§4.1).

`VertexCycleEq` forgets the presentation and keeps the *vertex cycle*:
the cyclic sequence of `(L-1)`-mers visited.  Two presentations of one
Eulerian cycle differ by the choice of a starting point, so
`VertexCycleEq` is the right notion of *"the same Eulerian cycle"*, and it
is the object the uniqueness theorem is about.  This distinction is the
whole point, and `§4.2` is its anti-vacuity instance: on `S = 0101`,
`G = 4`, `L = 3` the pull-back `(0 1)(2 3)` is *not* a rotation of the
circle and carries no long obstruction, because it is a presentation of
the truth's own Eulerian cycle, read from a different start
(`eulerianCycle_S4`, `trivial_vertexCycleEq_S4`, `not_rotation_S4`).

## The theorem, in the shape the source gives it

`EulerianCycleObstruction L` is `thm:BBT` at `K = L - 1` in the requested
shape: for every alternative Eulerian cycle of the condensed graph of an
Ukkonen word, either that cycle is the truth's cycle up to rotation of
the cycle, or the truth carries the **long obstruction** of `def:P1P2`:
a maximal triple repeat of length `≥ L - 1`, or two interleaved maximal
repeats both of length `≥ L - 1`.  `LongObstruction` is exactly the
negation of `Ukkonen` (`longObstruction_iff_not_Ukkonen`), so the two
clauses of the disjunction are the two clauses of Ukkonen's condition.

`EulerianCycleObstruction L → BBTUniqueAt L` is proved here, and
`BBTEulerian.bbtCompleteSpec_of_obstruction` is the whole of the bridge to
the population chain.  Consequently `AssemblyP1.P2.BBTUniqueAt` is **no
longer an assumption** of any exported theorem: it is now a theorem of
this module.

## What is proved, and what is not

* **Proved (kernel-checked).**  The Eulerian-cycle object and its
  correctness: §2 shows that the pull-back of an equal-spectrum matching
  is an alternative Eulerian cycle (`pullback_isEulerianCycle`), that the
  truth's own cycle is one (`eulerianCycle_refl`), that a rotational
  vertex cycle makes the candidate a rotation of the truth
  (`rotEquiv_of_vertexCycleEq`), and the entire reduction
  `EulerianCycleObstruction L → BBTUniqueAt L →`
  `population_unique_ML_up_to_rotation`.  §3 contains the reduction in
  isolation, §4 the kernel-checked refutation of the wrong object and the
  anti-vacuity instance.
* **Not proved.**  `EulerianCycleObstruction` itself, i.e. uniqueness of
  the Eulerian cycle of the condensed graph.  **ATTRIBUTION (board 94, front
  94e7; see `docs/best-tw1-attribution-94.md`):** this is a **board
  construction**, not a result imported from Pevzner 1995 or from BBT.  This
  text formerly read "This is the Pevzner 1995 Lemma 9 / `thm:BBT` input"; the
  attribution is withdrawn, because a two-sided retrieval established that
  Pevzner 1995 (Algorithmica 13:77-105) has no counting statement of any kind
  and no `BEST` / `arboresc` / `spanning` / `matrix-tree` / `determinant` /
  out-degree vocabulary at all, and BBT (Algorithmica 13:1-19, 2006) has no
  arborescence, no spanning-tree count, and no proof of its own Theorem 3 ---
  its Theorem 3 imports the step from Pevzner 1995, so **the chain is broken
  and terminates in nothing**.  What may be cited to Pevzner 1995 is Theorem 2,
  p. 81 (Abrham & Kotzig 1980, orbit connectivity on bicolored graphs) and
  Theorem 1 / Corollary 1, p. 80 (Kotzig-Nash-Williams balancedness); neither
  for a count, a bound, an out-degree estimate, or a uniqueness result.  The
  BEST theorem is cited from van Aardenne-Ehrenfest and de Bruijn, *Indag.
  Math.* (1951), or Tutte, LMS Lect. Notes 83 (1975).  The statement remains
  open here and is the single remaining mathematical input of the exported
  theorem.  No `sorry`, no
  `admit`, no new axiom: the exported theorem states it as an explicit
  hypothesis, and everything else in the chain is derived from it.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace AssemblyP1.BBTEulerian

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-! ## 1. The Eulerian cycle object of the condensed `(L-1)`-mer graph -/

/-- The origin of the circle of `G` positions, as a `Fin G`.  (Named because
`0 : Fin G` needs a `NeZero` instance that the arbitrary length `G` does not
carry.) -/
def origin (hG : 0 < G) : Fin G := ⟨0, hG⟩

@[simp] theorem origin_val (hG : 0 < G) : (origin hG).val = 0 := rfl

/-- **The successor of a traversal runs through the whole circle.**
`VisitsAll θ x` says that the first `G` iterates of `θ` at `x` are pairwise
distinct, i.e. `θ` is a `G`-cycle carrying `x`: the walk `fun x => θ x` is
*one* circuit of the graph and not a union of several.  This is the "single
Eulerian cycle" clause. -/
def VisitsAll {G : ℕ} (θ : Fin G → Fin G) (x : Fin G) : Prop :=
  Function.Injective (fun n : Fin G => θ^[n.val] x)

instance {G : ℕ} (θ : Fin G → Fin G) (x : Fin G) : Decidable (VisitsAll θ x) := by
  unfold VisitsAll
  infer_instance

/-- **An Eulerian cycle of the `(L-1)`-mer multigraph of the truth**, and
hence of its condensation, presented by the candidate-to-truth start map
`σ` of an equal-spectrum matching.

* `traverses`: consecutive elements of the listing `σ 0, σ 1, …` are
  joined by an edge, i.e. the vertex entered at `σ (i+1)` is the shift of
  the vertex entered at `σ i`.  This is
  `BBTSequenceGraph.match_next_vtx`;
* `single`: the successor `fun x => σ (nextPos (σ.symm x))` is a
  `G`-cycle, i.e. the walk is one closed circuit.

The condensation of `thm:BBT` is obtained from this multigraph by
contracting the unambiguous vertices
(`BBTSequenceGraph.branchStarts_eq_biUnion`), and an Eulerian cycle of the
multigraph induces one of the condensed graph; nothing in this definition
mentions the condensation explicitly, because `thm:BBT` asserts uniqueness
for the multigraph and the condensation is the same statement read on the
branch objects. -/
def EulerianCycle (σ : Fin G ≃ Fin G) : Prop :=
  (∀ i : Fin G, vtx hG L S (σ (nextPos hG i)) = vtx hG L S (nextPos hG (σ i))) ∧
  VisitsAll (fun x => σ (nextPos hG (σ.symm x))) (origin hG)

instance (σ : Fin G ≃ Fin G) : Decidable (EulerianCycle hG L S σ) := by
  unfold EulerianCycle
  infer_instance

/-- **The vertex cycle of a traversal**, i.e. the Eulerian cycle with the
presentation forgotten: the cyclic sequence of `(L-1)`-mers, modulo the
choice of the starting point.  `VertexCycleEq σ τ` says *the same Eulerian
cycle*, and is the object the uniqueness theorem is about. -/
def VertexCycleEq (σ τ : Fin G ≃ Fin G) : Prop :=
  ∃ k : Fin G, ∀ i : Fin G, vtx hG L S (σ i) = vtx hG L S (rotAdd hG k.val (τ i))

instance (σ τ : Fin G ≃ Fin G) : Decidable (VertexCycleEq hG L S σ τ) := by
  unfold VertexCycleEq
  infer_instance

/-- The identity presentation is a vertex cycle of itself, at every shift. -/
theorem vertexCycleEq_refl (σ : Fin G ≃ Fin G) (k : Fin G)
    (h : ∀ i : Fin G, vtx hG L S (σ i) = vtx hG L S (rotAdd hG k.val (σ i))) :
    VertexCycleEq hG L S σ σ :=
  ⟨k, h⟩

/-! ## 2. The Eulerian cycle of an equal-spectrum matching -/

/-- **Iterating the one-step rotation.** -/
theorem rotAdd_iterate (hG : 0 < G) (n : ℕ) (x : Fin G) :
    (nextPos hG)^[n] x = rotAdd hG n x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      unfold nextPos rotAdd
      apply Fin.ext
      show ((x.val + n) % G + 1) % G = (x.val + (n + 1)) % G
      rw [Nat.mod_add_mod]
      congr 1

/-- **One more step of the one-step rotation.** -/
theorem rotAdd_succ_add (hG : 0 < G) (n : ℕ) (x : Fin G) :
    rotAdd hG 1 (rotAdd hG n x) = rotAdd hG (n + 1) x := by
  apply Fin.ext
  show ((x.val + n) % G + 1) % G = (x.val + (n + 1)) % G
  rw [Nat.mod_add_mod]
  congr 1

/-- Shifts of the circle by less than a full turn are distinct: two shifts
`n`, `n'` of `G` positions agreeing at one position agree everywhere.  This
is the injectivity of the conjugating rotation, derived from
`BBTSequenceGraph.nextPos_inj` and `rotAdd_iterate`. -/
theorem rotAdd_inj_lt {G : ℕ} (hG : 0 < G) {n n' : Fin G} (x : Fin G)
    (h : rotAdd hG n.val x = rotAdd hG n'.val x) : n = n' := by
  have hinjg : Function.Injective (fun p : Fin G => rotAdd hG x.val p) := by
    have hfun : (fun p : Fin G => rotAdd hG x.val p) = (nextPos hG)^[x.val] := by
      funext p
      exact (rotAdd_iterate hG x.val p).symm
    rw [hfun]
    exact (nextPos_inj hG).iterate x.val
  have hshift : ∀ m : Fin G,
      rotAdd hG m.val x = rotAdd hG x.val (rotAdd hG m.val (origin hG)) := by
    intro m
    apply Fin.ext
    show (x.val + m.val) % G = ((0 + m.val) % G + x.val) % G
    simp only [Nat.zero_add]
    rw [Nat.mod_add_mod, Nat.add_comm]
  have heq : rotAdd hG n'.val (origin hG) = rotAdd hG n.val (origin hG) :=
    hinjg ((hshift n').symm.trans (h.symm.trans (hshift n)))
  refine Fin.ext ?_
  have h1 : n'.val % G = n.val % G := by
    simpa only [rotAdd, Fin.val_mk, origin_val, Nat.zero_add] using congrArg Fin.val heq
  rw [Nat.mod_eq_of_lt n'.isLt, Nat.mod_eq_of_lt n.isLt] at h1
  exact h1.symm

/-- **The successor of a pull-back presentation.** -/
theorem altSucc_iterate (hG : 0 < G) (μ : Fin G ≃ Fin G) (n : ℕ) :
    ∀ x : Fin G, (fun y => μ (nextPos hG (μ.symm y)))^[n] x
      = μ (rotAdd hG n (μ.symm x)) := by
  induction n with
  | zero =>
      intro x
      simp
  | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', ih]
      have hsymm : μ.symm (μ (rotAdd hG n (μ.symm x))) = rotAdd hG n (μ.symm x) :=
        Equiv.symm_apply_apply μ _
      have hstep : nextPos hG (rotAdd hG n (μ.symm x)) = rotAdd hG (n + 1) (μ.symm x) := by
        unfold nextPos
        exact rotAdd_succ_add hG n _
      rw [hsymm, hstep]

/-- **The pull-back of an equal-spectrum matching is an alternative Eulerian
cycle of the `(L-1)`-mer multigraph of the truth.**

The `traverses` clause is `BBTSequenceGraph.match_next_vtx`, reused
unchanged.  The `single` clause is the elementary computation that the
successor of the pull-back is the conjugate `μ ∘ rot₁ ∘ μ⁻¹` of the
one-step rotation by a bijection, hence a `G`-cycle; this is the step at
which the walk is a *cycle* rather than a decomposition of the circle, and
it is exactly the clause an arbitrary permutation of the starts can fail
(§4). -/
theorem pullback_isEulerianCycle {E : Fin G → α} {σ : Fin G → Fin G}
    (hm : Matching (L := L) hG S E σ) :
    EulerianCycle hG L S (pullback hG L S E hm.1) := by
  set μ : Fin G ≃ Fin G := pullback hG L S E hm.1 with hμdef
  refine ⟨?_, ?_⟩
  · intro i
    exact match_next_vtx hG L S E hm i
  · intro n₁ n₂ hn
    have h₁ := altSucc_iterate hG μ n₁ (origin hG)
    have h₂ := altSucc_iterate hG μ n₂ (origin hG)
    have hrot : rotAdd hG n₁.val (μ.symm (origin hG))
        = rotAdd hG n₂.val (μ.symm (origin hG)) := by
      refine Equiv.injective μ ?_
      have hn' : (fun y => μ (nextPos hG (μ.symm y)))^[n₁.val] (origin hG)
          = (fun y => μ (nextPos hG (μ.symm y)))^[n₂.val] (origin hG) := by
        simpa using hn
      rw [h₁, h₂] at hn'
      exact hn'
    exact Fin.ext (congrArg Fin.val (rotAdd_inj_lt hG (μ.symm (origin hG)) hrot))

/-- **The truth's own Eulerian cycle.** -/
theorem eulerianCycle_refl : EulerianCycle hG L S (Equiv.refl (α := Fin G)) := by
  refine ⟨?_, ?_⟩
  · intro i
    rfl
  · intro n₁ n₂ h
    have h' : (nextPos hG)^[n₁.val] (origin hG) = (nextPos hG)^[n₂.val] (origin hG) := by
      simpa using h
    have h₁ := rotAdd_iterate hG n₁.val (origin hG)
    have h₂ := rotAdd_iterate hG n₂.val (origin hG)
    rw [h₁, h₂] at h'
    exact rotAdd_inj_lt hG (origin hG) h'

/-- **A rotational vertex cycle makes the candidate a rotation of the
truth.**  This is the conclusion of `thm:BBT`: if the vertex cycle of the
alternative traversal of the condensed graph is the truth's own vertex
cycle, then the candidate spells the truth up to a cyclic shift. -/
theorem rotEquiv_of_vertexCycleEq {E : Fin G → α} (μ : Fin G ≃ Fin G) (hL : 2 ≤ L)
    (hk : VertexCycleEq hG L S μ (Equiv.refl (α := Fin G)))
    (hwin : ∀ s : Fin G, window (L := L) hG E s = window (L := L) hG S (μ s)) :
    RotEquiv hG E S := by
  obtain ⟨k, hk⟩ := hk
  have h0 : E = fun s => S (μ s) := by
    funext s
    have hE : E s = cyc hG E s.val :=
      (congrArg E (Fin.ext (Nat.mod_eq_of_lt s.isLt))).symm
    have hS : S (μ s) = cyc hG S (μ s).val :=
      (congrArg S (Fin.ext (Nat.mod_eq_of_lt (μ s).isLt))).symm
    have hwin0 := congrFun (hwin s) ⟨0, by omega⟩
    simp only [window] at hwin0
    rw [hE, hS]
    simpa only [Nat.add_zero] using hwin0
  have hsym : ∀ s : Fin G, S (μ s) = S (rotAdd hG k.val s) := by
    intro s
    have hS : S (μ s) = cyc hG S (μ s).val :=
      (congrArg S (Fin.ext (Nat.mod_eq_of_lt (μ s).isLt))).symm
    have hS' : S (rotAdd hG k.val s) = cyc hG S (rotAdd hG k.val s).val :=
      (congrArg S (Fin.ext (Nat.mod_eq_of_lt (rotAdd hG k.val s).isLt))).symm
    have hk0 := congrFun (hk s) ⟨0, by omega⟩
    simp only [vtx, nodeWindow, Equiv.refl_apply] at hk0
    rw [hS, hS']
    simpa only [Nat.add_zero] using hk0
  rw [h0]
  refine ⟨G - k.val, ?_⟩
  intro i
  show S (μ ⟨(i.val + (G - k.val)) % G, Nat.mod_lt _ hG⟩) = S i
  have hklt : k.val < G := k.isLt
  have hrot : rotAdd hG k.val ⟨(i.val + (G - k.val)) % G, Nat.mod_lt _ hG⟩ = i := by
    apply Fin.ext
    show (((i.val + (G - k.val)) % G + k.val) % G) = i.val
    exact rotAdd_neg_cancel hG k.val i.val i.isLt hklt
  have h1 := hsym ⟨(i.val + (G - k.val)) % G, Nat.mod_lt _ hG⟩
  rw [h1, hrot]

/-! ## 3. The long obstruction and `thm:BBT` in Eulerian-cycle form -/

/-- **The long obstruction of `def:P1P2` at `K = L - 1`:** a maximal triple
repeat of length `≥ L - 1`, or two interleaved maximal repeats both of
length `≥ L - 1`.  These are exactly the two ways in which `Ukkonen` (hence
`P2`, by `P2.imp_Ukkonen`) can fail. -/
def LongObstruction (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  (∃ e a b c : Fin G, (mkGenome hG S).IsTripleRepeat e a b c ∧ L - 1 ≤ e.val) ∨
  (∃ e₁ e₂ a b c d : Fin G, (mkGenome hG S).IsRepeat e₁ a b ∧
      (mkGenome hG S).IsRepeat e₂ c d ∧ Interleaved (mkGenome hG S) a b c d ∧
      L - 1 ≤ e₁.val ∧ L - 1 ≤ e₂.val)

/-- **`LongObstruction` is the negation of `Ukkonen`, clause by clause**: a
maximal triple repeat of length `≥ L - 1`, or an interleaved maximal repeat
pair *both* of whose constituents have length `≥ L - 1`. -/
theorem longObstruction_iff_not_Ukkonen {hG : 0 < G} {L : ℕ} {S : Fin G → α} :
    LongObstruction hG L S ↔ ¬ Ukkonen hG L S := by
  constructor
  · rintro (⟨e, a, b, c, ht, hlen⟩ | ⟨e₁, e₂, a, b, c, d, h1, h2, h3, hlen1, hlen2⟩) hU
    · exact absurd (hU.1 e a b c ht) (by omega)
    · exact absurd (hU.2 e₁ e₂ a b c d h1 h2 h3) (by omega)
  · intro h
    by_cases h1 : ∃ e a b c : Fin G,
        (mkGenome hG S).IsTripleRepeat e a b c ∧ L - 1 ≤ e.val
    · exact Or.inl h1
    · right
      by_cases h2 : ∃ e₁ e₂ a b c d : Fin G, (mkGenome hG S).IsRepeat e₁ a b ∧
          (mkGenome hG S).IsRepeat e₂ c d ∧ Interleaved (mkGenome hG S) a b c d ∧
          L - 1 ≤ e₁.val ∧ L - 1 ≤ e₂.val
      · exact h2
      · exfalso
        apply h
        refine ⟨?_, ?_⟩
        · intro e a b c ht
          by_contra hc
          exact h1 ⟨e, a, b, c, ht, by omega⟩
        · intro e₁ e₂ a b c d hr1 hr2 hi
          by_contra hc
          exact h2 ⟨e₁, e₂, a, b, c, d, hr1, hr2, hi, by omega, by omega⟩

/-- An `Ukkonen` word has no long obstruction. -/
theorem not_longObstruction_of_Ukkonen {hG : 0 < G} {L : ℕ} {S : Fin G → α}
    (hUkk : Ukkonen hG L S) : ¬ LongObstruction hG L S := by
  intro hLo
  exact (longObstruction_iff_not_Ukkonen (S := S)).mp hLo hUkk

/-- A `P2` word has no long obstruction (`P2` implies `Ukkonen`). -/
theorem not_longObstruction_of_P2 {hG : 0 < G} {L : ℕ} {S : Fin G → α}
    (hL : 2 ≤ L) (hP2 : P2 hG L S) : ¬ LongObstruction hG L S := by
  intro h
  rcases h with ⟨e, a, b, c, ht, hlen⟩ | ⟨e₁, e₂, a, b, c, d, h1, h2, h3, hlen1, hlen2⟩
  · exact absurd (P2.triple hG hP2 ht) (by omega)
  · rcases P2.interleaved hG hP2 h1 h2 h3 with hle | hle <;> omega

/-- **`thm:BBT` at `K = L - 1`, in the Eulerian-cycle form of Theorem 3 of
Bresler--Bresler--Tse 2013:** the `(L-1)`-mer graph built from the complete
`L`-spectrum, condensed, has a unique Eulerian cycle --- every alternative
Eulerian cycle has the *same vertex cycle* as the truth's. -/
def UniqueEulerianCycle (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α), Ukkonen hK L S →
    ∀ (σ : Fin K ≃ Fin K), EulerianCycle hK L S σ →
      VertexCycleEq hK L S σ (Equiv.refl (α := Fin K))

/-- **The same theorem in the requested obstruction form:** a non-rotational
alternative Eulerian cycle of the condensed graph forces either a maximal
triple repeat of length `≥ L - 1` or two interleaved maximal repeats both
of length `≥ L - 1`.  The first disjunct is exactly "the alternative
Eulerian cycle is the truth's own cycle, up to rotation of the cycle", so
this is `thm:BBT` with the dichotomy spelled out. -/
def EulerianCycleObstruction (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α), Ukkonen hK L S →
    ∀ (σ : Fin K ≃ Fin K), EulerianCycle hK L S σ →
      VertexCycleEq hK L S σ (Equiv.refl (α := Fin K)) ∨ LongObstruction hK L S

/-- The obstruction form and the uniqueness form of `thm:BBT` are
interchangeable: the second disjunct is excluded by the `Ukkonen`
hypothesis. -/
theorem uniqueEulerianCycle_of_obstruction {L : ℕ}
    (h : EulerianCycleObstruction (α := α) L) : UniqueEulerianCycle (α := α) L := by
  intro K hK S hUkk σ hEul
  rcases h K hK S hUkk σ hEul with hv | ho
  · exact hv
  · exact absurd ho (not_longObstruction_of_Ukkonen hUkk)

/-- ... and conversely. -/
theorem obstruction_of_uniqueEulerianCycle {L : ℕ}
    (h : UniqueEulerianCycle (α := α) L) : EulerianCycleObstruction (α := α) L := by
  intro K hK S hUkk σ hEul
  exact Or.inl (h K hK S hUkk σ hEul)

/-- **The dichotomy of #89, contrapositively: a non-rotational alternative
Eulerian cycle of the condensed graph forces the long obstruction** --- a
maximal triple repeat of length `≥ L - 1`, or two interleaved maximal
repeats both of length `≥ L - 1`.  This is the statement the packet was
asked for, with the hypothesis read at the right object: *non-rotational
Eulerian cycle of the condensed `(L-1)`-mer graph*, not *non-rotational
permutation of the starts* (see §4 for the two kernel-checked refutations of
the latter reading). -/
theorem longObstruction_of_nonrotational {L : ℕ}
    (h : UniqueEulerianCycle (α := α) L)
    {K : ℕ} (hK : 0 < K) (S : Fin K → α) (hUkk : Ukkonen hK L S)
    (σ : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S σ)
    (hnot : ¬ VertexCycleEq hK L S σ (Equiv.refl (α := Fin K))) :
    LongObstruction hK L S := by
  exact False.elim (hnot (h K hK S hUkk σ hEul))

/-- **The reduction to `thm:BBT` as the project states it:** an `Ukkonen`
truth and a candidate with the same complete `L`-spectrum determine each
other up to cyclic rotation.  Nothing here uses the graph structure beyond
`BBTSequenceGraph.match_next_vtx`, which is §3 of `BBTCondense`. -/
theorem bbtCompleteSpec_of_obstruction {L : ℕ} (hL : 2 ≤ L)
    (hObs : EulerianCycleObstruction (α := α) L) :
    ∀ (K : ℕ) (hK : 0 < K) (S E : Fin K → α), Ukkonen hK L S →
      specCount (L := L) hK S = specCount (L := L) hK E → RotEquiv hK E S := by
  intro K hK S E hUkk hspec
  obtain ⟨σ, hm⟩ := exists_matching hK S E hspec
  have hEul : EulerianCycle hK L S (pullback hK L S E hm.1) :=
    pullback_isEulerianCycle hK L S hm
  rcases hObs K hK S hUkk (pullback hK L S E hm.1) hEul with hv | ho
  · exact rotEquiv_of_vertexCycleEq hK L S (pullback hK L S E hm.1) hL hv
      (fun s => (pullback_window hK L S E hm s).symm)
  · exact absurd ho (not_longObstruction_of_Ukkonen hUkk)

/-- **`AssemblyP1.P2.BBTUniqueAt` is a theorem, not an assumption.** -/
theorem bbtUniqueAt_of_obstruction {L : ℕ} (hL : 2 ≤ L)
    (hObs : EulerianCycleObstruction (α := α) L) : BBTUniqueAt (α := α) L := by
  intro K hK W E hUkk hspec
  exact bbtCompleteSpec_of_obstruction hL hObs K hK W E hUkk hspec

/-- **`thm:BBT` at `K = L - 1` for a `P2` truth, in the form the population
chain consumes:** a candidate with the same complete `L`-spectrum is a
cyclic shift of the truth. -/
theorem bbt_of_P2_obstruction {L : ℕ} (hL : 2 ≤ L)
    (hObs : EulerianCycleObstruction (α := α) L) :
    ∀ (K : ℕ) (hK : 0 < K) (S E : Fin K → α), P2 hK L S →
      specCount (L := L) hK S = specCount (L := L) hK E → RotEquiv hK E S := by
  intro K hK S E hP2 hspec
  exact bbtCompleteSpec_of_obstruction hL hObs K hK S E
    (P2.imp_Ukkonen hL hP2) hspec

/-! ## 4. Which objects are, and are not, alternative Eulerian cycles -/

section Objects

variable {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-! ### 4.1 A permutation of the starts which is not an Eulerian cycle -/

/-- `S = 001`, at `G = 3`, `L = 3` (so `K = 2`). -/
def S3 : Fin 3 → Fin 2 := ![0, 0, 1]

theorem hG3 : 0 < 3 := by decide

/-- The permutation `(0 2 1)` of the three starts of `S3`. -/
def tau3 : Fin 3 ≃ Fin 3 := Equiv.swap 1 2

/-- **The vertex cycle of `tau3` is not the truth's vertex cycle.**  The
three `(L-1)`-mers of `S = 001` are pairwise distinct, and `tau3` reads them
in an order which is not a rotation of the truth's order.  This is the
"arbitrary permutation of the starts" object: it is *not* a counterexample
to `thm:BBT`, because it is not an Eulerian cycle of the condensed graph at
all (`not_eulerianCycle_validity` below). -/
theorem not_vertexCycleEq : ¬ VertexCycleEq hG3 3 S3 tau3 (Equiv.refl (α := Fin 3)) := by
  decide

/-- **`tau3` is not an Eulerian cycle of the condensed graph**: the vertex
it enters at the second start is not the shift of the vertex it enters at
the first.  This is the kernel-checked reason why the theorem of #89 must be
stated for Eulerian cycles and not for permutations of equal-labelled
starts: the object `tau3` lies outside `thm:BBT`. -/
theorem not_eulerianCycle_validity : ¬ EulerianCycle hG3 3 S3 tau3 := by
  decide

/-! ### 4.2 A non-rotational pull-back which is a *trivial* Eulerian cycle

The instance below is the anti-vacuity check for the present module: the
pull-back of an equal-spectrum matching need not be a rotation of the
circle, and it need not carry a long obstruction --- because it is a
presentation of the truth's own Eulerian cycle, read from a different
start.  A statement of `thm:BBT` in terms of *non-rotational pull-backs*
would be false on this instance; a statement in terms of *non-rotational
Eulerian cycles* is not. -/

/-- `S = 0101`, at `G = 4`, `L = 3` (so `K = 2`). -/
def S4 : Fin 4 → Fin 2 := ![0, 1, 0, 1]

theorem hG4 : 0 < 4 := by decide

/-- The pull-back `(0 1)(2 3)`: an involution, hence not a rotation of the
four-position circle (`not_rotation_S4` below). -/
def tau4 : Fin 4 ≃ Fin 4 := (Equiv.swap 0 1).trans (Equiv.swap 2 3)

/-- It *is* an alternative Eulerian cycle of the `(L-1)`-mer multigraph of
`S = 0101`. -/
theorem eulerianCycle_S4 : EulerianCycle hG4 3 S4 tau4 := by
  decide

/-- And its vertex cycle is the truth's own vertex cycle, read from the
start `1`: no long obstruction is available, and none is needed. -/
theorem trivial_vertexCycleEq_S4 :
    VertexCycleEq hG4 3 S4 tau4 (Equiv.refl (α := Fin 4)) := by
  decide

/-- ... while the pull-back itself is **not** a rotation of the circle.  So
"the pull-back is not a rotation" is *not* the hypothesis that forces the
long obstruction: the object that does is a non-rotational *Eulerian
cycle*. -/
theorem not_rotation_S4 : ¬ IsRotation hG4 tau4 := by
  rintro ⟨s, hs⟩
  have e0 : tau4 (0 : Fin 4) = 1 := by decide
  have e1 : tau4 (1 : Fin 4) = 0 := by decide
  have h0 : (0 + s) % 4 = 1 := by
    have h := hs (0 : Fin 4)
    rw [e0] at h
    exact Fin.mk.inj h.symm
  have h1 : (1 + s) % 4 = 0 := by
    have h := hs (1 : Fin 4)
    rw [e1] at h
    exact Fin.mk.inj h.symm
  have hq := Nat.mod_add_div s 4
  omega

end Objects

end AssemblyP1.BBTEulerian
