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
  the Eulerian cycle of the condensed graph.  This is the Pevzner 1995
  Lemma 9 / `thm:BBT` input; it is still open here and is the single
  remaining mathematical input of the exported theorem.  No `sorry`, no
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

/-! ## 5. The condensation bookkeeping of an alternative Eulerian cycle

`docs/bbt-eulerian-cycle-89.md` §6 lists the sub-steps a proof of
`EulerianCycleObstruction` needs.  The first of them --- *"an alternative
Eulerian cycle differs from the truth's only at branch occurrences"* --- was
available only for the pull-back of an equal-spectrum `Matching`
(`BBTSequenceGraph.match_next_vtx`, `choices_only_at_branch`), because §2's
object was tied to a matching.  `EulerianCycle` is *not* tied to a matching,
and this section redoes the bookkeeping for an arbitrary `EulerianCycle` of
the condensed `(L-1)`-mer multigraph, in the form the final theorem consumes.

Three points are separated, because they are three different claims and only
the first is bookkeeping.

* **Multiplicity.**  `card_visits_eq_deg` and `card_succVisits_eq_deg`: an
  Eulerian cycle enters a vertex exactly `deg` times, i.e. it uses every
  edge of the multigraph exactly once, so the multiset of visited vertices is
  a *presentation-independent* property of the multigraph.  Hence an
  alternative Eulerian cycle cannot be a genuine rematching of the truth at
  more places than the number of occurrences of the vertices involved
  (`card_departCharged_le_deg`).
* **Locality at branch objects.**  `altSucc_same_vtx`,
  `forced_at_unambiguous_of_eulerian` and `departure_at_branch`: at an
  occurrence `x` of the truth, the alternative cycle leaves along an edge
  with *the same target vertex* as the truth
  (`vtx (altSucc σ x) = vtx (nextPos x)`), so a departure is a *rematching
  of two distinct occurrences of one and the same vertex*, and it can happen
  only where that vertex is a branch object.  `card_depart_le_branchStarts`
  is the quantitative form.
* **Excluding relabelled presentations.**  `departSet_empty_iff_isRotation`:
  a presentation with no departures at all is a rotation of the circle, and
  a rotation has the truth's vertex cycle
  (`vertexCycleEq_of_isRotation`).  So the only presentations excluded by
  the bookkeeping are the relabellings of the truth's own cycle, and
  `branchDeparture_of_nonVertexCycleEq` shows that anything else produces a
  genuine branch occurrence of the truth's traversal.

`condensationBookkeeping` bundles the whole bookkeeping into one statement
and `branchDeparture_of_nonVertexCycleEq` is the single theorem the final
uniqueness step should cite: an alternative Eulerian cycle whose *vertex
cycle* is not the truth's yields, in the truth's own traversal, a branch
occurrence carrying a pair of distinct occurrences of the same vertex.
**No hypothesis at all is used** --- in particular no `Ukkonen`, no `P2` and
no primitivity: the bookkeeping is a property of the multigraph, not of the
admissibility of the word.  Primitivity is needed only by the *next* step,
the maximal extension of a branch pair to a maximal repeat
(`docs/audit-p2-direct-proof-maximal-extension-2026-09-21.md`), which this
section does not touch; the multiplicity cap `∀ v, deg v ≤ 2` needed by
`card_depart_le_two_mul_branchVerts` is likewise taken as a hypothesis,
because deriving it from `P2` is part of that same step. -/

section Bookkeeping

variable {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-- **The successor of the alternative traversal, in the truth's own
frame.**  `altSucc hG σ x` is the truth start at which the alternative
Eulerian cycle continues after its occurrence at `x`: the alternative cycle
is a cyclic listing `σ 0, σ 1, …` of the edges of the multigraph, and
`altSucc` is the successor relation of that listing, transported to the
truth's positions.  It is a bijection, being the conjugate of `nextPos` by
`σ`. -/
def altSucc (hG : 0 < G) (σ : Fin G ≃ Fin G) : Fin G → Fin G :=
  fun x => σ (nextPos hG (σ.symm x))

theorem altSucc_apply (hG : 0 < G) (σ : Fin G ≃ Fin G) (x : Fin G) :
    altSucc hG σ x = σ (nextPos hG (σ.symm x)) := rfl

/-- **The successor of an alternative Eulerian cycle is a permutation of the
circle**: the walk is a single circuit, so no position is visited twice and
none is skipped.  (The `single` clause of `EulerianCycle` says this; this is
the same fact as an injectivity of the successor map.) -/
theorem altSucc_bij (hG : 0 < G) (σ : Fin G ≃ Fin G) :
    Function.Bijective (altSucc hG σ) := by
  constructor
  · intro a b h
    have h' : σ (nextPos hG (σ.symm a)) = σ (nextPos hG (σ.symm b)) := h
    have h'' : nextPos hG (σ.symm a) = nextPos hG (σ.symm b) := σ.injective h'
    exact σ.injective (nextPos_inj hG h'')
  · intro b
    refine ⟨σ (nextPos hG (σ.symm b)), ?_⟩
    have h' : σ (nextPos hG (σ.symm (σ (nextPos hG (σ.symm b))))) = b := by
      rw [Equiv.symm_apply_apply]
      exact Equiv.apply_symm_apply σ b
    exact h'

/-- **The occurrences at which the alternative Eulerian cycle departs from
the truth's traversal.**  These are the *chords* of the condensation in the
truth's own frame. -/
noncomputable def departSet (hG : 0 < G) (L : ℕ) (S : Fin G → α)
    (σ : Fin G ≃ Fin G) : Finset (Fin G) :=
  Finset.univ.filter (fun x : Fin G => altSucc hG σ x ≠ nextPos hG x)

instance (hG : 0 < G) (σ : Fin G ≃ Fin G) :
    DecidablePred (fun x : Fin G => altSucc hG σ x ≠ nextPos hG x) :=
  fun x => inferInstanceAs (Decidable (altSucc hG σ x ≠ nextPos hG x))

theorem mem_departSet (hG : 0 < G) (L : ℕ) (S : Fin G → α) (σ : Fin G ≃ Fin G)
    {x : Fin G} :
    x ∈ departSet hG L S σ ↔ altSucc hG σ x ≠ nextPos hG x := by
  simp only [departSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Multiplicity: an Eulerian cycle enters a vertex exactly `deg` times.**
The listing `σ 0, σ 1, …` of an Eulerian cycle is a permutation of the
starts, so the number of positions at which it enters the vertex `v` is the
number of occurrences of `v`, i.e. its out-degree --- the same number the
truth's own traversal has.  This is the *edge-multiset* content of
"Eulerian", and it holds for every `σ`, in particular for every alternative
Eulerian cycle. -/
theorem card_visits_eq_deg (σ : Fin G ≃ Fin G) (v : Fin (L - 1) → α) :
    (Finset.univ.filter (fun i : Fin G => vtx hG L S (σ i) = v)).card = deg hG L S v := by
  calc (Finset.univ.filter (fun i : Fin G => vtx hG L S (σ i) = v)).card
      = (fibre hG L S v).card := by
        refine Finset.card_bij (fun i _ => σ i) ?_ ?_ ?_
        · intro i hi
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (mem_fibre hG S (v := v) (r := σ i)).mpr (Finset.mem_filter.mp hi).2⟩
        · intro _ _ _ _ heq
          exact σ.injective heq
        · intro b hb
          refine ⟨σ.symm b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · exact (mem_fibre hG S (v := v) (r := σ.symm b)).mpr hb
          · exact Equiv.apply_symm_apply σ b
    _ = deg hG L S v := card_fibre hG L S v

/-- **... and it *leaves* a vertex exactly `deg` times too**, the
`altSucc` version of `card_visits_eq_deg`.  So the in-degree bookkeeping of
the multigraph (`inDeg_eq_deg`) is reproduced by every Eulerian cycle. -/
theorem card_succVisits_eq_deg (σ : Fin G ≃ Fin G) (v : Fin (L - 1) → α) :
    (Finset.univ.filter (fun x : Fin G => vtx hG L S (altSucc hG σ x) = v)).card
      = deg hG L S v := by
  calc (Finset.univ.filter (fun x : Fin G => vtx hG L S (altSucc hG σ x) = v)).card
      = (fibre hG L S v).card := by
        refine Finset.card_bij (fun x _ => altSucc hG σ x) ?_ ?_ ?_
        · intro x hx
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (mem_fibre hG S (v := v) (r := altSucc hG σ x)).mpr
              (Finset.mem_filter.mp hx).2⟩
        · intro _ _ _ _ heq
          exact (altSucc_bij hG σ).1 heq
        · intro b hb
          refine ⟨σ (nextPos hG (σ.symm b)), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · rw [altSucc, Equiv.symm_apply_apply]
            exact (mem_fibre hG S (v := v) (r := b)).mpr hb
          · rw [altSucc, Equiv.symm_apply_apply]
            exact Equiv.apply_symm_apply σ b
    _ = deg hG L S v := card_fibre hG L S v

/-- **Multiplicity in the truth's frame: the occurrences entered *after* the
position `x` are `deg` many.**  This is the count the departures are charged
against. -/
theorem card_nextPosVisits_eq_deg (v : Fin (L - 1) → α) :
    (Finset.univ.filter (fun x : Fin G => vtx hG L S (nextPos hG x) = v)).card
      = deg hG L S v := by
  calc (Finset.univ.filter (fun x : Fin G => vtx hG L S (nextPos hG x) = v)).card
      = (fibre hG L S v).card := by
        refine Finset.card_bij (fun x _ => nextPos hG x) ?_ ?_ ?_
        · intro x hx
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (mem_fibre hG S (v := v) (r := nextPos hG x)).mpr
              (Finset.mem_filter.mp hx).2⟩
        · intro _ _ _ _ heq
          exact nextPos_inj hG heq
        · intro b hb
          refine ⟨prevPos hG b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · rw [nextPrev hG b]
            exact (mem_fibre hG S (v := v) (r := b)).mpr hb
          · exact nextPrev hG b
    _ = deg hG L S v := card_fibre hG L S v

/-- **The target vertex of a departure.**  The `traverses` clause of
`EulerianCycle`, read in the truth's frame: the alternative cycle leaves the
occurrence `x` along an edge whose *target vertex* is the target vertex of
the truth's own edge out of `x`.  Consequently a departure at `x` is a
*rematching of occurrences of one and the same vertex*, not a visit to a new
vertex: the alternative cycle reuses exactly the vertex multiset of the
truth.  This is the bridge between the multigraph layer and the condensed
branch objects. -/
theorem altSucc_same_vtx (σ : Fin G ≃ Fin G)
    (hEul : EulerianCycle hG L S σ) (x : Fin G) :
    vtx hG L S (altSucc hG σ x) = vtx hG L S (nextPos hG x) := by
  have h1 := hEul.1 (σ.symm x)
  have h2 : σ (σ.symm x) = x := Equiv.apply_symm_apply σ x
  simpa only [altSucc, h2] using h1

/-- **No choice at an unambiguous vertex, for an arbitrary Eulerian cycle.**
If the vertex the truth enters at `x` is not a branch object, the
alternative cycle is forced to continue exactly where the truth does: the
two occurrences spelling that vertex are the same occurrence.  This is
`BBTSequenceGraph.forced_at_unambiguous` re-proved without any `Matching`
hypothesis, which is what an alternative Eulerian cycle of the condensed
graph needs. -/
theorem forced_at_unambiguous_of_eulerian (σ : Fin G ≃ Fin G)
    (hEul : EulerianCycle hG L S σ) {x : Fin G}
    (hdeg : deg hG L S (vtx hG L S (nextPos hG x)) ≤ 1) :
    altSucc hG σ x = nextPos hG x :=
  occ_unique hG L S _ hdeg (altSucc_same_vtx hG L S σ hEul x) rfl

/-- **Departures of an alternative Eulerian cycle live at branch
occurrences.**  If the alternative Eulerian cycle continues somewhere other
than where the truth does, then the vertex the truth enters there is a
branch object, i.e. an occurrence of a condensed vertex --- so the
alternative cycle uses every edge of the multigraph exactly once, *except*
that at branch objects it permutes the occurrences.  No `Matching`, no
`Ukkonen`, no primitivity. -/
theorem departure_at_branch (σ : Fin G ≃ Fin G) (hEul : EulerianCycle hG L S σ)
    {x : Fin G} (hd : altSucc hG σ x ≠ nextPos hG x) :
    Branch hG L S (vtx hG L S (nextPos hG x)) := by
  by_contra hn
  have hdeg : deg hG L S (vtx hG L S (nextPos hG x)) ≤ 1 := by
    unfold Branch deg at hn
    unfold deg
    omega
  exact hd (forced_at_unambiguous_of_eulerian hG L S σ hEul hdeg)

/-- ... i.e. the *vertex* the truth enters at a departure is a condensed
vertex of `thm:BBT`. -/
theorem mem_branchStarts_of_departure (σ : Fin G ≃ Fin G)
    (hEul : EulerianCycle hG L S σ) {x : Fin G}
    (hd : altSucc hG σ x ≠ nextPos hG x) :
    nextPos hG x ∈ branchStarts hG L S :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    departure_at_branch hG L S σ hEul hd⟩

/-- **Multiplicity, quantitatively: the departures charged to a vertex `v`
are charged against its `deg` occurrences.**  So the freedom of an
alternative Eulerian cycle at a condensed vertex is bounded by the
multiplicity of that vertex, and cannot be spread over more positions than
the vertex actually occupies. -/
theorem card_departCharged_le_deg (σ : Fin G ≃ Fin G) (v : Fin (L - 1) → α) :
    ((departSet hG L S σ).filter
        (fun x : Fin G => vtx hG L S (nextPos hG x) = v)).card ≤ deg hG L S v := by
  refine Finset.card_le_card ?_
  intro x hx
  exact (mem_fibre hG S (v := v) (r := x)).mpr (Finset.mem_filter.mp hx).2

/-- **Total count: the whole freedom of an alternative Eulerian cycle is at
most the number of branch occurrences**, the quantitative form of "alternate
Eulerian choices occur only at condensed branch objects" --- now for an
arbitrary `EulerianCycle`, not only for a pull-back of a `Matching`. -/
theorem card_depart_le_branchStarts (σ : Fin G ≃ Fin G)
    (hEul : EulerianCycle hG L S σ) :
    (departSet hG L S σ).card ≤ (branchStarts hG L S).card := by
  have hsub : (departSet hG L S σ).image (fun x : Fin G => nextPos hG x)
      ⊆ branchStarts hG L S := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact mem_branchStarts_of_departure hG L S σ hEul
      (Finset.mem_filter.mp hx).2
  calc (departSet hG L S σ).card
      = ((departSet hG L S σ).image (fun x : Fin G => nextPos hG x)).card :=
        (Finset.card_image_of_injective _ (nextPos_inj hG)).symm
    _ ≤ (branchStarts hG L S).card := Finset.card_le_card hsub

/-- ... hence at most `G`, and, under the multiplicity cap, at most twice
the number of condensed vertices. -/
theorem card_depart_le_card (σ : Fin G ≃ Fin G) (hEul : EulerianCycle hG L S σ) :
    (departSet hG L S σ).card ≤ G := by
  calc (departSet hG L S σ).card ≤ (branchStarts hG L S).card :=
        card_depart_le_branchStarts hG L S σ hEul
    _ ≤ (Finset.univ : Finset (Fin G)).card := Finset.card_le_univ _
    _ = G := by simp

theorem card_depart_le_two_mul_branchVerts (σ : Fin G ≃ Fin G)
    (hEul : EulerianCycle hG L S σ)
    (hcap : ∀ v : Fin (L - 1) → α, deg hG L S v ≤ 2) :
    (departSet hG L S σ).card ≤ 2 * (branchVerts hG L S).card :=
  calc (departSet hG L S σ).card ≤ (branchStarts hG L S).card :=
        card_depart_le_branchStarts hG L S σ hEul
    _ ≤ 2 * (branchVerts hG L S).card :=
        card_branchStarts_le_two_mul_branchVerts hG L S hcap

/-! ### 5.1 Excluding mere relabelled presentations -/

/-- **A relabelled presentation of the truth's own cycle has no
departures.**  A rotation of the circle is the truth's own traversal read
from a different start, and reads the vertices in the same cyclic order. -/
theorem departSet_empty_of_isRotation (σ : Fin G ≃ Fin G) (hrot : IsRotation hG σ) :
    (departSet hG L S σ) = ∅ := by
  obtain ⟨s, hs⟩ := hrot
  ext x
  simp only [mem_departSet, Finset.mem_univ, true_and]
  intro hne
  have hstep : σ (nextPos hG (σ.symm x)) = nextPos hG x := by
    have h1 : σ (nextPos hG (σ.symm x)) = nextPos hG (σ (σ.symm x)) := by
      have h := hs (nextPos hG (σ.symm x))
      rwa [Equiv.symm_apply_apply] at h
    simpa using h1
  exact hne hstep

/-- **Conversely: an alternative Eulerian cycle with no departure at all is
a rotation of the circle.**  No departure means the alternative cycle agrees
with the truth *everywhere*, not merely up to a relabelling; and a
step-by-step map of the circle is a rotation
(`BBTSequenceGraph.isRotation_of_step`).  So "no departure" and "rotation"
are the same condition, and the relabellings of the truth's own Eulerian
cycle are exactly the presentations with an empty departure set. -/
theorem isRotation_of_departSet_empty (σ : Fin G ≃ Fin G)
    (hEul : EulerianCycle hG L S σ) (he : (departSet hG L S σ) = ∅) :
    IsRotation hG σ := by
  apply isRotation_of_step hG
  intro i
  have hmem : σ i ∉ departSet hG L S σ := by
    rw [he]
    simp
  have hne : altSucc hG σ (σ i) ≠ nextPos hG (σ i) := by
    exact fun h => hmem ((mem_departSet hG L S σ).mpr h)
  have heq : altSucc hG σ (σ i) = nextPos hG (σ i) := by
    apply Classical.byContradiction
    exact hne
  simpa only [altSucc, Equiv.apply_symm_apply] using heq

theorem departSet_empty_iff_isRotation (σ : Fin G ≃ Fin G)
    (hEul : EulerianCycle hG L S σ) :
    (departSet hG L S σ) = ∅ ↔ IsRotation hG σ :=
  ⟨isRotation_of_departSet_empty hG L S σ hEul,
    departSet_empty_of_isRotation hG L S σ⟩

/-- **A rotation of the circle has the truth's vertex cycle.**  This is the
"merely relabelled" observation at the level of the *vertex cycle*, the
object the uniqueness theorem is about. -/
theorem vertexCycleEq_of_isRotation (σ : Fin G ≃ Fin G) (hrot : IsRotation hG σ) :
    VertexCycleEq hG L S σ (Equiv.refl (α := Fin G)) := by
  obtain ⟨s, hs⟩ := hrot
  exact ⟨⟨s % G, Nat.mod_lt _ hG⟩, fun i => hs i⟩

/-- Hence a presentation that is not the truth's vertex cycle is in
particular not a rotation: the relabelled presentations are exactly the ones
the uniqueness theorem has already accounted for. -/
theorem not_isRotation_of_not_vertexCycleEq (σ : Fin G ≃ Fin G)
    (hnot : ¬ VertexCycleEq hG L S σ (Equiv.refl (α := Fin G))) :
    ¬ IsRotation hG σ := fun hrot => hnot (vertexCycleEq_of_isRotation hG L S σ hrot)

/-- **The truth's own vertex cycle is a presentation of an Eulerian cycle
with no departure at all**: `Equiv.refl` *is* the truth's traversal. -/
theorem departSet_empty_of_refl : (departSet hG L S (Equiv.refl (α := Fin G))) = ∅ := by
  ext x
  simp only [mem_departSet, Finset.mem_univ, true_and]
  rfl

/-! ### 5.2 The bundled statement, and the one theorem the final step cites -/

/-- **The condensation bookkeeping of an alternative Eulerian cycle**,
bundled: the multiset of visited vertices is the truth's (multiplicity),
the alternative cycle leaves every occurrence along an edge of the truth's
own target vertex, it departs only at branch occurrences, the departures are
charged against the multiplicity of the vertex concerned, and the
presentations with no departure at all are exactly the rotations --- i.e.
the mere relabellings of the truth's cycle.  No hypothesis is required. -/
def CondensationBookkeeping (hG : 0 < G) (L : ℕ) (S : Fin G → α) (σ : Fin G ≃ Fin G) :
    Prop :=
  EulerianCycle hG L S σ →
    (∀ v : Fin (L - 1) → α,
        ((Finset.univ : Finset (Fin G)).filter
          (fun i : Fin G => vtx hG L S (σ i) = v)).card = deg hG L S v) ∧
    (∀ v : Fin (L - 1) → α,
        ((Finset.univ : Finset (Fin G)).filter
          (fun x : Fin G => vtx hG L S (altSucc hG σ x) = v)).card = deg hG L S v) ∧
    (∀ x : Fin G, vtx hG L S (altSucc hG σ x) = vtx hG L S (nextPos hG x)) ∧
    (∀ x : Fin G, altSucc hG σ x ≠ nextPos hG x →
        Branch hG L S (vtx hG L S (nextPos hG x))) ∧
    (∀ v : Fin (L - 1) → α,
        ((departSet hG L S σ).filter
          (fun x : Fin G => vtx hG L S (nextPos hG x) = v)).card ≤ deg hG L S v) ∧
    (departSet hG L S σ).card ≤ (branchStarts hG L S).card ∧
    ((departSet hG L S σ) = ∅ ↔ IsRotation hG σ)

/-- ... and it holds, with no hypothesis beyond the Eulerian-cycle
hypothesis itself. -/
theorem condensationBookkeeping (σ : Fin G ≃ Fin G) :
    CondensationBookkeeping hG L S σ := by
  intro hEul
  exact ⟨fun v => card_visits_eq_deg hG L S σ v,
    fun v => card_succVisits_eq_deg hG L S σ v,
    fun x => altSucc_same_vtx hG L S σ hEul x,
    fun _ hd => departure_at_branch hG L S σ hEul hd,
    fun v => card_departCharged_le_deg hG L S σ v,
    card_depart_le_branchStarts hG L S σ hEul,
    departSet_empty_iff_isRotation hG L S σ hEul⟩

/-- **The branch occurrences an alternative Eulerian cycle yields in the
truth's traversal.**  If an alternative Eulerian cycle of the condensed
`(L-1)`-mer graph has a vertex cycle that is *not* the truth's, then in the
truth's own traversal there is a position at which the alternative cycle
continues elsewhere; the vertex the truth enters there is a branch object,
hence a condensed vertex, and it carries a pair of distinct occurrences in
the truth --- the two ends of the chord, i.e. the data the next step of the
proof (maximal extension of a branch pair, then the triple/interleaved
dichotomy) consumes.  Because `not_isRotation_of_not_vertexCycleEq` has
already excluded the relabelled presentations, the position is a genuine
rematching and not an artefact of the choice of starting point.

No `Ukkonen`, no `P2`, no primitivity: this is a statement about the
multigraph. -/
theorem branchDeparture_of_nonVertexCycleEq (σ : Fin G ≃ Fin G)
    (hEul : EulerianCycle hG L S σ)
    (hnot : ¬ VertexCycleEq hG L S σ (Equiv.refl (α := Fin G))) :
    ∃ x : Fin G, altSucc hG σ x ≠ nextPos hG x ∧
      Branch hG L S (vtx hG L S (nextPos hG x)) ∧
      ∃ a b : Fin G, a ≠ b ∧ vtx hG L S a = vtx hG L S b ∧
        vtx hG L S a = vtx hG L S (nextPos hG x) := by
  have hndep : (departSet hG L S σ).card ≥ 1 := by
    have hne : (departSet hG L S σ) ≠ ∅ := by
      intro he
      exact not_isRotation_of_not_vertexCycleEq hG L S σ hnot
        (isRotation_of_departSet_empty hG L S σ hEul he)
    rw [Finset.card_ne_zero]
    intro h
    exact hne h
  obtain ⟨x, hx⟩ := Finset.card_ne_zero.mp hndep
  have hd : altSucc hG σ x ≠ nextPos hG x := (mem_departSet hG L S σ).mp hx
  obtain ⟨a, b, hab, ha, hb⟩ :=
    branch_has_two_occurrences hG L S _ (departure_at_branch hG L S σ hEul hd)
  refine ⟨x, hd, departure_at_branch hG L S σ hEul hd, a, b, hab, ?_, ?_⟩
  · exact ha.trans (altSucc_same_vtx hG L S σ hEul x).symm
  · exact hb.trans (altSucc_same_vtx hG L S σ hEul x).symm

/-- **... and a branch occurrence with a pair of distinct occurrences is
already enough for the next step, i.e. the condensation bookkeeping is not
vacuous**: the number of branch occurrences is positive exactly when the
truth admits a rematching at all.  (Only the *existence* direction is
claimed here; the dichotomy of `LongObstruction` is the next step and is not
attempted.) -/
theorem exists_branchStarts_of_departSet_ne_empty (σ : Fin G ≃ Fin G)
    (hEul : EulerianCycle hG L S σ) (hne : (departSet hG L S σ) ≠ ∅) :
    (branchStarts hG L S).card ≥ 1 := by
  obtain ⟨x, hx⟩ := Finset.card_ne_zero.mp (by rw [Finset.card_pos]; exact hne)
  have hx' := mem_branchStarts_of_departure hG L S σ hEul (Finset.mem_filter.mp hx).1
  have hsub : ({x} : Finset (Fin G)) ⊆ branchStarts hG L S :=
    Finset.singleton_subset_iff.mpr (by simpa using hx')
  have := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at this
  omega

end Bookkeeping

/-! ### 5.3 A kernel-checked instance: the bookkeeping output is the input
of the dichotomy

`S = 001011` at `G = 6`, `L = 3` (so `K = 2`) is the smallest binary
circular word whose condensed `(L-1)`-mer multigraph admits two *vertex
cycles*.  Its `(L-1)`-mers are `00, 01, 10, 01, 11, 10`, so the condensed
vertices are `01` and `10`, each of degree `2`, with branch occurrences
`{1, 3}` and `{2, 5}`: four branch occurrences, i.e. `2 + 2`.

`tau6` is the alternative Eulerian cycle which visits the branch occurrences
`1` and `3` one after the other, instead of the truth's `1, 2, 3, 5`.  The
instance records

* `eulerianCycle_S6`: it *is* an Eulerian cycle of the condensed graph;
* `not_vertexCycleEq_S6`: its vertex cycle is not the truth's (hence, by
  `not_isRotation_of_not_vertexCycleEq`, it is not a relabelling);
* `card_departSet_S6` and `card_branchStarts_S6`: all four branch
  occurrences are charged --- the departure set has the full `4` branch
  occurrences, the tight case of `card_depart_le_branchStarts`;
* `interleaved_obstruction_S6`: the two maximal extensions of the two
  branches are the interleaved pair `(1, 3)`, `(2, 5)`, both of length `2 =
  L - 1`, i.e. the *second* disjunct of `LongObstruction` holds here.  This is
  a single instance of the dichotomy, kernel-checked; the dichotomy itself is
  still not proved. -/

section Instance

/-- `S = 001011`, at `G = 6`, `L = 3` (so `K = 2`). -/
def S6 : Fin 6 → Fin 2 := ![0, 0, 1, 0, 1, 1]

theorem hG6 : 0 < 6 := by decide

/-- The alternative Eulerian cycle of `S6`: the listing
`0, 3, 4, 2, 1, 5` of the edges, i.e. the cyclic order
`00 → 01 → 11 → 10 → 01 → 10 → 00`, in which the two occurrences of `01`
(positions `1` and `3`) are used one after the other rather than being
separated. -/
def tau6 : Fin 6 ≃ Fin 6 :=
  { toFun := fun i => ![0, 3, 4, 2, 1, 5] i.val
    invFun := fun i => ![0, 1, 3, 4, 2, 5] i.val
    left_inv := by decide
    right_inv := by decide }

/-- It *is* an alternative Eulerian cycle of the condensed `(L-1)`-mer
multigraph of `S = 001011`. -/
theorem eulerianCycle_S6 : EulerianCycle hG6 3 S6 tau6 := by
  decide

/-- **Its vertex cycle is not the truth's vertex cycle**, so it is not a
relabelling of the truth's own cycle either.  This is the shape a proof of
`EulerianCycleObstruction` has to rule out, and it is a real instance of it:
the word does carry the long obstruction (`interleaved_obstruction_S6`). -/
theorem not_vertexCycleEq_S6 :
    ¬ VertexCycleEq hG6 3 S6 tau6 (Equiv.refl (α := Fin 6)) := by
  decide

/-- The condensation of `S = 001011` at `K = 2`: two condensed vertices,
each of degree `2`, with four branch occurrences --- `2 + 2`, the tight case
of `card_branchStarts_le_two_mul_branchVerts`. -/
theorem condense_S6 :
    ((branchVerts hG6 3 S6).card = 2 ∧ (branchStarts hG6 3 S6).card = 4 ∧
      deg hG6 3 S6 ![0, 1] = 2 ∧ deg hG6 3 S6 ![1, 0] = 2 ∧
      deg hG6 3 S6 ![0, 0] = 1 ∧ deg hG6 3 S6 ![1, 1] = 1) := by
  decide

/-- **All four branch occurrences are charged**: the alternative Eulerian
cycle departs from the truth at every position whose successor is a branch
occurrence, so `card_depart_le_branchStarts` is attained with equality. -/
theorem card_departSet_S6 :
    (departSet hG6 3 S6 tau6).card = 4 ∧ (branchStarts hG6 3 S6).card = 4 := by
  decide

/-- The two maximal extensions of the two branches are the interleaved pair
`(1, 3)`, `(2, 5)`, both of length `2 = L - 1`: the *second* disjunct of
`LongObstruction` holds on this instance.  Kernel-checked, one instance ---
not the dichotomy. -/
theorem interleaved_obstruction_S6 :
    (∃ e₁ e₂ a b c d : Fin 6, (mkGenome hG6 S6).IsRepeat e₁ a b ∧
      (mkGenome hG6 S6).IsRepeat e₂ c d ∧
      Interleaved (mkGenome hG6 S6) a b c d ∧ 2 ≤ e₁.val ∧ 2 ≤ e₂.val) := by
  decide

end Instance

end AssemblyP1.BBTEulerian
