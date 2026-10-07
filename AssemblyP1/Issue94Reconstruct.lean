import AssemblyP1.BBTUniqueEulerian

/-!
# Board 94, front 94recon: an Eulerian cycle can be *read off* a
# label-preserving permutation plus the `single` clause

This is a small reusable reconstruction step, and it is in the direction
`Issue94TW5Single` did not go.  That front proved that the second conjunct of
`BBTEulerian.EulerianCycle` (`single`, i.e. `VisitsAll (Succ hG σ) (origin hG)`)
is a **tautology** for every `σ : Fin G ≃ Fin G`, so `EulerianCycle` reduces to
its first conjunct `traverses`.  The consequence was that nothing ever had to
*produce* an `EulerianCycle`: the front could only delete a hypothesis from a
lemma whose `EulerianCycle` hypothesis somebody else was supposed to supply.

This module supplies one.  It answers the question "given that the successor of
some traversal is a single circuit, what *is* the traversal?", and it answers it
constructively: the traversal is the orbit listing of the successor, and that
listing is a permutation.

Concretely, fix `K`, an `(L-1)`-mer labelling `vtx hK L S`, and a bijection
`f : Fin K → Fin K` which preserves that labelling pointwise
(`∀ q, vtx hK L S (f q) = vtx hK L S q`).  Write

* `jump hK f q := f (nextPos hK q)` for the successor shape of a presentation by
  `f` (`Succ hK σ` is the conjugate `σ ∘ nextPos ∘ σ⁻¹`, so it is of this form),
  and

* `sigFun hK f i := (jump hK f)^[i] (origin hK)` for the orbit listing of
  `J = jump hK f`, and `sigEquiv hK f hV` for that listing as a permutation
  (the `hV` argument only certifies bijectivity; propositions are
  proof-irrelevant, so it does not affect the resulting equivalence).

If `single` holds for `J` --- i.e. `VisitsAll J (origin hK)`, so that `J` is one
`K`-cycle rather than a union of several --- then the listing is a bijection
`sigEquiv hK f hV : Fin K ≃ Fin K`, and it *is* an `EulerianCycle` of the
labelled graph.

## Named results

| theorem | what it says |
| --- | --- |
| `jump_bijective` | `f ∘ nextPos` is a bijection whenever `f` is |
| `injective_sigFun` | `single` for `J` *is* the injectivity of the listing |
| `sigFun_bijective` | the orbit listing is a permutation, from `VisitsAll` alone |
| `sigEquiv_apply` | `sigEquiv hK f hV i` is the `i`-th iterate of `f ∘ nextPos` at the origin |
| `sigEquiv_nextPos` | `sigEquiv hK f hV (nextPos hK i) = J (sigEquiv hK f hV i)`: the listing conjugates `nextPos` to `J` |
| `succ_eq_jump` | `Succ hK (sigEquiv hK f hV) = J`: the traversal reconstructed from `J` has successor exactly `J` |
| `eulerianCycle_of_labelPreserving_single` | main: `EulerianCycle hK L S (sigEquiv hK f hV)` |
| `exists_eulerianCycle_of_labelPreserving_single` | the same, existentially, so that no presentation has to be named |

The one place the `single` clause is used as a *hypothesis* rather than
discharged is the **wraparound case** of `sigEquiv_nextPos`, at
`i.val + 1 = K`: there `nextPos hK i = origin hK`, so the equation to prove is
`origin hK = J^[K] (origin hK)`, i.e. that the single circuit closes after
exactly `K` steps.  That is `BBTUniqueEulerian.iterate_G_eq`.  The ordinary case
`i.val + 1 < K` is pure `Function.iterate_succ`.

## What this does **not** do

* It does not touch `BBTEulerian.UniqueEulerianCycle`,
  `BBTEulerian.EulerianCycleObstruction`, or `hPevzner`.  All three are
  unchanged.
* It does not prove that a label-preserving `f` whose successor is single exists
  for a `Ukkonen` word, nor that such an `f` is unique.  Existence of an
  `EulerianCycle` was never the hard part --- `eulerianCycle_refl`
  (`AssemblyP1/BBTEulerian.lean:329`) already exhibits one --- so the hard part
  of `thm:BBT` is untouched and still open.
* It adds no `sorry`, no `admit`, no new axiom, no `native_decide`, no
  `unsafe`, and no change to any existing definition.

## A note on the name "label-preserving"

The hypothesis `hLP` here is `∀ q, vtx hK L S (f q) = vtx hK L S q` for a *plain
endomap* `f`.  This is **not** the same statement as
`Issue94TW5Single.LabelPreserving`, which is `∀ q, vtx hK L S (AltF hG σ q) =
vtx hK L S q` for a *presentation* `σ` (by `labelPreserving_iff_traverses` the
latter is `traverses`, the first conjunct of `EulerianCycle`).  They are
different hypotheses: `hLP` moves each start to a start of the same
`(L-1)`-mer, whereas `LabelPreserving` moves the traversal step.  No conversion
between them is claimed here, and no equivalence with `LabelPreserving` is
needed: this module never uses that notion at all. -/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace AssemblyP1.Issue94Reconstruct

open AssemblyP1
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTChords

variable {α : Type} [DecidableEq α] {K : ℕ}

/-! ## 1. The successor shape and the orbit listing -/

/-- **The successor shape determined by a label-preserving permutation.**
`f ∘ nextPos` is the shape a successor `Succ hK σ` has: the presentation `σ`
renames the one-step rotation `nextPos hK` into it.  It is a bijection whenever
`f` is. -/
def jump {K : ℕ} (hK : 0 < K) (f : Fin K → Fin K) : Fin K → Fin K :=
  fun q => f (nextPos hK q)

/-- **`jump` is a bijection as soon as `f` is.** -/
theorem jump_bijective {K : ℕ} (hK : 0 < K) (f : Fin K → Fin K)
    (hbij : Function.Bijective f) : Function.Bijective (jump hK f) := by
  have hinj : Function.Injective (jump hK f) := by
    intro a b hab
    apply nextPos_inj hK
    apply hbij.injective
    exact hab
  exact ⟨hinj, (Finite.injective_iff_surjective).mp hinj⟩

/-- **The orbit listing**: the `i`-th point of the walk
`J (origin hK), J (J (origin hK)), …` with `J = jump hK f`. -/
def sigFun {K : ℕ} (hK : 0 < K) (f : Fin K → Fin K) : Fin K → Fin K :=
  fun i => (jump hK f)^[i.val] (origin hK)

/-- **`single` is exactly the injectivity of the listing.** -/
theorem injective_sigFun {K : ℕ} (hK : 0 < K) (f : Fin K → Fin K)
    (hV : VisitsAll (jump hK f) (origin hK)) : Function.Injective (sigFun hK f) :=
  hV

/-- **The orbit listing of a single circuit is a permutation.**  `VisitsAll J
(origin hK)` is exactly the injectivity of `n ↦ J^[n] (origin hK)`, and `J`
takes values in a finite type, so injectivity is bijectivity. -/
theorem sigFun_bijective {K : ℕ} (hK : 0 < K) (f : Fin K → Fin K)
    (hV : VisitsAll (jump hK f) (origin hK)) : Function.Bijective (sigFun hK f) :=
  ⟨injective_sigFun hK f hV,
    (Finite.injective_iff_surjective).mp (injective_sigFun hK f hV)⟩

/-- **The reconstructed presentation**: the listing, as a permutation.  The
`single` hypothesis is an explicit argument only to supply the bijection
certificate; propositions are proof-irrelevant, so the resulting equivalence
does not depend on it. -/
noncomputable def sigEquiv {K : ℕ} (hK : 0 < K) (f : Fin K → Fin K)
    (hV : VisitsAll (jump hK f) (origin hK)) : Fin K ≃ Fin K :=
  Equiv.ofBijective (sigFun hK f) (sigFun_bijective hK f hV)

/-- The presentation is the orbit of `f ∘ nextPos` at the origin. -/
theorem sigEquiv_apply {K : ℕ} (hK : 0 < K) (f : Fin K → Fin K)
    (hV : VisitsAll (jump hK f) (origin hK)) (i : Fin K) :
    sigEquiv hK f hV i = (jump hK f)^[i.val] (origin hK) := rfl

/-! ## 2. The listing conjugates the one-step rotation to `J` -/

/-- **The reconstruction step.**  The orbit listing of `J` turns the one-step
rotation of the circle into `J`:
`sigEquiv hK f hV (nextPos hK i) = J (sigEquiv hK f hV i)`.

* the ordinary case `i + 1 < K`: `nextPos hK i` is the successor `i + 1` of the
  listing, so this is `Function.iterate_succ`;
* the wraparound case `i + 1 = K`: `nextPos hK i` is the origin, so this says the
  `K`-step circuit returns to its start, which is where `single` is used
  (`BBTUniqueEulerian.iterate_G_eq`). -/
theorem sigEquiv_nextPos {K : ℕ} (hK : 0 < K) (f : Fin K → Fin K)
    (hbij : Function.Bijective f) (hV : VisitsAll (jump hK f) (origin hK))
    (i : Fin K) :
    sigEquiv hK f hV (nextPos hK i) = jump hK f (sigEquiv hK f hV i) := by
  by_cases hlt : i.val + 1 < K
  · -- ordinary case: one more step of the listing
    have hn : nextPos hK i = (⟨i.val + 1, hlt⟩ : Fin K) := by
      unfold nextPos rotAdd
      apply Fin.ext
      exact Nat.mod_eq_of_lt hlt
    rw [hn]
    show (jump hK f)^[i.val + 1] (origin hK) = jump hK f (sigEquiv hK f hV i)
    rw [Function.iterate_succ_apply']
    exact congrArg (jump hK f) (sigEquiv_apply hK f hV i)
  · -- wraparound case: the circuit closes after `K` steps
    have hval : i.val + 1 = K := by omega
    have horigin : nextPos hK i = origin hK := by
      unfold nextPos rotAdd
      apply Fin.ext
      show ((i.val + 1) % K) = 0
      rw [hval]
      exact Nat.mod_self K
    have hclose : jump hK f ((jump hK f)^[i.val] (origin hK)) = origin hK := by
      have hstep : jump hK f ((jump hK f)^[K - 1] (origin hK))
          = (jump hK f)^[K] (origin hK) :=
        (Function.iterate_succ_apply' (f := jump hK f) (n := K - 1)
          (x := origin hK)).symm.trans
          (congrArg (fun n : ℕ => (jump hK f)^[n] (origin hK))
            (by omega : (K - 1) + 1 = K))
      rw [show i.val = K - 1 by omega, hstep,
        iterate_G_eq hK (jump hK f) (jump_bijective hK f hbij) hV]
    rw [horigin]
    show origin hK = jump hK f ((jump hK f)^[i.val] (origin hK))
    exact hclose.symm

/-- **The reconstructed traversal has successor exactly `J`.**
`Succ hK σ` is the conjugate `σ ∘ nextPos ∘ σ⁻¹`, so it is `J` as soon as `σ`
conjugates `nextPos` to `J`. -/
theorem succ_eq_jump {K : ℕ} (hK : 0 < K) (f : Fin K → Fin K)
    (hbij : Function.Bijective f) (hV : VisitsAll (jump hK f) (origin hK)) :
    Succ hK (sigEquiv hK f hV) = jump hK f :=
  funext fun x => by
    have h := sigEquiv_nextPos hK f hbij hV ((sigEquiv hK f hV).symm x)
    simpa only [Succ, Equiv.apply_symm_apply] using h

/-! ## 3. The reconstructed traversal is an Eulerian cycle -/

/-- **The main reconstruction theorem.**  A label-preserving bijection of the
starts, whose successor `J = f ∘ nextPos` is a single circuit, is *presented* by
the orbit listing of `J`, and that presentation is an Eulerian cycle of the
labelled graph.

The `traverses` clause is `sigEquiv_nextPos` followed by the label-preservation
of `f`; the `single` clause is the hypothesis `hV` read back through
`succ_eq_jump`. -/
theorem eulerianCycle_of_labelPreserving_single {K : ℕ} (hK : 0 < K) (L : ℕ)
    (S : Fin K → α) (f : Fin K → Fin K) (hbij : Function.Bijective f)
    (hLP : ∀ q : Fin K, vtx hK L S (f q) = vtx hK L S q)
    (hV : VisitsAll (jump hK f) (origin hK)) :
    EulerianCycle hK L S (sigEquiv hK f hV) := by
  refine ⟨?_, ?_⟩
  · -- `traverses`: the vertex entered one step along the listing is the
    -- label-preserving image of the one-step rotation of the previous start
    intro i
    have h := sigEquiv_nextPos hK f hbij hV i
    rw [h]
    exact hLP (nextPos hK (sigEquiv hK f hV i))
  · -- `single`: the successor of the reconstructed listing is `J`, which is
    -- single by hypothesis
    change VisitsAll (Succ hK (sigEquiv hK f hV)) (origin hK)
    rw [succ_eq_jump hK f hbij hV]
    exact hV

/-- **... existentially**, for consumers which only need some `EulerianCycle`
and would rather not name the presentation. -/
theorem exists_eulerianCycle_of_labelPreserving_single {K : ℕ} (hK : 0 < K) (L : ℕ)
    (S : Fin K → α) (f : Fin K → Fin K) (hbij : Function.Bijective f)
    (hLP : ∀ q : Fin K, vtx hK L S (f q) = vtx hK L S q)
    (hV : VisitsAll (jump hK f) (origin hK)) :
    ∃ σ : Fin K ≃ Fin K, EulerianCycle hK L S σ :=
  ⟨sigEquiv hK f hV, eulerianCycle_of_labelPreserving_single hK L S f hbij hLP hV⟩

end AssemblyP1.Issue94Reconstruct