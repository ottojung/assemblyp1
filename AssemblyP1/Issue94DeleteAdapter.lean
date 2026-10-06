import AssemblyP1.Issue94Reconstruct

/-!
# Board 94, deletion adapter: deleting one interlace component and re-reading an
# Eulerian cycle, and why that is *invisible* to `VertexCycleEq`

This module is the "deletion adapter" of `docs/cohn-lempel-component-route-94.md`
("**Deletion adapter:** define the component-deleted involution and prove it
remains bijective and `vtx`-preserving; then invoke `Issue94Reconstruct`"), plus
the "**vertex-cycle invisibility**" step that follows it.

## 1. The deletion

`f` is a bijection of the starts which preserves the `(L-1)`-mer labelling,
`∀ q, vtx hK L S (f q) = vtx hK L S q`.  Its nontrivial 2-orbits are the chords;
the Cohn--Lempel/Beck object of issue 94 is the interlacement matrix on those
chords, and the connected components of the interlacement graph are unions of
whole 2-orbits of `f`.

`delOn f D` is the map obtained by **deleting** the transpositions on a set `D`
of starts: it is the identity on `D` and `f` off `D`.  `IsOrbitClosed f D`,
`∀ q, q ∈ D ↔ f q ∈ D`, says exactly that `D` is a union of `f`-orbits, which
is the hypothesis a whole interlace component supplies.  Three consequences,
all proved here and none of them using the genome:

* `delOn_bijective` — the deletion is again a permutation of the starts;
* `delOn_vtx` — the deletion preserves the `(L-1)`-mer labelling (this is
  *immediate*: on `D` it is the identity, off `D` it is `f`);
* `exists_eulerianCycle_of_deleted` — **the adapter.**  If the deleted tour
  `jump hK (delOn f D)` is one circuit, then the deleted map has a genuine
  `EulerianCycle` presentation, obtained from
  `Issue94Reconstruct.exists_eulerianCycle_of_labelPreserving_single`.

The one-cycle hypothesis of `exists_eulerianCycle_of_deleted` is **not** proved
here and is proved nowhere in this repository.  It is the Cohn--Lempel input
(nonsingularity of a component block of the interlacement matrix), the single
piece of mathematics in the route that is genuinely external.

## 2. The `VertexCycleEq` consequence

`VertexCycleEq` is about vertex *labels*, so it only sees the two tours through
`vtx`.  §4 proves the structural lemma the route needs, and it turns out to be
weaker than the arc swap of the design note:

> **Cohn--Lempel conjugacy criterion (`vertexCycleEq_of_conjJump`).**  If the
> deleted tour `jump hK f'` is conjugate to the old tour `jump hK f` by a
> `vtx`-preserving permutation `c` of the starts, then the two listings are
> vertex-cycle equal: the old listing, read at position `i + m`, carries the
> `(L-1)`-mer that the new listing carries at position `i`, for a shift `m`
> which is the position of `c.symm (origin hK)` on the old tour.

The proof uses the definition of the reconstructions (`sigEquiv_apply`), one
induction on the iterate of a conjugate, and `Succ_apply`.

Two hypotheses in the statement are **not used**, and both weakenings are
deliberate:

* the `single` clause on the *old* tour (`_hV`) --- the conclusion holds for any
  `σ` whose successor is `J`, single or not;
* the bijectivity of `f` and `f'` --- only `c`'s being an equivalence and
  `vtx`-preserving is needed, plus the `single` clause on `J'` which is what
  makes the deleted listing a permutation.

Only the deleted tour has to be a single circuit, which is exactly the clause
`exists_eulerianCycle_of_deleted` produces from the Cohn--Lempel hypothesis.  In particular the arc swap
of the design note is **not** needed: any `vtx`-preserving conjugator does, and
conjugation by *any* permutation of the starts is what
`Issue94EulerianRealize` already produces when it pulls a matching back.

## 3. What is still missing

`vertexCycleEq_deletedConj_of_old` combines §4 with the old listing's own
`VertexCycleEq`, so the route now reads

```
  (old σ is vertex-cycle equal to the truth)   ← R1 / LadderVertexCycle, open
  + (deleted tour is Cohn--Lempel conjugate)   ← the external input
  ⟹  new σ' is vertex-cycle equal to the truth
```

Both remaining inputs are isolated.  The first is the residual R1 of
`Issue94R1LongWindow.lean` (which that file reduces to `R1_shift_step`); the
second is stated as the uninhabited `Prop` `DeletedConjProp` in §6.  Nothing in
this module depends on either.  No `sorry`, no `admit`, no new axiom, no
`native_decide`, no `unsafe`, and no change to any existing definition.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace AssemblyP1.Issue94DeleteAdapter

open AssemblyP1
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTChords
open AssemblyP1.Issue94Reconstruct

variable {α : Type} [DecidableEq α] {K : ℕ}

/-! ## 1. Deleting the chords of a union of `f`-orbits -/

/-- **Deleting the transpositions on `D`.**  On `D` the map is the identity, so
the chords `{q, f q}` with `q ∈ D` are removed from the support; off `D` it is
`f`, so every other chord is kept. -/
def delOn {K : ℕ} (f : Fin K → Fin K) (D : Finset (Fin K)) (q : Fin K) : Fin K :=
  if q ∈ D then q else f q

/-- A point of `D` is fixed by the deletion. -/
theorem delOn_self {f : Fin K → Fin K} {D : Finset (Fin K)} {q : Fin K} (h : q ∈ D) :
    delOn f D q = q := by simp [delOn, h]

/-- A point outside `D` is still moved by `f`. -/
theorem delOn_f {f : Fin K → Fin K} {D : Finset (Fin K)} {q : Fin K} (h : q ∉ D) :
    delOn f D q = f q := by simp [delOn, h]

/-- **`IsOrbitClosed f D`: `D` is a union of `f`-orbits.**

This is the hypothesis an *interlace component* supplies: the chords of the
support of `f` are the 2-orbits of `f`, and a connected component of the
interlacement graph is a union of whole chords, hence of whole 2-orbits.  Note
that both directions are needed, not just one: the statement is that `D`
contains no chord only one endpoint of which lies in `D`. -/
def IsOrbitClosed {K : ℕ} (f : Fin K → Fin K) (D : Finset (Fin K)) : Prop :=
  ∀ q : Fin K, q ∈ D ↔ f q ∈ D

/-- **The deletion is injective**, by the four cases of membership of `a`, `b`. -/
theorem delOn_injective {f : Fin K → Fin K} {D : Finset (Fin K)}
    (hf : Function.Bijective f) (hD : IsOrbitClosed f D) :
    Function.Injective (delOn f D) := by
  intro a b hab
  by_cases ha : a ∈ D <;> by_cases hb : b ∈ D
  · rw [delOn_self ha, delOn_self hb] at hab
    exact hab
  · rw [delOn_self ha, delOn_f hb] at hab
    rw [hab] at ha
    exact absurd ((hD b).mpr ha) hb
  · rw [delOn_f ha, delOn_self hb] at hab
    rw [← hab] at hb
    exact absurd ((hD a).mpr hb) ha
  · rw [delOn_f ha, delOn_f hb] at hab
    exact hf.injective hab

/-- **The deletion is a permutation of the starts.**  Kept chords keep their
endpoints (`f` is injective, and `D` is closed under `f` and under `f⁻¹`),
deleted chords collapse to the fixed points of `D`. -/
theorem delOn_bijective {f : Fin K → Fin K} {D : Finset (Fin K)}
    (hf : Function.Bijective f) (hD : IsOrbitClosed f D) :
    Function.Bijective (delOn f D) :=
  ⟨delOn_injective hf hD,
    (Finite.injective_iff_surjective).mp (delOn_injective hf hD)⟩

/-- **The deletion preserves the `(L-1)`-mer labelling.**  This is the whole of
the "vertex invisibility" of the deletion at this level: on `D` the deletion is
the identity, off `D` it is `f`.  Nothing about chords, components or the genome
is used. -/
theorem delOn_vtx {f : Fin K → Fin K} {D : Finset (Fin K)} {L : ℕ} {S : Fin K → α}
    (hK : 0 < K) (hLP : ∀ q : Fin K, vtx hK L S (f q) = vtx hK L S q) (q : Fin K) :
    vtx hK L S (delOn f D q) = vtx hK L S q := by
  by_cases h : q ∈ D
  · rw [delOn_self h]
  · rw [delOn_f h, hLP]

/-! ## 2. The adapter: a deleted one-cycle transition has a genuine Eulerian cycle -/

/-- **THE ADAPTER.**  Delete the chords on a union of `f`-orbits from a
`vtx`-preserving permutation `f` of the starts.  If the *deleted* tour
`jump hK (delOn f D)` is one circuit --- the Cohn--Lempel hypothesis --- then
the deleted map has a genuine `EulerianCycle` presentation of the labelled
`(L-1)`-mer graph.

This is `Issue94Reconstruct.exists_eulerianCycle_of_labelPreserving_single`
applied to `delOn f D`, whose bijectivity is `delOn_bijective` and whose
label-preservation is `delOn_vtx`.

`hV` is the external input and is **not** discharged anywhere.  It is the
statement that the component-deleted interlacement matrix is nonsingular over
GF(2); `DeletedConjProp` in §6 records the shape actually needed downstream. -/
theorem exists_eulerianCycle_of_deleted {L : ℕ} {S : Fin K → α}
    (hK : 0 < K) (f : Fin K → Fin K) (D : Finset (Fin K))
    (hbij : Function.Bijective f)
    (hLP : ∀ q : Fin K, vtx hK L S (f q) = vtx hK L S q)
    (hD : IsOrbitClosed f D)
    (hV : VisitsAll (jump hK (delOn f D)) (origin hK)) :
    ∃ σ : Fin K ≃ Fin K, EulerianCycle hK L S σ :=
  exists_eulerianCycle_of_labelPreserving_single hK L S (delOn f D)
    (delOn_bijective hbij hD) (delOn_vtx hK hLP) hV

/-! ## 3. Structural facts about the listing of a tour -/

/-- **`Succ` is a bijection.**  (`BBTUniqueEulerian.Succ_injective`, plus
finiteness.) -/
theorem Succ_bijective {K : ℕ} (hK : 0 < K) (σ : Fin K ≃ Fin K) :
    Function.Bijective (Succ hK σ) :=
  ⟨Succ_injective hK σ, (Finite.injective_iff_surjective).mp (Succ_injective hK σ)⟩

/-- `rotAdd hK (n + 1) x = nextPos hK (rotAdd hK n x)`: `rotAdd` in the `n`-slot
composes with the one-step rotation.  (`BBTVertexCycleReduction.rotAdd_succ_add`
is the other order of composition.) -/
theorem rotAdd_succ (hK : 0 < K) (n : ℕ) (x : Fin K) :
    rotAdd hK (n + 1) x = nextPos hK (rotAdd hK n x) := by
  have h2 : (x.val + n) + 1 = x.val + (n + 1) := by omega
  have hkey : (x.val + (n + 1)) % K = ((x.val + n) % K + 1) % K := by
    calc (x.val + (n + 1)) % K = ((x.val + n) + 1) % K := by rw [h2]
      _ = ((x.val + n) % K + 1) % K := (Nat.mod_add_mod (x.val + n) K 1).symm
  unfold nextPos rotAdd
  apply Fin.ext
  exact hkey

/-- **`Succ hK σ` carries the listing `σ` around the circle**:
`(Succ hK σ)^[n] (σ x) = σ (rotAdd hK n x)`.  This is `Succ_apply`, i.e. the
*direction* of the traversal, and needs no hypothesis at all. -/
theorem succ_iterate_listing (hK : 0 < K) {σ : Fin K ≃ Fin K} :
    ∀ (n : ℕ) (x : Fin K), (Succ hK σ)^[n] (σ x) = σ (rotAdd hK n x) := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', ih, Succ_apply hK σ (rotAdd hK n x),
        rotAdd_succ hK n x]

/-- The origin of the circle, at listing position `n`. -/
theorem rotAdd_origin (hK : 0 < K) (n : ℕ) :
    rotAdd hK n (origin hK) = ⟨n % K, Nat.mod_lt _ hK⟩ := by
  unfold rotAdd origin
  apply Fin.ext
  simp

/-! ## 4. The conjugacy criterion: Cohn--Lempel deletion is vertex-invisible -/

/-- **A conjugacy of tours is a conjugacy of listings.**  If
`J' q = c (J (c.symm q))` then `J'^[n] x = c (J^[n] (c.symm x))`, for every
`n`.  No hypothesis on `c` and no hypothesis on `J`, `J'`. -/
theorem iterate_conj {J J' : Fin K → Fin K} {c : Fin K ≃ Fin K}
    (hconj : ∀ q, J' q = c (J (c.symm q))) :
    ∀ (n : ℕ) (x : Fin K), J'^[n] x = c (J^[n] (c.symm x)) := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [Function.iterate_zero]
  | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply' (f := J') (n := n) (x := x), ih, hconj]
      rw [Equiv.symm_apply_apply,
        ← Function.iterate_succ_apply' (f := J) (n := n) (x := c.symm x)]

/-- **THE CRITERION.**  Let `f, f' : Fin K → Fin K` be label-preserving
endomaps of the starts, let `J = jump hK f` be the successor of the listing `σ`,
let `J' = jump hK f'` be a single circuit, and suppose `J'` is conjugate to `J`
by an equivalence `c` of the starts which **preserves the `(L-1)`-mer
labelling**.  Then for some shift `m : ℕ`,

```
  vtx hK L S (σ' i) = vtx hK L S (σ ⟨(i.val + m) % K⟩)
```

where `σ' = sigEquiv hK f' hV'` is the listing reconstructed from the deleted
tour.  Equivalently: the two listings are vertex-cycle equal.

This is the "vertex-cycle invisibility" of the deletion route, and it is much
weaker than the explicit maximal-repeat arc swap proposed in the design note.
`c` need not be any particular permutation; it only has to move each start to a
start carrying the same `(L-1)`-mer.  In the application of §6, `c` is the
conjugator between the old tour and the deleted tour, which is what the
Cohn--Lempel component deletion produces (the pull-back of the matching through
the alternative traversal, `Issue94EulerianRealize`). -/
theorem vertexCycleEq_of_conjJump {L : ℕ} {S : Fin K → α} {f f' : Fin K → Fin K}
    {σ : Fin K ≃ Fin K} (hK : 0 < K)
    (hsig : jump hK f = Succ hK σ)
    (_hV : VisitsAll (jump hK f) (origin hK))
    (hV' : VisitsAll (jump hK f') (origin hK))
    {c : Fin K ≃ Fin K}
    (hcvtx : ∀ q : Fin K, vtx hK L S (c q) = vtx hK L S q)
    (hconj : ∀ q, jump hK f' q = c (jump hK f (c.symm q))) :
    ∃ m : ℕ, ∀ i : Fin K,
      vtx hK L S (sigEquiv hK f' hV' i)
        = vtx hK L S (σ ⟨(i.val + m) % K, Nat.mod_lt _ hK⟩) := by
  have horbit : ∀ n : Fin K, (jump hK f)^[n.val] (σ (origin hK)) = σ n := by
    intro n
    rw [hsig, succ_iterate_listing hK n.val (origin hK), rotAdd_origin hK n.val]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt n.isLt)
  have hinj : Function.Injective
      (fun n : Fin K => (jump hK f)^[n.val] (σ (origin hK))) := by
    intro a b hab
    have hab' : (jump hK f)^[a.val] (σ (origin hK)) = (jump hK f)^[b.val] (σ (origin hK)) :=
      hab
    rw [horbit a, horbit b] at hab'
    exact σ.injective hab'
  obtain ⟨m, hm⟩ :=
    (Finite.injective_iff_surjective).mp hinj (c.symm (origin hK))
  have hm' : (jump hK f)^[m.val] (σ (origin hK)) = c.symm (origin hK) := hm
  have hkey : ∀ (i : Fin K),
      vtx hK L S (sigEquiv hK f' hV' i)
        = vtx hK L S ((jump hK f)^[i.val] (c.symm (origin hK))) := by
    intro i
    rw [sigEquiv_apply hK f' hV' i,
      iterate_conj (J := jump hK f) (J' := jump hK f') hconj (i.val) (origin hK),
      hcvtx]
  refine ⟨m.val, fun i => ?_⟩
  have hstep : (jump hK f)^[i.val] (c.symm (origin hK))
      = (Succ hK σ)^[i.val + m.val] (σ (origin hK)) := by
    rw [← hm, ← Function.iterate_add_apply, hsig]
  calc vtx hK L S (sigEquiv hK f' hV' i)
      = vtx hK L S ((jump hK f)^[i.val] (c.symm (origin hK))) := hkey i
    _ = vtx hK L S ((Succ hK σ)^[i.val + m.val] (σ (origin hK))) := by
        rw [hstep]
    _ = vtx hK L S (σ (⟨(i.val + m.val) % K, Nat.mod_lt _ hK⟩)) := by
        rw [succ_iterate_listing hK (i.val + m.val) (origin hK), rotAdd_origin hK]

/-- **The two extreme deletions, kernel-checked.**  At `K = 5` with `f` the
one-step rotation of the circle, the deletion with `D = ∅` is `f` itself and the
deletion with `D = univ` is the identity; both are permutations of the starts.
This is a non-vacuity check on `delOn` and `delOn_bijective`, not a claim about
any genome. -/
theorem delOn_extremes :
    Function.Bijective (delOn (fun q : Fin 5 => ⟨(q.val + 1) % 5, Nat.mod_lt _ (by decide)⟩) ∅)
      ∧ Function.Bijective
          (delOn (fun q : Fin 5 => ⟨(q.val + 1) % 5, Nat.mod_lt _ (by decide)⟩) (Finset.univ : Finset (Fin 5))) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> decide

/-! ## 5. `Nat` arithmetic on the listing index -/

/-- Resolving a modulus that is already inside a modulus:
`((a + b) % K + c) % K = (a + b + c) % K`. -/
theorem mod_mod_add (a b c K : ℕ) :
    ((a + b) % K + c) % K = (a + b + c) % K :=
  Nat.mod_add_mod (a + b) K c

/-- **Composing two listing shifts.**  Reading the old listing at
`(i + m) % K` and then rotating the result by `k` is the same as rotating by
`m + k` and reading at `i`: `((i + m) % K + k) % K = (i + (m + k) % K) % K`.
This is the `Nat` bookkeeping of composing the shift `m` of §4 with the
witness `k0` of `VertexCycleEq`. -/
theorem mod_sum_shifts (i m k K : ℕ) :
    ((i + m) % K + k) % K = (i + (m + k) % K) % K := by
  have h1 := Nat.mod_add_mod (i + m) K k
  have h2 := Nat.mod_add_mod (m + k) K i
  calc ((i + m) % K + k) % K = ((i + m) + k) % K := h1
    _ = (i + (m + k)) % K := by rw [Nat.add_assoc]
    _ = (((m + k) + i) % K) := by rw [Nat.add_comm]
    _ = ((m + k) % K + i) % K := h2.symm
    _ = (i + (m + k) % K) % K := by rw [Nat.add_comm]

/-! ## 6. The route, and the two inputs it still needs -/

/-- **Combining the criterion with the old listing's own `VertexCycleEq`.**  If
the old listing `σ` is already vertex-cycle equal to the truth and the deleted
tour is Cohn--Lempel conjugate to the old tour, then the newly reconstructed
listing `σ' = sigEquiv hK f' hV'` is vertex-cycle equal to the truth as well. -/
theorem vertexCycleEq_deletedConj_of_old {L : ℕ} {S : Fin K → α}
    {f f' : Fin K → Fin K} {σ : Fin K ≃ Fin K} (hK : 0 < K)
    (hsig : jump hK f = Succ hK σ)
    (hV : VisitsAll (jump hK f) (origin hK))
    (hV' : VisitsAll (jump hK f') (origin hK))
    {c : Fin K ≃ Fin K}
    (hcvtx : ∀ q : Fin K, vtx hK L S (c q) = vtx hK L S q)
    (hconj : ∀ q, jump hK f' q = c (jump hK f (c.symm q)))
    (hold : VertexCycleEq hK L S σ (Equiv.refl (α := Fin K))) :
    VertexCycleEq hK L S (sigEquiv hK f' hV') (Equiv.refl (α := Fin K)) := by
  obtain ⟨m, hm⟩ := vertexCycleEq_of_conjJump hK hsig hV hV' hcvtx hconj
  obtain ⟨k0, hk0⟩ := hold
  refine ⟨⟨(m + k0.val) % K, Nat.mod_lt _ hK⟩, fun i => ?_⟩
  have h1 := hm i
  have h2 := hk0 ⟨(i.val + m) % K, Nat.mod_lt _ hK⟩
  rw [h1, h2]
  apply congrArg (vtx hK L S)
  unfold rotAdd
  apply Fin.ext
  show ((i.val + m) % K + k0.val) % K = (i.val + (m + k0.val) % K) % K
  exact mod_sum_shifts i.val m k0.val K

/-- **THE REMAINING EXTERNAL INPUT, as a `Prop`.  Not proved, and nothing
depends on it.**

  * the deleted tour `jump hK f'` is one circuit --- the `hV'` clause, supplied
    by `exists_eulerianCycle_of_deleted` from the Cohn--Lempel hypothesis; and
  * there is a permutation `c` of the starts, **preserving the `(L-1)`-mer
    labelling**, conjugating `jump hK f` to `jump hK f'`.

For the Cohn--Lempel deletion `f' = delOn (AltF hK σ) D` with `D` a union of
`AltF hK σ`-orbits (e.g. one connected component of the interlacement graph),
the second clause is the statement that deleting `D` does not change the tour up
to a labelling-preserving relabelling of the starts.  `c` is *not* required to
be the maximal-repeat arc swap: any labelling-preserving conjugator will do,
which is the weakening relative to the design note that this module establishes. -/
def DeletedConjProp {L : ℕ} (S : Fin K → α) (hK : 0 < K) (f f' : Fin K → Fin K) : Prop :=
  VisitsAll (jump hK f') (origin hK) ∧
    ∃ c : Fin K ≃ Fin K,
      (∀ q : Fin K, vtx hK L S (c q) = vtx hK L S q) ∧
      ∀ q, jump hK f' q = c (jump hK f (c.symm q))

end AssemblyP1.Issue94DeleteAdapter