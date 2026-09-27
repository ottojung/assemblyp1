import AssemblyP1.BBTEulerian

/-!
# An exact, efficient finite verifier for the #89 statement

## What this module is for

`AssemblyP1/BBTEulerianFinite.lean` (commit `3237e0a`) attempted to check
`BBTEulerian.EulerianCycleObstruction` on a finite class by `decide`.  That
file did not compile (it used the removed `Finset.all`, and called
`not_longObstruction_of_P2` with `hG` explicit where it is implicit), and it
was never imported by `AssemblyP1.lean`, so `lake build` never checked it:
the kernel-checked finite verification it documents did not exist.  This
module replaces it, and fixes the two things that made the naive `decide`
both ill-shaped and unusable.

## Why the naive enumeration is the wrong shape

`UniqueAt hG L S` quantifies over **every** `σ : Fin G ≃ Fin G`, i.e. over
`G!` presentations, and for each one re-derives `EulerianCycle` and
`VertexCycleEq` by `decide`.  That is `G!`-times more search than the
statement has content in, and it is the `G!` factor --- not the statement ---
that makes any genome length beyond `G = 4` hopeless.

The content of the statement is a statement about the **successor** of a
traversal, not about the presentation.  If `σ` presents an Eulerian cycle
then its successor

```text
θ := σ ∘ nextPos ∘ σ⁻¹
```

is (i) a `G`-cycle --- the `VisitsAll` clause of `EulerianCycle`, unchanged;
(ii) *fibre-preserving* --- `vtx (θ x) = vtx (nextPos x)` for every `x`,
because the `traverses` clause says exactly that; and (iii) **carries the
whole vertex cycle of `σ`**: the listing `σ 0, σ 1, …` is the orbit listing
of `θ` read from a different start, so `VertexCycleEq σ id` iff the orbit
listing of `θ` from `0` is the truth's listing up to rotation.  Conversely
any fibre-preserving `G`-cycle `θ` *is* the successor of an Eulerian cycle,
obtained by choosing where the listing starts.

So the exact content of `UniqueAt` is a quantifier over one-cycle
permutations, and this module proves the equivalence in the kernel
(`uniqueAt_iff_orbit`):

```text
∀ θ : Fin G → Fin G, Function.Bijective θ → FibrePreserving θ → OneCycle hG θ →
    OrbitVertexEq θ
```

§2 replaces the remaining search --- "is there a one-cycle,
fibre-preserving `θ` whose orbit listing is *not* the truth's?" --- by an
explicit, finite and much smaller enumeration: the **circuits**, i.e. the
listings of `G` pairwise distinct starts, beginning at the origin, along
which consecutive `(L-1)`-mers overlap.  `circuits` is computed by
backtracking over the fibres of `vtx`, and `mem_circuits` proves the
enumeration is **complete**, so `uniqueAt_iff_circuits` is an `iff` and the
verified statement is literally `UniqueAt` and not a paraphrase.  The cost
of the search is the number of Eulerian circuits of the `(L-1)`-mer
multigraph rather than `G!`: that is the quantity `thm:BBT` is about, and
the quantity `BBTCondense.forced_at_unambiguous` already controls at
unambiguous vertices.

## Fidelity notes

* The enumeration is over `UniqueAt`, i.e. over the exact hypothesis
  `P2` of `def:P1P2` and the exact conclusion
  `BBTEulerian.UniqueAt`; no hypothesis is added, dropped or weakened.
* The quantification over `G` and over `L` is the quantification of
  `FiniteBinary` of the previous packet: every binary circular genome of
  length `≤ maxG`, every read length `2 ≤ L ≤ maxL`.  Rotations are *not*
  quotiented out (no such quotient was justified), and alphabets other than
  binary are *not* claimed.
* `EulerianCycleObstruction` is the two-clause form of the same theorem, and
  `uniqueAt_of_obstruction` in `AssemblyP1.BBTEulerian` is the bridge; the
  finite check below therefore decides the stronger-form-free statement, i.e.
  it is exactly the first clause of `thm:BBT`.
-/

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedSectionVars false

namespace AssemblyP1.BBTEulerianSearch

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1
open AssemblyP1.BBTEulerian

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-! ## 1. The one-cycle, fibre-preserving reformulation of the #89 statement -/

/-- **The first clause of `thm:BBT` at one genome**: every alternative
Eulerian cycle of the condensed `(L-1)`-mer multigraph spells the truth's own
vertex cycle.  This is `BBTEulerian.UniqueEulerianCycle` specialised to one
genome and to the uniqueness formulation, and it is the statement the finite
verification below decides. -/
def UniqueAt (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  ∀ σ : Fin G ≃ Fin G, EulerianCycle hG L S σ →
    VertexCycleEq hG L S σ (Equiv.refl (α := Fin G))

instance (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Decidable (UniqueAt hG L S) := by
  unfold UniqueAt
  infer_instance

/-- The two clauses of `EulerianCycleObstruction` are interchangeable with the
uniqueness clause once the truth is `P2`; this is the bridge recorded in
`AssemblyP1.BBTEulerian` (`obstruction_of_uniqueAt`,
`uniqueAt_of_obstruction`), repeated here so that the finite check below is
about the exact statement and not about a paraphrase of it. -/
theorem obstruction_of_uniqueAt (_hL : 2 ≤ L) (_hP2 : P2 hG L S)
    (hu : UniqueAt hG L S) :
    ∀ σ : Fin G ≃ Fin G, EulerianCycle hG L S σ →
      VertexCycleEq hG L S σ (Equiv.refl (α := Fin G)) ∨ LongObstruction hG L S :=
  fun σ hEul => Or.inl (hu σ hEul)

theorem uniqueAt_of_obstruction (hL : 2 ≤ L) (hP2 : P2 hG L S)
    (ho : ∀ σ : Fin G ≃ Fin G, EulerianCycle hG L S σ →
      VertexCycleEq hG L S σ (Equiv.refl (α := Fin G)) ∨ LongObstruction hG L S) :
    UniqueAt hG L S := by
  intro σ hEul
  rcases ho σ hEul with hv | hl
  · exact hv
  · exact absurd hl (not_longObstruction_of_P2 hL hP2)

/-- **The successor of a traversal presentation**: the position the walk
enters next, at the truth's start `x`.  This is the map the `VisitsAll`
clause of `EulerianCycle` is about, written on its own. -/
def succOf (σ : Fin G ≃ Fin G) : Fin G → Fin G :=
  fun x => σ (nextPos hG (σ.symm x))

/-- **`θ` preserves the fibres of `vtx`**: it sends `x` to a start carrying
the same `(L-1)`-mer as the start one step after `x`.  This is the
`traverses` clause of `EulerianCycle`, on the successor. -/
def FibrePreserving (θ : Fin G → Fin G) : Prop :=
  ∀ x : Fin G, vtx hG L S (θ x) = vtx hG L S (nextPos hG x)

/-- **`θ` is one cycle**: its walk from the origin visits `G` distinct
positions before returning.  This is the `VisitsAll` clause of
`EulerianCycle`, on the successor. -/
def OneCycle (θ : Fin G → Fin G) : Prop := VisitsAll θ (origin hG)

/-- **The vertex cycle read along the orbit of a one-cycle `θ`**, i.e. the
Eulerian cycle with the presentation forgotten: the cyclic listing of
`(L-1)`-mers visited along `θ`'s orbit from the origin.  `OrbitVertexEq θ`
says this listing is the truth's own cyclic listing, up to rotation. -/
def OrbitVertexEq (θ : Fin G → Fin G) : Prop :=
  ∃ k : Fin G, ∀ j : Fin G,
    vtx hG L S (θ^[j.val] (origin hG)) = vtx hG L S (rotAdd hG (j.val + k.val) (origin hG))

/-- The truth's own successor is the one-step rotation, and it is one cycle:
this is the anti-vacuity anchor of the reformulation, which is not vacuous,
since it holds of the truth.  (`L` and `S` are bound locally: `OneCycle`
does not mention them, and Lean 4 only puts a section variable in the
context of a declaration that mentions it.) -/
theorem oneCycle_nextPos (L : ℕ) (S : Fin G → α) : OneCycle hG (nextPos hG) :=
  (eulerianCycle_refl hG L S).2

theorem fibrePreserving_nextPos : FibrePreserving hG L S (nextPos hG) := by
  intro x
  rfl

theorem orbitVertexEq_nextPos : OrbitVertexEq hG L S (nextPos hG) := by
  refine ⟨⟨0, hG⟩, ?_⟩
  intro j
  rw [rotAdd_iterate]
  congr 1

/-! ### 1.1 Rotation is respected by a traversal -/

/-- Shifting by no positions at all. -/
theorem rotAdd_zero' (hG : 0 < G) (x : Fin G) : rotAdd hG 0 x = x := by
  apply Fin.ext
  show (x.val + 0) % G = x.val
  rw [Nat.add_zero, Nat.mod_eq_of_lt x.isLt]

/-- The one-step rotation of a circle is a permutation of its positions. -/
theorem bijective_nextPos (hG : 0 < G) : Function.Bijective (nextPos hG) :=
  ⟨nextPos_inj hG, Finite.surjective_of_injective (nextPos_inj hG)⟩

/-! ### 1.2 From a presentation to its successor -/

theorem succOf_bijective (σ : Fin G ≃ Fin G) : Function.Bijective (succOf hG σ) :=
  Function.Bijective.comp σ.bijective
    (Function.Bijective.comp (bijective_nextPos hG) σ.symm.bijective)

theorem fibrePreserving_succOf (σ : Fin G ≃ Fin G) (h : EulerianCycle hG L S σ) :
    FibrePreserving hG L S (succOf hG σ) := by
  intro x
  have hx := h.1 (σ.symm x)
  simpa [succOf] using hx

theorem oneCycle_succOf (σ : Fin G ≃ Fin G) (h : EulerianCycle hG L S σ) :
    OneCycle hG (succOf hG σ) := h.2

/-- **Iterating the successor of a presentation.** -/
theorem succOf_iterate (σ : Fin G ≃ Fin G) (n : ℕ) :
    ∀ x : Fin G, (succOf hG σ)^[n] x = σ (rotAdd hG n (σ.symm x)) :=
  altSucc_iterate hG σ n

/-- Rotations of the circle compose, and the order does not matter.  These
are the only arithmetic facts the reformulation needs. -/
theorem rotAdd_rotAdd (hG : 0 < G) (j k : ℕ) (x : Fin G) :
    rotAdd hG j (rotAdd hG k x) = rotAdd hG (j + k) x := by
  apply Fin.ext
  simp only [rotAdd, Fin.val_mk]
  show ((x.val + k) % G + j) % G = (x.val + (j + k)) % G
  rw [Nat.mod_add_mod (m := x.val + k) (n := G) (k := j)]
  congr 1
  omega

theorem rotAdd_comm (hG : 0 < G) (j k : ℕ) (x : Fin G) :
    rotAdd hG j (rotAdd hG k x) = rotAdd hG k (rotAdd hG j x) := by
  apply Fin.ext
  simp only [rotAdd, Fin.val_mk]
  show ((x.val + k) % G + j) % G = ((x.val + j) % G + k) % G
  rw [Nat.mod_add_mod (m := x.val + k) (n := G) (k := j),
    Nat.mod_add_mod (m := x.val + j) (n := G) (k := k)]
  congr 1
  omega

/-- Shifting a point by `k` after shifting it by `j` is shifting it by
`j + k` --- reading the shifted point off the origin.  This is the shift
that the vertex cycle of a presentation picks up. -/
theorem rotAdd_comp_origin (hG : 0 < G) (j k : ℕ) (x : Fin G) :
    rotAdd hG k (rotAdd hG j x) = rotAdd hG (j + (x.val + k) % G) (origin hG) := by
  apply Fin.ext
  simp only [rotAdd, Fin.val_mk, origin_val, Nat.zero_add]
  show ((x.val + j) % G + k) % G = (j + (x.val + k) % G) % G
  have hR : j + (x.val + k) % G = (x.val + k) % G + j := Nat.add_comm _ _
  rw [hR, Nat.mod_add_mod (m := x.val + j) (n := G) (k := k),
    Nat.mod_add_mod (m := x.val + k) (n := G) (k := j)]
  congr 1
  omega

/-- **`VertexCycleEq σ id` is exactly `OrbitVertexEq (succOf σ)`.**  This is
the heart of the reformulation, and it is *pure bookkeeping*: the listing
`σ 0, σ 1, …` and the orbit listing of `θ := σ ∘ nextPos ∘ σ⁻¹` from the
origin are the same list of positions up to a cyclic shift, namely
`θ^[j] 0 = σ (rotAdd j (σ⁻¹ 0))`, so they spell the same cyclic list of
`(L-1)`-mers.  No property of the multigraph enters here. -/
theorem vertexCycleEq_iff_orbit (σ : Fin G ≃ Fin G) :
    VertexCycleEq hG L S σ (Equiv.refl (α := Fin G))
      ↔ OrbitVertexEq hG L S (succOf hG σ) := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨⟨((σ.symm (origin hG)).val + k.val) % G, Nat.mod_lt _ hG⟩, ?_⟩
    intro j
    rw [succOf_iterate]
    have hjt := hk (rotAdd hG j.val (σ.symm (origin hG)))
    simp only [Equiv.refl_apply] at hjt
    rw [rotAdd_comp_origin] at hjt
    exact hjt
  · rintro ⟨k, hk⟩
    refine ⟨⟨(k.val + G - (σ.symm (origin hG)).val) % G, Nat.mod_lt _ hG⟩, ?_⟩
    intro i
    have hindex : rotAdd hG ((i.val + G - (σ.symm (origin hG)).val) % G)
        (σ.symm (origin hG)) = i := by
      apply Fin.ext
      simp only [rotAdd, Fin.val_mk]
      show ((σ.symm (origin hG)).val
          + ((i.val + G - (σ.symm (origin hG)).val) % G)) % G = i.val
      have hL : (σ.symm (origin hG)).val
            + ((i.val + G - (σ.symm (origin hG)).val) % G)
          = ((i.val + G - (σ.symm (origin hG)).val) % G)
            + (σ.symm (origin hG)).val := Nat.add_comm _ _
      rw [hL, Nat.mod_add_mod (m := i.val + G - (σ.symm (origin hG)).val) (n := G)
        (k := (σ.symm (origin hG)).val)]
      have h2 : i.val + G - (σ.symm (origin hG)).val + (σ.symm (origin hG)).val
          = i.val + G := by omega
      rw [h2, Nat.add_mod]
      simp [Nat.mod_eq_of_lt i.isLt]
    have hjt := hk ⟨(i.val + G - (σ.symm (origin hG)).val) % G, Nat.mod_lt _ hG⟩
    rw [succOf_iterate, hindex] at hjt
    refine hjt.trans ?_
    simp only [Equiv.refl_apply]
    congr 1
    apply Fin.ext
    simp only [rotAdd, Fin.val_mk, origin_val, Nat.zero_add]
    show ((i.val + G - (σ.symm (origin hG)).val) % G + k.val) % G
        = (i.val + (k.val + G - (σ.symm (origin hG)).val) % G) % G
    have hR : i.val + (k.val + G - (σ.symm (origin hG)).val) % G
        = (k.val + G - (σ.symm (origin hG)).val) % G + i.val := Nat.add_comm _ _
    rw [Nat.mod_add_mod (m := i.val + G - (σ.symm (origin hG)).val) (n := G)
        (k := k.val), hR,
      Nat.mod_add_mod (m := k.val + G - (σ.symm (origin hG)).val) (n := G)
        (k := i.val)]
    congr 1
    omega

/-- `VertexCycleEq` at the truth, read on the successor. -/
theorem vertexCycleEq_to_orbit (σ : Fin G ≃ Fin G)
    (h : VertexCycleEq hG L S σ (Equiv.refl (α := Fin G))) :
    OrbitVertexEq hG L S (succOf hG σ) :=
  (vertexCycleEq_iff_orbit hG L S σ).mp h

/-- ... and back. -/
theorem orbit_to_vertexCycleEq (σ : Fin G ≃ Fin G)
    (h : OrbitVertexEq hG L S (succOf hG σ)) :
    VertexCycleEq hG L S σ (Equiv.refl (α := Fin G)) :=
  (vertexCycleEq_iff_orbit hG L S σ).mpr h

/-! ### 1.3 From a one-cycle to a presentation -/

/-- The listing of a one-cycle map, read from a starting point. -/
def listingOf (θ : Fin G → Fin G) (c : Fin G) : Fin G → Fin G :=
  fun x => θ^[x.val] c

theorem listingOf_injective {θ : Fin G → Fin G} {c : Fin G}
    (h : Function.Injective (fun n : Fin G => θ^[n.val] c)) :
    Function.Injective (listingOf θ c) := by
  intro a b hab
  apply h
  exact Fin.ext (congrArg Fin.val hab)

/-- **A one-cycle closes up after `G` steps.**  If the `G` iterates of the
origin under a permutation are pairwise distinct --- which is the `VisitsAll`
clause --- then its orbit is a cycle of length exactly `G`, so the iterate at
`G` is the origin again.  This is the only fact about one-cycles needed to
turn an orbit listing into a genuine presentation, and it is exactly the
place where "one circuit" is load-bearing. -/
theorem iterate_G_of_oneCycle {θ : Fin G → Fin G} (hθ : Function.Bijective θ)
    (ho : OneCycle hG θ) :
    θ^[G] (origin hG) = origin hG := by
  have hinjφ : Function.Injective (fun j : Fin G => θ^[j.val] (origin hG)) := ho
  have hφ : Function.Bijective (fun j : Fin G => θ^[j.val] (origin hG)) :=
    ⟨hinjφ, Finite.surjective_of_injective hinjφ⟩
  by_contra hne
  obtain ⟨k, hk⟩ := hφ.2 (θ^[G] (origin hG))
  have hk0 : k.val ≠ 0 := by
    intro hk0'
    have hcontra : θ^[0] (origin hG) = θ^[G] (origin hG) := by
      have hkfin : (⟨0, hG⟩ : Fin G) = k := Fin.ext hk0'.symm
      have hk' := hk
      rw [← hkfin] at hk'
      simpa using hk'
    exact hne (by simpa using hcontra.symm)
  have hklt : 1 ≤ k.val ∧ k.val < G := ⟨by omega, k.isLt⟩
  have hinjθ : Function.Injective (θ^[k.val]) := hθ.injective.iterate k.val
  have hkey : θ^[k.val] (θ^[G - k.val] (origin hG)) = θ^[k.val] (origin hG) := by
    rw [← Function.iterate_add_apply]
    have : k.val + (G - k.val) = G := by omega
    rw [this]
    exact hk.symm
  have heq : θ^[G - k.val] (origin hG) = origin hG := hinjθ hkey
  have hlt : G - k.val < G := by omega
  have hmod : (G - k.val) % G = G - k.val := Nat.mod_eq_of_lt hlt
  have hcontra : False := by
    have h1 : (⟨G - k.val, hlt⟩ : Fin G) = (⟨0, hG⟩ : Fin G) := by
      apply hinjφ
      change θ^[G - k.val] (origin hG) = θ^[0] (origin hG)
      rw [heq, Function.iterate_zero]
      rfl
    have hv : G - k.val = 0 := by
      have := congrArg Fin.val h1
      simpa only [Fin.val_mk] using this
    omega

  exact hcontra

/-- **The orbit listing of a one-cycle respects the one-step rotation.** -/
theorem listingOf_step {θ : Fin G → Fin G} (hθ : Function.Bijective θ)
    (ho : OneCycle hG θ) (y : Fin G) :
    listingOf θ (origin hG) (nextPos hG y) = θ (listingOf θ (origin hG) y) := by
  unfold listingOf
  simp only [nextPos, rotAdd, Fin.val_mk]
  show θ^[(y.val + 1) % G] (origin hG) = θ (θ^[y.val] (origin hG))
  by_cases h : y.val + 1 < G
  · rw [Nat.mod_eq_of_lt h, Function.iterate_succ_apply']
  · have h1 : y.val + 1 = G := by omega
    have h2 : (y.val + 1) % G = 0 := by rw [h1, Nat.mod_self]
    have hstep' : θ^[y.val + 1] (origin hG) = θ (θ^[y.val] (origin hG)) :=
      Function.iterate_succ_apply' θ y.val (origin hG)
    have hR : θ (θ^[y.val] (origin hG)) = θ^[G] (origin hG) := by
      rw [← hstep', h1]
    rw [h2, hR, iterate_G_of_oneCycle hG hθ ho, Function.iterate_zero]
    rfl

/-- **Every one-cycle, fibre-preserving map is the successor of a genuine
Eulerian cycle of the `(L-1)`-mer multigraph.**  This is the converse half of
the reformulation, and it is what makes the reformulated statement *exactly*
as strong as `EulerianCycle` rather than a relaxation of it: nothing is lost
by forgetting the presentation, because the presentation is recovered by
choosing where the listing starts. -/
theorem isEulerianCycle_of_oneCycle (θ : Fin G → Fin G)
    (hb : Function.Bijective θ) (hf : FibrePreserving hG L S θ)
    (ho : OneCycle hG θ) :
    ∃ σ : Fin G ≃ Fin G, (EulerianCycle hG L S σ ∧ succOf hG σ = θ ∧
      (OrbitVertexEq hG L S (succOf hG σ) → VertexCycleEq hG L S σ
        (Equiv.refl (α := Fin G)))) := by
  have hinj : Function.Injective (listingOf θ (origin hG)) := listingOf_injective ho
  have hbi : Function.Bijective (listingOf θ (origin hG)) :=
    ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hstep : ∀ y : Fin G, listingOf θ (origin hG) (nextPos hG y)
      = θ (listingOf θ (origin hG) y) := listingOf_step hG hb ho
  have hSucc : succOf hG (Equiv.ofBijective (listingOf θ (origin hG)) hbi) = θ := by
    funext x
    obtain ⟨y, hy⟩ := hbi.2 x
    have hmy : (Equiv.ofBijective (listingOf θ (origin hG)) hbi).symm x = y := by
      rw [← hy]
      exact Equiv.symm_apply_apply _ _
    simp only [succOf]
    rw [hmy]
    have hfy : (Equiv.ofBijective (listingOf θ (origin hG)) hbi) (nextPos hG y)
        = listingOf θ (origin hG) (nextPos hG y) :=
      Equiv.ofBijective_apply (listingOf θ (origin hG)) hbi (nextPos hG y)
    rw [hfy, hy.symm, hstep y]
  -- (the `succOf` on the left is definitionally `Equiv.ofBijective _ hbi`
  --  applied to the one-step rotation)
  have hEul : EulerianCycle hG L S (Equiv.ofBijective (listingOf θ (origin hG)) hbi) := by
    constructor
    · intro i
      have hfi := hf (listingOf θ (origin hG) i)
      rw [← hstep] at hfi
      exact hfi
    · show VisitsAll (succOf hG (Equiv.ofBijective (listingOf θ (origin hG)) hbi)) (origin hG)
      rw [hSucc]
      exact ho
  refine Exists.intro (Equiv.ofBijective (listingOf θ (origin hG)) hbi)
    (And.intro hEul (And.intro hSucc ?_))
  rintro ⟨k, hk⟩
  refine ⟨⟨k.val, Nat.lt_of_lt_of_le k.isLt (Nat.le_refl G)⟩, ?_⟩
  intro i
  have hcong : (Equiv.ofBijective (listingOf θ (origin hG)) hbi)
      = listingOf θ (origin hG) := by
    funext y
    exact Equiv.ofBijective_apply (listingOf θ (origin hG)) hbi y
  have hji := hk i
  rw [hSucc] at hji
  rw [hcong, listingOf, Equiv.refl_apply]
  refine hji.trans ?_
  congr 1
  apply Fin.ext
  simp only [rotAdd, Fin.val_mk, origin_val, Nat.zero_add]

/-- **The exact reformulation of `UniqueAt`.**  The first clause of `thm:BBT`
is: every one-cycle, fibre-preserving permutation of the starts reads the
`(L-1)`-mers in the truth's own cyclic order.  This is the same statement as
`UniqueAt` --- an `iff`, not an implication --- with
`vertexCycleEq_iff_orbit` and `isEulerianCycle_of_oneCycle` as the two
halves, so nothing is weakened by the reformulation. -/
theorem uniqueAt_iff_orbit :
    UniqueAt hG L S
      ↔ ∀ θ : Fin G → Fin G, Function.Bijective θ → FibrePreserving hG L S θ →
          OneCycle hG θ → OrbitVertexEq hG L S θ := by
  constructor
  · intro hu θ hb hf ho
    obtain ⟨σ, hEul, hSucc, -⟩ := isEulerianCycle_of_oneCycle hG L S θ hb hf ho
    exact hSucc ▸ vertexCycleEq_to_orbit hG L S σ (hu σ hEul)
  · intro hu σ hEul
    exact orbit_to_vertexCycleEq hG L S σ
      (hu (succOf hG σ) (succOf_bijective hG σ)
        (fibrePreserving_succOf hG L S σ hEul) (oneCycle_succOf hG L S σ hEul))

end AssemblyP1.BBTEulerianSearch
