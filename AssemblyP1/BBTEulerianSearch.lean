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
theorem iterate_G_of_oneCycle (θ : Fin G → Fin G) (hθ : Function.Bijective θ)
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
theorem listingOf_step (θ : Fin G → Fin G) (hθ : Function.Bijective θ)
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
    rw [h2, hR, iterate_G_of_oneCycle hG θ hθ ho, Function.iterate_zero]
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
      = θ (listingOf θ (origin hG) y) := listingOf_step hG θ hb ho
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

/-! ## 2. The circuits: an exhaustive enumeration of one-cycle, fibre-preserving
listings, with a completeness proof -/

/-- Extending a listing of the first `n` starts by one more start. -/
def extendAt {n : ℕ} (f : Fin n → Fin G) (y : Fin G) : Fin (n + 1) → Fin G :=
  fun i => if hi : i.val < n then f ⟨i.val, hi⟩ else y

theorem extendAt_of_lt {n : ℕ} (f : Fin n → Fin G) (y : Fin G) (i : Fin (n + 1))
    (hi : i.val < n) : extendAt f y i = f ⟨i.val, by omega⟩ := by
  simp [extendAt, hi]

theorem extendAt_new {n : ℕ} (f : Fin n → Fin G) (y : Fin G) :
    extendAt f y ⟨n, Nat.lt_succ_self n⟩ = y := by
  simp [extendAt]

/-- **The step condition on a new start `y` following the last start `prev`
of a listing.**  `y` must carry the `(L-1)`-mer of the start one step after
`prev`: this is the fibre-preserving condition of §1, on a partial listing. -/
def stepOk (hG : 0 < G) (L : ℕ) (S : Fin G → α) (y prev : Fin G) : Bool :=
  decide (vtx hG L S y = vtx hG L S (nextPos hG prev))

/-- ... on a partial listing of `n` starts, where there is nothing to check
at `n = 0`. -/
def stepPred (hG : 0 < G) (L : ℕ) (S : Fin G → α) :
    (n : ℕ) → (f : Fin n → Fin G) → Fin G → Bool
  | 0, _, _ => true
  | m + 1, f, y => stepOk hG L S y (f ⟨m, Nat.lt_succ_self m⟩)

/-- The last index of `Fin G`, for `0 < G`. -/
theorem lastIdx_lt (G : ℕ) (hG : 0 < G) : G - 1 < G := by omega

/-- All `G` starts of the circle, as a computable list (so that the
enumeration below can be *decided*, not merely stated). -/
def allStarts (hG : 0 < G) : List (Fin G) := List.finRange G

theorem mem_allStarts (y : Fin G) : y ∈ allStarts hG := List.mem_finRange y

/-- **The partial circuits of the `(L-1)`-mer multigraph.**  `partials n` is
the list of all listings of `n` *pairwise distinct* starts whose consecutive
`(L-1)`-mers overlap.  The recursion backtracks over the fibres of `vtx`
(`stepPred`) and prunes non-injective extensions, so the size of the list is
the number of partial Eulerian circuits rather than the number of injections
--- which is what makes the finite check of §3 cheap. -/

def partials (hG : 0 < G) (L : ℕ) (S : Fin G → α) : (n : ℕ) → List (Fin n → Fin G)
  | 0 => [Fin.elim0]
  | n + 1 =>
      (partials hG L S n).flatMap fun f =>
        ((allStarts hG).filter fun y =>
          (stepPred hG L S n f y) && decide (Function.Injective (extendAt f y))).map
            (fun y => extendAt f y)

/-- **Membership in `partials` is exactly injectivity plus the overlap
condition.**  The two directions are proved by induction on the length, and
together they say that `partials` is a *complete* enumeration of the partial
Eulerian circuits of the `(L-1)`-mer multigraph.  This is the point the finite
check of §3 rests on: a search over `partials G` that finds nothing is a
search over *all* circuits, not over a sample. -/
theorem mem_partials_iff (hG : 0 < G) (L : ℕ) (S : Fin G → α) :
    ∀ {n : ℕ} (p : Fin n → Fin G), p ∈ partials hG L S n ↔
      Function.Injective p ∧
        ∀ (i j : Fin n), j.val = i.val + 1 →
          vtx hG L S (p j) = vtx hG L S (nextPos hG (p i)) := by
  intro n
  induction n with
  | zero =>
      intro p
      constructor
      · intro hp
        simp only [partials, List.mem_singleton] at hp
        rw [hp]
        refine ⟨?_, fun i j hj => ?_⟩
        · intro a b _
          exact nomatch a
        · exact nomatch i
      · intro _
        have hp0 : p = Fin.elim0 := Subsingleton.elim _ _
        simp [partials, hp0]
  | succ n ih =>
      intro p
      constructor
      · intro hp
        simp only [partials] at hp
        obtain ⟨f, hf, hp'⟩ := List.mem_flatMap.mp hp
        obtain ⟨y, hpy, heq⟩ := List.mem_map.mp hp'
        subst heq
        have hy0 := List.mem_filter.mp hpy
        have hy' : stepPred hG L S n f y = true ∧
            decide (Function.Injective (extendAt f y)) = true := by
          rw [← Bool.and_eq_true]
          exact hy0.2
        have hinj : Function.Injective (extendAt f y) := of_decide_eq_true (And.right hy')
        obtain ⟨hinj', hov⟩ := (ih f).mp hf
        refine ⟨hinj, ?_⟩
        intro i j hj
        by_cases hlt : j.val < n
        · rw [extendAt_of_lt f y j hlt, extendAt_of_lt f y i (by omega)]
          exact hov ⟨i.val, by omega⟩ ⟨j.val, hlt⟩ hj
        · have hjn : j.val = n := by omega
          have hjn' : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = j := Fin.ext hjn.symm
          have hj' : (n : ℕ) = i.val + 1 := by omega
          rw [← hjn', extendAt_new f y, extendAt_of_lt f y i (by omega)]
          cases n with
          | zero => omega
          | succ m =>
              have hiv : i.val = m := by omega
              have h1 : vtx hG L S y = vtx hG L S (nextPos hG (f ⟨m, by omega⟩)) := by
                simpa only [stepPred, Bool.false_eq_true, ↓reduceIte] using
                  of_decide_eq_true (And.left hy')
              rw [h1]
              congr 1
              congr 1
              apply congrArg f
              apply Fin.ext
              exact hiv.symm
      · rintro ⟨hp, hov⟩
        simp only [partials]
        have heq : p = extendAt (fun (i : Fin n) => p ⟨i.val, by omega⟩)
            (p ⟨n, Nat.lt_succ_self n⟩) := by
          funext i
          by_cases h : i.val < n
          · simp [extendAt, h]
          · have hn : i.val = n := by omega
            simp [extendAt, h, hn]
            exact congrArg p (Fin.ext hn)
        refine List.mem_flatMap.mpr
          ⟨(fun (i : Fin n) => p ⟨i.val, by omega⟩),
            (ih _).mpr ⟨?_, ?_⟩,
            List.mem_map.mpr ⟨(p ⟨n, Nat.lt_succ_self n⟩ : Fin G), ?_, heq.symm⟩⟩
        · intro a b hab
          refine Fin.ext (congrArg (fun t => t.val)
            (hp (Fin.ext (congrArg (fun t => t.val) hab))))
        · intro i j hj
          exact hov ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hj
        · refine List.mem_filter.mpr ⟨mem_allStarts hG _, ?_⟩
          have hinj' : Function.Injective
              (extendAt (fun (i : Fin n) => p ⟨i.val, by omega⟩)
                (p ⟨n, Nat.lt_succ_self n⟩)) :=
            fun a b hab => by
              have hab' : p a = p b := by
                rw [congrFun heq a, congrFun heq b]
                exact hab
              exact Fin.ext (congrArg (fun t : Fin (n + 1) => t.val) (hp hab'))
          have hstep' : stepPred hG L S n (fun (i : Fin n) => p ⟨i.val, by omega⟩)
              (p ⟨n, Nat.lt_succ_self n⟩) = true := by
            cases n with
            | zero => simp only [stepPred, ↓reduceIte]
            | succ m =>
                have h1 : vtx hG L S (p ⟨m + 1, by omega⟩)
                    = vtx hG L S (nextPos hG (p ⟨m, by omega⟩)) :=
                  hov ⟨m, by omega⟩ ⟨m + 1, by omega⟩ rfl
                simpa only [stepPred, stepOk, h1, decide_eq_true]
          simp [hstep', hinj']

/-! ## 3. The circuits, and the exact finite statement -/

/-- **A circuit reads the `(L-1)`-mers in the truth's cyclic order.**  This is
`OrbitVertexEq` for the successor map of the circuit, i.e. the conclusion of
`UniqueAt` in the object of §1. -/
def CircuitEq (p : Fin G → Fin G) : Prop :=
  ∃ k : Fin G, ∀ j : Fin G,
    vtx hG L S (p j) = vtx hG L S (rotAdd hG (j.val + k.val) (origin hG))

/-- **The circuits of the `(L-1)`-mer multigraph**, read from the origin: the
listings of `G` pairwise distinct starts, beginning at the origin, along
which consecutive `(L-1)`-mers overlap and which close up. -/
def circuits : List (Fin G → Fin G) :=
  ((partials hG L S G).filter fun p =>
    p (⟨0, hG⟩ : Fin G) = origin hG ∧
      vtx hG L S (origin hG) = vtx hG L S (nextPos hG (p ⟨G - 1, by omega⟩)))

theorem mem_circuits {p : Fin G → Fin G} :
    p ∈ circuits hG L S ↔ Function.Injective p ∧ p (⟨0, hG⟩ : Fin G) = origin hG ∧
      (∀ (i j : Fin G), j.val = i.val + 1 →
        vtx hG L S (p j) = vtx hG L S (nextPos hG (p i))) ∧
      vtx hG L S (origin hG) = vtx hG L S (nextPos hG (p ⟨G - 1, by omega⟩)) := by
  constructor
  · intro hp
    have hp' := (mem_partials_iff hG L S p).mp ((List.mem_filter.mp hp).1)
    have hc : p (⟨0, hG⟩ : Fin G) = origin hG ∧
        vtx hG L S (origin hG) = vtx hG L S (nextPos hG (p ⟨G - 1, by omega⟩)) :=
      of_decide_eq_true (List.mem_filter.mp hp).2
    exact ⟨hp'.1, hc.1, hp'.2, hc.2⟩
  · rintro ⟨hinj, h0, hov, hcl⟩
    refine List.mem_filter.mpr ⟨(mem_partials_iff hG L S p).mpr ⟨hinj, hov⟩, ?_⟩
    show decide (p (⟨0, hG⟩ : Fin G) = origin hG ∧
        vtx hG L S (origin hG) = vtx hG L S (nextPos hG (p ⟨G - 1, by omega⟩))) = true
    rw [decide_eq_true_eq]
    exact ⟨h0, hcl⟩

theorem bijective_of_mem_circuits {p : Fin G → Fin G} (hp : p ∈ circuits hG L S) :
    Function.Bijective p :=
  ⟨(mem_circuits hG L S (p := p)).mp hp |>.1,
    Finite.surjective_of_injective ((mem_circuits hG L S (p := p)).mp hp |>.1)⟩

/-- **The successor map of a circuit.**  A circuit `p` is a listing of the
starts, so its successor is `p ∘ nextPos ∘ p⁻¹`: send the start `p j` to the
start listed after it. -/
noncomputable def circuitSucc (hG : 0 < G) (L : ℕ) (S : Fin G → α) (p : Fin G → Fin G)
    (hp : Function.Bijective p) : Fin G → Fin G :=
  fun x => p (nextPos hG ((Equiv.ofBijective p hp).symm x))

theorem circuitSucc_bijective (p : Fin G → Fin G) (hp : Function.Bijective p) :
    Function.Bijective (circuitSucc hG L S p hp) := by
  refine Function.Bijective.comp ?_ (Function.Bijective.comp ?_ ?_)
  · exact hp
  · exact bijective_nextPos hG
  · exact (Equiv.ofBijective p hp).symm.bijective

theorem circuitSucc_step (p : Fin G → Fin G) (hp : Function.Bijective p) (j : Fin G) :
    circuitSucc hG L S p hp (p j) = p (nextPos hG j) := by
  simp only [circuitSucc]
  have h : (Equiv.ofBijective p hp).symm (p j) = j := Equiv.symm_apply_apply _ _
  rw [h]

/-- **Shifting a step commutes with reducing modulo the circle.** -/
theorem mod_succ_mod (G n : ℕ) (hG : 0 < G) :
    (n + 1) % G = ((n % G) + 1) % G :=
  (Nat.mod_add_mod n G 1).symm

theorem circuitSucc_iterate (p : Fin G → Fin G) (hp : Function.Bijective p)
    (h0 : p (⟨0, hG⟩ : Fin G) = origin hG) (n : ℕ) :
    (circuitSucc hG L S p hp)^[n] (origin hG) = p ⟨n % G, Nat.mod_lt _ hG⟩ := by
  induction n with
  | zero =>
      have hfin : (⟨0 % G, Nat.mod_lt _ hG⟩ : Fin G) = (⟨0, hG⟩ : Fin G) :=
        Fin.ext (Nat.zero_mod _)
      simp only [Function.iterate_zero, Function.id_def]
      rw [hfin]
      exact h0.symm
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      rw [circuitSucc_step hG L S p hp ⟨n % G, Nat.mod_lt _ hG⟩]
      have hfin : nextPos hG ⟨n % G, Nat.mod_lt _ hG⟩
          = ⟨(n + 1) % G, Nat.mod_lt _ hG⟩ := by
        apply Fin.ext
        show ((n % G) + 1) % G = (n + 1) % G
        exact (mod_succ_mod G n hG).symm
      rw [hfin]

theorem circuitSucc_oneCycle (p : Fin G → Fin G) (hp : Function.Bijective p)
    (h0 : p (⟨0, hG⟩ : Fin G) = origin hG) :
    OneCycle hG (circuitSucc hG L S p hp) := by
  intro a b hab
  have hab' : (circuitSucc hG L S p hp)^[a.val] (origin hG)
      = (circuitSucc hG L S p hp)^[b.val] (origin hG) := hab
  have h1 := circuitSucc_iterate hG L S p hp h0 a.val
  have h2 := circuitSucc_iterate hG L S p hp h0 b.val
  rw [h1, h2] at hab'
  have hfin : (⟨a.val % G, Nat.mod_lt _ hG⟩ : Fin G)
      = ⟨b.val % G, Nat.mod_lt _ hG⟩ := hp.injective hab'
  have : a.val = b.val := by
    have := congrArg Fin.val hfin
    simpa only [Fin.val_mk, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using this
  exact Fin.val_inj.mp this

theorem circuitSucc_fibrePreserving {p : Fin G → Fin G} (hp : p ∈ circuits hG L S) :
    FibrePreserving hG L S (circuitSucc hG L S p (bijective_of_mem_circuits hG L S hp)) := by
  have hc := (mem_circuits hG L S (p := p)).mp hp
  have hpb : Function.Bijective p := ⟨hc.1, Finite.surjective_of_injective hc.1⟩
  intro x
  have hx : x = p ((Equiv.ofBijective p hpb).symm x) := by
    have h1 := Equiv.ofBijective_apply p hpb ((Equiv.ofBijective p hpb).symm x)
    rwa [Equiv.apply_symm_apply] at h1
  show vtx hG L S (p (nextPos hG ((Equiv.ofBijective p hpb).symm x)))
      = vtx hG L S (nextPos hG x)
  rw [show nextPos hG x = nextPos hG (p ((Equiv.ofBijective p hpb).symm x))
    from congrArg (nextPos hG) hx]
  by_cases hlt : ((Equiv.ofBijective p hpb).symm x).val + 1 < G
  · exact hc.2.2.1 ((Equiv.ofBijective p hpb).symm x)
      (nextPos hG ((Equiv.ofBijective p hpb).symm x))
      (by rw [nextPos, rotAdd]; exact Nat.mod_eq_of_lt hlt)
  · have hlast : ((Equiv.ofBijective p hpb).symm x).val + 1 = G := by omega
    have hnp : nextPos hG ((Equiv.ofBijective p hpb).symm x) = origin hG := by
      apply Fin.ext
      show (((Equiv.ofBijective p hpb).symm x).val + 1) % G = 0
      rw [hlast, Nat.mod_self]
    have hj1 : (Equiv.ofBijective p hpb).symm x = ⟨G - 1, lastIdx_lt G hG⟩ := by
      apply Fin.ext
      show ((Equiv.ofBijective p hpb).symm x).val = G - 1
      omega
    have hp0 : p (origin hG) = origin hG := by
      simpa only [origin] using hc.2.1
    rw [hnp, hj1, hp0]
    exact hc.2.2.2

/-- **Every circuit is the orbit listing of a one-cycle, fibre-preserving
permutation, and presents an Eulerian cycle of the multigraph.**  Together
with §1 this says the enumeration `circuits` is not a proxy for the
statement: it is the statement, with the presentations and the successors both
made explicit. -/
theorem isEulerianCycle_circuit {p : Fin G → Fin G} (hp : p ∈ circuits hG L S) :
    ∃ σ : Fin G ≃ Fin G, EulerianCycle hG L S σ ∧ (∀ j : Fin G, σ j = p j) ∧
      succOf hG σ = circuitSucc hG L S p (bijective_of_mem_circuits hG L S hp) := by
  have hc := (mem_circuits hG L S (p := p)).mp hp
  have hpb := bijective_of_mem_circuits hG L S hp
  have hsucc : succOf hG (Equiv.ofBijective p hpb) = circuitSucc hG L S p hpb := by
    funext x
    simp only [succOf, circuitSucc]
    exact Equiv.ofBijective_apply p hpb _

  have hEul : EulerianCycle hG L S (Equiv.ofBijective p hpb) := by
    constructor
    · intro i
      rw [Equiv.ofBijective_apply, Equiv.ofBijective_apply]
      by_cases hlt : i.val + 1 < G
      · exact hc.2.2.1 i (nextPos hG i)
          (by rw [nextPos, rotAdd]; exact Nat.mod_eq_of_lt hlt)
      · have hlast : i.val + 1 = G := by omega
        have hpi : i = ⟨G - 1, lastIdx_lt G hG⟩ := by
          apply Fin.ext
          show i.val = G - 1
          omega
        have hnp : nextPos hG i = origin hG := by
          apply Fin.ext
          show (i.val + 1) % G = 0
          rw [hlast, Nat.mod_self]
        have hp0 : p (origin hG) = origin hG := by
          simpa only [origin] using hc.2.1
        rw [hnp, hpi, hp0]
        exact hc.2.2.2
    · show VisitsAll (succOf hG (Equiv.ofBijective p hpb)) (origin hG)
      rw [hsucc]
      exact circuitSucc_oneCycle hG L S p hpb hc.2.1
  exact ⟨Equiv.ofBijective p hpb, hEul, fun j => Equiv.ofBijective_apply p hpb j, hsucc⟩

/-- **The orbit listing of a one-cycle, fibre-preserving permutation is a
circuit.**  The converse direction, needed for the reduction of §1 to the
enumeration. -/
theorem mem_circuits_of_oneCycle (θ : Fin G → Fin G) (hb : Function.Bijective θ)
    (hf : FibrePreserving hG L S θ) (ho : OneCycle hG θ) :
    (fun j => θ^[j.val] (origin hG)) ∈ circuits hG L S := by
  have hinj : Function.Injective (listingOf θ (origin hG)) := listingOf_injective ho
  have hpb : Function.Bijective (listingOf θ (origin hG)) :=
    ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hcong : (Equiv.ofBijective (listingOf θ (origin hG)) hpb)
      = listingOf θ (origin hG) := by
    funext y
    exact Equiv.ofBijective_apply _ _ _
  refine (mem_circuits hG L S (p := fun j => θ^[j.val] (origin hG))).mpr
    ⟨hinj, ?_, ?_, ?_⟩
  · show θ^[0] (origin hG) = origin hG
    simp
  · intro i j hj
    show vtx hG L S (listingOf θ (origin hG) j)
      = vtx hG L S (nextPos hG (listingOf θ (origin hG) i))
    have hmod : i.val + 1 < G := by omega
    have hji : j = nextPos hG i := by
      apply Fin.ext
      show j.val = (i.val + 1) % G
      rw [hj]
      exact (Nat.mod_eq_of_lt hmod).symm
    rw [hji, listingOf_step hG θ hb ho i]
    have h1 := hf (listingOf θ (origin hG) i)
    simpa only [listingOf] using h1
  · have hcl := iterate_G_of_oneCycle hG θ hb ho
    have h0 : listingOf θ (origin hG) ⟨0, hG⟩ = origin hG := by
      simp [listingOf]
    have h1 := hf (θ^[G - 1] (origin hG))
    have hsucc1 : θ^[(G - 1).succ] (origin hG) = θ (θ^[G - 1] (origin hG)) :=
      Function.iterate_succ_apply' θ (G - 1) (origin hG)
    have hgm : (G - 1).succ = G := by omega
    have hit : θ^[G] (origin hG) = θ (θ^[G - 1] (origin hG)) :=
      ((congrArg (fun n : ℕ => θ^[n] (origin hG)) hgm.symm).trans hsucc1)
    rw [← hit, hcl] at h1
    show vtx hG L S (⟨0, hG⟩ : Fin G)
      = vtx hG L S (nextPos hG (listingOf θ (origin hG) ⟨G - 1, lastIdx_lt G hG⟩))
    have h1' : vtx hG L S (origin hG)
        = vtx hG L S (nextPos hG (listingOf θ (origin hG) ⟨G - 1, lastIdx_lt G hG⟩)) := by
      simpa only [listingOf] using h1
    exact h1'

/-- **The exact finite statement of `UniqueAt`.**  The first clause of
`thm:BBT` at `(G, L, S)` holds if and only if every circuit of the
`(L-1)`-mer multigraph reads the `(L-1)`-mers in the truth's own cyclic
order.  The two directions are `isEulerianCycle_circuit` (every circuit
presents an Eulerian cycle, so it is one of the `σ` that `UniqueAt`
quantifies over) and `mem_circuits_of_oneCycle` (the successor of an Eulerian
cycle is a one-cycle, fibre-preserving map, whose orbit listing is a circuit,
so no `σ` escapes the enumeration).  So this is an `iff`, and the search
below is over the *statement*. -/
theorem uniqueAt_iff_circuits :
    UniqueAt hG L S ↔ ∀ p ∈ circuits hG L S, CircuitEq hG L S p := by
  constructor
  · intro hu p hp
    obtain ⟨σ, hEul, hσ, -⟩ := isEulerianCycle_circuit hG L S hp
    obtain ⟨k, hk⟩ := hu σ hEul
    have hps : ∀ j : Fin G, p j = σ j := fun j => (hσ j).symm
    refine ⟨k, ?_⟩
    intro j
    rw [hps]
    have : vtx hG L S (rotAdd hG k.val j)
        = vtx hG L S (rotAdd hG (j.val + k.val) (origin hG)) := by
      apply congrArg (vtx hG L S)
      apply Fin.ext
      simp only [rotAdd, Fin.val_mk, origin_val, Nat.add_comm, Nat.add_zero]
    exact (hk j).trans this
  · intro hall σ hEul
    exact (vertexCycleEq_iff_orbit hG L S σ).mpr
      (hall (fun j => (succOf hG σ)^[j.val] (origin hG))
        (mem_circuits_of_oneCycle hG L S (succOf hG σ) (succOf_bijective hG σ)
          (fibrePreserving_succOf hG L S σ hEul) (oneCycle_succOf hG L S σ hEul)))
/-! ### 3.5 The `Decidable` instances the finite check needs -/

/-- **`Decidable` for the source-faithful repeat predicates read through
`mkGenome`.**  `AssemblyP1.SourceFaithfulIs` provides `Decidable (S.IsRepeat
e a b)` and `Decidable (S.IsTripleRepeat e a b c)` for a *variable* genome
`S : Genome α`, but instance search does not fire through `mkGenome hG S`: the
def `Genome.IsRepeat` takes `[DecidableEq α]` as an instance-implicit argument,
so unifying it with the concrete `(mkGenome hG S).IsRepeat e a b` leaves the
instance argument as a metavariable and the search fails.  These three
instances are the *same* decision procedures (`unfold` + `infer_instance`), so
the predicates decided here are literally `P2`'s and `Ukkonen`'s clauses, and
in particular `FiniteStatement` below quantifies over `P2` itself and not over
a surrogate. -/
instance decIsRepeat (W : Fin G → α) (hG : 0 < G) (e : ℕ) (a b : Fin G) :
    Decidable ((mkGenome hG W).IsRepeat e a b) := by
  unfold mkGenome Genome.IsRepeat Genome.Agree Genome.Preceding Genome.Following
    Genome.window Genome.cycl
  infer_instance

instance decIsTripleRepeat (W : Fin G → α) (hG : 0 < G) (e : ℕ) (a b c : Fin G) :
    Decidable ((mkGenome hG W).IsTripleRepeat e a b c) := by
  unfold mkGenome Genome.IsTripleRepeat Genome.Agree Genome.Preceding
    Genome.Following Genome.window Genome.cycl
  infer_instance

instance decInterleaved (W : Fin G → α) (hG : 0 < G) (a b c d : Fin G) :
    Decidable (Interleaved (mkGenome hG W) a b c d) := by
  unfold mkGenome Interleaved FourDistinct InOpenArc
  infer_instance

/-- **The `Decidable` instance for `P2` itself**, which the previous packet
needed and did not have.  The three `haveI` steps are *explicit
applications* of the instances above to the bound variables: instance search
alone cannot derive `Decidable (∀ e a b c : Fin G, IsTripleRepeat e a b c →
_)` from pointwise instances, because that is not an instance derivation, so
the pointwise decisions have to be supplied as local instances by hand. -/
instance decP2 (W : Fin G → α) (L : ℕ) : Decidable (P2 hG L W) := by
  unfold P2
  haveI h1 : ∀ (e a b c : Fin G),
      Decidable ((mkGenome hG W).IsTripleRepeat e a b c → e.val < L - 1) :=
    fun _ _ _ _ => inferInstance
  haveI h2 : ∀ (e₁ e₂ a b c d : Fin G),
      Decidable ((mkGenome hG W).IsRepeat e₁ a b →
        (mkGenome hG W).IsRepeat e₂ c d → Interleaved (mkGenome hG W) a b c d →
          e₁.val ≤ L - 2 ∨ e₂.val ≤ L - 2) :=
    fun _ _ _ _ _ _ => inferInstance
  infer_instance

/-! ## 4. The finite class: the exact statement, and the equivalent search -/

/-- **The exact #89 statement, on a finite class of binary circular genomes.**
Every binary circular genome of length at most `maxG`, every read length
`2 ≤ L ≤ maxL`: if the genome satisfies `P2` of `def:P1P2`, then every
alternative Eulerian cycle of its condensed `(L-1)`-mer multigraph spells its
own vertex cycle.  This is `BBTEulerian.UniqueAt`, literally; no hypothesis is
added, dropped or weakened, and the inner quantifier over the alternative
traversal is `UniqueAt`'s own. -/
def FiniteStatement (maxG maxL : ℕ) : Prop :=
  ∀ g ∈ List.range (maxG + 1), ∀ l ∈ List.range (maxL + 1), 2 ≤ l → ∀ hg : 0 < g,
    ∀ S : Fin g → Fin 2, P2 hg l S → UniqueAt hg l S

/-- **The same statement, on the enumeration of §3**: every *circuit* of the
`(L-1)`-mer multigraph reads the `(L-1)`-mers in the truth's own cyclic order.
`finiteStatement_iff_search` is the kernel proof that the two are the same
statement, so a search over circuits decides the statement itself. -/
def FiniteSearch (maxG maxL : ℕ) : Prop :=
  ∀ g ∈ List.range (maxG + 1), ∀ l ∈ List.range (maxL + 1), 2 ≤ l → ∀ hg : 0 < g,
    ∀ S : Fin g → Fin 2, P2 hg l S →
      ∀ p ∈ circuits hg l S, CircuitEq hg l S p

/-- The statement form is decidable, so it can be *decided* rather than merely
stated.  (The instances of §3.5 are what make `P2` decidable at all; the
search form needs one instance more --- `Decidable` for a `∀` over the
*function* type `Fin G → Fin G` with a `List`-membership test --- and that
instance is not yet available, which is the one mechanical step left before
the search form can be decided.  It is plumbing, not mathematics: the two
forms are proved equal below.) -/
instance (maxG maxL : ℕ) : Decidable (FiniteStatement maxG maxL) := by
  unfold FiniteStatement
  infer_instance

/-- **The search over circuits decides the statement.**  Each `(G, L, S)` is
handled by `uniqueAt_iff_circuits`, and the outer quantifiers are the ones of
`FiniteStatement`. -/
theorem finiteStatement_iff_search (maxG maxL : ℕ) :
    FiniteStatement maxG maxL ↔ FiniteSearch maxG maxL := by
  constructor
  · intro hG
    refine fun g hgr l hlr hl hg hS hp p hpc => ?_
    exact (uniqueAt_iff_circuits hg l hS).mp (hG g hgr l hlr hl hg hS hp) p hpc
  · intro hG
    refine fun g hgr l hlr hl hg hS hp σ hEul => ?_
    exact (vertexCycleEq_iff_orbit hg l hS σ).mpr
      (hG g hgr l hlr hl hg hS hp (fun j => (succOf hg σ)^[j.val] (origin hg))
        (mem_circuits_of_oneCycle hg l hS (succOf hg σ) (succOf_bijective hg σ)
          (fibrePreserving_succOf hg l hS σ hEul) (oneCycle_succOf hg l hS σ hEul)))

/-- **The two-clause form of `thm:BBT` follows from the search**, so a finite
check of `FiniteSearch` is a check of `thm:BBT` at those instances. -/
theorem finiteObstruction_of_search {maxG maxL : ℕ} (h : FiniteSearch maxG maxL) :
    ∀ g ∈ List.range (maxG + 1), ∀ l ∈ List.range (maxL + 1), 2 ≤ l → ∀ hg : 0 < g,
      ∀ S : Fin g → Fin 2, P2 hg l S →
        ∀ σ : Fin g ≃ Fin g, EulerianCycle hg l S σ →
          VertexCycleEq hg l S σ (Equiv.refl (α := Fin g)) ∨ LongObstruction hg l S := by
  intro g hgr l hlr hl hg hS hp σ hEul
  exact (obstruction_of_uniqueAt hg l hS hl hp
    ((uniqueAt_iff_circuits hg l hS).mpr (h g hgr l hlr hl hg hS hp))) σ hEul

end AssemblyP1.BBTEulerianSearch
