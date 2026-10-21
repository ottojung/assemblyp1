import AssemblyP1.Section62PhysicalOrbitObjective

/-!
# Uniqueness transport of the §6.2 ML objective to physical edge-orbit totals (#255/#261, L3 remainder)

The merged objective transport
`AssemblyP1.Section62PhysicalOrbitObjective.physMaximal_image_iff` reduces the
*maximality* (ties admitted) of the truth orbit flow over a candidate flow set
`F` to the maximality of its physical visit vector over the image
`physVisitVec '' F`.  It is objective-agnostic: the same reduction applies to the
exact iid score, the fixed-`N` product-binomial score, and any other score that
is a function of the visit-count vector.

The #255/#261 task asks for the transport of the exact oriented ML likelihood
objective *or its argmax / uniqueness*.  This module settles the uniqueness half
precisely, and finds that it does **not** transport:

* Maximality transports in both directions (`physMaximal_image_iff`).
* Uniqueness transports **forward** — a unique flow maximizer has a unique
  visit-vector maximizer (`physUniqueMaximal_image_of_flow`).
* Uniqueness transports **backward only when the visit map is injective on the
  candidate set** (`physUniqueMaximal_of_injective`,
  `physUniqueMaximal_iff_of_injective`).
* In general it fails.  The minimal length-`1` mixed-sign self-loop witness of
  `AssemblyP1.Section62PhysicalHalfIncidence` (`mixedLoop`) supplies two orbit
  IDs representing the *same* physical edge; two distinct orbit flows with
  disjoint support have the *same* physical visit vector
  (`MixedLoop.physVisitVec_twoRep_eq`).  On that witness the visit vector is the
  unique image maximizer while the flow is not a unique maximizer
  (`MixedLoop.physUniqueMaximal_not_transported`).

Hence the physical-orbit objective transport preserves *a* maximizer but not
uniqueness; recovering uniqueness needs an injectivity hypothesis on the visit
map, which the physical edge quotient does not provide for the two
representations of one physical edge.  This is a kernel-checked delimitation of
the L3 transport, not a closure of #255/#261.

## What is *not* claimed here

* No identification of a physical orbit flow with a single circular spelled
  genome, and no proof that the visit-vector image equals the spelled-spectrum
  set (both OPEN, and the latter is obstructed by the `AAATT` witness of
  `AssemblyP1.Section62NonSpelledFlow`).
* No classification of the general §6.2 flow domain; #261 remains OPEN.
* No `sorry` / `admit` / `axiom` / `native_decide`.
-/

namespace AssemblyP1.Section62PhysicalOrbitObjectiveUniqueness

open AssemblyP1.Section62Flow
open AssemblyP1.Section62PhysicalHalfIncidence
open AssemblyP1.Section62PhysicalEdgeOrbit
open AssemblyP1.Section62FlowCountVectorAdapter
open AssemblyP1.Section62PhysicalOrbitObjective

variable {A W : Type} [DecidableEq W]

/-- A candidate `A` is the **unique** maximizer of `score` over the candidate
set `S`: it is a maximizer, and every other element of `S` that ties with it is
equal to it.  `Maximal` admits ties; this strengthens it to uniqueness. -/
def UniqueMaximal {σ : Type*} (S : Set σ) (score : σ → ℚ) (A : σ) : Prop :=
  Maximal S score A ∧ ∀ B ∈ S, score B = score A → B = A

/-! ## Uniqueness transports forward, and backward only under injectivity -/

/-- **Uniqueness transports forward.**  If the truth orbit flow `f₀` is the
unique maximizer of the transported score over the candidate flow set `F`, then
its physical visit vector is the unique maximizer over the visit-vector image.
This holds for every score that is a function of the visit vector, including
the exact oriented ML objective. -/
theorem physUniqueMaximal_image_of_flow {ι : Type} (reps : List ι)
    (rep : ι → BdEdge A (Tagged W)) (F : Set (ι → ℕ))
    (score : (Tagged W → ℕ) → ℚ) (f₀ : ι → ℕ)
    (h : UniqueMaximal F (fun f => score (physVisitVec reps rep f)) f₀) :
    UniqueMaximal (Set.image (physVisitVec reps rep) F) score
        (physVisitVec reps rep f₀) := by
  refine ⟨?_, ?_⟩
  · exact (physMaximal_image_iff reps rep F score f₀).mpr h.1
  · intro B hB hscore
    obtain ⟨g, hgF, rfl⟩ := hB
    exact congrArg (physVisitVec reps rep) (h.2 g hgF hscore)

/-- **Uniqueness transports backward under injectivity.**  If the physical visit
vector is the unique maximizer over the visit-vector image and the visit map is
injective on the candidate set at `f₀`, then `f₀` is the unique maximizer over
`F`.  Injectivity is exactly the hypothesis the physical edge quotient lacks for
the two representations of one physical edge. -/
theorem physUniqueMaximal_of_injective {ι : Type} (reps : List ι)
    (rep : ι → BdEdge A (Tagged W)) (F : Set (ι → ℕ))
    (score : (Tagged W → ℕ) → ℚ) (f₀ : ι → ℕ)
    (h : UniqueMaximal (Set.image (physVisitVec reps rep) F) score
        (physVisitVec reps rep f₀))
    (hinj : ∀ g ∈ F, physVisitVec reps rep g = physVisitVec reps rep f₀ → g = f₀) :
    UniqueMaximal F (fun f => score (physVisitVec reps rep f)) f₀ := by
  refine ⟨?_, ?_⟩
  · exact (physMaximal_image_iff reps rep F score f₀).mp h.1
  · intro g hgF hgscore
    apply hinj g hgF
    exact h.2 (physVisitVec reps rep g) ⟨g, hgF, rfl⟩ hgscore

/-- Under injectivity of the visit map at `f₀`, uniqueness of the transported
maximizer and uniqueness of the visit-vector maximizer are equivalent. -/
theorem physUniqueMaximal_iff_of_injective {ι : Type} (reps : List ι)
    (rep : ι → BdEdge A (Tagged W)) (F : Set (ι → ℕ))
    (score : (Tagged W → ℕ) → ℚ) (f₀ : ι → ℕ)
    (hinj : ∀ g ∈ F, physVisitVec reps rep g = physVisitVec reps rep f₀ → g = f₀) :
    UniqueMaximal F (fun f => score (physVisitVec reps rep f)) f₀
      ↔ UniqueMaximal (Set.image (physVisitVec reps rep) F) score
          (physVisitVec reps rep f₀) :=
  ⟨physUniqueMaximal_image_of_flow reps rep F score f₀,
   fun h => physUniqueMaximal_of_injective reps rep F score f₀ h hinj⟩

/-! ## The non-injective witness: two orbit IDs, one physical edge -/

namespace MixedLoop

/-- Two orbit IDs, both representing the *same* physical edge: the minimal
length-`1` mixed-sign self-loop and its reverse-complement representation. -/
def twoIds : List (Fin 2) := [0, 1]

def twoRep : Fin 2 → BdEdge Bool (Tagged Bool)
  | 0 => mixedLoop
  | 1 => reverseEdge mixedLoop

/-- Weight one on the first orbit ID. -/
def flowA : Fin 2 → ℕ
  | 0 => 1
  | 1 => 0

/-- Weight one on the second orbit ID. -/
def flowB : Fin 2 → ℕ
  | 0 => 0
  | 1 => 1

/-- The two orbit IDs are the two representations of one physical edge. -/
theorem physMk_twoRep_eq : physMk (twoRep 0) = physMk (twoRep 1) := by
  simpa [twoRep] using (physMk_reverse mixedLoop).symm

/-- The two distinct orbit flows have the **same** physical visit vector: the
visit map is not injective on orbit flows, because it identifies the two
representations of one physical edge. -/
theorem physVisitVec_twoRep_eq :
    physVisitVec twoIds twoRep flowA = physVisitVec twoIds twoRep flowB := by
  funext v
  simp only [physVisitVec_apply, physPosTotal, twoIds, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, flowA, flowB, physMk_twoRep_eq]
  ring

/-- The two flows are distinct. -/
theorem flowA_ne_flowB : flowA ≠ flowB := by
  intro h
  have h0 : flowA 0 = flowB 0 := congrFun h 0
  simp [flowA, flowB] at h0

/-- The two-orbit candidate set. -/
def candSet : Set (Fin 2 → ℕ) := {flowA, flowB}

/-- **Uniqueness is not transported.**  On the minimal length-`1` mixed-sign
self-loop witness the physical visit vector is the unique maximizer of the
visit-vector image (a singleton), but the flow is *not* the unique maximizer:
`flowB` ties with `flowA` because the two orbit IDs represent the same physical
edge.  This holds for every score that is a function of the visit vector,
including the exact oriented ML objective. -/
theorem physUniqueMaximal_not_transported (score : (Tagged Bool → ℕ) → ℚ) :
    UniqueMaximal (Set.image (physVisitVec twoIds twoRep) candSet) score
        (physVisitVec twoIds twoRep flowA)
      ∧ ¬ UniqueMaximal candSet (fun f => score (physVisitVec twoIds twoRep f)) flowA := by
  have hvec : physVisitVec twoIds twoRep flowA = physVisitVec twoIds twoRep flowB :=
    physVisitVec_twoRep_eq
  refine ⟨?_, ?_⟩
  · constructor
    · intro B hB
      obtain ⟨g, hgF, rfl⟩ := hB
      have hg : g = flowA ∨ g = flowB := by simpa [candSet] using hgF
      rcases hg with hg | hg
      · simp [hg]
      · simp [hg, hvec]
    · intro B hB hscore
      obtain ⟨g, hgF, rfl⟩ := hB
      have hg : g = flowA ∨ g = flowB := by simpa [candSet] using hgF
      rcases hg with hg | hg
      · simp [hg]
      · simp [hg, hvec]
  · intro h
    have htie : score (physVisitVec twoIds twoRep flowB)
        = score (physVisitVec twoIds twoRep flowA) := by
      rw [hvec]
    exact flowA_ne_flowB (h.2 flowB (by simp [candSet]) htie).symm

end MixedLoop

end AssemblyP1.Section62PhysicalOrbitObjectiveUniqueness
