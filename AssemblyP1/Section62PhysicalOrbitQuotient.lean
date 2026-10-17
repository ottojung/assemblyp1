import AssemblyP1.Section62PhysicalHalfIncidence

/-!
# Reversal-quotiented physical signed-edge incidences (#261)

An oriented bidirected edge and its reverse-complement representation
must have ONE physical edge identity.  We quotient by the reversal
involution, and use merged per-endpoint lemmas to define positive and
negative half-incidences directly on the quotient.

This is a necessary formal ingredient, NOT a construction of the MB09
physical overlap graph: candidate edge support, parallel edge IDs,
flow balance, vertex bounds, genome spellings, and ML transport remain
separate open requirements.
-/

namespace AssemblyP1.Section62PhysicalOrbitQuotient

open AssemblyP1.Section62Flow
open AssemblyP1.Section62PhysicalHalfIncidence

variable {A W : Type} [DecidableEq W]

abbrev Edge := BdEdge A (Tagged W)

/-- Two tagged orientations denote the same abstract physical edge exactly
when one is the reverse-complement representation of the other. -/
def reverseSetoid (A W : Type) [DecidableEq W] : Setoid (BdEdge A (Tagged W)) where
  r e f := e = f ∨ e = reverseEdge f
  iseqv := {
    refl := by
      intro e
      exact Or.inl rfl
    symm := by
      intro e f h
      change e = f ∨ e = reverseEdge f at h
      rcases h with h | h
      · exact Or.inl h.symm
      · right
        calc
          f = reverseEdge (reverseEdge f) :=
            (reverseEdge_involutive (A := A) (W := W) f).symm
          _ = reverseEdge e := congrArg reverseEdge h.symm
    trans := by
      intro e f g h k
      change e = f ∨ e = reverseEdge f at h
      change f = g ∨ f = reverseEdge g at k
      rcases h with h | h
      · rcases k with k | k
        · exact Or.inl (h.trans k)
        · exact Or.inr (h.trans k)
      · rcases k with k | k
        · exact Or.inr (h.trans (congrArg reverseEdge k))
        · left
          exact h.trans ((congrArg reverseEdge k).trans
            (reverseEdge_involutive (A := A) (W := W) g))
  }

/-- An edge orbit is one edge object, not two independently weighted
oriented edge values. -/
def PhysicalOrbit (A W : Type) [DecidableEq W] : Type :=
  Quotient (reverseSetoid A W)

/-- Positive incident half-edges are well-defined on the physical
reversal orbit, including loop double incidence. -/
def orbitPos (v : Tagged W) : PhysicalOrbit A W → ℕ :=
  Quotient.lift (fun e : Edge (A := A) (W := W) => posHalf e v) (by
    intro e f h
    change e = f ∨ e = reverseEdge f at h
    rcases h with h | h
    · exact congrArg (fun x => posHalf x v) h
    · rw [h]
      exact posHalf_reverse f v)

/-- Negative incident half-edges are well-defined on the physical
reversal orbit. -/
def orbitNeg (v : Tagged W) : PhysicalOrbit A W → ℕ :=
  Quotient.lift (fun e : Edge (A := A) (W := W) => negHalf e v) (by
    intro e f h
    change e = f ∨ e = reverseEdge f at h
    rcases h with h | h
    · exact congrArg (fun x => negHalf x v) h
    · rw [h]
      exact negHalf_reverse f v)

theorem orbitPos_mk (e : Edge (A := A) (W := W)) (v : Tagged W) :
    orbitPos (A := A) v (Quotient.mk (reverseSetoid A W) e) = posHalf e v := rfl

theorem orbitNeg_mk (e : Edge (A := A) (W := W)) (v : Tagged W) :
    orbitNeg (A := A) v (Quotient.mk (reverseSetoid A W) e) = negHalf e v := rfl

/-- The two reversed tagged edge values are one physical edge. -/
theorem orbit_mk_reverse (e : Edge (A := A) (W := W)) :
    (Quotient.mk (reverseSetoid A W) e : PhysicalOrbit A W)
      = Quotient.mk (reverseSetoid A W) (reverseEdge e) := by
  apply Quotient.sound
  right
  exact (reverseEdge_involutive (A := A) (W := W) e).symm

/-- Weighted vertex visits are now defined ON orbit values, and cannot
depend on a choice of oriented edge representatives. -/
noncomputable def orbitVisits (support : Finset (PhysicalOrbit A W))
    (flow : PhysicalOrbit A W → ℕ) (v : Tagged W) : ℕ := by
  classical
  exact ∑ q ∈ support, flow q * orbitPos (A := A) v q

noncomputable def orbitNegativeVisits (support : Finset (PhysicalOrbit A W))
    (flow : PhysicalOrbit A W → ℕ) (v : Tagged W) : ℕ := by
  classical
  exact ∑ q ∈ support, flow q * orbitNeg (A := A) v q

/-- A physical balanced circulation is formulated without counted
representations: each edge orbit has only one flow variable. -/
def OrbitBalanced (support : Finset (PhysicalOrbit A W))
    (flow : PhysicalOrbit A W → ℕ) : Prop :=
  ∀ v : Tagged W, orbitVisits support flow v = orbitNegativeVisits support flow v

end AssemblyP1.Section62PhysicalOrbitQuotient
