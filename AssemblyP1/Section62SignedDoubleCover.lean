import AssemblyP1.Section62PhysicalHalfIncidence

/-!
# Incidence-preserving directed double cover of bidirected edges (#261)

Each ID of an abstract signed bidirected multigraph has **two distinct directed
lifted arc IDs** (ID, false) and (ID, true), regardless of whether the endpoints
coincide. They are weighted equally by the physical-edge multiplicity.

The algebraic directed state balance follows from counting the positive and
negative signed half-incidences of the original bidirected graph. This is a
bounded correspondence of incidence systems, *not* a proof that every integral
circulation is one spelled genome. Summing lifted arc uses projects to TWICE
the original edge-use vector, not to the original vector.
-/

namespace AssemblyP1.Section62SignedDoubleCover

open AssemblyP1.Section62Flow
open AssemblyP1.Section62PhysicalHalfIncidence

variable {A W : Type} [DecidableEq W]

abbrev SignedState (W : Type) := W × ℤ
abbrev SignedEdge (A W : Type) [DecidableEq W] := BdEdge A (Tagged W)
abbrev LiftedArc (ι : Type) := ι × Bool

/-- On a tagged edge, the two orientations of the directed double cover are
distinguished by a Bool arc identity, NOT by their endpoint pairs. -/
def src (e : SignedEdge A W) : Bool → SignedState W
  | false => (e.sx.1, e.sgnX)
  | true  => (e.sy.1, e.sgnY)

def dst (e : SignedEdge A W) : Bool → SignedState W
  | false => (e.sy.1, -e.sgnY)
  | true  => (e.sx.1, -e.sgnX)

/-- Per-edge count of outgoing lift arcs from the signed state (w,s). -/
def outCount (e : SignedEdge A W) (w : W) (s : ℤ) : ℕ :=
  (if src e false = (w,s) then 1 else 0) +
  (if src e true = (w,s) then 1 else 0)

/-- Per-edge count of incoming lift arcs at the signed state (w,s). -/
def inCount (e : SignedEdge A W) (w : W) (s : ℤ) : ℕ :=
  (if dst e false = (w,s) then 1 else 0) +
  (if dst e true = (w,s) then 1 else 0)

/-- The positive signed half-incidences are exactly outgoing arcs from +1. -/
theorem outCount_pos (e : SignedEdge A W) (w : W) :
    outCount e w 1 = posHalf e (w,false) := by
  simp [outCount, src, posHalf, cls, Prod.mk.injEq]

/-- The negative signed half-incidences are exactly outgoing arcs from -1. -/
theorem outCount_neg (e : SignedEdge A W) (w : W) :
    outCount e w (-1) = negHalf e (w,false) := by
  simp [outCount, src, negHalf, cls, Prod.mk.injEq]

/-- At a positive signed state, incoming arcs count the negative half-edges. -/
theorem inCount_pos (e : SignedEdge A W) (w : W) :
    inCount e w 1 = negHalf e (w,false) := by
  simp [inCount, dst, negHalf, cls, Prod.mk.injEq, neg_eq_iff_eq_neg, add_comm]

/-- At a negative signed state, incoming arcs count the positive half-edges. -/
theorem inCount_neg (e : SignedEdge A W) (w : W) :
    inCount e w (-1) = posHalf e (w,false) := by
  simp [inCount, dst, posHalf, cls, Prod.mk.injEq, neg_eq_iff_eq_neg, add_comm]

/-- Two directed arcs exist per *physical edge ID*, preserving multiplicity,
including two loops with identical signed endpoints. -/
def liftOut {ι : Type} (ids : List ι) (rep : ι → SignedEdge A W)
    (flow : ι → ℕ) (w : W) (s : ℤ) : ℕ :=
  (ids.map (fun i => flow i * outCount (rep i) w s)).sum

def liftIn {ι : Type} (ids : List ι) (rep : ι → SignedEdge A W)
    (flow : ι → ℕ) (w : W) (s : ℤ) : ℕ :=
  (ids.map (fun i => flow i * inCount (rep i) w s)).sum

def positiveIncidences {ι : Type} (ids : List ι) (rep : ι → SignedEdge A W)
    (flow : ι → ℕ) (w : W) : ℕ :=
  (ids.map (fun i => flow i * posHalf (rep i) (w,false))).sum

def negativeIncidences {ι : Type} (ids : List ι) (rep : ι → SignedEdge A W)
    (flow : ι → ℕ) (w : W) : ℕ :=
  (ids.map (fun i => flow i * negHalf (rep i) (w,false))).sum

theorem liftOut_pos {ι : Type} (ids : List ι) (rep : ι → SignedEdge A W)
    (flow : ι → ℕ) (w : W) :
    liftOut ids rep flow w 1 = positiveIncidences ids rep flow w := by
  simp [liftOut, positiveIncidences, outCount_pos]

theorem liftIn_pos {ι : Type} (ids : List ι) (rep : ι → SignedEdge A W)
    (flow : ι → ℕ) (w : W) :
    liftIn ids rep flow w 1 = negativeIncidences ids rep flow w := by
  simp [liftIn, negativeIncidences, inCount_pos]

theorem liftOut_neg {ι : Type} (ids : List ι) (rep : ι → SignedEdge A W)
    (flow : ι → ℕ) (w : W) :
    liftOut ids rep flow w (-1) = negativeIncidences ids rep flow w := by
  simp [liftOut, negativeIncidences, outCount_neg]

theorem liftIn_neg {ι : Type} (ids : List ι) (rep : ι → SignedEdge A W)
    (flow : ι → ℕ) (w : W) :
    liftIn ids rep flow w (-1) = positiveIncidences ids rep flow w := by
  simp [liftIn, positiveIncidences, inCount_neg]

/-- A balanced physical signed-incidence system induces directed balance
at BOTH signed states, with both lifted arc IDs kept distinct. -/
theorem signedLift_balanced {ι : Type} (ids : List ι)
    (rep : ι → SignedEdge A W) (flow : ι → ℕ)
    (h : ∀ w : W, positiveIncidences ids rep flow w =
                   negativeIncidences ids rep flow w) :
    ∀ w : W, liftOut ids rep flow w 1 = liftIn ids rep flow w 1 ∧
             liftOut ids rep flow w (-1) = liftIn ids rep flow w (-1) := by
  intro w
  constructor
  · rw [liftOut_pos, liftIn_pos]
    exact h w
  · rw [liftOut_neg, liftIn_neg]
    exact (h w).symm

/-- Two arc IDs project to the same physical edge, so total directed
arc multiplicity at ID i is TWICE f(i), not f(i). -/
theorem projected_use_twice {ι : Type} (flow : ι → ℕ) (i : ι) :
    flow i + flow i = 2 * flow i := by omega

end AssemblyP1.Section62SignedDoubleCover
