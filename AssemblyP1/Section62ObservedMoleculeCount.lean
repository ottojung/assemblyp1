import AssemblyP1.Section62GlobalSkippedBridge

/-!
Observed reverse-complement molecule-class occurrence counts from the proved
oriented Observation 7 identity, with palindromic read words counted once.

This is a derived theorem for *observed* strand classes of genuine reduced
closed signed walks. It does not settle the entire unobserved molecule-class
universe of MB09 section 6.1 or equate the implemented reduction to Myers.
-/

namespace AssemblyP1.Section62ObservedMoleculeCount

open Section62Flow
open AssemblyP1.Section62GlobalSpellingPreservation
open AssemblyP1.Section62GlobalSkippedBridge
open AssemblyP1.Section62CircularWindowAdapter
open Section62SpellingReductionCandidate

/-- Count one word for an RC-fixed molecule, or both distinct oriented words
for a two-strand molecule class. The equality check prevents double counting
palindromic words. -/
def classWordCount {A W : Type} [DecidableEq A]
    (toList : W → List A) (rc : W → W) (m : W)
    (reads : List (List A)) : Nat :=
  if toList (rc m) = toList m then
    wordCount (toList m) reads
  else
    wordCount (toList m) reads + wordCount (toList (rc m)) reads

/-- The class count does not depend on which strand represents the molecule.
The palindrome case is a singleton; the two-strand case uses commutativity. -/
theorem classWordCount_rc_invariant {A W : Type} [DecidableEq A]
    (toList : W → List A) (rc : W → W)
    (hInv : Function.Involutive rc) (m : W) (reads : List (List A)) :
    classWordCount toList rc (rc m) reads =
      classWordCount toList rc m reads := by
  unfold classWordCount
  rw [hInv m]
  by_cases h : toList (rc m) = toList m
  · simp [h]
  · have h' : toList m ≠ toList (rc m) := Ne.symm h
    simp [h, h', add_comm]

/-- The strand list is closed under an involutive reverse-complement map. -/
theorem rc_mem_strands {W : Type} (rc : W → W) (verts : List W)
    (hInv : Function.Involutive rc) (m : W)
    (hm : m ∈ strandsOf rc verts) :
    rc m ∈ strandsOf rc verts := by
  unfold strandsOf at hm ⊢
  rcases List.mem_append.mp hm with h | h
  · exact List.mem_append.mpr (Or.inr
      (List.mem_map.mpr ⟨m, h, rfl⟩))
  · obtain ⟨v, hv, heq⟩ := List.mem_map.mp h
    have hrc : rc m = v := by rw [← heq, hInv v]
    exact List.mem_append.mpr (Or.inl (by rw [hrc]; exact hv))

/-- Every observed molecule-class count equals its signed-walk departure
count, including an RC-palindromic word (counted once) and G<L multi-wrap
circular genomes. This is a corollary of two oriented Observation 7 equalities. -/
theorem observation7_observed_rc_class_count {A W : Type}
    [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rep rc : W → W)
    (L oMin : Nat) (verts : List W) (default : A)
    (hInv : Function.Involutive rc)
    (hLen : ∀ m ∈ strandsOf rc verts, (toList m).length = L)
    (walk : List (BdEdge A W)) (start : W)
    (hStart : (toList start).length = L)
    (hsp : SignedPath start start walk)
    (hsurv : ∀ e ∈ walk,
       e ∈ transitivelyReducedSpelling W toList rc L oMin verts
         (overlapEdges A W toList rep rc L oMin verts))
    (m : W) (hm : m ∈ strandsOf rc verts) :
    let D := (toList start ++ pathTail toList walk).take
      (pathTail toList walk).length
    classWordCount toList rc m ((List.range D.length).map (window D L)) =
      classWordCount toList rc m (walk.map (fun e => toList e.sx)) := by
  have hmrc := rc_mem_strands rc verts hInv m hm
  have h1 := observation7_reduced_signed_circuit_range_count
    toList rep rc L oMin verts default hLen walk start hStart hsp hsurv m hm
  have h2 := observation7_reduced_signed_circuit_range_count
    toList rep rc L oMin verts default hLen walk start hStart hsp hsurv (rc m) hmrc
  dsimp at h1 h2 ⊢
  have hG :
      ((toList start ++ pathTail toList walk).take
        (pathTail toList walk).length).length =
        (pathTail toList walk).length := by simp
  rw [hG] at h1 h2
  unfold classWordCount
  by_cases heq : toList (rc m) = toList m
  · simp [heq, h1]
  · simp [heq, h1, h2]

example : classWordCount (fun x : Nat => [x]) id 1 [[1], [1], [2]] = 2 := by
  decide

example : classWordCount (fun b : Bool => [b]) not false
    [[false], [true], [false]] = 3 := by
  decide

#print axioms classWordCount_rc_invariant
#print axioms rc_mem_strands
#print axioms observation7_observed_rc_class_count

end AssemblyP1.Section62ObservedMoleculeCount
