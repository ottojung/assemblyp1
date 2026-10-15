import AssemblyP1.Section62CircularWindowAdapter
import AssemblyP1.Section62PeriodicSeam
import AssemblyP1.Section62SourceSignedSeamAdapter

/-!
Bridge an aligned closed signed walk's linearized spelling to the circular
periodic-window function used in Observation 7. This is needed to discharge
CircularSpelling.hAnchors without assuming the target window equality.
-/

namespace AssemblyP1.Section62AnchoredWindowBridge

open AssemblyP1.Section62CircularWindowAdapter
open AssemblyP1.Section62PeriodicSeam
open AssemblyP1.Section62SourceSignedSeamAdapter
open Section62Flow Section62SpellingReductionCandidate
open AssemblyP1.Section62GlobalSpellingPreservation

theorem periodic_window_eq_drop_take {A : Type} (X : List A) (default : A)
    (G L s : Nat) (hG : 0 < G) (hXlen : X.length = L + G)
    (hseam : X.take L = X.drop G) (hs : s < G) :
    window (X.take G) L s = (X.drop s).take L := by
  have hDlen : (X.take G).length = G := by
    simp [List.length_take, hXlen]
  have hDpos : 0 < (X.take G).length := by omega
  apply List.ext_getElem
  · simp [window, hDlen, hG, hXlen]
    omega
  · intro i hi hi₂
    have hiL : i < L := by
      have hwlen : (window (X.take G) L s).length = L :=
        window_length_of_nonempty (X.take G) L s hDpos
      omega
    have hsi : s + i < X.length := by omega
    have hmod : (s + i) % G < G := Nat.mod_lt _ hG
    have hm := seam_periodic_prefix hG X default hXlen hseam (s + i) hsi
    have hproj : (X.take G).getD ((s + i) % G) default =
      (X.take G)[(s + i) % G] := by
      simp [List.getD, hDlen, hmod]
    have hx : X.getD (s + i) default = X[s+i] := by
      simp [List.getD, hsi]
    have heq : (X.take G)[(s+i)%G] = X[s+i] := by
      rw [hx, hproj] at hm
      exact hm.symm
    have htake : (X.take G)[(s+i)%G] = X[(s+i)%G] := by
      simp [List.getElem_take]
    rw [htake] at heq
    simp [window, hDlen, hG, heq]

/-- Concrete source-level bridge: every position of a real closed signed
overlap circuit's linearization has the same read word in its derived circular
genome. The graph model is the genuine MB09-style overlapEdges, not an
assumed generic ValidPath; this holds with readLen > genome length too. -/
theorem signed_circuit_window_eq_linear {A W : Type}
    [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rep rc : W → W) (readLen oMin : Nat)
    (verts : List W) (default : A)
    (hLen : ∀ r ∈ strandsOf rc verts, (toList r).length = readLen)
    (edges : List (BdEdge A W)) (start : W)
    (hStart : (toList start).length = readLen)
    (hsp : SignedPath start start edges)
    (hmem : ∀ e ∈ edges,
      e ∈ overlapEdges A W toList rep rc readLen oMin verts)
    (s : Nat) (hs : s < (pathTail toList edges).length) :
    window ((toList start ++ pathTail toList edges).take
      (pathTail toList edges).length) readLen s =
        ((toList start ++ pathTail toList edges).drop s).take readLen := by
  have hG := signed_circuit_tail_pos toList rep rc readLen oMin verts
    hLen edges start start hsp hmem
  have hseam := signed_circuit_seam toList rep rc readLen oMin verts
    hLen edges start hStart hsp hmem
  have hXlen : (toList start ++ pathTail toList edges).length =
      readLen + (pathTail toList edges).length := by simp [hStart]
  exact periodic_window_eq_drop_take
    (toList start ++ pathTail toList edges) default
    (pathTail toList edges).length readLen s hG hXlen hseam hs

#print axioms periodic_window_eq_drop_take
#print axioms signed_circuit_window_eq_linear

end AssemblyP1.Section62AnchoredWindowBridge
