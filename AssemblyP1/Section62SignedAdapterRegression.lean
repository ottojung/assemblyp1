import AssemblyP1.Section62CircularWindowAdapter
import AssemblyP1.Section62SourceSignedSeamAdapter

/-!
# Non-vacuity regression: the signed-circuit → aligned-circular-genome adapter

This module instantiates the `Section62SourceSignedSeamAdapter` projection on
two concrete legal signed overlap circuits, so that the adapter's hypotheses
are concretely true (verified by `decide`/`rfl`, not assumed) and its
conclusions are checked against exact expected words.

* Instance 1 is the board's length-`readLen` = 3, length-`G` = 4 cycle
  `ABC → BCD → CDA → DAB → ABC` with proper 2-letter overlaps and extension 1
  each.  The aligned circular genome is `D = ABCD` (the first `G` letters of
  the linearization), and the raw `pathTail` is `DABC`, a rotation by
  `readLen % G = 3`.
* Instance 2 has `readLen = 5 > G = 3`: the cycle `ABCAB → BCABC → CABCA →
  ABCAB` with proper 4-letter overlaps and extension 1 each.  Here the length-5
  reads wrap around the length-3 genome *twice*; the merged periodic window
  (`Section62CircularWindowAdapter.window`, whose length-exactness is
  `window_length_of_nonempty`) still yields genuine 5-letter reads.

For each instance we record the two revert witnesses the board asked for:

* reverting the aligned-genome convention back to the raw `pathTail` makes the
  start-0 anchor window equal the wrong read (concretely `DAB ≠ ABC`);
* reverting the periodic window back to the pre-PR-219 rotation-only window
  makes the `G < readLen` "window" too short to be a read
  (concretely `[0,1,2] ≠ ABCAB`, length 3 ≠ 5).

This module claims NO full `CircularSpelling`, NO `hInteriorSkipped`, NO
Observation 7, and NO Myers/MB09 algorithm equivalence.  It only checks the
adapter's seam/periodicity conclusions and the anchored half of
`CircularSpelling.hAnchors` (`anchors 0 (extensions readLen walk)` mapped
through the window equals the visited read strands) on the two concrete
instances.
-/

namespace AssemblyP1.Section62SignedAdapterRegression

open AssemblyP1.Section62OverlapSuffix
open AssemblyP1.Section62GlobalSpellingPreservation
open AssemblyP1.Section62CircularStarts
open AssemblyP1.Section62CircularWindowAdapter
open AssemblyP1.Section62SourceSignedSeamAdapter
open AssemblyP1.Section62Flow
open AssemblyP1.Section62SpellingReductionCandidate

/-- The pre-PR-219 rotation-only window, kept here ONLY as the revert target of
the non-vacuity witnesses.  It does not produce a `readLen`-long cyclic window
when `0 < D.length < readLen`. -/
def rotationWindow {A : Type} (D : List A) (readLen s : Nat) : List A :=
  (D.drop s ++ D.take s).take readLen

/-! ## Instance 1: `readLen = 3`, `G = 4`, cycle ABC → BCD → CDA → DAB → ABC -/

def abc : List Nat := [0, 1, 2]
def bcd : List Nat := [1, 2, 3]
def cda : List Nat := [2, 3, 0]
def dab : List Nat := [3, 0, 1]

def cycleVerts : List (List Nat) := [abc, bcd, cda, dab]

def cycleEdges : List (BdEdge Nat (List Nat)) :=
  [bdEdge id abc bcd 2, bdEdge id bcd cda 2, bdEdge id cda dab 2,
    bdEdge id dab abc 2]

def cycPathTail : List Nat := pathTail id cycleEdges
def cycX : List Nat := id abc ++ cycPathTail
def cycD : List Nat := cycX.take cycPathTail.length

theorem cycle_hLen : ∀ s ∈ strandsOf id cycleVerts, (id s).length = 3 := by
  intro s hs
  have h8 : strandsOf id cycleVerts = [abc, bcd, cda, dab, abc, bcd, cda, dab] := by
    simp [strandsOf, cycleVerts]
  rw [h8] at hs
  simp only [List.mem_cons, List.mem_nil] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem cycle_hsp : SignedPath abc abc cycleEdges := by
  unfold SignedPath Step cycleEdges
  refine ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ?_⟩
  exact List.IsChain.cons (by rfl)
    (List.IsChain.cons (by rfl)
      (List.IsChain.cons (by rfl) (List.IsChain.singleton _)))

theorem cycle_hmem :
    ∀ e ∈ cycleEdges, e ∈ overlapEdges Nat (List Nat) id id 3 1 cycleVerts := by
  intro e he
  unfold cycleEdges at he
  simp only [List.mem_cons, List.mem_nil] at he
  rcases he with rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · decide

/-- The projected steps are exactly the source `(overlap, arrival strand)` pairs. -/
theorem regression_graphSteps_1 :
    graphSteps id cycleEdges = [(2, bcd), (2, cda), (2, dab), (2, abc)] := by
  rfl

/-- The projected walk is a concrete legal `ValidPath` from the first read. -/
theorem regression_validPath_1 :
    ValidPath 3 (id abc) (graphSteps id cycleEdges) := by
  simp [graphSteps, ValidPath]

/-- The projected walk's final target read is the first read again (closure). -/
theorem regression_pathTarget_1 :
    pathTarget (id abc) (graphSteps id cycleEdges) = id abc := by
  decide

/-- The adapter's own projection theorem, instantiated on the concrete cycle. -/
theorem regression_validProjection_1 :
    ValidPath 3 (id abc) (graphSteps id cycleEdges) ∧
      pathTarget (id abc) (graphSteps id cycleEdges) = id abc :=
  signedPath_valid_graph_steps id id id 3 1 cycleVerts cycle_hLen cycleEdges abc abc
    cycle_hsp cycle_hmem

/-- The concrete linearization is `ABCDABC` and its aligned genome is `ABCD`. -/
theorem regression_X_1 : cycX = [0, 1, 2, 3, 0, 1, 2] := by rfl
theorem regression_D_1 : cycD = [0, 1, 2, 3] := by rfl
theorem regression_tail_len_1 : cycPathTail.length = 4 := by rfl

/-- The concrete seam hypothesis holds exactly. -/
theorem regression_seam_1 : cycX.take 3 = cycX.drop 4 := by rfl

/-- The adapter derives the exact cyclic seam from the genuine signed circuit. -/
theorem regression_adapter_seam_1 :
    (id abc ++ pathTail id cycleEdges).take 3 =
      (id abc ++ pathTail id cycleEdges).drop (pathTail id cycleEdges).length :=
  signed_circuit_seam id id id 3 1 cycleVerts cycle_hLen cycleEdges abc (by rfl)
    cycle_hsp cycle_hmem

/-- The start-0 anchor window of the aligned genome is the first visited read. -/
theorem regression_anchor_1 : window cycD 3 0 = abc := by decide

/-- The anchored half of `CircularSpelling.hAnchors` holds concretely: the
anchored windows of the aligned genome are exactly the visited read strands. -/
theorem regression_anchors_1 :
    (anchors 0 (extensions 3 cycleEdges)).map (window cycD 3) =
      cycleEdges.map (fun e => id e.sx) := by
  decide

/-- The raw `pathTail` is the rotation of the aligned genome by `readLen % G`. -/
theorem regression_tail_rotation_1 : cycPathTail = window cycD 4 3 := by decide

/-- The adapter's index-mapping theorem instantiated on the concrete cycle. -/
theorem regression_periodic_mapping_1 (i : Nat) (hi : i < cycX.length) :
    cycX.getD i 0 = cycD.getD (i % cycPathTail.length) 0 :=
  signed_circuit_aligned_periodicity id id id 3 1 cycleVerts cycle_hLen cycleEdges abc 0
    (by rfl) cycle_hsp cycle_hmem i hi

/-- Concrete wrap checks of the index mapping (non-vacuity of the modulo bridge). -/
example : cycX.getD 4 0 = cycD.getD 0 0 := by decide
example : cycX.getD 6 0 = cycD.getD 2 0 := by decide

/-- **Revert witness (alignment):** using the raw `pathTail` as the genome, the
start-0 anchor window is `DAB`, not the first visited read `ABC`.  Fails. -/
theorem regression_revert_alignment_misses_1 :
    window cycPathTail 3 0 = [3, 0, 1] ∧ [3, 0, 1] ≠ abc := by
  exact ⟨by decide, by decide⟩

/-! ## Instance 2: `readLen = 5`, `G = 3`, cycle ABCAB → BCABC → CABCA → ABCAB -/

def e5ab : List Nat := [0, 1, 2, 0, 1]
def e5bc : List Nat := [1, 2, 0, 1, 2]
def e5ca : List Nat := [2, 0, 1, 2, 0]

def cycle5Verts : List (List Nat) := [e5ab, e5bc, e5ca]

def cycle5Edges : List (BdEdge Nat (List Nat)) :=
  [bdEdge id e5ab e5bc 4, bdEdge id e5bc e5ca 4, bdEdge id e5ca e5ab 4]

def cyc5PathTail : List Nat := pathTail id cycle5Edges
def cyc5X : List Nat := id e5ab ++ cyc5PathTail
def cyc5D : List Nat := cyc5X.take cyc5PathTail.length

theorem cycle5_hLen : ∀ s ∈ strandsOf id cycle5Verts, (id s).length = 5 := by
  intro s hs
  have h6 : strandsOf id cycle5Verts = [e5ab, e5bc, e5ca, e5ab, e5bc, e5ca] := by
    simp [strandsOf, cycle5Verts]
  rw [h6] at hs
  simp only [List.mem_cons, List.mem_nil] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem cycle5_hsp : SignedPath e5ab e5ab cycle5Edges := by
  unfold SignedPath Step cycle5Edges
  refine ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ?_⟩
  exact List.IsChain.cons (by rfl)
    (List.IsChain.cons (by rfl) (List.IsChain.singleton _))

theorem cycle5_hmem :
    ∀ e ∈ cycle5Edges, e ∈ overlapEdges Nat (List Nat) id id 5 1 cycle5Verts := by
  intro e he
  unfold cycle5Edges at he
  simp only [List.mem_cons, List.mem_nil] at he
  rcases he with rfl | rfl | rfl
  · decide
  · decide
  · decide

/-- The concrete linearization is `ABCABCAB` and its aligned genome is `ABC`. -/
theorem regression_X_2 : cyc5X = [0, 1, 2, 0, 1, 2, 0, 1] := by rfl
theorem regression_D_2 : cyc5D = [0, 1, 2] := by rfl
theorem regression_tail_len_2 : cyc5PathTail.length = 3 := by rfl

/-- The concrete seam hypothesis holds exactly. -/
theorem regression_seam_2 : cyc5X.take 5 = cyc5X.drop 3 := by rfl

/-- The adapter derives the exact cyclic seam for the `G < readLen` circuit too. -/
theorem regression_adapter_seam_2 :
    (id e5ab ++ pathTail id cycle5Edges).take 5 =
      (id e5ab ++ pathTail id cycle5Edges).drop (pathTail id cycle5Edges).length :=
  signed_circuit_seam id id id 5 1 cycle5Verts cycle5_hLen cycle5Edges e5ab (by rfl)
    cycle5_hsp cycle5_hmem

/-- The merged periodic window yields a genuine length-5 read that wraps twice
around the length-3 genome: the anchor window is the first visited read. -/
theorem regression_anchor_2 : window cyc5D 5 0 = e5ab := by decide

/-- The anchored half of `CircularSpelling.hAnchors` holds concretely in the
`G < readLen` regime (repeated seam wraps). -/
theorem regression_anchors_2 :
    (anchors 0 (extensions 5 cycle5Edges)).map (window cyc5D 5) =
      cycle5Edges.map (fun e => id e.sx) := by
  decide

/-- The raw `pathTail` is the rotation of the aligned genome by `readLen % G = 2`. -/
theorem regression_tail_rotation_2 : cyc5PathTail = window cyc5D 3 2 := by decide

/-- The adapter's index-mapping theorem instantiated on the `G < readLen` cycle. -/
theorem regression_periodic_mapping_2 (i : Nat) (hi : i < cyc5X.length) :
    cyc5X.getD i 0 = cyc5D.getD (i % cyc5PathTail.length) 0 :=
  signed_circuit_aligned_periodicity id id id 5 1 cycle5Verts cycle5_hLen cycle5Edges e5ab 0
    (by rfl) cycle5_hsp cycle5_hmem i hi

/-- Concrete wrap checks of the index mapping across the doubled seam. -/
example : cyc5X.getD 5 0 = cyc5D.getD 2 0 := by decide
example : cyc5X.getD 7 0 = cyc5D.getD 1 0 := by decide

/-- **Revert witness (alignment):** on the raw `pathTail` genome, the start-0
window of the `G < readLen` instance is `CABCA`, not the first visited read
`ABCAB`.  Fails. -/
theorem regression_revert_alignment_misses_2 :
    window cyc5PathTail 5 0 = [2, 0, 1, 2, 0] ∧ [2, 0, 1, 2, 0] ≠ e5ab := by
  exact ⟨by decide, by decide⟩

/-- **Revert witness (periodic window):** reverting to the rotation-only window
makes the `G < readLen` "window" of the aligned genome too short to be a read:
`[0,1,2]` (length 3 ≠ 5), not `ABCAB`.  Fails. -/
theorem regression_revert_periodic_window_misses_2 :
    rotationWindow cyc5D 5 0 = [0, 1, 2] ∧ rotationWindow cyc5D 5 0 ≠ e5ab := by
  exact ⟨by decide, by decide⟩

#print axioms regression_graphSteps_1
#print axioms regression_validPath_1
#print axioms regression_pathTarget_1
#print axioms regression_validProjection_1
#print axioms regression_X_1
#print axioms regression_D_1
#print axioms regression_seam_1
#print axioms regression_adapter_seam_1
#print axioms regression_anchor_1
#print axioms regression_anchors_1
#print axioms regression_tail_rotation_1
#print axioms regression_periodic_mapping_1
#print axioms regression_revert_alignment_misses_1
#print axioms regression_X_2
#print axioms regression_D_2
#print axioms regression_seam_2
#print axioms regression_adapter_seam_2
#print axioms regression_anchor_2
#print axioms regression_anchors_2
#print axioms regression_tail_rotation_2
#print axioms regression_periodic_mapping_2
#print axioms regression_revert_alignment_misses_2
#print axioms regression_revert_periodic_window_misses_2

end AssemblyP1.Section62SignedAdapterRegression
