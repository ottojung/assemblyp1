/-!
# §6.2 spelling preservation does not transport vertex visits (#284)

This module isolates the exact invariant that the spelling-preserving §6.2
transitive reduction preserves, and the one it does **not**.

The reduction (see `Section62SpellingReductionCandidate`) replaces a direct
overlap edge `sx → sy` of length `l` by a two-edge path `sx → m → sy` with
proper overlaps `l₁, l₂` satisfying the composition law `l₁ + l₂ = L + l`, under
which the two paths spell the same word (`spellPath_eq_spellDirect`).  A
simultaneous reduction therefore preserves the spelled word of every walk, hence
the *full* length-`L` window multiset of that word.

What it does not preserve is the **physical class count**: the multiset of
vertices (observed read molecules) visited by the walk.  The concrete `L = 5`
witness below shows two walks with the same spelled word and the same full
window multiset but different vertex multisets, and it shows that the full
window multiset contains an *unobserved* window (a seam window that is not an
observed read vertex).  Consequently no function of the invariant window
multiset can recover the physical class counts, and any §6.2 flow or ML
objective computed from graph vertices requires a separate transport argument.

This module is deliberately self-contained (Lean core only, no Mathlib import)
so that the transport diagnostic stands independently of the heavy §6.2 chain.
It adds new definitions and theorems only; it does not redefine
`isReducibleB`, `transitivelyReduced`, `SpelledFeasible62`, or
`StepsSurviveReduction`, and it does not reprove any merged §6.2 theorem.
-/

namespace AssemblyP1.Section62VisitTransport

variable {A : Type}

/-! ## Spelled words, windows, and vertex visits -/

/-- Concatenation of a list of words. -/
def cats : List (List A) → List A
  | [] => []
  | (x :: xs) => x ++ cats xs

/-- The word spelled by a walk: the first vertex followed by each later vertex
with its incoming overlap dropped. -/
def spellWalk (vs : List (List A)) (ovs : List Nat) : List A :=
  match vs with
  | [] => []
  | v :: rest => v ++ cats (rest.zipWith (fun w o => w.drop o) ovs)

/-- The list of all length-`L` contiguous windows of a word (with multiplicity). -/
def windows (L : Nat) (w : List A) : List (List A) :=
  (List.range (w.length + 1 - L)).map (fun i => (w.drop i).take L)

/-- The vertices visited by a walk, i.e. the physical class count.  Two walks
have the same physical class counts only if their vertex lists agree (up to
reordering); the witness below uses lists of different lengths, so list
inequality already implies multiset inequality. -/
def vertexMultiset (vs : List (List A)) : List (List A) := vs

/-! ## Window-multiplicity invariance under a detour replacement -/

/-- Equal words have equal length-`L` window multisets. -/
theorem windows_congr {L : Nat} {w v : List A} (h : w = v) :
    windows L w = windows L v := by rw [h]

/-- **Window-multiplicity invariance under a detour replacement.**  If the
two-edge detour `sx → m → sy` spells the same word as the direct edge
`sx → sy` — which is exactly what the composition law `l₁ + l₂ = L + l` gives
(`Section62SpellingReductionCandidate.spellPath_eq_spellDirect`) — then the
full length-`L` window multiset is preserved. -/
theorem windows_detour_eq {L : Nat} {sx m sy : List A} {l1 l2 l : Nat}
    (hspell : spellWalk [sx, m, sy] [l1, l2] = spellWalk [sx, sy] [l]) :
    windows L (spellWalk [sx, m, sy] [l1, l2]) = windows L (spellWalk [sx, sy] [l]) := by
  rw [hspell]

/-! ## The `L = 5` witness -/

/-- `sx = 01234`. -/
private def w5sx : List Nat := [0, 1, 2, 3, 4]
/-- `m₁ = 23412` (the intermediate read of the direct one-step detour). -/
private def w5m1 : List Nat := [2, 3, 4, 1, 2]
/-- `m₂ = 12341` (the intermediate read of the second reduction step). -/
private def w5m2 : List Nat := [1, 2, 3, 4, 1]
/-- `sy = 41200`. -/
private def w5sy : List Nat := [4, 1, 2, 0, 0]
/-- The unobserved seam window `34120`. -/
private def w5unobs : List Nat := [3, 4, 1, 2, 0]

/-- The one-step detour `sx → m₁ → sy` (overlaps `3, 3`) spells the same word as
the direct edge `sx → sy` (overlap `1`). -/
theorem witness_single_spell_eq :
    spellWalk [w5sx, w5m1, w5sy] [3, 3] = spellWalk [w5sx, w5sy] [1] := by rfl

/-- The two-step detour `sx → m₂ → m₁ → sy` (overlaps `4, 4, 3`) spells the same
word as the direct edge. -/
theorem witness_two_spell_eq :
    spellWalk [w5sx, w5m2, w5m1, w5sy] [4, 4, 3] = spellWalk [w5sx, w5sy] [1] := by rfl

/-- The full window multiset is the same for the direct edge and the one-step
detour. -/
theorem witness_windows_eq_single :
    windows 5 (spellWalk [w5sx, w5m1, w5sy] [3, 3]) =
      windows 5 (spellWalk [w5sx, w5sy] [1]) := by
  rw [witness_single_spell_eq]

/-- The full window multiset is the same for the direct edge and the two-step
detour. -/
theorem witness_windows_eq_two :
    windows 5 (spellWalk [w5sx, w5m2, w5m1, w5sy] [4, 4, 3]) =
      windows 5 (spellWalk [w5sx, w5sy] [1]) := by
  rw [witness_two_spell_eq]

/-- The full window multiset of the spelled word, exactly: the four observed
vertices of the two-step detour plus the one unobserved seam window. -/
theorem witness_windows_eq :
    windows 5 (spellWalk [w5sx, w5sy] [1]) =
      [w5sx, w5m2, w5m1, w5unobs, w5sy] := by rfl

/-- The physical class counts differ between the direct edge and the one-step
detour, even though the spelled word is identical. -/
theorem witness_vertex_ne_single :
    (vertexMultiset [w5sx, w5sy] : List (List Nat)) ≠
      vertexMultiset [w5sx, w5m1, w5sy] := by decide

/-- The physical class counts differ between the direct edge and the two-step
detour, even though the spelled word is identical. -/
theorem witness_vertex_ne_two :
    (vertexMultiset [w5sx, w5sy] : List (List Nat)) ≠
      vertexMultiset [w5sx, w5m2, w5m1, w5sy] := by decide

/-- The seam window `34120` is a length-`5` window of the spelled word. -/
theorem witness_unobserved_mem_windows :
    w5unobs ∈ windows 5 (spellWalk [w5sx, w5sy] [1]) := by decide

/-- The seam window `34120` is not a vertex of the direct walk. -/
theorem witness_unobserved_not_vertex :
    w5unobs ∉ (vertexMultiset [w5sx, w5sy] : List (List Nat)) := by decide

/-- **Observed/unobserved decomposition for the direct edge.**  The invariant
window multiset splits (as a multiset) as the two direct vertices plus three
unobserved windows. -/
theorem witness_windows_split_direct :
    List.Perm (windows 5 (spellWalk [w5sx, w5sy] [1]))
      ((vertexMultiset [w5sx, w5sy] : List (List Nat)) ++ [w5m2, w5m1, w5unobs]) := by
  decide

/-- **Observed/unobserved decomposition for the two-step detour.**  The same
invariant window multiset splits as the four detour vertices plus one unobserved
window: the observed part grew while the unobserved part shrank. -/
theorem witness_windows_split_two :
    List.Perm (windows 5 (spellWalk [w5sx, w5m2, w5m1, w5sy] [4, 4, 3]))
      ((vertexMultiset [w5sx, w5m2, w5m1, w5sy] : List (List Nat)) ++ [w5unobs]) := by
  decide

/-- **The precise obstruction.**  No function of the invariant window multiset
can transport physical class counts: any such function would have to send the
same window multiset to two different vertex multisets. -/
theorem no_transport_function (F : List (List Nat) → List (List Nat)) :
    F (windows 5 (spellWalk [w5sx, w5sy] [1])) =
        (vertexMultiset [w5sx, w5sy] : List (List Nat)) →
      F (windows 5 (spellWalk [w5sx, w5m1, w5sy] [3, 3])) =
          (vertexMultiset [w5sx, w5m1, w5sy] : List (List Nat)) →
      False := by
  intro h1 h2
  rw [witness_windows_eq_single] at h2
  exact witness_vertex_ne_single (h1.symm.trans h2)

/-! ## Required bridge (OPEN) and its relation to physical class counts -/

/-- **The required transport lemma (OPEN, refuted in general).**  To carry a §6.2
vertex-throughput or ML objective through the reduction one would need the
physical class counts to be determined by the invariant window multiset of the
spelled word.  The witness above shows this is false without extra hypotheses:
the same window multiset admits different vertex decompositions because the
spelled word has unobserved seam windows. -/
def transport_required (vs : List (List A)) (ovs : List Nat) : Prop :=
  ∀ (vs' : List (List A)) (ovs' : List Nat),
    spellWalk vs ovs = spellWalk vs' ovs' → vertexMultiset vs = vertexMultiset vs'

/-- The transport lemma fails already at `L = 5`. -/
theorem transport_required_false :
    ¬ transport_required [w5sx, w5sy] [1] := by
  intro h
  exact witness_vertex_ne_single (h [w5sx, w5m1, w5sy] [3, 3] witness_single_spell_eq)

#print axioms windows_congr
#print axioms windows_detour_eq
#print axioms witness_single_spell_eq
#print axioms witness_two_spell_eq
#print axioms witness_windows_eq
#print axioms witness_vertex_ne_single
#print axioms witness_vertex_ne_two
#print axioms witness_windows_split_direct
#print axioms witness_windows_split_two
#print axioms no_transport_function
#print axioms transport_required_false

end AssemblyP1.Section62VisitTransport
