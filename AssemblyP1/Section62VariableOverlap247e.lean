import AssemblyP1.Section62BidirectedFlow

/-!
# Front 247e: the `AAABBABB → AAAABABB` variable-overlap walk at `oMin = 1`

This is an **additive**, self-contained audit module.  It imports only
`AssemblyP1.Section62BidirectedFlow` and instantiates the literal MB09 §6.2
objects on the issue-#247 witness alphabet `{A, B}` (`A ↔ B` reverse
complement).  It changes no existing definition and preserves every original
theorem.

## The question

Board #247 message 27 proposes the *oriented* witness `S = AAABBABB`,
`D = AAAABABB`, `L = 3`, observed strand windows
`{AAA, AAB, ABB, BBA, BAB, BAA}`, and the variable-overlap cyclic strand walk

```
AAA → AAA → AAB → BAB → ABB → BBA → BAA → AAA
```

with successive overlaps `[2, 2, 1, 2, 2, 2, 2]`.  It asks whether this is a
genuine MB09 §6.2 bidirected flow at `oMin = 1`, even though the *oriented*
window `ABA` is unobserved.

## Verdict (kernel-checked below)

**Refuted as a §6.2 flow.**  In the source's bidirected *molecule* graph
(MB09 §3.1, §4.1: a read is an unordered reverse-complement strand pair,
represented once) the walk's molecule throughput is

`{AAA: 2, AAB: 2, ABA: 1, BAA: 2}`,

while `D`'s molecule spectrum is

`{AAA: 2, AAB: 2, ABA: 2, BAA: 2}`.

The counts differ at `ABA` (`1 ≠ 2`), so the walk violates MB09 Observation 7
("the number of times `W` visits `r` equals the number of times `r` appears as
a submolecule of the molecule spelled by `W`").  Equivalently, its overlap-`1`
edge `AAB → BAB` is removed by the source's transitive edge reduction: the two
strictly longer overlaps `AAB → ABA` and `ABA → BAB` spell the same string
`AABAB`, and `ABA` **is** an observed molecule here — it is the reverse
complement of the sampled read `BAB`.  (The repository's `isReducibleLongerB`
already removes it; the literal `isReducibleB` is arithmetically vacuous.)

**But `D` is a genuine §6.2 candidate anyway.**  Its *molecule* window walk
uses only full overlaps `L − 1 = 2`,

```
AAA → AAA → AAB → ABA → BAB → ABB → BBA → BAA
```

and visits `ABA` twice; its molecule throughput equals `D`'s molecule spectrum
exactly.  The board's "unobserved `ABA`" is a *strand-orientation* artifact:
as a molecule, `ABA` is the reverse complement of the observed read `BAB`, so
molecule support equality holds.

## Scope

The statements below are finite computations (`decide`).  They are statements
about the *molecule* reading of §6.2, which is the reading the source text
uses.  The oriented reading, in which `ABA` is genuinely absent, is a
different (stronger) model and is not asserted here.
-/

namespace AssemblyP1.Section62VariableOverlap247e

set_option maxHeartbeats 1000000

/-! ## The two-symbol alphabet and molecule classes -/

/-- Two-symbol alphabet with reverse-complement involution `A ↔ B`. -/
inductive Base where
  | A
  | B
  deriving DecidableEq, Inhabited, Repr

instance : Fintype Base where
  elems := {Base.A, Base.B}
  complete := by intro x; cases x <;> simp

/-- Reverse complement of a symbol. -/
def comp : Base → Base
  | .A => .B
  | .B => .A

/-- A strand is a word over `Base`. -/
abbrev Strand := List Base

/-- Bit encoding (`A ↦ 0`, `B ↦ 1`). -/
def bitA : Base → Nat
  | .A => 0
  | .B => 1

/-- Reverse complement of a strand (MB09 §3.1). -/
def rc (w : Strand) : Strand := w.reverse.map comp

/-- Binary code of a strand, most significant symbol first. -/
def code (w : Strand) : Nat := w.foldl (fun a b => a * 2 + bitA b) 0

/-- Molecule-class representative: the minimum-code strand of `{w, rc w}`.
MB09 §4.1 represents each `k`-molecule only once. -/
def rep (w : Strand) : Strand := if code w ≤ code (rc w) then w else rc w

/-- The length-`3` strand `abc`. -/
def m3 (a b c : Base) : Strand := [a, b, c]

/-! ## The literal §6.2 graph on the observed read molecules -/

/-- Observed read *molecules*, one representative per class:
`{AAA}`, `{AAB, ABB}`, `{BBA, BAA}`, `{BAB, ABA}`. -/
def readVerts : List Strand :=
  [m3 .A .A .A, m3 .A .A .B, m3 .B .A .A, m3 .A .B .A]

/-- Read length `L = 3`. -/
def readLen : Nat := 3

/-- Overlap threshold `o_min = 1`. -/
def oMin : Nat := 1

/-- The literal §6.2 bidirected overlap graph on the observed molecules. -/
def graph : List (AssemblyP1.Section62Flow.BdEdge Base Strand) :=
  AssemblyP1.Section62Flow.overlapEdges Base Strand id rep rc readLen oMin readVerts

/-- The `AAB → BAB` overlap-`1` edge used by the proposed walk. -/
def edgeAAB_BAB : AssemblyP1.Section62Flow.BdEdge Base Strand :=
  AssemblyP1.Section62Flow.bdEdge rep (m3 .A .A .B) (m3 .B .A .B) 1

/-- The literal "spelled by two shorter overlaps" reduction is vacuous on this
edge, exactly as the arithmetic audit predicts. -/
theorem edgeAAB_BAB_not_reducibleB :
    AssemblyP1.Section62Flow.isReducibleB Base Strand id rc readLen readVerts
      edgeAAB_BAB = false := by
  decide

/-- The repository's longer-overlap reduction **removes** the overlap-`1` edge. -/
theorem edgeAAB_BAB_reducibleLonger :
    AssemblyP1.Section62Flow.isReducibleLongerB Base Strand id rc readLen readVerts
      edgeAAB_BAB = true := by
  decide

/-- The reduction witness: the intermediate read `ABA` (a strand of the observed
molecule `{BAB, ABA}`) has both overlaps strictly longer than `1`.  This is the
kernel-checked form of "`AAB → ABA → BAB` spells the same `AABAB`". -/
theorem edgeAAB_BAB_longer_witness :
    AssemblyP1.Section62Flow.maxOverlap Base Strand id readLen (m3 .A .A .B) (m3 .A .B .A) = 2
    ∧ AssemblyP1.Section62Flow.maxOverlap Base Strand id readLen (m3 .A .B .A) (m3 .B .A .B) = 2
    ∧ (m3 .A .A .B ++ (m3 .B .A .B).drop 1) = (m3 .A .A .B ++ (m3 .A .B .A).drop 2 ++ (m3 .B .A .B).drop 2) := by
  decide

/-! ## The candidate and its molecule spectra -/

/-- The competing circular genome `D = AAAABABB`, length `8`. -/
def D8 : Fin 8 → Base := ![.A, .A, .A, .A, .B, .A, .B, .B]

/-- The true circular genome `S = AAABBABB`, length `8`. -/
def S8 : Fin 8 → Base := ![.A, .A, .A, .B, .B, .A, .B, .B]

/-- Circular symbol access. -/
def cyc8 (g : Fin 8 → Base) (i : Nat) : Base := g ⟨i % 8, Nat.mod_lt _ (by norm_num)⟩

/-- Length-`3` circular window at start `r`. -/
def win8 (g : Fin 8 → Base) (r : Nat) : Strand :=
  [cyc8 g r, cyc8 g (r + 1), cyc8 g (r + 2)]

/-- The molecule spectrum of a length-`8` genome at a molecule `v`. -/
def spec8 (g : Fin 8 → Base) (v : Strand) : Nat :=
  (Finset.univ.filter (fun r : Fin 8 => rep (win8 g r.val) = v)).card

/-- The molecule visits of a cyclic strand walk (as a list of strands). -/
def visitsOf (strands : List Strand) (v : Strand) : Nat :=
  (strands.filter (fun s => rep s = v)).length

/-! ## The proposed variable-overlap walk -/

/-- The proposed strand walk. -/
def boardStrands : List Strand :=
  [m3 .A .A .A, m3 .A .A .A, m3 .A .A .B, m3 .B .A .B,
   m3 .A .B .B, m3 .B .B .A, m3 .B .A .A]

/-- The proposed overlaps. -/
def boardOverlaps : List Nat := [2, 2, 1, 2, 2, 2, 2]

/-- The placement offsets of the walk in `D` (`D`'s windows at these starts are
exactly the walk's strands). -/
def boardOffsets : List Nat := [0, 1, 2, 4, 5, 6, 7]

/-- The walk's reads are exactly `D`'s length-`3` windows at the stated offsets;
together with the offset/overlap relation below this is "the walk spells `D`". -/
theorem board_walk_spells_D :
    boardOffsets.map (win8 D8) = boardStrands := by
  decide

/-- The offset increments reproduce the claimed overlaps
(`readLen − overlap = next offset − current offset`). -/
theorem board_offsets_overlaps :
    boardOverlaps = [readLen - (boardOffsets[1]! - boardOffsets[0]!),
                     readLen - (boardOffsets[2]! - boardOffsets[1]!),
                     readLen - (boardOffsets[3]! - boardOffsets[2]!),
                     readLen - (boardOffsets[4]! - boardOffsets[3]!),
                     readLen - (boardOffsets[5]! - boardOffsets[4]!),
                     readLen - (boardOffsets[6]! - boardOffsets[5]!),
                     readLen - (8 - boardOffsets[6]!)] := by
  decide

/-! ## The refutation: Observation 7 fails for the proposed walk -/

/-- `D`'s molecule spectrum counts the `ABA` molecule twice. -/
theorem D_ABA_spec : spec8 D8 (m3 .A .B .A) = 2 := by
  decide

/-- The proposed walk visits the `ABA` molecule only once. -/
theorem board_ABA_visits : visitsOf boardStrands (m3 .A .B .A) = 1 := by
  decide

/-- Hence the walk's molecule throughput differs from `D`'s molecule spectrum:
it is **not** a genuine §6.2 flow for `D`. -/
theorem board_walk_not_spectrum :
    visitsOf boardStrands (m3 .A .B .A) ≠ spec8 D8 (m3 .A .B .A) := by
  decide

/-- Full failure statement: the walk's visit count vector is not `D`'s spectrum. -/
theorem board_walk_not_spectrum_all :
    ¬ (∀ v ∈ readVerts, visitsOf boardStrands v = spec8 D8 v) := by
  decide

/-! ## The positive result: `D` is a genuine §6.2 candidate via full overlaps -/

/-- `D`'s full-overlap (`L − 1`) window walk. -/
def DfullStrands : List Strand := (List.range 8).map (win8 D8)

/-- Every step of `D`'s full-overlap walk is a graph edge of length `L − 1`. -/
theorem D_full_walk_steps_in_graph :
    ∀ i : Fin 8,
      AssemblyP1.Section62Flow.bdEdge rep (win8 D8 i.val) (win8 D8 (i.val + 1)) (readLen - 1)
        ∈ graph := by
  decide

/-- `D`'s full-overlap walk realizes `D`'s molecule spectrum exactly
(Observation 7 holds). -/
theorem D_full_walk_realizes_spectrum :
    ∀ v ∈ readVerts, visitsOf DfullStrands v = spec8 D8 v := by
  decide

/-- `ABA` is in `D`'s molecule support. -/
theorem ABA_in_D_support : 0 < spec8 D8 (m3 .A .B .A) := by
  decide

/-- `ABA` is an observed read molecule: it is the reverse complement of `BAB`. -/
theorem ABA_is_observed : (m3 .A .B .A) ∈ readVerts := by
  decide

/-- `ABA` is the reverse complement of the sampled strand `BAB`, which is why it
is observed as a molecule even though the oriented window `ABA` was not sampled. -/
theorem ABA_eq_rc_BAB : m3 .A .B .A = rc (m3 .B .A .B) := by
  decide


/-! ## Direct source flow endpoints for full-overlap walks -/

/-- The candidate's full-overlap spelling viewed as a cyclic read circuit. -/
def fullSpellD : AssemblyP1.Section62Flow.Spelling Base Strand 8 :=
  ⟨fun i => win8 D8 i.val, by decide⟩

/-- The truth's full-overlap spelling viewed as a cyclic read circuit. -/
def fullSpellS : AssemblyP1.Section62Flow.Spelling Base Strand 8 :=
  ⟨fun i => win8 S8 i.val, by decide⟩

/-- The (L-1=2) overlap threshold at which all full-window steps are
retained under either source spelling-preserving reduction. -/
def fullOverlapMin : Nat := 2

/-- Unlike mere read support / visit-count checks, this directly certifies
the *whole* source-model conjunction for the candidate, including reduction,
incidence signs, flow conservation, vertex lower bounds and zero terminals. -/
theorem D_full_spelled_feasible62 :
    AssemblyP1.Section62Flow.SpelledFeasible62 Base Strand id rep rc
      readLen fullOverlapMin readVerts fullSpellD
      (fullSpellD.flow rep readLen)
      (AssemblyP1.Section62Flow.noTerminals Strand) (spec8 D8) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> decide
  · intro i
    fin_cases i <;> decide
  · intro i
    fin_cases i <;> decide
  · intro i
    unfold AssemblyP1.Section62Flow.OppositeAtInterior
    fin_cases i <;> decide
  · refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro e he
      exact Nat.zero_le _
    · intro v hv
      simp only [readVerts, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> decide
    · intro v hv
      simp only [readVerts, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> decide
    · intro v hv
      simp only [readVerts, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> decide
    · intro v
      exact ⟨rfl, rfl⟩

/-- The same direct whole-flow proof for the circular truth. -/
theorem S_full_spelled_feasible62 :
    AssemblyP1.Section62Flow.SpelledFeasible62 Base Strand id rep rc
      readLen fullOverlapMin readVerts fullSpellS
      (fullSpellS.flow rep readLen)
      (AssemblyP1.Section62Flow.noTerminals Strand) (spec8 S8) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> decide
  · intro i
    fin_cases i <;> decide
  · intro i
    fin_cases i <;> decide
  · intro i
    unfold AssemblyP1.Section62Flow.OppositeAtInterior
    fin_cases i <;> decide
  · refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro e he
      exact Nat.zero_le _
    · intro v hv
      simp only [readVerts, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> decide
    · intro v hv
      simp only [readVerts, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> decide
    · intro v hv
      simp only [readVerts, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> decide
    · intro v
      exact ⟨rfl, rfl⟩

#print axioms D_full_spelled_feasible62
#print axioms S_full_spelled_feasible62

/-! ## Kernel and axiom audit -/

#print axioms edgeAAB_BAB_not_reducibleB
#print axioms edgeAAB_BAB_reducibleLonger
#print axioms edgeAAB_BAB_longer_witness
#print axioms board_walk_spells_D
#print axioms board_offsets_overlaps
#print axioms D_ABA_spec
#print axioms board_ABA_visits
#print axioms board_walk_not_spectrum
#print axioms board_walk_not_spectrum_all
#print axioms D_full_walk_steps_in_graph
#print axioms D_full_walk_realizes_spectrum
#print axioms ABA_in_D_support
#print axioms ABA_is_observed
#print axioms ABA_eq_rc_BAB

end AssemblyP1.Section62VariableOverlap247e
