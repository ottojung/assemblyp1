import AssemblyP1.Section62SpelledFlowMaximality

/-!
# The corrected oriented-strand source model for the MB09 §6.2 bidirected graph (#261)

## The defect this module repairs

The historical project model `AssemblyP1.Section62BidirectedFlow` builds the
bidirected overlap graph from the strand enumeration

```text
strandsOf rc verts = verts ++ verts.map rc
```

and derives the two endpoint incidences with `sgnRep` / `sgnTgt`, which compare
the *strand word* `s` against the *molecule-class representative*:

```text
sgnRep s mx = if s = mx then 1 else -1
sgnTgt s my = if s = my then -1 else 1
```

For a molecule whose reverse complement is itself (`rc w = w`, an
RC-palindrome), the class has only one word.  The enumeration then repeats the
same strand value (`strandsOf rc [w] = [w, w]`), the four strand-pair overlaps
collapse to a single `BdEdge` *value*, and both physical orientations receive the
same departure sign `+1` and the same arrival sign `-1`.  The opposite signs are
simply not representable.  Erasing duplicate list entries cannot repair this,
because the information distinguishing the two orientations has already been
discarded by the time the edge value is formed.

## The repair

We separate the *orientation* from the *nucleotide word*.  An oriented strand is
a pair

```text
OStrand W = W × Bool
```

whose first component is the molecule-class representative and whose second is
the strand orientation (`false` = representative orientation, `true` =
reverse-complement orientation).  The signed incidences are *derived from the
bit*, not from word equality:

```text
depSign s = if s.2 then -1 else 1      -- departure incidence
arrSign s = if s.2 then 1 else -1      -- arrival incidence
```

The corrected graph is obtained by *reusing the historical construction* at the
strand type `OStrand W`: set

```text
oRep  s = (s.1, false)          -- canonical class representative
oRc   s = (s.1, !s.2)           -- reverse-complement orientation flip
oTo   s = toList (oWord s)      -- word of the oriented strand
oWord s = if s.2 then rc s.1 else s.1
```

Then `strandsOf oRc (oVerts verts) = verts.map (·,false) ++ verts.map (·,true)`
enumerates the two orientations of every observed class exactly once — even for
palindromes — and the existing `overlapEdges`, `Feasible62`, `throughput`,
`balance`, `Spelling` and the flow-to-count-vector adapter all apply verbatim.
The key identity is that the historical sign function *becomes* the bit-derived
sign on the tagged type:

```text
sgnRep s (oRep s) = depSign s,      sgnTgt s (oRep s) = arrSign s.
```

This is the sense in which the corrected model reuses rather than redefines the
project feasibility object.

## Scope

* The historical model is labelled **bounded / non-faithful for RC-palindromic
  molecule classes** until a correspondence theorem is supplied.  On
  non-palindromic classes the tagged and historical graphs agree (exhibited
  below on an exact finite instance).
* This module is a *representation repair*.  It does not, by itself, decide the
  throughput-image (incidence/Graver) question, the transitive-reduction
  interaction, or the source-fidelity of the §6.1 product-binomial surrogate;
  those stay OPEN in `docs/issue261-general-bidirected-flow-ml.md`.
* No `sorry` / `admit` / `axiom` / `native_decide`.
-/

namespace AssemblyP1.Section62OrientedStrandFlow

open AssemblyP1.Section62Flow

/-! ## Oriented strands -/

/-- An oriented strand: a molecule-class representative paired with an explicit
strand-orientation bit, kept separate from the nucleotide word.  `false` is the
class-representative orientation, `true` its reverse-complement. -/
abbrev OStrand (W : Type) : Type := W × Bool

/-- The nucleotide word of an oriented strand. -/
def oWord {W : Type} (rcW : W → W) (s : OStrand W) : W :=
  if s.2 then rcW s.1 else s.1

/-- Reverse-complement orientation flip: same molecule class, opposite bit. -/
def oRc {W : Type} (s : OStrand W) : OStrand W := (s.1, !s.2)

/-- The canonical representative oriented strand of a molecule class. -/
def oRep {W : Type} (s : OStrand W) : OStrand W := (s.1, false)

/-- Departure signed incidence, derived from the orientation bit: `+1` for the
representative orientation, `-1` for the reverse-complement orientation. -/
def depSign {W : Type} (s : OStrand W) : ℤ :=
  match s.2 with
  | false => 1
  | true => -1

/-- Arrival signed incidence, derived from the orientation bit: `-1` for the
representative orientation, `+1` for the reverse-complement orientation. -/
def arrSign {W : Type} (s : OStrand W) : ℤ :=
  match s.2 with
  | false => -1
  | true => 1

/-- **The historical sign function is the bit-derived departure sign** on the
tagged strand type. -/
theorem sgnRep_oRep {W : Type} [DecidableEq W] (s : OStrand W) :
    sgnRep s (oRep s) = depSign s := by
  obtain ⟨c, b⟩ := s
  cases b
  · simp [sgnRep, depSign, oRep]
  · have hne : ((c, true) : OStrand W) ≠ (c, false) :=
      fun h => Bool.noConfusion (congrArg Prod.snd h)
    simp [sgnRep, depSign, oRep, hne]

/-- **The historical sign function is the bit-derived arrival sign** on the
tagged strand type. -/
theorem sgnTgt_oRep {W : Type} [DecidableEq W] (s : OStrand W) :
    sgnTgt s (oRep s) = arrSign s := by
  obtain ⟨c, b⟩ := s
  cases b
  · simp [sgnTgt, arrSign, oRep]
  · have hne : ((c, true) : OStrand W) ≠ (c, false) :=
      fun h => Bool.noConfusion (congrArg Prod.snd h)
    simp [sgnTgt, arrSign, oRep, hne]

/-- Both orientations of a molecule class are distinct `OStrand` values, even when
their words coincide. -/
theorem oRep_ne_self_rc {W : Type} (c : W) :
    ((c, false) : OStrand W) ≠ (c, true) := by
  intro h
  exact Bool.noConfusion (congrArg Prod.snd h)

/-- The reverse-complement orientation flip is an involution. -/
theorem oRc_involutive {W : Type} : Function.Involutive (oRc (W := W)) := by
  intro s
  obtain ⟨c, b⟩ := s
  cases b <;> rfl

/-! ## The corrected graph, built by reusing the historical construction -/

/-- The linearization of an oriented strand. -/
def oTo {A W : Type} (toListW : W → List A) (rcW : W → W) (s : OStrand W) : List A :=
  toListW (oWord rcW s)

/-- The observed molecule classes, each tagged with the representative
orientation. -/
def oVerts {W : Type} (verts : List W) : List (OStrand W) :=
  verts.map (fun c => (c, false))

/-- The **corrected** MB09 §6.2 bidirected overlap graph: the historical
`overlapEdges` construction applied to the tagged strand type, with the
bit-derived representative `oRep` and the orientation flip `oRc`. -/
def oEdges {A W : Type} [DecidableEq A] [DecidableEq W] (toListW : W → List A)
    (rcW : W → W) (readLen oMin : Nat) (verts : List W) : List (BdEdge A (OStrand W)) :=
  overlapEdges A (OStrand W) (oTo toListW rcW) oRep oRc readLen oMin (oVerts verts)

/-- The tagged strand enumeration is the two orientations of every observed class,
in order. -/
theorem strandsOf_oVerts {W : Type} (verts : List W) :
    strandsOf (oRc (W := W)) (oVerts verts)
      = verts.map (fun c => ((c, false) : OStrand W))
        ++ verts.map (fun c => ((c, true) : OStrand W)) := by
  simp [strandsOf, oVerts, oRc, List.map_map]

/-- **Signed incidences of the corrected graph are bit-derived.**  Every edge
produced by `bdEdge oRep` has `sgnX = depSign` of its departure strand and
`sgnY = arrSign` of its arrival strand. -/
theorem bdEdge_oRep_sgnX {A W : Type} [DecidableEq W] (sx sy : OStrand W) (len : Nat) :
    (bdEdge (A := A) oRep sx sy len).sgnX = depSign sx := by
  simp only [bdEdge, sgnRep_oRep]

/-- Arrival half of `bdEdge_oRep_sgnX`. -/
theorem bdEdge_oRep_sgnY {A W : Type} [DecidableEq W] (sx sy : OStrand W) (len : Nat) :
    (bdEdge (A := A) oRep sx sy len).sgnY = arrSign sy := by
  simp only [bdEdge, sgnTgt_oRep]

/-- A palindrome's two orientations have the same word. -/
theorem oWord_pal {W : Type} {rcW : W → W} {c : W} (h : rcW c = c) :
    oWord rcW ((c, false) : OStrand W) = oWord rcW ((c, true) : OStrand W) := by
  simp [oWord, h]

/-- The reverse-complement orientation carries the reverse-complement word. -/
theorem oWord_oRc {W : Type} {rcW : W → W} (hrc : Function.Involutive rcW) (s : OStrand W) :
    oWord rcW (oRc s) = rcW (oWord rcW s) := by
  obtain ⟨c, b⟩ := s
  cases b
  · rfl
  · show c = rcW (rcW c)
    exact (hrc c).symm

/-- The historical strand enumeration of a palindromic class repeats the single
strand value, so the four strand-pair overlaps collapse to one `BdEdge` value. -/
theorem strandsOf_pal {W : Type} {rcW : W → W} {c : W} (h : rcW c = c) :
    strandsOf rcW [c] = [c, c] := by
  simp [strandsOf, h]

/-! ## The historical model is non-faithful on palindromes

The two physical orientations of a palindromic class have equal words, so the
historical `bdEdge` — which stores the word and derives its signs from word
equality — cannot distinguish them.  This is the exact statement that the
historical model is bounded/non-faithful on RC-fixed classes. -/

/-- **Historical sign collision.**  For a palindromic class, the representative
strand and its reverse complement receive the *same* departure and arrival signs
under `sgnRep`/`sgnTgt`, because the words coincide. -/
theorem historical_pal_sign_collision {W : Type} [DecidableEq W] {rep rcW : W → W} {c : W}
    (h : rcW c = c) :
    sgnRep c (rep c) = sgnRep (rcW c) (rep c)
      ∧ sgnTgt c (rep c) = sgnTgt (rcW c) (rep c) := by
  rw [h]
  exact ⟨rfl, rfl⟩

/-- **Historical edge collision.**  For a palindromic class, the historical edge
built from the representative departure strand *is* the historical edge built
from its reverse-complement departure strand: the word-level model has only one
edge value to give. -/
theorem historical_pal_edge_collision {A W : Type} [DecidableEq W] {rep rcW : W → W}
    {c : W} (h : rcW c = c) (sy : W) (len : Nat) :
    bdEdge (A := A) rep c sy len = bdEdge (A := A) rep (rcW c) sy len := by
  rw [h]

/-- **Corrected edge distinction.**  In the tagged model the two orientations give
*different* edge values even though their words coincide, so both physical
orientations are representable. -/
theorem tagged_pal_edge_distinct {A W : Type} [DecidableEq W] (sx sy : OStrand W) (len : Nat) :
    bdEdge (A := A) oRep ((sx.1, false) : OStrand W) sy len
      ≠ bdEdge (A := A) oRep ((sx.1, true) : OStrand W) sy len := by
  intro h
  have hx : ((sx.1, false) : OStrand W) = (sx.1, true) := congrArg BdEdge.sx h
  exact Bool.noConfusion (congrArg Prod.snd hx)

/-! ## Concrete witnesses on the two-symbol DNA alphabet

We instantiate the model on `Bool`-words with Watson–Crick complement `not`, so
that the whole repair is `decide`-checkable on exact finite instances. -/

/-- DNA reverse complement on `Bool`-words. -/
def rcB (w : List Bool) : List Bool := w.reverse.map not

/-- A numeric code of a `Bool`-word, used to pick a canonical representative. -/
def codeB (w : List Bool) : Nat :=
  w.foldl (fun a b => a * 2 + (if b then 1 else 0)) 0

/-- Canonical molecule-class representative: the lexicographically smaller (by
`codeB`) of a word and its reverse complement. -/
def repB (w : List Bool) : List Bool :=
  if codeB w ≤ codeB (rcB w) then w else rcB w

/-- The length-`4` RC-palindrome `ATAT`. -/
def pal4 : List Bool := [true, false, true, false]

/-- A length-`3` non-palindromic word `ATT`. -/
def np3 : List Bool := [true, false, false]

theorem map_not_comp_not (w : List Bool) : w.map (not ∘ not) = w := by
  induction w with
  | nil => rfl
  | cons a t ih => cases a <;> simp [ih]

theorem rcB_involutive : Function.Involutive rcB := by
  intro w
  simp only [rcB, List.map_reverse, List.map_map, List.reverse_reverse, map_not_comp_not]

theorem pal4_is_palindrome : rcB pal4 = pal4 := by decide

theorem np3_not_palindrome : rcB np3 ≠ np3 := by decide

theorem repB_pal4 : repB pal4 = pal4 := by decide

theorem repB_np3 : repB np3 = np3 := by decide

theorem repB_rcB_np3 : repB (rcB np3) = np3 := by decide

/-! ### The palindrome: historical collision versus corrected graph -/

/-- The one historical edge value a palindromic self-overlap can take. -/
def histPalEdge : BdEdge Bool (List Bool) := bdEdge repB pal4 pal4 2

/-- The historical graph on the palindromic class repeats that single edge value
four times. -/
theorem historical_pal_graph_quadruple :
    overlapEdges Bool (List Bool) id repB rcB 4 2 [pal4]
      = [histPalEdge, histPalEdge, histPalEdge, histPalEdge] := by decide

/-- Both physical orientations collapse to one sign pair in the historical
graph: `(+1, -1)` four times.  The opposite signs are unrepresentable. -/
theorem historical_pal_sign_pairs :
    (overlapEdges Bool (List Bool) id repB rcB 4 2 [pal4]).map
        (fun e => (e.sgnX, e.sgnY)) = [(1, -1), (1, -1), (1, -1), (1, -1)] := by
  decide

/-- The corrected graph on the palindromic class has four *distinct* edges, one
per pair of physical orientations. -/
theorem corrected_pal_graph_nodup :
    (oEdges (A := Bool) (W := List Bool) id rcB 4 2 [pal4]).Nodup := by decide

/-- The corrected graph's four sign pairs are all four sign combinations, so both
physical orientations are representable. -/
theorem corrected_pal_sign_pairs :
    (oEdges (A := Bool) (W := List Bool) id rcB 4 2 [pal4]).map
        (fun e => (e.sgnX, e.sgnY)) = [(1, -1), (1, 1), (-1, -1), (-1, 1)] := by
  decide

/-- The corrected graph has exactly one edge per orientation pair, all with the
palindrome word. -/
theorem corrected_pal_graph_words :
    (oEdges (A := Bool) (W := List Bool) id rcB 4 2 [pal4]).map
        (fun e => (oWord rcB e.sx, oWord rcB e.sy)) =
      [(pal4, pal4), (pal4, pal4), (pal4, pal4), (pal4, pal4)] := by
  decide

/-- A unit flow on the representative-orientation self-loop of the corrected
graph. -/
def unitTaggedFlow : BdFlow Bool (OStrand (List Bool)) :=
  fun e => if e = bdEdge (A := Bool) oRep ((pal4, false) : OStrand (List Bool))
      ((pal4, false) : OStrand (List Bool)) 2 then 1 else 0

/-- The corrected candidate's count vector on the tagged vertex set: one
occurrence of the palindrome class. -/
def taggedSingletonSpectrum : OStrand (List Bool) → ℕ :=
  fun s => if s = ((pal4, false) : OStrand (List Bool)) then 1 else 0

/-- The historical candidate's count vector on the word vertex set. -/
def histSingletonSpectrum : List Bool → ℕ := fun w => if w = pal4 then 1 else 0

/-- **Corrected throughput.**  The unit flow through the palindrome self-loop
counts exactly once. -/
theorem corrected_pal_throughput_one :
    throughput Bool (OStrand (List Bool)) oRep unitTaggedFlow
      (oEdges (A := Bool) (W := List Bool) id rcB 4 2 [pal4])
      ((pal4, false) : OStrand (List Bool)) = 1 := by decide

/-- The unit self-loop is balanced at the class representative. -/
theorem corrected_pal_balance_zero :
    balance Bool (OStrand (List Bool)) oRep unitTaggedFlow
      (noTerminals (OStrand (List Bool)))
      (oEdges (A := Bool) (W := List Bool) id rcB 4 2 [pal4])
      ((pal4, false) : OStrand (List Bool)) = 0 := by decide

/-- **The corrected model accepts the one-copy palindromic candidate** as a
zero-terminal §6.2 feasible flow with count vector `taggedSingletonSpectrum`. -/
theorem corrected_pal_feasible_one :
    Feasible62 Bool (OStrand (List Bool)) oRep
      (oVerts [pal4]) (oEdges (A := Bool) (W := List Bool) id rcB 4 2 [pal4])
      unitTaggedFlow (noTerminals (OStrand (List Bool))) taggedSingletonSpectrum := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, noTerminals_usage_zero _⟩
  · intro e _; exact Nat.zero_le _
  · intro v hv
    have hv' : v = ((pal4, false) : OStrand (List Bool)) := by simpa [oVerts] using hv
    rw [hv', corrected_pal_throughput_one]
  · intro v hv
    have hv' : v = ((pal4, false) : OStrand (List Bool)) := by simpa [oVerts] using hv
    rw [hv', corrected_pal_balance_zero]
  · intro v hv
    have hv' : v = ((pal4, false) : OStrand (List Bool)) := by simpa [oVerts] using hv
    rw [hv', corrected_pal_throughput_one]
    simp [taggedSingletonSpectrum]

/-- **The historical model rejects the same one-copy palindromic candidate.**
With the single edge-value flow of the historical graph, `throughput` folds the
same value four times, forcing count `4` and contradicting the candidate spectrum
`1`.  This is the concrete feasibility difference produced by the palindrome
aliasing. -/
theorem historical_pal_throughput_four :
    throughput Bool (List Bool) repB
      (fun e => if e = histPalEdge then 1 else 0)
      (overlapEdges Bool (List Bool) id repB rcB 4 2 [pal4]) pal4 = 4 := by decide

/-- The historical model is *not* feasible for the one-copy palindromic candidate
under its natural unit flow. -/
theorem historical_pal_not_feasible_one :
    ¬ Feasible62 Bool (List Bool) repB [pal4]
        (overlapEdges Bool (List Bool) id repB rcB 4 2 [pal4])
        (fun e => if e = histPalEdge then 1 else 0)
        (noTerminals (List Bool)) histSingletonSpectrum := by
  intro h
  have hthrough := h.1.2.2.2 pal4 (by simp)
  rw [historical_pal_throughput_four] at hthrough
  norm_num [histSingletonSpectrum] at hthrough

/-! ### The non-palindrome: historical and corrected graphs agree

For a non-palindromic class the word map `oWord` is a bijection between the two
tagged orientations and the two historical strands, and the signs agree.  We
record the exact finite agreement on `np3`. -/

/-- The historical graph on the non-palindromic class. -/
def histNpGraph : List (BdEdge Bool (List Bool)) :=
  overlapEdges Bool (List Bool) id repB rcB 3 2 [np3]

/-- The corrected graph on the non-palindromic class. -/
def corrNpGraph : List (BdEdge Bool (OStrand (List Bool))) :=
  oEdges (A := Bool) (W := List Bool) id rcB 3 2 [np3]

/-- On a non-palindrome the historical and corrected graphs have the same number
of edges. -/
theorem nonpal_graph_lengths_eq : histNpGraph.length = corrNpGraph.length := by
  decide

/-- The sign pairs of the historical and corrected non-palindromic graphs agree. -/
theorem nonpal_sign_pairs_eq :
    histNpGraph.map (fun e => (e.sgnX, e.sgnY))
      = corrNpGraph.map (fun e => (e.sgnX, e.sgnY)) := by
  decide

/-- The words of the historical edges are the words of the corrected edges, in
order, on the non-palindromic class. -/
theorem nonpal_words_eq :
    histNpGraph.map (fun e => (e.sx, e.sy))
      = corrNpGraph.map (fun e => (oWord rcB e.sx, oWord rcB e.sy)) := by
  decide

/-- On the non-palindromic class the corrected graph is `Nodup`, matching the
historical graph. -/
theorem nonpal_corrected_nodup : corrNpGraph.Nodup := by decide

theorem nonpal_historical_nodup : histNpGraph.Nodup := by decide

end AssemblyP1.Section62OrientedStrandFlow
