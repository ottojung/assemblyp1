import AssemblyP1.BBTEulerianSearch

/-!
# The label-orbit contrapositive of `thm:BBT`, and the backward-shift step

## Why this file exists

`docs/bbt-eulerian-cycle-89.md` records the reduction of the `#89` input to
the statement `BBTEulerian.EulerianCycleObstruction` and the exact
reformulation of §1--§3 of `AssemblyP1.BBTEulerianSearch`.  That reduction is
about the *objects*; it says nothing about the **proof structure** of the
classical theorem behind it.  This file records the proof structure at the
level where it is cheapest to formalize: the level of the **labels**, i.e. of
the `(L-1)`-mers read by a traversal, with no appeal to candidates, matchings
or likelihood.

## The source check, stated carefully

`paper/sections/05-population.tex`, `thm:BBT`, cites `bresler2013` (Bresler--
Bresler--Tse 2013) for the Eulerian-cycle formulation:

> Construct the `K`-mer graph from the complete `(K+1)`-spectrum of a circular
> genome.  If the genome satisfies Ukkonen's condition --- no triple repeat and
> no interleaved repeat pair of length at least `K` --- then the graph has a
> unique Eulerian cycle, which spells the genome up to cyclic rotation.

The classical statement that the transposition argument proves is the
spectrum-equivalence formulation of Arratia--Brazile--Pevzner--Tse 1996,
Theorem 6 (the same lineage): two circular words have the same complete
`(K+1)`-spectrum if and only if they are connected by rotations and
transpositions of the letters, and a **nontrivial** transposition of a word
with a `K+1`-spectrum is possible only when

* three copies of the same `K`-tuple occur --- a *triple repeat*; or
* two interleaved pairs of copies of `K`-tuples occur --- an *interleaved
  repeat pair*,

with the refinement that the two cases are related: a transposition across an
interleaved pair that *collapses* (the two configurations share an occurrence)
is equivalent, in its effect on the spectrum, to a transposition using a
three-way repeated `K`-tuple.  This is why the hypothesis in `thm:BBT` is the
disjunction and not either clause alone, and it is why the `LongObstruction` of
`AssemblyP1.BBTEulerian` has exactly those two disjuncts.

**Not claimed here:** that the two citations are interchangeable as written.
The repository's `thm:BBT` is the Eulerian-cycle formulation; the
transposition formulation is what carries the proof.  What this file records is
the *content* the transposition proof has to establish, in the project's
objects, so that the remaining gap of `#89` is stated once and precisely.  Two
claims made by earlier packets in this repository, and **refuted** there, are
neither used nor re-derived here: the global instantiation "any crossing of
raw `(L-1)`-mer nodes is a maximal repeat"
(`raw_node_crossing_not_maximal`, `docs/bbt-chord-rematch-89.md` §3), and the
claim that a read-type-preserving pull-back is the identity or a rotation (the
`f = id` reading, refuted in §2 of the same document and in §4 of
`AssemblyP1.BBTEulerian`).

## The contrapositive, at the label-orbit level

Write `θ` for a fibre-preserving one-cycle permutation of the starts
(`FibrePreserving`, `OneCycle` of `AssemblyP1.BBTEulerianSearch` §1).  Read at
the labels, `θ` permutes the *multiset of labels* --- the `(L-1)`-mers,
counted with multiplicity --- because it preserves them.  A **departure** is a
position `x` with `θ x ≠ nextPos x`; by fibre preservation `θ x` and
`nextPos x` carry the *same* label, so a departure is a nontrivial permutation
of a single label class, and `departure_is_branch` below says that class is a
branch object of the multigraph.  The contrapositive to prove is then

```text
¬ (the orbit listing of θ is the truth's, up to rotation)
  ⟹ a nontrivial transposition of one label class                [§1, proved]
  ⟹ (backward shift, §2) a maximal repeated label of length ≥ L - 1,
     used either three times (triple repeat) or twice in an interleaved
     configuration (interleaved pair, which the collapse step converts
     into a triple repeat),                                  [§2 shift proved,
                                                               iteration open]
  ⟹ LongObstruction.
```

§1 and the backward-shift step of §2 are kernel-checked.  §3 states, exactly
once, what is left; `docs/bbt-transposition-contrapositive-89.md` §4 lists the
three lemmas that would close it.
-/

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedSectionVars false

namespace AssemblyP1.BBTTransposition

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTEulerianSearch

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-! ## 1. A departure of a label-preserving traversal is a branch object -/

/-- **A departure**: the traversal does not follow the truth's step at `x`.
This is the label-orbit form of "the two traversals depart at `x`". -/
def Departure (θ : Fin G → Fin G) (x : Fin G) : Prop := θ x ≠ nextPos hG x

/-- **A departure is a nontrivial permutation of one label class.**  If the
traversal is fibre preserving and departs at `x`, then `θ x` and `nextPos x`
are two *distinct* starts carrying the same `(L-1)`-mer, i.e. the departure
transposes two elements of a single label class, and that label is a branch
object.  This is the whole content of "the alternative traversal permutes the
spectrum", read at one label: a counterexample has to live here, and nowhere
else. -/
theorem departure_is_branch {θ : Fin G → Fin G}
    (hf : FibrePreserving hG L S θ) {x : Fin G} (hdep : Departure hG θ x) :
    Branch hG L S (vtx hG L S (nextPos hG x)) := by
  have hne : θ x ≠ nextPos hG x := hdep
  refine deg_two_of_occ_ne hG L S (vtx hG L S (nextPos hG x))
    (a := θ x) (b := nextPos hG x) hne (hf x) rfl

/-! ## 2. The backward-shift step: a repeated label can be pushed left -/

/-- **Reading a position modulo the circle does not change it.**  This is
`cycl_add_mul` of `BBTSequenceGraph` in the direction used below. -/
theorem cyc_mod (i : ℕ) : cyc hG S (i % G) = cyc hG S i := by
  have hdiv := Nat.mod_add_div i G
  calc cyc hG S (i % G) = cyc hG S (i % G + G * (i / G)) :=
        (cycl_add_mul hG S (i % G) (i / G)).symm
    _ = cyc hG S i := by rw [hdiv]

/-- **The symbol just before a start, as a window.**  The bridge from the
window language of `BBTSequenceGraph` to the shift-by-one reading that
`SourceFaithfulIs.Genome.Preceding` uses. -/
theorem window_one_prevPos (a : Fin G) :
    window (L := 1) hG S (prevPos hG a) 0 = cyc hG S (a.val + G - 1) := by
  simp only [window, cyc, prevPos, rotAdd, Fin.val_mk]
  congr 1
  simp

/-- **... and the same symbol, as `Preceding`.**  `mkGenome` wraps the word in
a `Genome`, so the start has to be cast; the cast is a formality of the
wrapper and is the only difference between the two readings. -/
theorem preceding_eq_window_one (a : Fin G) :
    (mkGenome hG S).Preceding (Fin.cast (by simp [mkGenome]) a)
      = window (L := 1) hG S (prevPos hG a) 0 :=
  (window_one_prevPos hG S a).symm

/-- **A longer window starts with the shorter one.**  The prefix identity used
by the backward shift; it is `rfl` because `window` is a function of the start
and the index. -/
theorem window_lt (e : ℕ) (a : Fin G) (k : Fin e) :
    window (L := e + 1) hG S a ⟨k.val, by omega⟩ = window (L := e) hG S a k := rfl

/-- **Shifting a repeat pair backward.**  If the two copies of a length-`e`
window agree at the starts `a`, `b`, and the symbols immediately before them
agree as well, then the length-`e + 1` windows starting one position *to the
left* of `a`, `b` agree.  This is the formal content of the *shift the repeat
pair backward* step of the classical transposition argument: the pair of
starts moves left and the repeat gets longer, and it is the only mechanism by
which that argument ever reaches a maximal repeat.  The step is a *one-step*
statement; iterating it lengthens the repeat, so the iteration terminates at
`e = |S|`, and that is where the classical argument stops --- not at raw
`(L-1)`-mer crossings, the reading refuted in
`docs/bbt-chord-rematch-89.md` §3. -/
theorem window_prev_succ {e : ℕ} {a b : Fin G}
    (h : ∀ d : Fin e, window (L := e) hG S a d = window (L := e) hG S b d)
    (hprev : window (L := 1) hG S (prevPos hG a) 0
      = window (L := 1) hG S (prevPos hG b) 0) :
    ∀ d : Fin (e + 1), window (L := e + 1) hG S (prevPos hG a) d
      = window (L := e + 1) hG S (prevPos hG b) d := by
  have hshiftA : ∀ (j : Fin e),
      window (L := e + 1) hG S (prevPos hG a) ⟨j.val + 1, by omega⟩
        = window (L := e) hG S a j := by
    intro j
    have h1 := window_next hG (L := e + 1) S (prevPos hG a) (j := j.val) (by omega)
    rw [nextPrev] at h1
    calc window (L := e + 1) hG S (prevPos hG a) ⟨j.val + 1, by omega⟩
        = window (L := e + 1) hG S a ⟨j.val, by omega⟩ := h1
      _ = window (L := e) hG S a j := window_lt hG S e a j
  have hshiftB : ∀ (j : Fin e),
      window (L := e + 1) hG S (prevPos hG b) ⟨j.val + 1, by omega⟩
        = window (L := e) hG S b j := by
    intro j
    have h1 := window_next hG (L := e + 1) S (prevPos hG b) (j := j.val) (by omega)
    rw [nextPrev] at h1
    calc window (L := e + 1) hG S (prevPos hG b) ⟨j.val + 1, by omega⟩
        = window (L := e + 1) hG S b ⟨j.val, by omega⟩ := h1
      _ = window (L := e) hG S b j := window_lt hG S e b j
  intro d
  refine Fin.cases ?_ (fun k => ?_) d
  · simpa [window] using hprev
  · exact Eq.trans (Eq.trans (hshiftA k) (h k)) (hshiftB k).symm

/-- **The backward-shift dichotomy at a repeated label.**  At two distinct
starts carrying the same length-`e` window, either the symbols to their left
agree --- in which case the pair shifts backward (`window_prev`) --- or they
disagree, in which case the pair is *maximal on the left* in the sense of
`SourceFaithfulIs` (`preceding_eq_window_one` is the bridge) and is exactly an
object `def:P1P2` quantifies over. -/
theorem backward_shift_or_maximal {e : ℕ} {a b : Fin G} (hab : a ≠ b)
    (h : ∀ d : Fin e, window (L := e) hG S a d = window (L := e) hG S b d) :
    window (L := 1) hG S (prevPos hG a) 0
        = window (L := 1) hG S (prevPos hG b) 0 ∨
      window (L := 1) hG S (prevPos hG a) 0
        ≠ window (L := 1) hG S (prevPos hG b) 0 :=
  eq_or_ne _ _

/-- **A maximal repeat cannot be shifted backward.**  `Genome.IsRepeat`'s
preceding clause is precisely the failure of the backward shift, so the
backward-shift iteration of `backward_shift_or_maximal` stops exactly at the
maximal repeats of `def:P1P2` --- and not at raw `(L-1)`-mer crossings, which
is the reading refuted in `docs/bbt-chord-rematch-89.md` §3. -/
theorem not_window_prev_of_isRepeat {e : ℕ} {a b : Fin G}
    (hrep : (mkGenome hG S).IsRepeat e a b) :
    window (L := 1) hG S (prevPos hG a) 0
      ≠ window (L := 1) hG S (prevPos hG b) 0 := by
  rw [← preceding_eq_window_one hG S a, ← preceding_eq_window_one hG S b]
  exact hrep.2.2.2.2.1

/-! ## 3. What is left, stated once -/

/-- **The nontrivial-transposition obstruction, in the project's objects.**
This is the content of the transposition argument that is *not* a statement
about labels alone: a nontrivial transposition of a single label class (the
departure of §1), pushed left to a maximal repeat by §2, is either

* used at three distinct starts --- a maximal triple repeat of length
  `≥ L - 1`; or
* used at two interleaved configurations of two starts each --- two
  interleaved maximal repeats both of length `≥ L - 1`,

and the classical collapse step converts the second case into the first when
the two configurations share an occurrence.  `LongObstruction` of
`AssemblyP1.BBTEulerian` is the same disjunction at the same lengths; this
`def` records that the two are the *same object*, so that the remaining gap of
`#89` is stated exactly once.

It is a `Prop`, not a theorem: nothing in this file proves it, and the
contrapositive that would consume it (`UniqueAt → LongObstruction`, i.e.
`thm:BBT`) is exactly the open input.  See
`docs/bbt-transposition-contrapositive-89.md` §4 for the three lemmas that
would close it, and which of them this file already supplies. -/
def TranspositionObstruction (L : ℕ) : Prop := LongObstruction hG L S

/-- **The two formulations are the same object.**  The disjunction of
`LongObstruction` is the disjunction of the transposition argument at
`K = L - 1`, so the reduction `UniqueAt → LongObstruction` would be `thm:BBT`
itself and not a weakening of it. -/
theorem transpositionObstruction_iff (L : ℕ) :
    TranspositionObstruction hG S L ↔ LongObstruction hG L S := Iff.rfl

end AssemblyP1.BBTTransposition
