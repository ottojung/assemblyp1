# The label-orbit contrapositive of `thm:BBT`, and what is still missing

This note records the *proof structure* behind `#89` at the level of labels
(the `(L-1)`-mers read by a traversal), together with the exact part of it that
is now kernel-checked in `AssemblyP1/BBTTransposition.lean`.

It does **not** claim a proof of `thm:BBT`. It claims: the contrapositive has a
short chain, each link of the chain is a specific lemma, one link is proved, and
the remaining links are named and not smuggled.

## 1. The source check, stated carefully

`paper/sections/05-population.tex`, `thm:BBT`, cites `bresler2013` and states
the Eulerian-cycle formulation:

> Build the `K`-mer graph from the complete `(K+1)`-spectrum of a circular
> genome. If the genome satisfies Ukkonen's condition — no triple repeat and no
> interleaved repeat pair of length at least `K` — then the graph has a unique
> Eulerian cycle, which spells the genome up to cyclic rotation.

The statement that actually carries the proof is the spectrum-equivalence
formulation of Arratia–Brazile–Pevzner–Tse 1996, Theorem 6, in the same
lineage: two circular words have the same complete `(K+1)`-spectrum only if they
are connected by rotations and **transpositions** of letters, and a nontrivial
transposition is possible only when

* three copies of the same `K`-tuple occur (a *triple repeat*), or
* two interleaved pairs of copies of `K`-tuples occur (an *interleaved repeat
  pair*),

with the collapse refinement: a transposition across an interleaved pair whose
two configurations share an occurrence is, in its effect on the spectrum,
equivalent to a transposition on a three-way repeated `K`-tuple.

This is why the repository's hypothesis is the *disjunction*
(`def:P1P2`), and why `AssemblyP1.BBTEulerian.LongObstruction` has exactly those
two disjuncts at the same lengths.

**Not claimed.** That the two citations are interchangeable as written. The
repository states the Eulerian-cycle form; the transposition form is the proof.
What follows is the *content* the transposition proof must establish, in this
repository's objects, so that the remaining gap is stated once.

Two earlier claims in this repository are **refuted** and are neither used nor
re-derived here:

* `raw_node_crossing_not_maximal` (`docs/bbt-chord-rematch-89.md` §3): a crossing
  of raw `(L-1)`-mer nodes need not be a maximal repeat. The backward shift
  below is precisely the repair, and it is what makes the *maximal* repeat — not
  a raw crossing — the stopping point.
* the `f = id` reading of a read-type-preserving pull-back (§2 of the same
  document, §4 of `AssemblyP1/BBTEulerian.lean`).

## 2. The contrapositive, at the label-orbit level

`AssemblyP1.BBTEulerianSearch` §1 gives the exact reformulation: it suffices to
consider permutations `θ` that preserve the label fibres and are a single
cycle, and the conclusion to negate is that `θ`'s orbit listing is the truth's
listing up to rotation (`OrbitVertexEq`).

Read such a `θ` at the labels. Because `θ` preserves the fibres, it permutes
the multiset of `(L-1)`-mers; the *whole* content of a counterexample is the
set of positions where it does not follow the truth's step. Write

```text
Departure θ x  ≔  θ x ≠ nextPos x
```

A **departure** is a nontrivial permutation of a single label class, and its
label is a branch object. From there the chain is:

```text
¬ OrbitVertexEq
  ⟹ a nontrivial transposition of one label class            [proved]
  ⟹ backward shift: a maximal repeated label, length ≥ L-1   [step proved, iteration open]
  ⟹ used three times, or twice interleaved                   [open]
  ⟹ collapse turns the interleaved case into a triple repeat  [open]
  ⟹ LongObstruction.
```

## 3. What is kernel-checked

In `AssemblyP1/BBTTransposition.lean`:

| statement | content |
| --- | --- |
| `Departure` | the label-orbit form of "the two traversals differ at `x`" |
| `departure_is_branch` | a departure permutes one label class nontrivially, and that label is a branch object of the multigraph |
| `cyc_mod` | reading a position modulo the circle does not change the symbol (`cycl_add_mul` in the direction used) |
| `window_lt` | a longer window starts with the shorter one (the prefix identity of the shift) |
| `window_prev_succ` | **the backward-shift step**: equal length-`e` windows at `a`, `b` together with equal preceding symbols give equal length-`e+1` windows at `prevPos a`, `prevPos b` |
| `window_one_prevPos` | the symbol before a start, in the window language |
| `preceding_eq_window_one` | the same symbol as `SourceFaithfulIs.Genome.Preceding`, the bridge between the window language of `BBTSequenceGraph` and the shift-by-one reading of `SourceFaithfulIs` (the `Fin.cast` is a formality of `mkGenome`) |
| `backward_shift_or_maximal` | at two distinct starts with equal length-`e` windows, either the preceding symbols agree (shift) or they disagree (maximal on the left) |
| `not_window_prev_of_isRepeat` | a maximal repeat cannot be shifted backward; this reads `Genome.IsRepeat`'s preceding clause |
| `TranspositionObstruction`, `transpositionObstruction_iff` | the gap, stated once, as the same `Prop` as `BBTEulerian.LongObstruction` |

`lake build` is green; the module has no `sorry` and no `admit`.

The shift is a *one-step* statement and the classical step is the iteration.
Note that the iteration is well-founded for a reason worth recording: each step
moves the starts left by one **and** lengthens the repeat, so it cannot run past
`e = |S|`. It is a termination obligation, not a finiteness-of-search
assumption.

## 4. What is left, as three lemmas

1. **Iteration/termination.** From a departure and fibre preservation, produce
   the sequence of backward shifts and show it reaches a pair of distinct starts
   with equal windows and *inequal* preceding symbols — i.e. an `IsRepeat` at
   length `≥ L - 1`. This needs the classical detail that the shift preserves
   the transposition structure (a departure at the label level stays a
   departure along the shift), which is the content of the multigraph
   traversal lemmas of `BBTCondense`.
2. **The dichotomy.** A repeated label used by the shifted transposition is used
   either at three distinct starts (an `IsTripleRepeat` of length `≥ L - 1`) or
   at two configurations of two starts each that are `Interleaved`. This is
   where the two-sided maximality of `Genome.IsRepeat` is actually used, and
   where the `Following` clause enters.
3. **The collapse.** A shared-occurrence interleaved-pair transposition yields
   a three-way repeated label, converting the second disjunct of
   `LongObstruction` into the first.

Lemmas 2 and 3 are the ones that the classical argument performs combinatorially
on the `(K+1)`-spectrum; nothing in this repository yet models the shared
occurrence, and `docs/bbt-chord-rematch-89.md` §3 is a warning that the
obvious chord reading of it is false.
