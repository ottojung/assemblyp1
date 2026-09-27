# #89: a complete proof strategy for `UniqueEulerianCycle`

_Status: the mathematical core is settled (proved here, and re-verified by
exhaustive search over small instances); the Lean formalization of the
remaining steps is in progress in `AssemblyP1/BBTUniqueEulerian.lean`._

## 1. The statement to be proved

`AssemblyP1.BBTEulerian.UniqueEulerianCycle L`: for every `K`, every
`S : Fin K → α` with `Ukkonen hK L S`, and every traversal
`σ : Fin K ≃ Fin K` satisfying `EulerianCycle hK L S σ`, the vertex cycle of
`σ` is the truth's vertex cycle, i.e. `VertexCycleEq hK L S σ id`.

`EulerianCycle` has two clauses.  The `single` clause
(`VisitsAll (fun x => σ (nextPos (σ.symm x))) (origin hG)`) is **automatic**:
the successor of a pull-back presentation is the conjugate
`σ ∘ rot₁ ∘ σ⁻¹` of the one-step rotation, hence a `G`-cycle, and
`pullback_isEulerianCycle` already proves it.  So the hypothesis reduces to

```text
traverses  ∀ i, vtx (σ (nextPos i)) = vtx (nextPos (σ i))          (T)
```

and the whole content is: (T) forces the vertex cycle to be a rotation of the
truth's, under `Ukkonen`.

## 2. The master reformulation

Write `ρ = nextPos`, `W = vtx` (the `(L-1)`-mer at a start), `K = L - 1`, and
let `J := σ ρ σ⁻¹` be the successor permutation *of the listing* `σ 0, σ 1, …`
(i.e. `J (σ i) = σ (i+1)`).  Then (T) is exactly

```text
∀ x, W (J x) = W (ρ x)                    (T')
```

because `x = σ i` ranges over all positions.  Putting `f := J ∘ ρ⁻¹` gives

```text
W (f q) = W (q)  ∀q,  f bijective,  J = f ∘ ρ,  σ i = Jⁱ (σ 0).   (★)
```

So: **alternative Eulerian cycles are exactly the label-preserving
permutations `f` for which `f ∘ ρ` is a `G`-cycle** (a `G`-cycle
automatically, since `J = σρσ⁻¹`), and the vertex cycle of the listing is the
label sequence along the `J`-cycle.  This is the classical reformulation:
`f` chooses, at every step, *which occurrence* of the next `(L-1)`-mer to
visit.

## 3. The three lemmas the proof needs

**Lemma 1 (three occurrences).**  If three distinct starts spell the same
`(L-1)`-mer and they are *not* all congruent modulo the least period `p` of
`S`, they extend simultaneously to a **maximal triple repeat** of length
`≥ K`; hence `Ukkonen` forbids it.  So under `Ukkonen`, three occurrences of
one `(L-1)`-mer force all three starts to be congruent mod `p`.  In
particular:

* `p = G` (primitive truth): every `(L-1)`-mer occurs **at most twice**;
* `p < G` (non-primitive): two starts spelling the same `(L-1)`-mer are
  congruent mod `p` (take a third occurrence at `a + p`), so the
  `(L-1)`-mers of the primitive root are pairwise distinct.

**Lemma 2 (crossing pairs).**  If two doubled pairs — `W a = W b`,
`W c = W d`, four distinct starts — *interleave*, then (primitivity gives
termination of the simultaneous extension) they extend to two **interleaved
maximal repeats**, both of length `≥ K`, contradicting `Ukkonen`.  So under
`Ukkonen` the doubled pairs of the primitive truth are pairwise
non-interleaving.

**Lemma 3 (the minimal chord).**  Let `f` be a bijection with
`W (f q) = W q`, whose support is a set of *non-crossing* pairs, and let
`J = f ∘ ρ` be a `G`-cycle.  Then `f = id`.

*Proof.*  Fibres have size `≤ 2`, so `f` is an involution which is a product
of disjoint transpositions, each on a doubled pair.  Suppose `f ≠ id` and
choose a support pair `(a, b)`, `a < b`, minimizing `b - a`.  By
non-crossing, no support pair has an endpoint strictly between `a` and `b`
(otherwise it is nested inside `(a, b)` and shorter, or it crosses).  Hence
`J x = f (x+1) = x + 1` for `a ≤ x < b - 1` and `J (b-1) = f b = a`, so
`J` restricts to the cycle `a, a+1, …, b-1, a` of length `b - a < G`: `J` is
not a `G`-cycle.  Contradiction. ∎

This is the heart of `thm:BBT`, and it is the classical
"non-crossing chords force a single cyclic trail" step, in the exact shape
the `Fin G → α` word layer supports.

## 4. The two cases

* **`p = G` (primitive).**  By Lemma 1 every `(L-1)`-mer occurs `≤ 2` times;
  by Lemma 2 the doubled pairs are non-crossing.  Since `J` is a `G`-cycle,
  Lemma 3 gives `f = id`, i.e. `J = ρ`, i.e. `σ i = σ 0 + i` and

  ```text
  W (σ i) = W (rotAdd (σ 0) i).
  ```

* **`p < G` (a power).**  By Lemma 1 two starts with the same `(L-1)`-mer are
  congruent mod `p`, so `f` preserves residues mod `p`; hence
  `J x = f (x+1) ≡ x + 1 (mod p)`, so `σ i ≡ σ 0 + i (mod p)`, and as `W`
  is `p`-periodic,

  ```text
  W (σ i) = W (rotAdd (σ 0) i).
  ```

In both cases `VertexCycleEq hK L S σ id` holds with the single shift
`k = σ 0`, i.e. the vertex cycle of `σ` is not merely *a* rotation of the
truth's: it is the truth's own vertex cycle read from the start `σ 0`.

`L ≤ 1` is vacuous (`vtx` has empty domain, so all `vtx` agree), so the
theorem holds for every `L`, exactly as `UniqueEulerianCycle` is stated.

## 5. Evidence

`scripts/verify_eulerian_cycle_uniqueness_89.py` (exhaustive search over all
circular words, all traversals) found no counterexample; re-run here with the
*faithful* formal definitions of `IsRepeat`, `IsTripleRepeat`, `Interleaved`
and `Ukkonen` (`scripts/verify_eulerian_unique_faithful_89.py`):

```text
G = 2 … 10, alphabet size 2, K = 1 … 4, all words satisfying Ukkonen,
all label-preserving permutations f with f ∘ ρ a G-cycle:
no traversal whose vertex cycle is not a rotation of the truth's.
```

The same search **without** the `Ukkonen` filter does produce failures — e.g.
`S = 001001`, `G = 6`, `K = 1`, listing `0 3 1 2 4 5`, whose label sequence
`000011` is not a rotation of `001001` — so both clauses of `Ukkonen` are
load-bearing, as Lemma 1 and Lemma 2 predict (`001001` violates the
triple-repeat clause: the starts `0, 1, 3` spell a maximal triple repeat of
length `1`).

## 6. Formalization status

`AssemblyP1/BBTUniqueEulerian.lean` develops, in order: the `WSeq`/`Agree`
layer and the de Bruijn shift; the period arithmetic (least period divides
every period); the master reformulation (★); Lemma 1; Lemma 2; Lemma 3; and
the two cases.  `L ≤ 1` is discharged separately.
