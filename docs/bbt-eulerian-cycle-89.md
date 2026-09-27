# #89: `thm:BBT` as uniqueness of the condensed graph's Eulerian cycle

_Status: kernel-checked Lean object, reduction and refutations, 2026-09-26.
The uniqueness step itself (`AssemblyP1.BBTEulerian.EulerianCycleObstruction`)
is **not** proved; it is the one remaining input of the exported population
theorem. No `sorry`, no `admit`, no new axiom: `#print axioms` reports only
`propext`, `Classical.choice` and `Quot.sound` for every theorem named here.
Full `lake build` passes._

## 1. The literature correction that re-centres the packet

Bresler–Bresler–Tse 2013 (*Optimal assembly for high throughput shotgun
sequencing*), Theorem 3, is a statement about **one object**: the `K`-mer
graph built from the complete `(K+1)`-spectrum of a circular genome `s`,
*condensed* (unambiguous vertices contracted). Its conclusion is

> if `s` satisfies Ukkonen's condition --- no triple repeat and no
> interleaved repeat pair of length `≥ K` --- then the condensed graph has
> a **unique Eulerian cycle**, and that cycle spells `s` up to cyclic
> rotation.

Two consequences for issue #89, both of which the previous packet
(`docs/bbt-chord-rematch-89.md`, §5) got wrong:

* the hypothesis ranges over **Eulerian cycles of that graph**, not over
  permutations of the starts. A permutation of equal-labelled starts that
  does not traverse the multigraph, or whose successor is not a single
  cycle, is *outside the theorem* and says nothing about it;
* the conclusion is a statement about the **vertex cycle** (the cyclic
  sequence of `K`-mers visited), not about the *presentation* of that
  cycle (which start one calls the first element).

`docs/bbt-chord-rematch-89.md` §5 stated the remaining step as

```text
remaining: a read-type-preserving permutation μ of the starts, coming from an
          equal-spectrum matching, which is not a rotation, either has two
          interleaving maximal repeats of length ≥ L-1, or forces a maximal
          triple repeat of length ≥ L-1.
```

**That statement is false**, and §4 below contains two kernel-checked
refutations of its two failure modes, one of them an instance that the
*whole* family of such claims gets wrong.

## 2. The object, formalized: `EulerianCycle`

`AssemblyP1/BBTEulerian.lean` introduces the missing object, on the
`(L-1)`-mer multigraph that `AssemblyP1/BBTCondense.lean` already builds
(`vtx`, `deg`, `Branch`, `branchStarts`, `branchStarts_eq_biUnion`):

```text
VisitsAll θ x     := (fun n : Fin G => θ^[n.val] x) is injective

EulerianCycle hG L S σ
  := (∀ i, vtx hG L S (σ (nextPos i)) = vtx hG L S (nextPos hG (σ i)))   -- traverses
     ∧ VisitsAll (fun x => σ (nextPos hG (σ.symm x))) (origin hG)         -- one circuit

VertexCycleEq hG L S σ τ
  := ∃ k : Fin G, ∀ i, vtx hG L S (σ i) = vtx hG L S (rotAdd hG k (τ i))
```

* the first clause of `EulerianCycle` is exactly
  `BBTSequenceGraph.match_next_vtx` (both traversals enter the same vertex);
* the second clause is what makes the walk a *single* circuit: the
  successor of a pull-back presentation is the conjugate
  `μ ∘ rot₁ ∘ μ⁻¹` of the one-step rotation, hence a `G`-cycle
  (`altSucc_iterate`, `rotAdd_inj_lt`, both proved here);
* `VertexCycleEq` is "the same Eulerian cycle", with the starting point
  forgotten, and it is the object the uniqueness theorem is about.

## 3. The theorem, in the source's shape

```text
LongObstruction hG L S :=
    (∃ e a b c, IsTripleRepeat e a b c ∧ L - 1 ≤ e.val)
  ∨ (∃ e₁ e₂ a b c d, IsRepeat e₁ a b ∧ IsRepeat e₂ c d ∧
      Interleaved a b c d ∧ L - 1 ≤ e₁.val ∧ L - 1 ≤ e₂.val)

UniqueEulerianCycle L :=
    ∀ K hK S, Ukkonen hK L S → ∀ σ : Fin K ≃ Fin K,
        EulerianCycle hK L S σ → VertexCycleEq hK L S σ (id)

EulerianCycleObstruction L :=
    ∀ K hK S, Ukkonen hK L S → ∀ σ : Fin K ≃ Fin K,
        EulerianCycle hK L S σ →
          VertexCycleEq hK L S σ (id) ∨ LongObstruction hK L S
```

`EulerianCycleObstruction` is `thm:BBT` at `K = L - 1` with the
dichotomy spelled out: a non-rotational alternative Eulerian cycle forces
either a maximal triple repeat of length `≥ L - 1` or two interleaved
maximal repeats both of length `≥ L - 1`. The two alternatives are the two
clauses of `def:P1P2`, and

* `longObstruction_iff_not_Ukkonen : LongObstruction hG L S ↔ ¬Ukkonen hG L S`
  (proved: the obstruction is the negation of Ukkonen's condition, clause
  by clause), and
* `not_longObstruction_of_P2` (proved) discharge them against `P2`,

so the two forms of the theorem are interchangeable
(`uniqueEulerianCycle_of_obstruction`, `obstruction_of_uniqueEulerianCycle`).

## 4. Which objects are and are not alternative Eulerian cycles

Two kernel-checked (`decide`) instances, both in
`AssemblyP1/BBTEulerian.lean` §4.

### 4.1 A permutation of the starts that is not a traversal at all

`S = 001`, `G = 3`, `L = 3` (so `K = 2`), permutation `τ₃ = (0 2 1)`:

* `not_vertexCycleEq` : the vertex cycle of `τ₃` is not a rotation of the
  truth's vertex cycle (the three `K`-mers `00, 01, 10` are pairwise
  distinct and `τ₃` reorders them);
* `not_eulerianCycle_validity` : `τ₃` is **not** an `EulerianCycle` of the
  condensed graph --- it fails the traverses clause (the vertex it enters
  at the second start is not the shift of the vertex it enters at the
  first).

So an instance of the "arbitrary permutation" form is not a counterexample
to `thm:BBT`: it is not an object the theorem is about.

### 4.2 A non-rotational pull-back with no long obstruction (anti-vacuity)

`S = 0101`, `G = 4`, `L = 3` (so `K = 2`), pull-back `τ₄ = (0 1)(2 3)`:

* `eulerianCycle_S4` : `τ₄` **is** an alternative Eulerian cycle of the
  condensed `(L-1)`-mer multigraph;
* `trivial_vertexCycleEq_S4` : its vertex cycle **is** the truth's vertex
  cycle, read from the start `1`;
* `not_rotation_S4` : `τ₄` is **not** a rotation of the circle.

Here the pull-back is non-rotational, `S` has no maximal repeat of any
length and no triple repeat, so `P2` holds with room to spare, and no long
obstruction is available --- yet the conclusion of `thm:BBT` holds, because
the alternative Eulerian cycle is the truth's own cycle. **This is the
decisive point: "the pull-back is not a rotation" is not the hypothesis that
forces the long obstruction; "the alternative Eulerian *cycle* is not the
truth's cycle" is.**

## 5. The reduction (fully proved)

Everything except the uniqueness step itself is now in the kernel:

| theorem | content |
| --- | --- |
| `pullback_isEulerianCycle` | the pull-back of an equal-spectrum matching is an alternative Eulerian cycle of the condensed graph (traverses: `match_next_vtx`; one circuit: `altSucc_iterate` + `rotAdd_inj_lt`) |
| `eulerianCycle_refl` | the truth's own traversal is one |
| `rotEquiv_of_vertexCycleEq` | a rotational vertex cycle makes the candidate a rotation of the truth |
| `bbtCompleteSpec_of_obstruction` | `EulerianCycleObstruction` ⟹ `P2.BBTCompleteSpectrumUniqueness` at `K = L - 1` |
| `bbtUniqueAt_of_obstruction` | ⟹ `P2.BBTUniqueAt` |
| `bbt_of_P2_obstruction` | the `P2`-flavoured form the population chain consumes |
| `longObstruction_of_nonrotational` | the requested dichotomy, contrapositively: a **non-rotational alternative Eulerian cycle of the condensed graph** forces a maximal triple repeat of length `≥ L - 1` or two interleaved maximal repeats both of length `≥ L - 1` |

Consequence: **`AssemblyP1.P2.BBTUniqueAt` is no longer an assumption.**
`AssemblyP1/PopulationUniqueness.lean` now takes

```text
(hPevzner : AssemblyP1.BBTEulerian.EulerianCycleObstruction (α := α) L)
```

and derives `BBTUniqueAt` inside the proof from `2 ≤ L` (which `hL : 1 < L`
already gives). The exported theorems
`population_unique_ML_up_to_rotation`,
`population_unique_ML_up_to_rotation_same_length` and
`population_tie_implies_rotation` keep their conclusions; their single
structural premise is now the Eulerian-cycle uniqueness input in the
source's own shape, and it is the *only* unproved statement in the chain.

## 6. The remaining step, isolated

The one open statement is `EulerianCycleObstruction` (equivalently
`UniqueEulerianCycle`): the uniqueness of the Eulerian cycle of the
condensed `(L-1)`-mer multigraph of an `Ukkonen` word. It has been
verified by exhaustive search --- `scripts/verify_eulerian_cycle_uniqueness_89.py`
enumerates all circular words over a finite alphabet, all `K`, and all
single-circuit traversals of the multigraph, and finds no word satisfying
Ukkonen's condition at `K` for which two traversals have different vertex
cycles:

```text
$ python3 scripts/verify_eulerian_cycle_uniqueness_89.py 9 2
G = 9, alphabet size 2, 512 words
  (word, K) pairs satisfying Ukkonen at K : 3090
  max number of traversals of one multigraph : 40320
  all traversals have the same vertex cycle : YES
```

(also `8 2` and `7 3`.) A finite search is evidence, not a proof, and it
is recorded as such.

The sub-steps the proof of `UniqueEulerianCycle` needs, in the order a
proof would take them:

1. **the condensation bookkeeping**, already available:
   `BBTSequenceGraph.branchStarts_eq_biUnion` and
   `card_choices_le_branchStarts`; an alternative Eulerian cycle differs
   from the truth's only at branch occurrences, by
   `BBTSequenceGraph.choices_only_at_branch`;
2. **maximal extension of a branch pair**: two distinct occurrences of the
   same `(L-1)`-mer extend to a *maximal* repeat of length `≥ L-1`. This is
   the bridge between the condensed objects (`Branch`, branch occurrences)
   and the maximal repeats ranged over by `def:P1P2`, and it is the step
   the maximal-extension audit (`docs/audit-p2-direct-proof-maximal-extension-2026-09-21.md`)
   shows cannot be replaced by "raw node pairs are maximal repeats";
3. **the dichotomy**: a non-trivial difference of two Eulerian cycles of the
   condensed graph produces either three occurrences of one branch object
   (a maximal triple repeat of length `≥ L-1`) or two interleaved pairs of
   branch occurrences whose maximal extensions interleave.

Step 2 needs primitivity of the truth to keep the maximal extension below
`G` (an extension of length `≥ G` makes the truth a power); the population
chain has `IsPrimitive` for the truth, but the BBT step is applied to the
truth alone, so a primitivity hypothesis has to be threaded into
`BBTCompleteSpectrumUniqueness` or an extension bound proved directly.
Step 3 is the combinatorial core and is not attempted here.

## 6a. Step 2 as proved (`AssemblyP1/BBTMaximalExtension.lean`)

Step 2 is now **proved, kernel-checked**, in
`AssemblyP1/BBTMaximalExtension.lean`, and two of the claims recorded above
are corrected by it.

| theorem | content |
| --- | --- |
| `Agrees`, `agrees_iff_agree` | agreement of two occurrences at an arbitrary length, identified with `Genome.Agree` on the same word |
| `agrees_mono` | agreement is downward closed in the length |
| `preceding_eq_of_agrees_ge` | agreement over a full turn makes the two **preceding** symbols agree: the pair is periodic and carries no maximal repeat at all |
| `max_of_agrees` | the agreement lengths below `G` have a maximum `m ≥ e₀`, `m < G`, and `m+1` is not an agreement length whenever `m+1 < G` |
| `exists_maximalRepeat` | **the maximal extension**: if `a ≠ b` agree at length `1 ≤ e₀ < G` and their preceding symbols differ, then `(a, b)` is a maximal repeat of length `e` with `e₀ ≤ e < G` |
| `maximalRepeat_of_branch` | **step 2 for a branch pair**: two distinct starts carrying the same `(L-1)`-mer whose preceding symbols differ give a maximal repeat of length `≥ L-1`, with the `L-1 ≥ G` case discharged by `preceding_eq_of_agrees_ge` |
| `maximalRepeat_of_branchVertex` | the same, read at a branch vertex, so the occurrences are the two realisations of one condensed vertex |
| `interleaved_disjunct`, `triple_disjunct` | the two disjuncts of `LongObstruction` are *assembled* from repeats of length `≥ L-1` obtained as above |

Two corrections.

* **Primitivity is not needed for the length bound.**  The claim recorded
  in the audit and in §6 above ("step 2 needs primitivity to keep the
  maximal extension below `G`") is refuted by `exists_maximalRepeat` and
  `maximalRepeat_of_branch`: the agreement lengths are capped at `G - 1`,
  and `Genome.IsRepeat` only asks for `e < S.len`, so the produced maximal
  repeat always has `e < G` for **any** truth, periodic or not.  What
  primitivity would exclude is the *unbounded* extension, and that case is
  excluded here by the weaker, local hypothesis that the two preceding
  symbols differ (`preceding_eq_of_agrees_ge`).  No primitivity hypothesis
  has to be threaded into `BBTCompleteSpectrumUniqueness`.
* **A raw branch pair is not a maximal repeat, and this is now recorded as
  a kernel-checked instance rather than prose.**  `S = 0111`, `G = 4`,
  `L = 2`: the symbol `1` is a branch object of multiplicity 3
  (`branch_0111`), realised at the starts `2` and `3`
  (`branchPair_0111`), and those starts have *equal* preceding symbols
  (`preceding_eq_branchPair_0111`), so they support **no** maximal repeat
  at any length below `|S|` (`not_maximalRepeat_branchPair_0111`).
  Stepping the pair one position backwards gives the starts `1`, `2`, which
  do support the maximal repeat of length `2 ≥ L-1 = 1`
  (`maximalRepeat_of_branch_0111`, `maximalRepeat_of_extendedBranchPair_0111`).
  So the occurrence pair must be **extended backwards** before it can be
  used as a constituent of `def:P1P2`; the `Preceding a ≠ Preceding b`
  hypothesis of `maximalRepeat_of_branch` is doing real work, and the
  instance shows exactly why the raw branch-pair claim of
  `docs/bbt-chord-rematch-89.md` §5 is refuted.

`#print axioms` for every theorem named above reports only `propext`,
`Classical.choice` and `Quot.sound`.  No `sorry`, no `admit`, no new
axiom.

### What is still missing, precisely

1. **The backward extension.**  `maximalRepeat_of_branch` needs a pair
   `a, b` of occurrences of one `(L-1)`-mer with different preceding
   symbols; a branch pair need not have them (§3 above).  Extending
   backwards until the preceding symbols differ is still open; the
   obstruction is the periodic case, in which the extension never
   terminates and no maximal repeat exists.
2. **Step 3, the dichotomy.**  Nothing here produces *two* maximal repeats
   with alternating starts, or a maximal triple repeat: one maximal repeat
   is a single constituent of the interleaved clause, and `interleaved_disjunct`
   still needs a second one whose starts interleave.  This is the
   combinatorial core and is untouched.
3. Consequently `EulerianCycleObstruction` is **still not proved**, and it
   remains the single open input of
   `population_unique_ML_up_to_rotation`.  `BBTMaximalExtension.EulerianCycleGap`
   names the missing statement as a `Prop`; it is not inhabited and nothing
   depends on it.

### Extra search evidence for the statement itself

The statement was re-verified on two further ranges of
`scripts/verify_eulerian_cycle_uniqueness_89.py` (finite search, evidence
only, not a proof):

```text
$ python3 scripts/verify_eulerian_cycle_uniqueness_89.py 10 2
G = 10, alphabet size 2, 1024 words
  (word, K) pairs satisfying Ukkonen at K : 6890
  max number of traversals of one multigraph : 362880
  all traversals have the same vertex cycle : YES

$ python3 scripts/verify_eulerian_cycle_uniqueness_89.py 8 3
G = 8, alphabet size 3, 6561 words
  (word, K) pairs satisfying Ukkonen at K : 42000
  all traversals have the same vertex cycle : YES
```

The `G = 10` range includes non-primitive words (e.g. every word of period
`5`), so the uniqueness statement is not merely true on primitive words in
this range.

## 7. Scope and non-goals

* `AssemblyP1/BBTCondense.lean` is unchanged. Its §4 result
  (`spectrum_unique_of_P1`: uniqueness in the branch-free stratum) is
  subsumed by, and consistent with, the statement above.
* The reverse-complement-collapsed part of the model, the finite-sampling
  part, and the #70 regression `primitivity_insufficient` are untouched.
* Nothing here changes the statement of any exported theorem's conclusion,
  and nothing introduces an axiom.
