# #89 BBT chord/rematch work: what is proved, and the exact remaining adapter gap

_Status: kernel-checked partial results, 2026-09-26. `P2.BBTUniqueAt` is **not**
closed; the exported theorem
`AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation` still takes
`(hBBT : BBTUniqueAt L)`. No `sorry`, no `admit`, no new axiom; `#print axioms`
reports only `propext`, `Classical.choice`, `Quot.sound` for every theorem
mentioned below._

This note records the packet that followed the route sketched in the #89 comments
(condense unambiguous paths / maximal repeats, alternate Eulerian traversal as a
local rematching, transposition/chord lemma, non-interleaving chords force a
unique cyclic trail). It contains one proved combinatorial core, one proved
generic adapter, one proved refutation of the route's raw-node formulation, and a
precisely located remaining gap.

## 1. Proved: the abstract cyclic transposition / chord lemma

`AssemblyP1/BBTChords.lean`, section 1, on the smallest useful data structure — an
abstract permutation of `Fin G`, rotations of the circle, and interleaving of
four starts, with no words, spectra or graphs:

```text
chord_lemma       : 3 ≤ G → (∀ x, R (R x) = x) → R ≠ id →
                     (all pairs of distinct two-element orbits of R do not
                      interleave) → ¬ IsRotation R
chord_lemma_cross : the contrapositive, as the adapter consumes it:
                    a nontrivial rotational involution has two crossing orbits
chord_lemma_sanity: on Fin 4, the rotation by two is a nonidentity involution
                    whose orbits {0,2},{1,3} do interleave (anti-vacuity)
```

Equivalently: *a nonidentity involution of a circle of at least three positions
whose chords are pairwise non-interleaving is not a rotation of that circle.*
The proof is a two-case split on the shift `t` (`0 < t < G`, then `t ≠ 1` because
`2 t ≡ 0 (mod G)` would give `G ∣ 2`), and exhibits the two crossing chords
`{0, t}` and `{1, R 1}` by modular arithmetic. This is the abstract
"non-interleaving chords forbid a single cyclic trail" step of the route.

## 2. Proved: the generic equal-spectrum matching adapter

Section 2. These lemmas are the Eulerian-traversal correspondence in the form the
reduction needs, and they do **not** depend on the chord analysis:

| theorem | content |
| --- | --- |
| `startsOf`, `nodeStartsOf` | the `specCount` / `nodeCount` fibres, as definitions |
| `Matching` | `σ` is a bijection with `window S r = window E (σ r)`: the two traversals of the same `(L-1)`-mer multigraph, matched start by start |
| `exists_matching` | equal complete spectra give such a matching (one fibre equivalence per read type; injectivity fibrewise, surjectivity from `Finite.injective_iff_surjective`) |
| `matching_rotation_imp` | a rotational matching is a rotation of the words, i.e. exactly `RotEquiv hG E S` |

`matching_rotation_imp` is the only direction of "`σ` is a rotation ⟺ `E` is a
rotation of `S`" that is formalized. The converse is deliberately absent: a
matching need not be unique inside a read-type fibre, so the statement is about
the *existence* of a rotational matching, and the reduction only needs this
direction.

## 3. Proved: raw `(L-1)`-mer chords do **not** work (R1/R2 correction)

The route as first phrased instantiates the two ends of a chord as the two
occurrences of a repeated `(L-1)`-mer, and would conclude that two crossing
chords yield an interleaved pair of *maximal* repeats, contradicting the
interleaved clause of `def:P1P2`. **That inference is false**, and the packet
now contains a kernel-checked refutation (`raw_node_crossing_not_maximal`, plus
`scripts/verify_raw_node_chord_refutation.py`):

* `S = 00101`, `G = 5`, `L = 3` **satisfies P2** (exhaustively verified; the P2
  predicate is not `decide`-able at that quantifier depth in Lean, so this part
  is the script's, not the kernel's);
* the length-`2` mers `01` and `10` are each repeated, at the **crossing** pairs
  of starts `{1,3}` and `{2,4}` (`InterleavedStarts`, kernel-checked);
* **neither pair is a maximal repeat**: `{1,3}` agrees on the following symbol
  and `{2,4}` agrees on the preceding symbol, so `IsRepeat` fails for both
  (kernel-checked, in the `cyc`/`nodeWindow` formulation of the same conditions).

So crossing of raw node pairs is *compatible* with P2, and this is the same
phenomenon the earlier audit recorded for the maximal-extension step
(`docs/audit-p2-direct-proof-maximal-extension-2026-09-21.md`: crossing raw pairs
can collapse onto the same maximal pair). Consequently:

* the abstract chord lemma of §1 is **not** refuted — it never claimed that raw
  node pairs are its chords; it is a statement about an abstract involution and
  is retained unchanged;
* what is invalidated is the *instantiation* of that involution by raw node
  pairs. The correct object is the **maximal-repeat block**: the simultaneous
  two-sided maximal extension of the occurrences of a repeated `(L-1)`-mer.
  This block is unique for a given pair, and it is what the interleaved clause
  of `def:P1P2` ranges over (it is an object of `IsRepeat`). P2 forbids *blocks*
  of length `≥ L-1` from interleaving, while internal duplicate nodes may cross,
  exactly as the counterexample shows.

## 4. The exact remaining adapter gap

`BBTUniqueAt` is still open. Everything below is the honest residue, in the order
it has to be attacked.

1. **Block assignment (not formalized).** For a repeated `(L-1)`-mer `v` with
   occurrence set `A_v`, form the simultaneous maximal extension
   `(A_v, e_v)` — the largest `e` for which the occurrences of `v` agree on a
   window of length `e` at suitably shifted starts, together with the two-sided
   maximality making `IsRepeat e_v a' b'` true. This is the analogue of
   `RepeatAdapter.extend_triple` (private) for pairs; it must also be proved
   **unique** for a given pair, because the chord lemma needs a well-defined
   involution.

2. **Factoring of the alternative Eulerian choices by blocks (open, and the
   real content).** Two traversals of the same multigraph differ by local
   switches at the doubly-visited nodes. Under the `(L-1)`-mer multiplicity cap
   (the triple-repeat clause of P2, available as
   `RepeatAdapter.primitive_nodeCount_le_two` given primitivity and
   `¬ HasLongTripleRepeat`) each doubled node contributes one switch. What has
   to be shown, and is *not* shown, is:

   ```text
   the set of switched nodes is a union of whole maximal-repeat blocks, and
   the switched blocks factor the alternative traversal, so that
   "no two switched blocks of length ≥ L-1 interleave" forces the
   candidate traversal to be the truth traversal up to cyclic shift.
   ```

   This is the step at which the audited failure bites, and the #89 packet
   cannot shortcut it: the block assignment is not fibre-local, so the fibrewise
   matching of §2 says nothing about it.

3. **Where the chord lemma would then apply.** Once (1) and (2) are available, the
   proved §1 applies verbatim: the induced permutation of truth boundary
   occurrences is a product of disjoint transpositions, its two-element orbits
   are the switched blocks, and pairwise non-interleaving of those blocks (P2)
   contradicts `chord_lemma`. `matching_rotation_imp` then converts the
   conclusion into `RotEquiv`, and `BBTCompleteSpectrumUniqueness` follows
   without any change of statement.

4. **Small unsolved interface, for the record.** Two P2-adjacent facts are used
   as hypotheses above and are *not* bridged in this repository:
   `¬ HasLongTripleRepeat` from the triple-repeat clause of `P2`
   (`SourceFaithfulIs.IsTripleRepeat` vs `RepeatAdapter.IsMaximalTriple`), and
   the two notions of primitivity (`PopulationReduction.IsPrimitive` vs
   `RepeatAdapter.IsPrimitive`). Both are needed to invoke
   `RepeatAdapter.primitive_nodeCount_le_two` and hence the multiplicity cap.
   They are ordinary comparison lemmas, not mathematical obstacles, but they are
   not written.

## 5. What this does not do

* It does not prove `BBTUniqueAt`, and does not change the statement of any
  exported theorem.
* It does not revive the raw-`K`-mer maximal-extension argument; the packet
  contains a counterexample to it.
* It does not touch the finite-sampling or reverse-complement-collapsed parts of
  the model, and the #70 regression `primitivity_insufficient` is unaffected.
