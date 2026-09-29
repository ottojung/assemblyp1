# #89 BBT chord/rematch work: what is proved, and the exact remaining gap

> **SUPERSEDED IN PART by `docs/bbt-eulerian-cycle-89.md` (2026-09-26).**
> §5 of this note states the remaining step in terms of *non-rotational
> read-type-preserving pull-back permutations*. **That statement is false**,
> and §4 of `docs/bbt-eulerian-cycle-89.md` contains two kernel-checked
> refutations (`S = 001`, `G = 3`, `L = 3` for a permutation that is not a
> traversal at all; `S = 0101`, `G = 4`, `L = 3` for a non-rotational
> pull-back that carries no long obstruction because it is a presentation
> of the truth's own Eulerian cycle). The theorem of Bresler–Bresler–Tse
> 2013, Theorem 3 is about **Eulerian cycles of the condensed `K`-mer
> graph**, and the corrected statement, its object, and the whole reduction
> are in `AssemblyP1/BBTEulerian.lean` and
> `docs/bbt-eulerian-cycle-89.md`. Sections 1–4 of this note remain accurate
> as a record of the chord route and of the raw-node-chord refutation; §5
> and §6 are superseded. In particular `P2.BBTUniqueAt` is now a *theorem*
> (`BBTEulerian.bbtUniqueAt_of_obstruction`), not an assumption of the
> exported population theorem.

_Status: kernel-checked partial results, 2026-09-26 (`c39108d` + this packet).
`P2.BBTUniqueAt` is **not** closed; the exported theorem
`AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation` still takes
`(hBBT : BBTUniqueAt L)`. No `sorry`, no `admit`, no new axiom; `#print axioms`
reports only `propext`, `Classical.choice`, `Quot.sound` for every theorem
mentioned below. Full `lake build` passes._

This note records two layers of work on the #89 route (chords / local rematching
of truth boundary occurrences, uniqueness of the Eulerian cycle at `K = L-1`):

* §1–§3: the previously proved abstract core, the matching adapter, and the
  kernel-checked refutation of the raw `(L-1)`-mer chord instantiation
  (`AssemblyP1/BBTChords.lean`, unchanged in this packet);
* §4 (new): the **condensed `(L-1)`-mer graph of `thm:BBT`** and the
  traversal-choice dichotomy for an alternative Eulerian traversal
  (`AssemblyP1/BBTCondense.lean`), including a closed complete-spectrum
  uniqueness theorem in the `P1` stratum;
* §5: the exact remaining implication, now stated in the *known-multiplicity*
  form, together with the two interface facts still missing and the
  discipline the sibling audit imposed on the argument.

**ATTRIBUTION (board 94, front 94e7; see `docs/best-tw1-attribution-94.md`).**
§5 and the "Pevzner" attributions in it are **relabelled as the board's own
construction**.  Nothing in §5 is imported from Pevzner 1995 or from BBT.

## 1. Proved: the abstract cyclic transposition / chord lemma

`AssemblyP1/BBTChords.lean`, section 1, on the smallest useful data structure —
an abstract permutation of `Fin G`, rotations of the circle, and interleaving of
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

**Limitation relevant to §5.** `chord_lemma` needs an *involution*. The map
induced by an alternative Eulerian traversal is a permutation, not known to be an
involution; see §5.

## 2. Proved: the generic equal-spectrum matching adapter

`BBTChords.lean`, section 2. These lemmas are the Eulerian-traversal
correspondence in the form the reduction needs, and they do **not** depend on the
condensation analysis:

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
contains a kernel-checked refutation (`raw_node_crossing_not_maximal`, plus
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
  pairs. The correct object is the one `thm:BBT` itself uses: the **condensed
  `(K+1)`-mer graph**, contracted along unambiguous vertices (§4).

## 4. Proved: the condensed `(L-1)`-mer graph and the traversal-choice dichotomy

`AssemblyP1/BBTCondense.lean`, source-aligned with `thm:BBT` (Bresler–Bresler–Tse
2013, Theorem 3, read with Bresler's dissertation, Appendix B): build the
`K`-mer graph from the spectrum, contract the **unambiguous** vertices (vertices
of multiplicity one), and what remains has as vertices the **branch objects**
(vertices of multiplicity `≥ 2`). The module encodes that architecture directly
on the de Bruijn multigraph of the word, with no bespoke "block" concept:

| theorem | content |
| --- | --- |
| `vtx`, `deg`, `inDeg`, `Branch` | the `(L-1)`-mer multigraph of the truth: vertex at a start, out-degree = `nodeCount`, in-degree, branch object |
| `nextPos_inj`, `nextPrev`, `prevNext` | the one-step rotation of the circle is a bijection (the modular arithmetic used throughout) |
| `inDeg_eq_deg` | **balance**: in-degree = out-degree, vertex by vertex |
| `deg_two_of_occ_ne`, `occ_of_branch`, `branch_has_two_occurrences` | a branch object is a vertex with two distinct occurrences, i.e. a repeated `K`-mer |
| `branchVerts`, `mem_branchVerts` | the **condensed vertex set** (the image of the branch occurrences — a finset of vertices even though the vertex type is not a `Fintype`) |
| `branchStarts_eq_biUnion` | the branch occurrences are the disjoint union of the fibres of the condensed vertices |
| `card_branchStarts_le_two_mul_branchVerts` | under the multiplicity cap, branch occurrences ≤ `2 ×` condensed vertices |
| `P1` | `def:P1P2`'s P1, in multigraph language: no branch object at all |
| `pullback`, `pullback_window`, `pullback_isEquiv` | the candidate→truth map of a matching: an `Equiv` of the circle that preserves read types |
| `match_next_vtx` | **both traversals enter the same vertex**: the vertex the candidate enters at `s` is the vertex the truth enters at the truth start carrying the candidate's read at `s` |
| `forced_at_unambiguous` | **no choice at an unambiguous vertex**: if that vertex is not a branch object, the two traversals agree there |
| `choices_only_at_branch` | **traversals differ only at branch objects** |
| `choiceSet`, `card_choices_le_branchStarts`, `card_choices_le_card` | the choice points inject into the branch occurrences; their number is bounded by the size of the condensation |
| `card_choices_le_two_mul_branchVerts` | with the multiplicity cap, the choice points are charged to the condensed vertices |
| `isRotation_of_step` | a step-by-step successor map on a circle is a rotation |
| `pullback_isRotation` | under P1, the pull-back of any matching is a rotation |
| `pullback_rotation_RotEquiv`, `rotAdd_neg_cancel` | a rotational pull-back is a rotation of the words: `RotEquiv hG E S` |
| `bbt_of_unambiguous`, `spectrum_unique_of_P1` | **`thm:BBT` in the branch-free (P1) stratum**: the complete `L`-spectrum determines such a word up to cyclic rotation |
| `condense_sanity_00101` | kernel-checked (`decide`): for `S = 00101`, `L = 3` the branch objects are `01` and `10`, both of degree `2`, their occurrences are `1,2,3,4`, and the segment leaving a branch occurrence is *degenerate* |

`condense_sanity_00101` also records, in prose, why §3's refutation is not an
artifact of a wrong object choice: branch objects and maximal repeats are
different objects (a maximal repeat of `00101` has length `3 > K = 2`, while a
branch object is a repeat of length exactly `K`), and the maximal unambiguous
segment leaving a branch occurrence can be trivial. §3/§4 use respectively the
second and the first of these objects, and the P2 clauses of `def:P1P2` speak
about maximal repeats, so both are needed.

### 4.1 The map is a permutation, not an arbitrary start map

A sibling audit (direct `#89` worker) found that a "step map" version of the
traversal argument is **false for arbitrary start maps**: `S = 0001`, `G = 4`,
`L = 3` is primitive and satisfies P2, yet admits a constant such map. Every
statement of `BBTCondense` is therefore about a *permutation that preserves read
types*:

* `pullback` is a `Fin G ≃ Fin G` (`pullback_isEquiv`), built from
  `Matching.1 : Function.Bijective σ`, i.e. from the equal-spectrum matching
  itself, not from a hand-chosen map;
* `pullback_window` is the fibre-preservation statement: the truth start
  assigned to a candidate start carries the same read;
* `not_const_of_injective` records (kernel-checked) that injectivity alone
  excludes constant maps, with no fixed-point assumption.

No theorem in this module is stated for a non-injective start map, and none
would be sound.

## 5. The exact remaining gap: the board's own known-multiplicity step

**ATTRIBUTION (board 94, front 94e7).**  The heading of this section formerly
read "The exact remaining gap: the Pevzner known-multiplicity step", and the
body formerly read "the input that closes it is **not** the unknown-multiplicity
condensation theorem but Pevzner 1995, Lemma 9, in its *known-multiplicity*
form".  **Both attributions are withdrawn.**  A two-sided retrieval on this
board established that Pevzner 1995 (Algorithmica 13:77--105) contains no
counting statement of any kind and no `BEST` / `arboresc` / `spanning` /
`matrix-tree` / `determinant` / out-degree / `repeat` / `spectrum` / `K-mer` /
`condens` vocabulary, and that BBT (Algorithmica 13:1--19, 2006) contains no
arborescence, no spanning-tree count, and **no proof of its own Theorem 3** ---
its Theorem 3 imports this step from Pevzner 1995, so **the citation chain is
broken and terminates in nothing**.  The step below is a **board construction**.
What may still be cited to Pevzner 1995 is Theorem 2, p. 81 (proof pp. 82--86),
the exchange/reflection orbit-connectivity argument on bicolored graphs, which
Pevzner himself attributes to Abrham & Kotzig 1980; and Theorem 1 /
Corollary 1, p. 80, the Kotzig--Nash-Williams balancedness criterion, from Kotzig
1968 / Nash-Williams.  Neither may be cited for a count, a bound, an
out-degree estimate, or a uniqueness result.  The BEST theorem is cited directly
from van Aardenne-Ehrenfest and de Bruijn, *Indag. Math.* (1951), or Tutte,
LMS Lect. Notes 83 (1975).  The two later uses of the word "Pevzner" in this
section (below, in "Why the chord lemma of §1 does not supply it") are relabelled
the same way: they refer to *this board's setting*, not to a source.

`spectrum_unique_of_P1` closes `thm:BBT` for words with **no** branch object. For
a word that *has* branch objects, §4 confines every alternative traversal to the
branch occurrences and bounds how many choice points there are, but the
uniqueness of the Eulerian cycle is not proved. Reading Bresler's dissertation
(Appendix B), the input that closes it is **not** the unknown-multiplicity
condensation theorem but the **known-multiplicity form** --- the board's own
reduction, which is exactly the setting here, since the complete spectrum
supplies every edge
multiplicity. The single remaining statement is:

```text
remaining:  a read-type-preserving permutation μ of the starts, coming from an
            equal-spectrum matching, which is not a rotation, either has two
            interleaving maximal repeats of length ≥ L-1, or forces a maximal
            triple repeat of length ≥ L-1.
```

Given §4, it is enough to state it for the pull-back: given
`μ = pullback hm.1` with `¬ IsRotation μ`, produce either

* `e₁ e₂ a b c d` with `IsRepeat e₁ a b`, `IsRepeat e₂ c d`,
  `Interleaved a b c d`, `L - 1 ≤ e₁` and `L - 1 ≤ e₂` — contradicted by
  `P2.interleaved`; or
* `e a b c` with `IsTripleRepeat e a b c` and `L - 1 ≤ e` — contradicted by
  `P2.triple`.

That statement would give `BBTUniqueAt` in the `2 ≤ L`, `3 ≤ G` regime: the
remaining `G ≤ 2` cases are finite and can be discharged separately, and
`L = 1` is not in the range of the project (`def:population` fixes `L ≥ 2`).

**Why the chord lemma of §1 does not supply it.** `chord_lemma` produces two
crossing orbits of a nontrivial rotational involution. In the board's setting
the induced permutation is not known to be an involution, so `chord_lemma` cannot
be applied; and the alternative Eulerian cycle of the *truth* is a rotation, so
one must first prove that the pull-back is a rotation. Concretely, the missing
link is: *the choice points of §4 are non-empty and force the two long
interleaved repeats* — i.e. the count bound of §4 must be upgraded from
quantitative to **the board's own dichotomy** (the `t_w = 1` reduction of
§5, above; see `docs/best-tw1-attribution-94.md`). Nothing in this packet
establishes that.

**Interface facts still not bridged** (as in the previous revision of this note):

* `¬ HasLongTripleRepeat` from the triple-repeat clause of `P2`
  (`SourceFaithfulIs.IsTripleRepeat` vs `RepeatAdapter.IsMaximalTriple`), and
* the two notions of primitivity (`PopulationReduction.IsPrimitive` vs
  `RepeatAdapter.IsPrimitive`),

both needed to invoke `RepeatAdapter.primitive_nodeCount_le_two`. In
`BBTCondense` the multiplicity cap is instead an explicit hypothesis
(`hcap : ∀ v, deg v ≤ 2`), so nothing in this module depends on those bridges.

## 6. Coordination and what this does not do

* Coordinated conceptually with the sibling `P2RepeatResidual` packet (separate
  branch/worktree; no shared state, no shared files).
* It does not prove `BBTUniqueAt`, and does not change the statement of any
  exported theorem. `spectrum_unique_of_P1` is a *new, additional* theorem about
  the `P1` stratum; it is not wired into `BBTCompleteSpectrumUniqueness`, whose
  statement is untouched.
* It does not revive the raw-`K`-mer maximal-extension argument; the packet
  contains a counterexample to it.
* It does not formalize the unknown-multiplicity condensation theorem of
  Appendix B, which is not needed here: multiplicities are known.
* It does not touch the finite-sampling or reverse-complement-collapsed parts of
  the model, and the #70 regression `primitivity_insufficient` is unaffected.
