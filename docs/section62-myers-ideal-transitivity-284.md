# Exact idealized string-graph transitivity: source-fidelity boundary

**Primary source:** Eugene W. Myers, *The fragment assembly string graph*,
Bioinformatics 21 Suppl. 2 (2005), ii79–ii85, §2 (p. ii81), §3 and Fig. 4
(pp. ii81–ii82):
https://www.cs.utoronto.ca/~brudno/csc2427/myers.pdf

Myers §2 describes an edge f→h as *transitive* if a two-hop path f→g→h
spells the **same sequence**. In the error-free equal-read-length oriented
overlap model, the implementation
`Section62SpellingReductionCandidate.isReducibleSpellingB` tests genuine
observed intermediate strands, two proper overlaps and the length law
`l1 + l2 = L + directOverlap`.

## Kernel-checked exact equivalence

`Section62MyersIdealTransitivity.TwoHopSameSpelling` is a semantic,
word-equality definition: an observed intermediate strand `m` and legal
two-hop suffix/prefix overlaps exist whose entire spelled word equals
the direct edge's spelled word.

`reducible_iff_ideal_two_hop` proves **both directions** of equivalence to
the implementation under the explicit hypotheses that all three reads have
length `L` and the direct edge is a proper overlap. The nontrivial
converse compares exact spelled-word lengths: equality of a two-edge
spelling (length `3L-l1-l2`) and the direct spelling (length `2L-l`)
forces `l1+l2=L+l`.

`reduced_mem_iff_no_ideal_detour` lifts this iff to the actual edge
filter: a proper equal-length edge survives the implemented reduction
**iff** it belongs to the input graph and no observed legal two-hop detour
spells the same word.

`overlapLens_gt_direct_of_comp` (pure `Nat`, by `omega`) plus its lift
`twoHop_overlaps_gt_direct` record requirement (3) of #284: whenever the
spelling identity holds for a proper overlap edge, the length identity
`l1+l2=L+e.len` is forced (same spelled-length comparison as the converse
above), and hence both replacement overlaps are forced strictly longer
than the direct edge overlap (`e.len < l1` and `e.len < l2`).

Both theorems are Lean-kernel-checked; their axiom audit uses only
`[propext, Quot.sound]`, no `sorryAx` or `native_decide`. The two new
`overlapLens` declarations above are source-stated with `omega`-closed
proofs (the arithmetic core additionally replayed standalone through the
pinned Lean kernel); full-module `lake build` replay of this file remains
for the integrator with a warm Mathlib cache.

## Still outside the theorem

This is equivalence to the **idealized mathematical two-hop
same-spelling relation**, not a proof that the repository reproduces
the complete practical Myers 2005 algorithm. Myers §3/Fig. 4 explicitly
uses `FUZZ=10` and extra marking passes for *approximate/noisy*
overlaps. The full algorithm also handles contained reads, orientation,
multiple overlaps and edge collapsing. Those behaviors must be
compared separately. In the equal-length, error-free, deduplicated
setting, the containment concern simplifies, but this is not a
formal equivalence theorem for the practical algorithm.

### Compatibility boundary (what has and has not been compared)

| Myers feature | Evidence available in the cited paper | Relation to this formalization |
|---|---|---|
| Exact transitivity | §2 defines a transitive edge by a two-edge path spelling the same sequence. | **Proved equivalent** for proper equal-length, error-free observed overlaps by `reducible_iff_ideal_two_hop`. |
| Approximate/noisy overlaps (`FUZZ = 10`) | §3 and Fig. 4 describe approximate overlap handling and additional marking passes. | **Not modeled**: predicates here use exact suffix-prefix equality. No claim that a fuzzy deletion preserves spelling is made. |
| Contained reads | Myers' algorithm handles containment as a separate graph-construction concern. | **Not separately modeled**: every formal vertex is a fixed-length observed read and every edge is a proper overlap. Containment preprocessing is outside the iff theorem. |
| Multiple/parallel overlaps and edge collapsing | The practical construction can retain distinct overlap/edge identities and has collapsing behavior. | **Not compared at identifier level**: the formal relation is over read strands and overlap lengths; equivalence of multiplicities or collapse policy is open. |
| Bidirected orientation | Myers' model includes orientations; the repository also represents reverse-complement strands. | The theorem is stated for the repository's oriented strand/overlap relation, but does not assert every practical representation or canonicalization choice is identical. |

The exact-transitivity row is the narrow correspondence supported by the
kernel theorem. The other rows are explicit non-claims, not presumed
compatibilities. In particular, idealized equivalence must not be cited as
validation of Myers' complete implementation or of MB09's full preprocessing
pipeline. Closing those rows requires an inspectable source specification and a
separate comparison of definitions and edge identity; this note does not infer
implementation details from the title or citation alone.

The Observation 7 theorem in PR #265 is already unconditional for the
repository's `transitivelyReducedSpelling` graph; this module narrows
its source-fidelity gap without changing its hypotheses.
