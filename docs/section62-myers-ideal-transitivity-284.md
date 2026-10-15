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

Both theorems are Lean-kernel-checked; their axiom audit uses only
`[propext, Quot.sound]`, no `sorryAx` or `native_decide`.

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

The Observation 7 theorem in PR #265 is already unconditional for the
repository's `transitivelyReducedSpelling` graph; this module narrows
its source-fidelity gap without changing its hypotheses.
