# Board 94: Pevzner transposition route

## Provenance correction

A previous board-94 audit concluded that Pevzner 1995 did not contain a relevant Euler-tour connectivity statement. That conclusion came from an incomplete extraction.

Pavel Pevzner, *DNA Physical Mapping and Alternating Eulerian Cycles in Colored Graphs*, Algorithmica 13 (1995), Section 5 ("Ukkonen's Conjecture"), contains the directly relevant result:

**Theorem 3. Every two words with the same q-gram composition can be transformed into each other by transpositions and rotations.**

The proof explicitly reduces fixed q-gram composition to Eulerian paths in the directed de Bruijn graph, replaces directed edges by black/white pairs in a bicolored graph, and invokes the earlier order-exchange theorem. Order exchanges are exactly Ukkonen transpositions; reflections disappear because every cycle in the constructed bicolored graph is even.

Pevzner's later *Computational Molecular Biology*, section 5.7, states the graph version directly: every two Eulerian cycles in a directed graph can be transformed into one another by a sequence of Euler switches.

This changes the best proof architecture: we do not need to invent a global traversal-order induction from scratch.

## Match to AssemblyP1

Set q = L. Pevzner's repeated (q-1)-grams are exactly our vtx objects.

Existing kernel-checked facts already provide most of the local argument:

1. P2 + primitivity give multiplicity at most two; nontrivial branch vertices have two occurrences (DoubledPair / AltF_sq / orbit_is_doubledPair).
2. For 2 <= L, crossing support chords of a genuine Eulerian traversal coalesce to one deterministic maximal extension (Issue94TW4Coalesce.crossingChordsCoalesce_of_two_le).
3. A coalesced pair is a maximal-repeat ladder (BBTLadder.ladder_of_coalescing / ladder_chord_identities).
4. Corresponding positions along the two copies have identical vertex labels (BBTLadder.ladder_arc_eq).
5. Pointwise vertex-invisible rearrangements preserve VertexCycleEq (Issue94TransposePreserve).

## New local target: one benign Euler switch

Prove:

> If sigma is an Eulerian listing already VertexCycleEq to the truth, x and y are two branch (L-1)-mers interlaced in that listing, and tau is obtained by the directed Euler switch at x,y, then under P2, primitivity, 2 <= L <= K and Ukkonen, tau is still VertexCycleEq to the truth.

Proof plan:

1. Transport the four occurrences of x,y through the current VertexCycleEq rotation witness to truth-circle starts. Rotation preserves cyclic interleaving.
2. The two occurrence pairs are doubled branch pairs in truth coordinates.
3. Apply crossingChordsCoalesce_of_two_le: the two raw crossing pairs share one maximal extension.
4. ladder_of_coalescing writes the four occurrences as two shifts of one maximal-repeat pair.
5. Unfold the Euler switch: it exchanges the two trails between the interlaced branch vertices.
6. Those trails are the two corresponding portions of the common maximal-repeat ladder. ladder_arc_eq gives equality of their vertex labels point-by-point.
7. Hence the switched listing has the same vertex reading as the old listing, so VertexCycleEq is preserved.

The switch need not be forbidden. S=00101, L=3 is the canonical benign case: crossing raw repeated 2-mers coalesce into one maximal repeat, so a switch may alter edge presentation without altering the vertex cycle. This is why the target is VertexCycleEq, not AltF=id.

## Global proof using Pevzner

Once the local benign-switch lemma is kernel-checked:

1. Pevzner Theorem 3 supplies a finite sequence of rotations and Euler switches from the truth word/tour to any equal-spectrum candidate.
2. Truth is VertexCycleEq initially.
3. Rotations preserve VertexCycleEq.
4. At each switch, the induction hypothesis identifies the current vertex word with the truth up to rotation, so the switch's four occurrences transport to truth coordinates.
5. The local benign-switch lemma preserves VertexCycleEq.
6. Induction gives VertexCycleEq for the target tour.

This should feed directly into Issue94Interface.P2LongUnique.

## Formalization recommendation

Prefer a small local proof of Pevzner connectivity rather than formalizing bicolored graphs. Define an Euler switch on a cyclic edge listing and induct on the number of successor pairings that disagree with the target tour. If two tours differ, choose a wrong transition; following the target pairing locates a second disagreement that is interlaced with the first; one switch fixes at least one target transition; recurse.

Keep the Cohn-Lempel component-deletion route as an independent cross-check, but it is no longer the preferred global architecture.

## Sources

- P. A. Pevzner, *DNA Physical Mapping and Alternating Eulerian Cycles in Colored Graphs*, Algorithmica 13 (1995), 77-105, Section 5, Theorem 3.
- P. A. Pevzner, *Computational Molecular Biology: An Algorithmic Approach*, section 5.7.
- L. Traldi, *Circuit partitions and signed interlacement in 4-regular graphs*, for the modern directed-Euler-system transposition statement.
