# Scalar primitive spellings on the variable-length leaf

**Issue:** #83, packet 3  
**Status:** mathematical proof plus bounded exact computation; the branching/equivalence claim is refuted (2026-09-24)

## Setup

Fix a length `L`, and let `E` be the positive edge types of a weakly connected
balanced directed graph.  An edge-type count vector `c` is **primitive** when
`gcd(c_e : c_e>0)=1`.  A cyclic edge-type spelling is a cyclic word in `E`
whose consecutive edges compose and whose multiplicities are `c`.  It is
**primitive** when the cyclic edge-type word is not a nontrivial power.

For a primitive balanced vector `c0`, every integer normalized-spectrum
competitor has counts `m c0` for some positive integer `m`: if the competing
length is `H`, integrality and the equality
`H c0 = G cD` force `G | H`, and after cancelling the gcd the multiplier is an
integer.  The question is whether some `m>1` has a primitive spelling.

## Correct theorem and the branching obstruction

The no-branching direction is correct. If every vertex has at most one
outgoing edge type, weak connectivity and balance make the support a single
directed cycle, so every cyclic spelling of `m c0` is `W^m`, with `W^m` the
power of the unique primitive spelling `W`. Thus no multiple has a primitive
spelling.

The converse as previously stated is false: branching is not equivalent to
having two cyclic edge-type spellings modulo rotation. The cut-at-two-visits
splice only gives a *rooted/linear* Euler-tour change when the two visits are
actually spliceable. After forgetting the cut (forgetting the starting vertex),
swapping two excursions at their common vertex can be a rotation. It is not a
new edge-type necklace.

A transparent counterexample is the figure-eight graph: vertex `v` has two
separate directed 2-cycles, one with edge types `a,b` and one with `c,d`. Its
edge-type count vector `(1,1,1,1)` is primitive, and `v` branches, but its only
cyclic spellings are `abcd` and `cdab`, which are rotations. Nevertheless
`2c0` has the primitive spelling `abcdabcdcdcd` (with the symbols understood as
the corresponding edge types). More generally, two closed excursions based at
`v` can be concatenated in either order, but `XY` and `YX` are rotations at the
base point; the splice is invisible to cyclic equivalence.

The valid existence statement is therefore only the implication
`c0` has two distinct cyclic spellings modulo rotation => `2c0` has a
primitive spelling, proved by the concatenation lemma below. Branching is a
sufficient condition for a local splice in some graphs, but not an iff
criterion for cyclic necklaces. This note makes no claim about a
branching-equivalence or a multiple-base-necklaces theorem.

## Proof

If every vertex has at most one outgoing edge type, the support graph is a
functional digraph.  Weak connectivity and balance imply that it is one
directed cycle.  Since the vector `c0` is primitive, the corresponding cyclic
edge-type word is `W`, not a power.  Every spelling of `m c0` follows that
unique successor at every occurrence, so its word is `W^m`.

For the remaining valid implication, let `A` and `B` be distinct cyclic
spellings of `c0`, each of length `N=sum c0`. The cyclic word `AB` spells
`2c0`. **Concatenation lemma.** If `A` and `B` have the same length and are not
rotations of one another, then `AB` is primitive. Indeed, if `AB=U^r` with
`r>1`, then cutting the periodic word at the boundary between `A` and `B` shows
that `A` and `B` are powers of the same block; since they have equal length, the
two powers are rotations. This contradicts the choice of `A,B`.

The word lemma requested in issue #83 is also valid in its sharper form: for
nonempty `A,B` with different first symbols, `AABB` is not a square. If
`AABB=XX`, then `|A|+|B|=2|X|`; the first symbol of `X` is the first symbol
of `A`, while the first symbol of the second copy of `X` is the first symbol
of `B`. These would have to be equal, a contradiction. The fixed linear cut in
`AABB` is essential to this direct proof; one must not silently identify words
under rotation before comparing the two first symbols.

The last sentence is important: primitiveness of the **count vector** is not
being confused with primitiveness of a spelling.  The former controls the
arithmetic ray; the branching condition controls whether repeated copies can
be interlaced into a non-periodic cyclic word.

## Sharp example

For `L=2`, let `c0` be the vector `(AA,AB,BA)=(1,1,1)`, obtained from the
primitive word `AAB`.  The doubled vector is `(2,2,2)`, and the word
`AAABAB` is primitive while having exactly that doubled spectrum.  It is not
`AAB` squared.  This is the `m=2` case predicted by the theorem.

At the other extreme, a single directed edge-type cycle with count vector
`c0` has no primitive spelling at any multiple: every spelling is `W^m`.

## Reproducible computation

Run:

```text
python3 scripts/verify_scalar_primitive_spellings.py
```

The script checks the `AAB`/`AAABAB` witness and exhaustively enumerates all
binary words of lengths at most eight.  For every primitive length-two
spectrum, it verifies the dichotomy “a branching first vertex exists iff the
doubled spectrum has a primitive spelling.”  This is finite computational
evidence only; the theorem above is the hand proof and does not depend on the
search.

## Consequences and remaining boundary

For normalized-spectrum identifiability across lengths, a primitive balanced
spectrum is therefore a clean criterion boundary: its support graph is
intrinsically forced exactly when no larger scalar multiple can repair the
periodicity.  The theorem does not claim that every non-primitive **word**
associated with a primitive vector is safely repairable; it classifies the
existence question for some multiple, which is the question in #83.  A
remaining variant is to ask for the least `m>1`, or to impose a fixed upper
bound on candidate length.  Those are refinement questions, not obstructions
to the present existence theorem.
