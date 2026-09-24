# Scalar primitive spellings on the variable-length leaf

**Issue:** #83, packet 3  
**Status:** mathematical proof plus bounded exact computation (2026-09-24)

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

## Theorem

Let `c0` be a primitive balanced vector whose support is weakly connected.
Then the following are equivalent:

1. `c0` has a branching vertex, meaning a vertex with at least two distinct
   outgoing edge types.
2. `m c0` has a primitive cyclic edge-type spelling for `m=2` (and hence for
   at least one `m>1`).
3. `c0` has at least two distinct cyclic edge-type spellings modulo rotation.

If there is no branching vertex, every cyclic spelling of `m c0` is the word
`W^m`, where `W` is the unique cyclic spelling of `c0`.  In particular no
`m>1` is primitive.

## Proof

If every vertex has at most one outgoing edge type, the support graph is a
functional digraph.  Weak connectivity and balance imply that it is one
directed cycle.  Since the vector `c0` is primitive, the corresponding cyclic
edge-type word is `W`, not a power.  Every spelling of `m c0` follows that
unique successor at every occurrence, so its word is `W^m`.

Conversely, suppose `v` has two distinct outgoing edge types `a` and `b`.
Take any Eulerian circuit and read it cyclically.  Consider the two successive
outgoing edges at the visit to `v` that follows a chosen cut.  The cyclic order
of the occurrences of `a` and `b` can be reversed by the standard Eulerian
splice at `v`: equivalently, decompose the circuit at `v` and concatenate the
resulting closed trails in the opposite order.  The result is Eulerian.  Since
`a` and `b` are distinct edge types, the two resulting edge-type necklaces are
distinct (if they were equal, the cyclic order at the cut would be the same).
This proves (1) implies (3).  The other implications are immediate except for
the primitive construction below.

Let `A` and `B` be distinct cyclic spellings of `c0`, each of length `N=sum c0`.
The cyclic word `AB` spells `2c0`.  **Concatenation lemma.** If `A` and `B` have
the same length and are not rotations of one another, then `AB` is primitive.
Indeed, if `AB=U^r` with `r>1`, then cutting the periodic word at the boundary
between `A` and `B` shows that `A` and `B` are powers of the same block; since
they have equal length, the two powers are rotations.  This contradicts the
choice of `A,B`.  Therefore (1) implies (2), and `(3)` is equivalent to
`(1)` by the preceding argument.

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
