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
Cut an Eulerian circuit at all its visits to `v`. The maximal closed subtrails
between successive visits can be reattached in the opposite order at `v`,
without changing multiplicities or adjacency. A reattachment that exchanges
the cyclic order of occurrences of `a` and `b` gives a different edge-type
necklace: otherwise that order would be invariant. This proves (1) implies (3).

Choose representatives `A,B` of two distinct necklaces, each of length
`N=sum c0`, cut at occurrences of the branching vertex `v`, and rotate both
cuts to that same vertex. Endpoint compatibility now holds by construction,
and the cyclic word `AB` spells `2c0`. **Concatenation lemma.** If `A,B` have
the same length and are not rotations, then `AB` is primitive. If `AB=U^r`
with `r>1`, the equal-length factors are powers of rotations of the same
primitive block, hence rotations of one another, a contradiction. Thus (1)
implies (2).

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

The all-capacities-`>=2` regime does not remove the dichotomy. A branching
example with `AA:AB:BA:BB=2:2:2:2` has multiple spellings and primitive
doubled spellings, as checked in the bounded artifact. A nonbranching example
is the single loop type with capacity two, whose doubled spelling is `aa` and
is nonprimitive. Thus capacities uniformly at least two are neither an
ambiguity criterion nor an obstruction to primitive repair.

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
