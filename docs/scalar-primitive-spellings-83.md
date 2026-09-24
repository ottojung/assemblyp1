# Scalar primitive spellings on the variable-length leaf

**Issue:** #83, packet 3  
**Status:** direct mathematical proof, with one standard combinatorics-on-words theorem imported

## Setup

Let `c0` be a nonzero balanced integer edge-type count vector with strongly connected support and

`gcd(c0_e : c0_e > 0) = 1`.

A cyclic edge-type spelling uses each edge type `e` exactly `c0_e` times, with consecutive edge types incidence-compatible. A spelling is **primitive** when its cyclic word is not a nontrivial power.

Normalized-spectrum equality across candidate lengths puts all integer count vectors on the same primitive ray: every such count vector is `m c0` for a positive integer `m`. The question here is exactly when some nontrivial scalar multiple `m c0`, `m>1`, has a primitive spelling.

## Theorem

> Some scalar multiple `m c0`, `m>1`, admits a primitive cyclic Eulerian edge-type spelling **iff** the support graph has a vertex with at least two distinct outgoing edge types. In the branching case, `m=2` already suffices.

This statement is about existence of a primitive realization somewhere on the scalar ray. It does **not** say that branching gives two distinct spelling necklaces at the base vector `c0`, and it does not by itself say that an arbitrary particular primitive truth `g c0` has a distinct normalized-spectrum competitor.

## Proof: branching implies a primitive spelling of `2c0`

Take an Eulerian cyclic edge-type spelling `C` of `c0`. Suppose a support vertex `v` has two distinct outgoing edge types. Since `C` uses every positive edge type, choose two occurrences of `v` immediately before occurrences of two different outgoing types. Cut the cyclic spelling at those two visits. This gives two nonempty closed `v`-to-`v` words `A` and `B`, with different first edge types, and `C = AB` after choosing the corresponding cyclic representative.

Then

`A A B B`

is a valid cyclic Eulerian edge-type spelling of `2c0`: each of `A` and `B` is a closed walk based at `v`, so the four blocks concatenate, and every edge count of `C=AB` is doubled.

It remains to prove that `AABB` is primitive. Suppose

`A^2 B^2 = U^k`

for some `k>1`. Every edge-type multiplicity in the left-hand word is then divisible by `k`, so `k` divides `gcd(2c0)=2`; hence `k=2`. We therefore have

`A^2 B^2 = U^2`.

By the Lyndon–Schützenberger word-equation theorem, an equation `x^n y^m = z^p` with nonempty words and `n,m,p >= 2` forces `x,y,z` to commute, equivalently to be powers of a common primitive word. Applied here, `A` and `B` must have the same first symbol. But the cuts were chosen so that their first edge types differ. Contradiction. Thus `AABB` is primitive.

This argument deliberately avoids the false stronger claim that branching produces multiple base necklaces. For example, a figure-eight support can have a unique base cyclic spelling up to rotation even though its doubled count vector has a primitive spelling obtained by grouping the two copies of the two closed excursions as `AABB`.

## Proof: no branching forbids every primitive scalar multiple

If every support vertex has at most one outgoing edge type, strong connectivity makes the support a directed cycle, including the one-vertex loop case. Balance forces all positive capacities around that cycle to be equal. Since `gcd(c0)=1`, every support capacity is therefore exactly one.

Consequently every cyclic Eulerian spelling of `m c0` follows the same directed cycle `m` times. It is the `m`-fold power of the base cycle, so it is nonprimitive for every `m>1`.

This proves the theorem.

## Example

For `L=2`, the primitive word `AAB` has count vector

`(AA, AB, BA) = (1,1,1)`.

Its support branches at vertex `A`. The doubled vector `(2,2,2)` has the primitive realization `AAABAB`, rather than only the square `(AAB)^2`.

The theorem also covers a figure-eight graph cleanly. If its two closed `v`-excursions are edge-type words `A=ab` and `B=cd`, then the base spelling `AB=abcd` is unique up to rotation, but `AABB=ababcdcd` is a valid primitive spelling of the doubled vector. This illustrates why the scalar theorem must not be conflated with uniqueness of the base spectrum fibre.

## Imported result and epistemic status

The only imported word-combinatorics result is the classical Lyndon–Schützenberger theorem used above. The primary source is R. C. Lyndon and M. P. Schützenberger, “The equation a^M = b^N c^P in a free group,” *Michigan Mathematical Journal* **9** (1962), 289–298, DOI `10.1307/mmj/1028998766`. It proves that for exponents at least two the solutions in a free group are powers of a common element; the free-monoid word form used here is the corresponding positive-word specialization. A convenient independently checkable formalization of the word form is the Archive of Formal Proofs entry `Combinatorics_Words/Lyndon_Schutzenberger`, which states that `x^a y^b = z^c` with all three exponents at least two forces the words to commute.

The branching theorem itself is a direct mathematical proof conditional only on that standard imported theorem. No bounded computation is needed for the proof.

## Consequence and remaining quantifier boundary

The theorem exactly answers the ray-level existence question:

- nonbranching primitive rays have no primitive realization at any larger scalar multiple;
- branching primitive rays already have a primitive realization at multiplier two.

It does **not** yet characterize normalized-spectrum identifiability of an arbitrary fixed primitive truth whose count vector is `g c0`. In particular, if the truth itself lies at `2c0`, existence of one primitive spelling of `2c0` need not produce a distinct orbit. That orbit/distinctness quantifier is a separate problem and must remain explicit.
