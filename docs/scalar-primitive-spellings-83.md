# Scalar primitive spellings on the variable-length leaf

**Issue:** #83, packet 3  
**Status:** direct mathematical proof, with one standard combinatorics-on-words theorem imported

## Setup

Let `c0` be a nonzero balanced integer edge-type count vector with strongly connected support and

`gcd(c0_e : c0_e > 0) = 1`.

A cyclic edge-type spelling uses each edge type `e` exactly `c0_e` times, with consecutive edge types incidence-compatible. A spelling is **primitive** when its cyclic word is not a nontrivial power.

Normalized-spectrum equality across candidate lengths puts all integer count vectors on the same primitive ray: every such count vector is `m c0` for a positive integer `m`.

## Theorem

> The support graph has a vertex with at least two distinct outgoing edge types **iff**, for every integer `m >= 2`, `m c0` admits a primitive cyclic Eulerian edge-type spelling.

Equivalently, if the support does not branch in outgoing edge type, no nontrivial scalar multiple admits a primitive spelling; if it does branch, every scalar multiple from two onward does.

This statement is about primitive realizations along a scalar ray. It does **not** say that branching gives two distinct spelling necklaces at the base vector `c0`.

## Proof: branching gives a primitive spelling for every `m >= 2`

Take an Eulerian cyclic edge-type spelling `C` of `c0`. Suppose a support vertex `v` has two distinct outgoing edge types. Since `C` uses every positive edge type, choose two occurrences of `v` immediately before occurrences of two different outgoing types. Cut the cyclic spelling at those two visits. This gives two nonempty closed `v`-to-`v` words `A` and `B`, with different first edge types, and `C = AB` after choosing the corresponding cyclic representative.

For any integer `m >= 2`,

`A^m B^m`

is a valid cyclic Eulerian edge-type spelling of `m c0`: each block is a closed walk based at `v`, so the blocks concatenate, and every edge count of `C=AB` is multiplied by `m`.

It remains to prove this spelling primitive. Suppose

`A^m B^m = U^k`

for some `k>1`. Every edge-type multiplicity in the left-hand word is then divisible by `k`, so `k` divides

`gcd(m c0) = m gcd(c0) = m`.

Thus `m >= 2` and `k >= 2`. By the Lyndon–Schützenberger word-equation theorem, an equation `x^n y^p = z^q` with nonempty words and `n,p,q >= 2` forces `x,y,z` to commute, equivalently to be powers of a common primitive word. Applied here, `A` and `B` must have the same first symbol. But the cuts were chosen so that their first edge types differ. Contradiction. Hence `A^m B^m` is primitive for every `m >= 2`.

This argument deliberately avoids the false stronger claim that branching produces multiple base necklaces. A figure-eight support can have a unique base cyclic spelling up to rotation even though every multiplied count vector `m c0`, `m>=2`, has a primitive spelling obtained as `A^m B^m`.

## Proof: no branching forbids every primitive scalar multiple

If every support vertex has at most one outgoing edge type, strong connectivity makes the support a directed cycle, including the one-vertex loop case. Balance forces all positive capacities around that cycle to be equal. Since `gcd(c0)=1`, every support capacity is therefore exactly one.

Consequently every cyclic Eulerian spelling of `m c0` follows the same directed cycle `m` times. It is the `m`-fold power of the base cycle, so it is nonprimitive for every `m>1`.

This proves the theorem.

## Example

For `L=2`, the primitive word `AAB` has count vector

`(AA, AB, BA) = (1,1,1)`.

Its support branches at vertex `A`. For every `m>=2`, the vector `(m,m,m)` therefore has a primitive realization. At `m=2`, one such realization is `AAABAB`, rather than only the square `(AAB)^2`.

The theorem also covers a figure-eight graph cleanly. If its two closed `v`-excursions are edge-type words `A=ab` and `B=cd`, then the base spelling `AB=abcd` can be unique up to rotation while `A^m B^m` is a valid primitive spelling of `m c0` for every `m>=2`. This illustrates why the scalar theorem must not be conflated with uniqueness of the base spectrum fibre.

## Imported result and epistemic status

The only imported word-combinatorics result is the classical Lyndon–Schützenberger theorem used above. The primary source is R. C. Lyndon and M. P. Schützenberger, “The equation a^M = b^N c^P in a free group,” *Michigan Mathematical Journal* **9** (1962), 289–298, DOI `10.1307/mmj/1028998766`. It proves that for exponents at least two the solutions in a free group are powers of a common element; the free-monoid word form used here is the corresponding positive-word specialization. A convenient independently checkable formalization of the word form is the Archive of Formal Proofs entry `Combinatorics_Words/Lyndon_Schutzenberger`, which states that `x^a y^b = z^c` with all three exponents at least two forces the words to commute.

The branching theorem itself is a direct mathematical proof conditional only on that standard imported theorem. No bounded computation is needed for the proof.

## Fixed-truth consequence: exact variable-length primitive identifiability boundary

Let a primitive truth `S` have complete-spectrum count vector

`c_S = g c0`,

where `g` is the gcd of the positive coordinates and `c0` is the primitive integer point on its normalized-spectrum ray. Candidates are allowed to have arbitrary positive length but are required to be primitive, and equality is modulo cyclic rotation.

Normalized-spectrum equality is exactly membership on the same integer ray: a candidate with the same normalized spectrum has count vector `m c0` for some positive integer `m`.

If the support branches, choose `m>=2` with `m != g`: take `m=2` unless `g=2`, in which case take `m=3`. The theorem supplies a primitive spelling of `m c0`. Its length differs from that of `S`, so it cannot lie in the truth's rotation orbit. Thus every branching primitive truth has a distinct variable-length primitive candidate with the same normalized complete spectrum.

If the support does not branch, it is a directed cycle and the proof above shows that every realization at scalar `m>1` is a nonprimitive power. Since `S` itself is primitive, necessarily `g=1`; hence there is no other primitive realization anywhere on the normalized-spectrum ray.

Therefore, under this oriented, primitive, strongly-connected complete-spectrum model:

> **A primitive truth is identifiable among variable-length primitive candidates from its normalized complete spectrum iff its spectrum support has no vertex with two distinct outgoing edge types.**

This is a fixed-truth classification, not merely a ray-level existence statement. It closes the earlier `g=2` orbit caveat because branching supplies primitive realizations at every multiplier `m>=2`, allowing a competitor at a different scalar and therefore a different length.
