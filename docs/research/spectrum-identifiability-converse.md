# Spectrum identifiability does not imply the P2/Ukkonen repeat condition

## Status and answer

_2026-09-24. Mathematical proof for one exact model; computational evidence
only for discovery; primary-source audit._

Under the complete oriented, same-length `2`-spectrum model, the converse

```text
complete-spectrum identifiability modulo rotation
  implies the project P2 condition
```

is **false**. The cleanest witness found is the primitive circular genome

```text
S = AAAB,       |S| = 4,       L = 2.
```

Its complete spectrum uniquely identifies it up to rotation, but it violates
P2 at its maximal length-1 triple repeat. This refutes necessity, not the
forward theorem that P2 is sufficient.

## Exact model

A candidate is a circular word over an arbitrary finite alphabet, with
orientation fixed and **no reverse-complement collapse**. Candidates have
exactly the observed length. The observation is the complete integer
multiplicity vector

```text
spec_L(D)(w) = number of start positions carrying the oriented word w.
```

Genome equivalence is cyclic rotation only. Write

```text
Unique_S  iff  spec_L(D) = spec_L(S) implies D is a rotation of S
```

for every same-length oriented circular candidate `D`, over every finite
alphabet. Primitivity is not imposed as a candidate-class restriction; the
witness is primitive anyway.

P2 at `K = L - 1 = 1` is Bresler–Bresler–Tse's Ukkonen condition after
substitution: no maximal triple repeat and no interleaved pair of maximal
repeats has length at least `1`. Its triple-repeat clause is equivalent here to
requiring that no symbol occur at three distinct starts.

## Exact spectrum and the failed condition

For `L >= 2`, this graph bijection can also be stated in terms of BEST:
the number of edge-distinct cyclic Euler tours is

```text
tau_r(G) * product_v (outdeg(v) - 1)!,
```

where `tau_r` is the number of directed spanning arborescences rooted at
`r`. Thus the usual best-possible count is one exactly when
`tau_r(G) = 1` and every outdegree is at most one. **This formula must not be
applied verbatim to labeled-word identifiability without a quotient.** BEST
counts parallel copies as distinct edges, whereas two parallel copies carrying
the same observed `L`-mer are indistinguishable in a spectrum. The exact
word-level criterion therefore counts cyclic Euler tours modulo parallel-copy
permutations (or, equivalently, count edge-type sequences with prescribed
multiplicity). If the genome is restricted to primitive circular words, a
word-level class of `m` tours corresponds to `m` periodic traversals of a
primitive root, and the quotient still has to be taken. The `AAAB` proof
below does not depend on this subtlety: its forced tour is unique even in the
finer edge-distinct sense.

The four cyclic 2-mers of `S = AAAB`, in start order, are

```text
AA, AA, AB, BA.
```

Hence

```text
spec_2(S) = { AA:2, AB:1, BA:1 },       total mass 4.
```

At starts `0`, `1`, and `2`, the symbols are all `A`. Their preceding symbols
are `B`, `A`, `B`, not all equal, and their following symbols are `A`, `A`,
`B`, not all equal. Therefore these three starts are a maximal length-1
triple repeat under the source definition. Since `1 = K`, this is a prohibited
long triple repeat, so

```text
not P2(S,2).
```

The failure already occurs at the triple-repeat clause; no interleaved pair is
needed.

## Uniqueness proof

Let `D` be any length-4 circular word with the displayed spectrum. Use the
order-1 de Bruijn multigraph, with one vertex per observed symbol and one
directed edge per observed 2-mer. Its edge multiset is

```text
AA -> AA  with multiplicity 2,
AB -> BA  with multiplicity 1,
BA -> AA  with multiplicity 1.
```

The two copies of `AA -> AA` form a loop at `AA`; the other two edges form the
forced chain

```text
AA --AB--> BA --BA--> AA.
```

Any genome spelling this spectrum is an Eulerian circuit in this multigraph.
After visiting the non-loop chain, the only unused outgoing edge at `AA` is the
self-loop, which must then be traversed twice before returning to `AA` to
complete the circuit. Up to the initial rotation, the edge sequence is therefore

```text
AA, AB, BA, AA,
```

which spells `AAAB`. No different circular ordering or alphabet symbol can have
this spectrum. Thus `Unique_S` holds. **[mathematical proof]**

The same argument also proves uniqueness among all alphabets, not merely after
restricting discovery to a binary alphabet. A bounded exact search over
primitive binary circular words, ordered first by `(L, |S|)`, independently
found `AAAB` before proceeding to larger scopes; the universal uniqueness
claim above is proved directly and is not inferred from that search.
**[computational evidence, exhaustive in the binary scope searched before the
first hit]**

## Consequences for the converse frontier

1. **The literal P2 converse fails.** P2 is a clean structural sufficient region,
   but a forbidden maximal triple repeat need not create spectrum ambiguity.
   The example is a triple repeat without an interleaving; its copy count is
   encoded exactly by the spectrum.

2. **A weaker necessary condition can be graph-theoretic.** In the
   same-length model, the exact property is uniqueness of the positive
   multiplicity circulation / Eulerian circuit compatible with the observed
   spectrum. P2 is not this property. Repeats of higher multiplicity and
   non-interleaved triple repeats need not create competing traversals. More
   precisely, for `L >= 2`, the observed integer multiplicities determine a
   directed multigraph on observed `(L-1)`-mers: each distinct observed
   `L`-mer `a_1...a_L` is an edge
   `a_1...a_{L-1} -> a_2...a_L` with its integer multiplicity. Every
   same-length circular word with the observed spectrum is exactly a cyclic
   Euler tour of this graph, modulo rotation of the starting point and modulo
   permutation of indistinguishable parallel copies carrying the same
   `L`-mer. Complete-spectrum identifiability is therefore equivalent to
   having exactly one such label-and-rotation class of Euler tours. This is an
   exact necessary-and-sufficient graph property, but it is local to the
   observed graph rather than P2 repeat syntax.

3. **Do not conflate this with finite-data ML.** Complete-spectrum uniqueness
   concerns the observation `spec_L(S)`. It does not establish unique ML for a
   particular finite sample, uniform recovery, or variable-length candidates.
   Those quantifiers remain separate as required by issue #82.

4. **No claim about variable-length identifiability follows.** The proof uses
   total mass `4` and forces the same length. Equal normalized spectra can
   arise at different lengths, as the project's existing primitive counterexample
   `AAB` versus `AAABAB` already demonstrates.

## Primary-literature audit

### Bresler, Bresler, and Tse (2013)

In *Optimal assembly for high throughput shotgun sequencing*, the distinctions
are explicit:

- The **Ukkonen condition** section says that interleaved repeats or triple
  repeats of length at least `L-1` force equal-likelihood ambiguity at the
  stated read-length boundary. This is a source-stated obstruction under that
  model, not a conclusion that the later strengthened conditions are necessary
  for every data instance.
- **Theorem 1** says that if an interleaved pair or a triple repeat has *all*
  copies unbridged, there is another same-length sequence with equal observed
  likelihood. The required hypothesis includes the actual read set and the
  unbridged-copy condition. It does not say that the mere presence of a triple
  repeat forces ambiguity for every read realization.
- **Theorem 3** is an implication: if Ukkonen's condition holds, the condensed
  graph from the complete spectrum has a unique Eulerian cycle. The paper does
  not state the converse of Theorem 3. `AAAB` is consistent with that logical
  boundary.
- **Theorem 6** gives sufficient conditions for the MultiBridging algorithm:
  all interleaved repeats bridged, all triple repeats all-bridged, and coverage.
  The paper's “Gap to lower bound” explicitly says MultiBridging needs all three
  triple copies bridged whereas the lower-bound obstruction needs only one
  bridged copy. This is a gap, not an iff theorem.
- The abstract's broad phrase “necessary and sufficient conditions” concerns
  the paper's reconstruction framework. It must not be read as the converse of
  Theorem 3 for a fixed spectrum. Theorem 1 is the concrete necessary
  obstruction and includes read-position/bridging hypotheses absent from the
  bare repeat test.

Primary source: Guy Bresler, Ma'ayan Bresler, and David Tse, *Optimal assembly
for high throughput shotgun sequencing*, BMC Bioinformatics 14(Suppl 5):S18
(2013), sections “Ukkonen's condition,” “Lower bounds,” and “Towards optimal
assembly,” Theorems 1, 3, and 6, and “Gap to lower bound.” DOI
`10.1186/1471-2105-14-S5-S18`; open text PMCID `PMC3706340`.

### Shomorony et al. (2016)

Shomorony et al. use coverage plus bridged interleaved repeats and all-bridged
triple repeats as the sufficient information-feasibility set `I_s` for
Not-So-Greedy reconstruction. Their Discussion asks for an ML implication; it
does not claim a converse or a necessary repeat syntax for all identifiable
instances. The present witness concerns P2/Ukkonen-style bare repeat syntax,
not whether a particular read realization belongs to `I_s`.

Primary source: Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, and David
N. C. Tse, *Information-optimal genome assembly via sparse read-overlap graphs*,
Bioinformatics 32(17) (2016), i494–i502, especially Eq. (1), §5, and the
Discussion. DOI `10.1093/bioinformatics/btw450`.

### Kamath et al. (2017), HINGE

HINGE describes “optimal repeat resolution” relative to the particular reads:
bridged repeats remain resolved, while unbridged repeats are collapsed. Its
Introduction and Figure 1 distinguish a single-bridged triple repeat (case E),
which admits a single traversal, from an unbridged triple repeat (case D), which
admits multiple traversals. This supports the same warning: bridge state and
graph traversability matter; bare presence of a triple repeat is not equivalent
to non-identifiability. It provides no bare-spectrum converse theorem.

Primary source: Govinda M. Kamath, Ilan Shomorony, Fei Xia, Thomas A. Courtade,
and David N. C. Tse, *HINGE: long-read assembly achieves optimal repeat
resolution*, Genome Research 27(5) (2017), 747–756, Introduction, Results, and
Fig. 1. DOI `10.1101/gr.216465.116`; open text PMCID `PMC5411769`.

## Epistemic ledger

| Claim | Status |
|---|---|
| `spec_2(AAAB) = {AA:2, AB:1, BA:1}` and that spectrum has one circular spelling | mathematical proof |
| `AAAB` is primitive | mathematical proof (it has no proper period) |
| `AAAB` has a maximal length-1 triple repeat and fails P2/Ukkonen at `K=1` | mathematical proof + source definition |
| BBT Theorem 1 requires the stated all-unbridged hypothesis; Theorem 3 is a sufficient implication; Theorem 6 is algorithmic sufficiency | source fact |
| Bounded binary search independently finds the minimal `(L,|S|)` example | computational evidence, exhaustive only for the stated scope |
| A direct characterization of all bare-spectrum identifiability obstructions | open |
| Finite-data ML, uniform-recovery, and population-ML converses | not addressed by this witness |

## Reproduction and future boundary

The discovery enumeration grouped all binary words of a fixed length by exact
integer oriented spectrum and canonical rotation, then checked the maximal
triple-repeat clause. No generated artifact is needed to establish the witness:
the de Bruijn proof above covers every alphabet. A next useful question is to
characterize when a maximal triple or interleaved repeat changes the set of
Eulerian traversals. That graph condition, rather than P2 syntax alone, is the
plausible necessary-and-sufficient frontier for the complete-spectrum model.
