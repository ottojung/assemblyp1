# Issue #272 target 5: the all-unbridged obstruction is not the exact condition

_Status: 2026-10-21. Source-level analysis with a kernel-checked counterexample.
Companion Lean module:
[`AssemblyP1/FiniteBreslerObstructionGap.lean`](../AssemblyP1/FiniteBreslerObstructionGap.lean),
audited by
[`AssemblyP1/FiniteBreslerObstructionGapAudit.lean`](../AssemblyP1/FiniteBreslerObstructionGapAudit.lean),
with the independent computational cross-check
[`scripts/verify_272_bresler_obstruction.py`](../scripts/verify_272_bresler_obstruction.py)._

This note makes one bounded increment on the remaining open axis of issue #272:
the relationship between the **original information-theoretic repeat-bridging
obstruction** and the exact necessary-and-sufficient condition for finite
Bayesian recovery.  It complements
[`source-notes/issue272-is-necessity.md`](source-notes/issue272-is-necessity.md),
which settled that the `I_s` sufficient condition is **not necessary** for
read-only decoder certainty.

## The source obstruction (attributed)

Bresler--Bresler--Tse (2013), *Optimal assembly for high throughput shotgun
sequencing*, Theorem 1:

> Given a DNA sequence `s` and a set of reads, if there is a pair of
> interleaved repeats or a triple repeat whose copies are all unbridged, then
> there is another sequence `s'` of the same length under which the likelihood
> of observing the reads is the same.

Their summary is that a **necessary** condition for reconstruction is that all
interleaved and triple repeats are bridged (at least one copy bridged).  The
merged repository transcribes the repeat/bridging layer faithfully
([`AssemblyP1/SourceFaithfulIs.lean`](../AssemblyP1/SourceFaithfulIs.lean),
[`AssemblyP1/HistoricalCovers.lean`](../AssemblyP1/HistoricalCovers.lean)); the
external equal-likelihood construction is **not** formalized and is supplied as
an attributed premise.

The obstruction is deliberately distinct from the `I_s` **sufficient**
condition: `I_s` (the MultiBridging/Not-So-Greedy hypothesis) requires every
triple repeat to be **all-bridged**, whereas the source obstruction only
requires the absence of an **all-unbridged** triple.  The gap between
"all-bridged" and "not all-unbridged" is exactly what
[`source-notes/issue272-is-necessity.md`](source-notes/issue272-is-necessity.md)
kernel-checked from the sufficiency side.

## The determination

**The source obstruction is necessary but not sufficient for read-only decoder
certainty, and therefore is not the exact necessary-and-sufficient condition.**

* **Necessity** (`sourceObstruction_necessary_of_bresler`) is proved from the
  attributed Bresler--Bresler--Tse premise: if the truth genome carries an
  all-unbridged interleaved pair or triple repeat, there is a same-length
  competitor with the same read likelihood, hence a competitor realizing the
  observed read-string set in a different rotation orbit; the read-only
  posterior is therefore not one.  The premise is a hypothesis of the theorem,
  not an axiom.
* **Non-sufficiency**
  (`sourceObstruction_not_sufficient_for_readOnly_certainty`) is an
  unconditional kernel-checked counterexample.

## Explicit hypotheses (candidate universe, read model, truth)

The counterexample lives in the same finite read model the merged adapter uses,
so nothing is smuggled in through a change of convention:

* **Orientation.** Oriented circular reads (no reverse-complement collapse),
  matching the 2016 single-strand model; the genome equivalence is **cyclic
  rotation** (the merged canonical rotation code `orbit`).
* **Genome length.** Candidates have the **same length `G`** as the truth, over
  the **same finite alphabet** (the two-symbol alphabet `Bit = Fin 2`).
* **Read model.** A fixed common read length `L` with `2 ≤ L ≤ G`; a set `R` of
  sampled start positions induces the **distinct read-string set**
  `observedTypes_ofFinset S L R`.
* **Observation.** The read-string set `Y = Finset (Fin L → Bit)`.
* **Likelihood.** The read-realizable **support indicator** `p w Y = 1` iff some
  start set induces exactly `Y`, the support of any faithful read likelihood;
  only its positivity enters certainty. Prior `π ≡ 1`.
* **Obstruction.** The literal Bresler--Bresler--Tse predicate: an all-unbridged
  triple repeat or an all-unbridged interleaved pair, at the saturated match
  starts `MatchStarts S L Y`.

## The counterexample

Genome `AABB` (length `4`), read length `L = 2`, sampled starts `R = {0, 1}`.
Induced read-string set

```
Y = {AA, AB}.
```

**The obstruction is absent.** `AABB` has no triple repeat (its only repeats are
the length-`1` pairs `A` at `{0,1}` and `B` at `{2,3}`, two copies each) and no
interleaved pair (the two pairs do not alternate), so neither clause of the
source obstruction applies.  Kernel endpoint: `not_sourceObstruction_aabb`.

**No read-only decoder is certain.** The read-realizable support of
`Y = {AA, AB}` is not a single rotation class: the competitor `AAAB` also
realizes `Y` (its length-`2` windows are `AA, AA, AB, BA`, induced by
`R = {0, 2}`), and `orbit AAAB ≠ orbit AABB`.  Hence `Y` is not `Unambiguous`,
so no read-only decoder is certain at `Y`.  Kernel endpoints:
`realizable_aaab`, `orbit_aaab_ne_aabb`, `not_unambiguous_aabb`.

| fact | kernel endpoint | value at `(AABB, 2, {0,1})` |
|---|---|---|
| read-string set | `Yaabb` | `{AA, AB}` |
| all-unbridged triple repeat | `not_sourceObstruction_aabb` | absent |
| all-unbridged interleaved pair | `not_sourceObstruction_aabb` | absent |
| source obstruction | `not_sourceObstruction_aabb` | **absent** |
| competitor realizing `Y` | `realizable_aaab` | `AAAB` via `{0,2}` |
| competitor orbit differs | `orbit_aaab_ne_aabb` | yes |
| `Y` is `Unambiguous` | `not_unambiguous_aabb` | **no** |
| read-only decoder certain | `not_unambiguous_aabb` | **no** |
| predictive mass positive | `counterexample` | yes |

The bundled statement is `counterexample`, and the non-sufficiency theorem is
`sourceObstruction_not_sufficient_for_readOnly_certainty`.  Together with the
attributed necessity, `sourceObstruction_not_exact_condition` records that the
obstruction is not the exact condition.

## Bounded computational evidence

[`scripts/verify_272_bresler_obstruction.py`](../scripts/verify_272_bresler_obstruction.py)
independently re-derives the witness and exhaustively searches every same-length
binary model with genome length `G ≤ 7` and `L < G` for observations that carry
no obstruction yet are ambiguous.  It confirms that the gap is not an isolated
artifact of the chosen witness (several length-`4` models already exhibit it).
This is **bounded evidence, not a theorem** (the search's completeness is not
proved).

## Relation to the merged #272 objects

* `I_s` (`isPromiseReadString`) is the merged **sufficient** condition; its
  sufficiency is the external Not-So-Greedy premise
  ([`FiniteSideInformationReadStringAdapter.lean`](../AssemblyP1/FiniteSideInformationReadStringAdapter.lean),
  `sufficient_readStringIS_of_fibreUnique`), not proved here.
* [`FiniteIsNotNecessaryCertainty.lean`](../AssemblyP1/FiniteIsNotNecessaryCertainty.lean)
  (PR #384) showed `I_s` is **not necessary** for read-only certainty.  The
  present module is the complementary fact about the *source obstruction*: it is
  necessary (attributed) but not sufficient.  Neither `I_s` nor the
  all-unbridged obstruction is the exact condition.
* The merged `Unambiguous` / `posteriorMass` / `Realizable` objects and the
  repeat/bridging layer are imported and reused unchanged; nothing is redefined
  or reproved.  No `#266` / `#269` / `#271` object is touched.

## Remaining open cases

1. **The exact necessary-and-sufficient condition in source terms.** The
   read-only certainty set is exactly `Unambiguous` (merged target 3).  Whether
   `Unambiguous` admits a purely repeat-bridging characterization strictly
   between the source obstruction and `I_s` is not claimed here; the exhaustive
   search only bounds it for `G ≤ 7`, binary alphabet.
2. **Algorithm-specific necessity for the literal 2016 Not-So-Greedy decoder.**
   OPEN; requires formalizing the external algorithm, exactly as recorded in
   [`source-notes/issue272-is-necessity.md`](source-notes/issue272-is-necessity.md).
