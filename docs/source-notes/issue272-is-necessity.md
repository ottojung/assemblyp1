# Issue #272 subclaim (1): is `I_s` necessary for decoder-level certainty?

_Status: 2026-10-21. Source-level analysis with a kernel-checked counterexample.
Companion Lean module:
[`AssemblyP1/FiniteIsNotNecessaryCertainty.lean`](../../AssemblyP1/FiniteIsNotNecessaryCertainty.lean),
audited by
[`AssemblyP1/FiniteIsNotNecessaryCertaintyAudit.lean`](../../AssemblyP1/FiniteIsNotNecessaryCertaintyAudit.lean),
with the independent computational cross-check
[`scripts/verify_272_is_necessity.py`](../../scripts/verify_272_is_necessity.py)._

## The question

The merged order results
([`FiniteReadStringIsVsUnambiguous`](../../AssemblyP1/FiniteReadStringIsVsUnambiguous.lean),
PR #356) show that the Shomorony--Kim--Courtade--Tse (2016) information-feasibility
predicate `I_s` is **sufficient** and that it is incomparable with the read-only
promise `Unambiguous`. They say nothing about **necessity**. This note determines,
at the source level, whether `I_s` is necessary for **decoder-level certainty**:

> If a read-only decoder is certain on a positive-probability observation, must
> the truth genome satisfy `I_s`?

## The determination

**`I_s` is sufficient but NOT necessary for decoder-level certainty.** There is a
positive-predictive observation at which a read-only decoder is certain, produced
by a truth genome that fails `I_s`. The counterexample is minimal and kernel-checked.

The failure is on the **all-bridged triple-repeat clause** (and independently on
the historical-coverage clause), and it is exactly the gap between the source's
*own* necessity theorem and `I_s`: Bresler--Bresler--Tse (2013) Theorem 1 forces a
competing same-likelihood genome only when **all** copies of a problematic triple
repeat are unbridged, whereas `I_s` requires **every** copy to be bridged. A
maximal triple repeat with *some but not all* copies bridged is therefore outside
the reach of the published necessity obstruction while still failing `I_s`.

## Explicit hypotheses (candidate universe, read model, truth)

The counterexample lives in the same finite read model the merged adapter uses, so
nothing is smuggled in through a change of convention:

* **Orientation.** Oriented circular reads (no reverse-complement collapse),
  matching the 2016 single-strand model; the genome equivalence is **cyclic
  rotation** (the merged canonical rotation code `orbit`).
* **Genome length.** Candidates have the **same length `G`** as the truth, over the
  **same finite alphabet** (here the two-symbol alphabet `Bit = Fin 2`). This is
  the finite same-length slice the repository already uses for the `I_s`-versus-
  `Unambiguous` decision; it is stated as a hypothesis rather than assumed silently.
* **Read model.** A fixed common read length `L` with `2 ≤ L ≤ G`; a set `R` of
  sampled start positions induces the **distinct read-string set**
  `observedTypes_ofFinset S L R` (the source's deduplication preprocessing; see
  [`ConditionalIdentifiability`](../../AssemblyP1/ConditionalIdentifiability.lean) §7).
* **Observation.** The read-string set `Y = Finset (Fin L → Bit)`.
* **Likelihood.** The read-realizable **support indicator** `p w Y = 1` iff some
  start set induces exactly `Y` (`Realizable3`), the support of any faithful read
  likelihood; only its positivity enters certainty. Prior `π ≡ 1`.
* **`I_s`.** The literal historical predicate
  `HistoricalInformationFeasibleLiteral` (the §6.4 coverage + all-bridged
  three-occurrence + bridged-interleaved clauses), read through the merged
  read-string adapter `isPromiseReadString`.

## The counterexample

Genome `AAAB` (length `4`), read length `L = 3`, sampled starts `R = {0, 2}`.
Induced read-string set

```
Y = {AAA, ABA}.
```

**`I_s` fails.** Historical coverage holds, and the length-`1` word `A` occurs at
the three distinct starts `{0, 1, 2}` — a literal three-occurrence repeat, indeed
a *maximal* triple repeat (preceding symbols `B, A, A` and following symbols
`A, A, B` are each non-constant). At read length `3` a read bridges a length-`1`
copy only from the immediately preceding start; among the match starts `{0, 2}`
only start `0` bridges the middle copy at `1`. So the triple is not all-bridged and
`I_s` fails. Kernel endpoints: `coverage_holds`, `triple_occurrence`,
`triple_not_allBridged`, `not_isPromise_aaab`.

**A read-only decoder is certain.** The read-realizable support of `Y` is exactly
the four rotations of `AAAB`: a length-`4` binary circle with both `AAA` and `ABA`
as length-`3` windows has exactly one `B`, forced to sit so that the circle is
`AAAB` up to rotation (`realizable_orbit`, `unambiguous_yaaab`). Hence `Y` is
`Unambiguous`, so by the merged target-3 characterization
(`exists_readOnly_decoder_certain_iff_support_singleton`,
[`FiniteReadOnlyDecoderCertainty`](../../AssemblyP1/FiniteReadOnlyDecoderCertainty.lean),
PR #345) some read-only decoder reaches posterior one at `Y`
(`some_readOnly_decoder_certain`).

The two facts are packaged as `counterexample` and as the negation
`is_not_necessary_for_readOnly_certainty`, which states outright that no theorem
of the form "read-only certainty implies `I_s`" can hold on this model.

| fact | kernel endpoint | value at `(AAAB, 3, {0,2})` |
|---|---|---|
| read-string set | `Yaaab` | `{AAA, ABA}` |
| historical coverage holds | `coverage_holds` | yes |
| triple occurrence `A` at `{0,1,2}` | `triple_occurrence` | yes (maximal) |
| triple all-bridged | `triple_not_allBridged` | **no** |
| `I_s` (`isPromiseReadString`) | `not_isPromise_aaab` | **fails** |
| every realizer is a rotation | `realizable_orbit` | yes (4 rotations) |
| read-only decoder certain | `some_readOnly_decoder_certain` | **yes** |
| predictive mass positive | `predictive_pos_yaaab` | yes |

## Source-level reconciliation with the 2016 / 2013 theorems

Attribution is explicit; the external theorems are **not** formalized here.

1. **`I_s` is sufficient (2016, Theorem 1; Bresler et al. 2013, Theorem 6).**
   Shomorony et al. Eq. (1) inherits the MultiBridging conditions of Bresler et al.
   (coverage; all triple repeats all-bridged; interleaved pairs bridged) and proves
   the Not-So-Greedy construction recovers the truth up to cyclic shift. This is
   the attributed sufficient condition, unchanged.
2. **The published necessity is strictly weaker for triple repeats (2013,
   Theorem 1).** Bresler et al. show that if a problematic **interleaved pair or
   triple repeat has all of its copies unbridged**, then there is another sequence
   of the same length with the same read likelihood. For **interleaved pairs**,
   `I_s`'s "bridged" clause is the exact complement of "all copies unbridged", so
   that clause of `I_s` is tight against the source necessity theorem. For
   **triple repeats**, `I_s` demands *all* copies bridged, while the necessity
   theorem only forbids *all* copies unbridged. The gap is a triple repeat with
   **some-but-not-all** copies bridged — precisely the counterexample above, whose
   middle copy is bridged and whose outer copies are not.
3. **Consequence.** `I_s` is *not* the necessary condition for unambiguous
   read-only recovery; the true necessary condition is strictly weaker on triple
   repeats (and, as the coverage-clause witnesses show, the §6.4 interval-coverage
   condition is also not necessary). The repository already records this gap
   qualitatively in
   [`literature-status.md`](../literature-status.md) §3; the present module makes
   it concrete and kernel-checked.

## Scope and trust boundary

* **Information-theoretic / read-only-decoder level (settled here).** "Decoder
  certainty" is the exact target-3 notion (some read-only decoder reaches
  posterior one). At this level the determination is definitive: `I_s` is not
  necessary. The proof is unconditional over the stated finite model; the only
  imported result is the merged target-3 characterization.
* **The specific 2016 Not-So-Greedy algorithm (OPEN).** The algorithm is **not**
  formalized in this repository — it remains the attributed external premise in
  [`ConditionalIdentifiability`](../../AssemblyP1/ConditionalIdentifiability.lean).
  Whether the *particular* Not-So-Greedy decoder happens to be correct on
  non-`I_s` inputs is an algorithmic question outside the kernel boundary and
  stays **OPEN**. This module asserts nothing about it. (For the concrete witness
  the length-`(L-1)` read-overlap graph is disconnected, so the witness does not
  automatically transfer to the algorithm; a transfer would require formalizing
  the algorithm and its graph construction.)

## Bounded computational evidence

[`scripts/verify_272_is_necessity.py`](../../scripts/verify_272_is_necessity.py)
independently re-derives the witness and exhaustively searches every same-length
model with alphabet size `k ≤ 3`, genome length `G ≤ 7`, and `L < G`, recording
each certainty-holding `I_s` failure by the clause that fails first:

| failing clause of `I_s` | certainty-holding counterexamples found |
|---|---|
| historical coverage | 19383 |
| all-bridged triple repeat | 31704 |
| bridged interleaved pair | **0** |

This is **bounded evidence, not a theorem** (the search's completeness is not
proved). It is consistent with the source analysis: the interleaved clause is the
one tight against Bresler et al.'s necessity theorem, while the triple clause and
the historical-coverage clause are not necessary. The first triple-clause witness
found is exactly the kernel-checked `(AAAB, L = 3, R = {0,2})`.

## Relation to the merged `Y = {AA, BB}` direction-2 witness

The merged
[`unambiguous_not_imp_isPromiseRS`](../../AssemblyP1/FiniteReadStringIsVsUnambiguous.lean)
already exhibits a length-`4`, `L = 2` observation `{AA, BB}` that is `Unambiguous`
while the realizer `BBAA` fails `I_s` (on historical coverage). Read as a
necessity statement it is also a counterexample to `I_s` necessity; the present
module adds the `L = 3` **triple-clause** witness, which is the one that speaks
directly to the Bresler all-unbridged-versus-all-bridged gap, and packages the
negation of necessity explicitly (`is_not_necessary_for_readOnly_certainty`).

## No duplication

* `FiniteBayesianSideInformation` (`Unambiguous`, `jointMass`, `predictiveMass`,
  `posteriorMass`, `posteriorMass_eq_one_iff`) is imported and reused unchanged.
* `FiniteReadOnlyDecoderCertainty` (PR #345) is imported and reused unchanged; the
  target-3 characterization is applied, not re-proved.
* `FiniteSideInformationReadStringAdapter` (PR #297) and `HistoricalCovers` are
  imported and reused unchanged.
* `FiniteReadStringIsVsUnambiguous` (PR #356) is imported for the rotation code
  `orbit`, `Sp4`, `toGenome4`; its results are not restated.
* `#266` (`ConditionalIdentifiability`) and `#269` (`FiniteBayesDecision`) cores
  are neither imported nor modified. No general ML result is touched.

## Remaining open cases

1. **Algorithm-specific necessity for the literal Not-So-Greedy decoder.** OPEN;
   requires formalizing the algorithm (graph construction, Eulerian spelling) so
   that "the decoder is correct on this input" becomes a kernel-checkable
   proposition. The existing `AAAB`, `L = 3`, `Y = {AAA, ABA}` certainty witness
   has two disconnected components in the usual oriented de Bruijn graph
   (`AA → AA` and `AB → BA`), so it does not establish what the historical
   decoder does. See the bounded diagnostic
   [`issue272-next-open-slice.md`](../issue272-next-open-slice.md). This instance's
   algorithmic behavior remains OPEN until the source's domain and disconnected
   input handling are established; no counterexample to the decoder is claimed.
2. **Exact necessary condition.** The source necessity theorem (all-unbridged)
   and `I_s` (all-bridged) leave a strict gap on triple repeats. Whether the exact
   necessary-and-sufficient condition for same-length orbit certainty is
   "coverage ∧ no all-unbridged triple ∧ no all-unbridged interleaved pair" is not
   claimed; the exhaustive search only bounds it for `G ≤ 7`, `k ≤ 3`.
