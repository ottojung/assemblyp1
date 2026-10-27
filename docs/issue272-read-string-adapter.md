# The literal read-string adapter for the read-dependent `I_s` family (#272)

This note records the Lean module
[`AssemblyP1/FiniteSideInformationReadStringAdapter.lean`](../AssemblyP1/FiniteSideInformationReadStringAdapter.lean)
(axiom audit
[`AssemblyP1/FiniteSideInformationReadStringAdapterAudit.lean`](../AssemblyP1/FiniteSideInformationReadStringAdapterAudit.lean)),
which discharges the first of the two obligations left OPEN by the merged
`#272` modules
[`FiniteBayesianSideInformation`](../AssemblyP1/FiniteBayesianSideInformation.lean),
[`FiniteSideInformationOrder`](../AssemblyP1/FiniteSideInformationOrder.lean),
[`FiniteSideInformationSourcePromise`](../AssemblyP1/FiniteSideInformationSourcePromise.lean)
and the ordering module
[`FiniteSideInformationOrdering`](../AssemblyP1/FiniteSideInformationOrdering.lean).

## 1. The placement/string gap, and the adapter

The source event `I_s(S, R)` of Shomorony--Kim--Courtade--Tse (2016) is a
property of the candidate genome `S` **and the sampled start set** `R`, whereas
the observed data are read *strings*.  Reading the promise as a function of a
single observation type therefore silently conflates the latent placement with
the observed string (the gap analysed in
[`ConditionalIdentifiability`](../AssemblyP1/ConditionalIdentifiability.lean),
#266).  The adapter resolves the typing:

```
isPromiseReadString S L Y  :=
  ∃ R : Finset (Fin S.len),
    observedTypes_ofFinset S L R = Y ∧ HistoricalInformationFeasibleLiteral S L R
```

The observation type is the distinct read-string set `Finset (Fin L → α)`; the
placement-level source predicate `HistoricalInformationFeasibleLiteral` (the
literal §6.4 predicate of
[`HistoricalCovers`](../AssemblyP1/HistoricalCovers.lean)) is **marginalised
over the placements `R` compatible with `Y`**, i.e. those inducing exactly the
observed string set.  This is the joint property of candidate and observation
that #266 requires, not a property of either alone.

## 2. The adapter is genuinely read-dependent

`ReadDependence` proves, on a concrete length-`4` model over the four-symbol
alphabet `Base`, that the adapter promise is neither read-only nor truth-only:

- `spellABCG_promises_Yall` — `ABCG` promises its full read-string set
  `{AB, BC, CG, GA}`.  `ABCG` has pairwise distinct symbols, so it has no repeat
  at all: the triple and interleaved bridging clauses of `I_s` are vacuous while
  string coverage is saturated.
- `spellAAAA_not_promises_Yall` — `AAAA` cannot promise `{AB, BC, CG, GA}`:
  every window of `AAAA` is `AA`, so no start set induces that four-element set.
- `spellABCG_not_promises_Yone` — `ABCG` cannot promise the singleton `{AB}`:
  the only start set inducing `{AB}` is `{0}`, where historical coverage fails.
- `not_readOnly` / `not_truthOnly` / `readDependent` — the promise is a function
  of neither the observation alone nor the candidate alone, so it lies **outside
  both** `AdmReadOnly` (the merged read-only family) and `AdmTruthOnly` (the
  #262 source-property family).

## 3. Applying the union criterion to the read-dependent `I_s` family

The family `AdmReadStringIS` is the set of promises pointwise equivalent to the
adapter (`AdmReadStringIS n L hn E ↔ ∀ w Y, E w Y ↔ isPromiseReadStringSpelling …`).
It is closed under logical equivalence (`admReadStringIS_congr`), so the merged
family-relative criterion applies:

- `unionAdmissible_readStringIS_iff` — the union of all admissible sufficient
  promises is the adapter itself, **provided the adapter is sufficient**.
- `weakest_readStringIS_iff_sufficient` — a weakest admissible sufficient
  promise exists **iff** the adapter promise is sufficient.  This is the exact
  reduction of `weakest_admissible_iff_union` to the external premise.
- `sufficient_readStringIS_of_fibreUnique` / `weakest_readStringIS_of_fibreUnique`
  — feasible-fibre uniqueness of the adapter (the published Not-So-Greedy
  guarantee, an attributed premise, not proved here) implies sufficiency and
  hence existence of the weakest promise.  This is the merged
  `fibreUnique_of_decoder` / `conditional_certain_of_fibreUnique` chain
  instantiated on the read-string adapter.

## 4. `I_s` necessity obstructions

The three clauses of the literal historical `I_s` are each necessary:

- `historicalLiteral_coverage` — historical coverage is necessary.
- `historicalLiteral_tripleBridged` — every literal three-occurrence repeat is
  all-bridged.
- `historicalLiteral_interleavedBridged` — every interleaved pair of repeats is
  bridged.

The triple-bridging clause cannot be dropped.  The concrete witnesses
`ABXABYABZ` and `ABXABZABY` (length `9`, read length `4`, sampled starts
`{0, 3, 6}`) each carry the length-`2` repeat `AB` as a maximal triple occurrence
at starts `0, 3, 6` (`IsTripleRepeat`, `IsTripleOccurrence`), historical coverage
holds, but no length-`4` read straddles any copy (`abxab_not_allBridged`,
`abxabz_not_allBridged`); hence `HistoricalInformationFeasibleLiteral` fails
(`abxab_not_feasible`, `abxabz_not_feasible`, bundled in
`unbridged_triple_witness`).  The two witnesses differ in the flanking symbols
(`X,Y,Z` vs `X,Z,Y`), showing the obstruction is robust across contexts.

## 5. What remains OPEN

1. **`I_s` necessity for the specific Not-So-Greedy decoder.** Whether the
   source predicate `I_s` is necessary for the *particular* 2016 decoder (as
   opposed to sufficient for certainty via the external guarantee) remains OPEN
   and is a source-level question.  Nothing here asserts the external theorem;
   the decoder guarantee enters only as the attributed `fibreUnique` premise.
2. **Ordering of `I_s` against `Unambiguous`.** The adapter is now a well-typed
   single-observation-type promise and is read-dependent (§2), but no implication
   `I_s ⇒ Unambiguous` or `Unambiguous ⇒ I_s` is claimed: sufficiency alone does
   not order promises (merged `Incomparable.sufficient_promises_incomparable`).
3. **A concrete decoder-level certainty endpoint.** LANDED (see §6): the
   kernel-checked endpoint
   [`AssemblyP1.FiniteSideInformationDecoderEndpoint.lean`](../AssemblyP1/FiniteSideInformationDecoderEndpoint.lean)
   takes a read-only decoder `A` on the read-string observation type, attributes
   the published Not-So-Greedy correctness guarantee to it as an explicit
   hypothesis `hA` (`IsCorrectReadStringDecoder`), derives feasible-fibre
   uniqueness via the merged `fibreUnique_of_decoder`, and concludes that the
   conditional posterior on the true orbit class equals one via
   `conditional_certain_of_fibreUnique`.  The external guarantee remains an
   attributed premise (not proved here); what is kernel-checked is the exact
   decoder-to-certainty bridge on the literal adapter.

## 6. The concrete decoder-level certainty endpoint

`AssemblyP1/FiniteSideInformationDecoderEndpoint.lean` (axiom audit
`FiniteSideInformationDecoderEndpointAudit.lean`) supplies the endpoint whose
absence the earlier status rows recorded.  The external guarantee is stated as
the hypothesis, not asserted:

```
IsCorrectReadStringDecoder hn orbit A :=
  ∀ w Y, isPromiseReadStringSpelling n L hn w Y → orbit (A Y) = orbit w
```

| statement | status | theorem |
|---|---|---|
| Correct decoder ⇒ adapter fibre uniqueness | kernel-checked | `fibreUnique_readStringIS_of_decoder` |
| Correct decoder ⇒ adapter sufficient | kernel-checked | `sufficient_readStringIS_of_decoder` |
| Correct decoder ⇒ weakest admissible sufficient promise exists | kernel-checked | `weakest_readStringIS_of_decoder` |
| Correct decoder ⇒ conditional posterior on true orbit = 1 | kernel-checked | `conditional_certain_readStringIS_of_decoder` |
| Bundled weakest-existence and pointwise certainty | kernel-checked | `weakest_and_certain_readStringIS_of_decoder` |

The correctness hypothesis `hA` is the published Shomorony--Kim--Courtade--Tse
(2016) Not-So-Greedy guarantee, attributed and not proved; it is
hypothesis-essential (deleting it makes the proof fail to typecheck).  Every
endpoint depends only on `propext`, `Classical.choice`, `Quot.sound`.

See also
[`issue272-side-information-order.md`](issue272-side-information-order.md),
[`issue272-is-vs-unambiguous-ordering.md`](issue272-is-vs-unambiguous-ordering.md),
and
[`issue272-finite-bayesian-side-information.md`](issue272-finite-bayesian-side-information.md).

## 7. Scope of the concrete alignment

The adapter is aligned at the **event/fibre** level: its observation is a set of
distinct read strings, and its promise at `(w,Y)` holds exactly when at least one
latent start set `R` induces `Y` on `w` and satisfies the literal source predicate
`I_s(w,R)`.  Thus the kernel-checked implication from `IsCorrectReadStringDecoder`
to `conditional_certain_readStringIS_of_decoder` applies to the same observation
and event fibre; it does not replace that event by `I_s(w,R)` at one unobserved
placement.

This alignment is intentionally **not** a fully specified random-read
likelihood.  In particular, `Y` is a `Finset` and forgets repeated read
multiplicities, while the adapter existentially quantifies compatible start
sets rather than summing their sampling probabilities.  The decoder endpoint
allows an arbitrary nonnegative `p w Y`; its conditional posterior conclusion is
valid for every such likelihood satisfying its hypotheses, but no source-faithful
finite sampling law or normalized prior/likelihood is instantiated by this
module.  The theorem names establish an exact conditional bridge on the aligned
fibre under the attributed decoder-correctness premise, not the published
algorithmic theorem in Lean and not a new concrete assembly-model bridge.
