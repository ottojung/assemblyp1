# Issue #272, target 3: read-only decoder certainty and supplied side information

_Status: 2026-10-18. Mathematical formalization front. Answers target 3 of #272
(certainty achievable by a read-only decoder, versus certainty given a supplied
truth-dependent promise) and records a bounded target-4 increment (minimum versus
weakest sufficient promise). Companion Lean module:
[`AssemblyP1/FiniteReadOnlyDecoderCertainty.lean`](../AssemblyP1/FiniteReadOnlyDecoderCertainty.lean),
axiom-audited by
[`AssemblyP1/FiniteReadOnlyDecoderCertaintyAudit.lean`](../AssemblyP1/FiniteReadOnlyDecoderCertaintyAudit.lean)._

This document does **not** re-derive the posterior-iff theorem. It reuses the
merged exact posterior semantics `π(g)·p_g(r)·1_E(g,r)` of
[`AssemblyP1/FiniteBayesianSideInformation.lean`](../AssemblyP1/FiniteBayesianSideInformation.lean)
(PR #195) and the promise-order results of
[`AssemblyP1/FiniteSideInformationOrder.lean`](../AssemblyP1/FiniteSideInformationOrder.lean)
(PR #204) and
[`AssemblyP1/FiniteSideInformationOrdering.lean`](../AssemblyP1/FiniteSideInformationOrdering.lean)
(PR #244) unchanged.

## The theorem

A **read-only decoder** is a map `A : Obs → Genome` guessing the truth from the
observed read alone.  Write `posteriorMass π p (fun _ _ => True) orbit r (orbit (A r))`
for its conditional success on the orbit class of its guess at read `r` (the
trivial promise `E ≡ True` is the absence of side information).

**Theorem (`exists_readOnly_decoder_certain_iff_support_singleton`,
kernel-checked).**

```
(∃ A : Obs → Genome,
    posteriorMass π p (fun _ _ => True) orbit r (orbit (A r)) = 1)
  ↔ Unambiguous π p orbit r ∧ ∃ g, 0 < π g ∧ 0 < p g r
```

i.e. **some read-only decoder is certain at `r` iff the supported truth-fibre of
`r` is nonempty and lies in a single orbit class.**  The two halves are:

- `readOnly_decoder_certain_implies_unambiguous` — the "only when" direction: no
  read-only decoder can manufacture certainty the read alone does not already
  provide.  If any decoder reaches posterior one at `r`, the positive-prior,
  positive-likelihood candidates at `r` already share one orbit class.
- the reverse direction: if the support is a single nonempty orbit class, pick
  any positive candidate and output its orbit; the merged
  `readOnly_posterior_eq_one_iff` then gives posterior one.

`readOnly_predictive_pos_iff` records that the nonempty conjunct is exactly the
positive predictive mass `0 < predictiveMass π p (fun _ _ => True) r`.

## Certainty table

```
                                        posterior = 1 achievable at r?
read-only decoder (no side information)  iff Unambiguous r and support nonempty
                                        (theorem above)
supplied promise E, E holds at truth     iff the E-supported fibre lies in one orbit
                                        (merged posteriorMass_eq_one_iff)
side channel Z                           iff the supported fibre of (R, Z) is one orbit
                                        (merged posteriorMassZ_eq_one_iff)
```

The read-only row is the exact boundary: `readOnly_certain_set_eq_weakest` pairs
the theorem with the merged `unambiguous_isWeakest_readonly`, so the set of reads
at which *any* read-only decoder can be certain is exactly the weakest admissible
sufficient read-only promise `Unambiguous`.  Nothing weaker suffices, nothing
stronger is needed.

## "The side information must actually be supplied"

`admReadOnly_iff_factorable` makes "inferable from the read" a theorem:

```
AdmReadOnly E  ↔  ∃ φ : Obs → Prop, ∀ g r, E g r ↔ φ r
```

A promise can be evaluated from `R = r` alone exactly when it is read-only.
`truthDependent_not_factorable` is the contrapositive: a truth-dependent promise
(`¬ AdmReadOnly E`) is **not** a function of the observation, so it is genuine
extra information that must be supplied, never inferred.

`TwoCandidateDecoder.side_information_must_be_supplied` instantiates this on the
merged two-candidate model:

- `no_readOnly_decoder_certain` — no read-only decoder is certain at the
  ambiguous read `0` (both candidates have positive likelihood and distinct
  orbits);
- `promise_certain` (merged) — the *supplied* truth-dependent promise
  `E = (g = 0)` gives posterior one;
- `twoCandidate_E_not_admReadOnly` — that `E` is not read-only, so it is supplied
  rather than inferred.

## Minimum versus weakest sufficient promise (target 4, bounded)

The order convention is `Stronger E₁ E₂` iff `E₁ ⇒ E₂` (stronger = more
informative), so the **minimum** sufficient promise is the strongest event and
the **weakest** is the largest event.

- `IsMinimumSufficient` / `empty_isMinimumSufficient` — the empty promise is a
  minimum sufficient promise (sufficient vacuously, implies everything).
- `minimum_exists_unique` — a minimum sufficient promise exists in every model
  and is unique up to logical equivalence.
- `weakest_isMaximal` — a weakest (maximum) sufficient promise, when it exists,
  is maximal.
- `minimum_without_weakest` — on the merged `NoWeakestProb` model a minimum
  exists but no weakest does (reusing `NoWeakestProb.no_weakest_sufficient`).

The trivial minimum must therefore not be confused with a genuine weakest (least
informative) sufficient promise: the minimum is the uninformative empty event,
whereas the weakest is the meaningful extremum whose existence is characterized
by the merged `weakest_iff_union` / `weakest_admissible_iff_union`.

## Epistemic status

| Component | Status | Where |
|---|---|---|
| Read-only decoder certainty iff singleton supported fibre | kernel-checked | `exists_readOnly_decoder_certain_iff_support_singleton` |
| Necessary half ("only when") | kernel-checked | `readOnly_decoder_certain_implies_unambiguous` |
| Read-only certainty set = weakest read-only promise | kernel-checked | `readOnly_certain_set_eq_weakest` |
| Inferable-from-read iff read-only (factorization) | kernel-checked | `admReadOnly_iff_factorable`, `truthDependent_not_factorable` |
| Concrete "supplied, not inferred" instance | kernel-checked | `TwoCandidateDecoder.side_information_must_be_supplied` |
| Minimum sufficient promise exists and is unique | kernel-checked | `minimum_exists_unique` |
| Minimum without weakest on `NoWeakestProb` | kernel-checked | `minimum_without_weakest` |
| Decoder-level certainty on the literal read-string `I_s` adapter | **OPEN** | attributed external premise; see below |

Every endpoint depends only on the three permitted axioms (`propext`,
`Classical.choice`, `Quot.sound`); no `sorry`, `admit`, `axiom`, or
`native_decide` is used.

## What remains OPEN (unchanged)

1. **`I_s` necessity for the specific Not-So-Greedy decoder.** Source-level, OPEN;
   see
   [`issue272-side-information-order.md`](issue272-side-information-order.md) §6.
2. **Ordering of `I_s` against `Unambiguous`.** Still **neither** at the promise
   level; the read-dependent literal adapter is
   [`AssemblyP1/FiniteSideInformationReadStringAdapter.lean`](../AssemblyP1/FiniteSideInformationReadStringAdapter.lean)
   (see [`issue272-read-string-adapter.md`](issue272-read-string-adapter.md)).
3. **Decoder-level certainty endpoint on the read-string `I_s` family.** The
   abstract bridge `sufficient_readStringIS_of_fibreUnique` /
   `weakest_readStringIS_iff_sufficient` reduces it to the external 2016
   Not-So-Greedy guarantee, which remains an attributed premise; nothing here
   proves it.

## Relationship to sibling fronts (no duplication)

- **#266** owns the latent-placement / conditional-identifiability core; this
  module only reuses the merged read-string adapter by name.
- **#269** (`AssemblyP1/FiniteBayesDecision.lean`) owns finite MAP/zero-one
  optimality; not duplicated here.
- The merged `#272` modules are imported and their `Sufficient`, `Stronger`,
  `Unambiguous`, `AdmReadOnly`, `IsWeakestSufficient`, and `NoWeakestProb`
  objects are reused unchanged.
