# Issue #272: the read-string `I_s` adapter versus `Unambiguous` — kernel-checked incomparability

_Status: 2026-10-19 (bounded increment; `I_s`-vs-`Unambiguous` ordering now
kernel-checked at the adapter level). Mathematical formalization front.
Companion Lean module:
[`AssemblyP1/FiniteReadStringIsVsUnambiguous.lean`](../AssemblyP1/FiniteReadStringIsVsUnambiguous.lean),
audited by
[`AssemblyP1/FiniteReadStringIsVsUnambiguousAudit.lean`](../AssemblyP1/FiniteReadStringIsVsUnambiguousAudit.lean).
Extends, without duplicating, the merged modules
[`FiniteBayesianSideInformation`](../AssemblyP1/FiniteBayesianSideInformation.lean)
(PR #195, `b0a6e9f`),
[`FiniteSideInformationOrder`](../AssemblyP1/FiniteSideInformationOrder.lean)
(PR #204, `c312cbbc`),
[`FiniteSideInformationOrdering`](../AssemblyP1/FiniteSideInformationOrdering.lean)
and the literal read-string adapter
[`FiniteSideInformationReadStringAdapter`](../AssemblyP1/FiniteSideInformationReadStringAdapter.lean)
(PR #297)._

## The question

[`issue272-is-vs-unambiguous-ordering.md`](issue272-is-vs-unambiguous-ordering.md)
left the ordering of the **read-dependent** source-faithful `I_s` promise against
the read-only `Unambiguous` promise **OPEN** once the literal read-string adapter
made the question well typed. The earlier verdict ("neither") was structural: it
argued that `I_s` is truth-dependent and `Unambiguous` is read-only, so they live
in different promise families, and that sufficiency alone never orders a
truth-dependent promise against `Unambiguous`. What was missing was a
kernel-checked *decision on the adapter itself*: does `I_s ⇒ Unambiguous`, does
`Unambiguous ⇒ I_s`, or neither, on positive-probability read-string
observations?

## The answer

**Neither**, now kernel-checked on the merged literal read-string adapter by
concrete finite read-realizable models. The reason the two directions both fail
is that the two promises constrain **different fibres**:

* `Unambiguous π p orbit Y` constrains the **read-realizable support** of `Y`:
  every candidate `g` that can produce the observed read-string set `Y`
  (`p g Y > 0`) lies in a single rotation class. The model takes the
  read-realizable support likelihood `p g Y = 1` iff some start set on `g`
  induces exactly `Y`; this is the support of any faithful read likelihood, and
  only its positivity enters `Unambiguous`.
* `isPromiseReadString S L Y` constrains the **`I_s`-feasible fibre** of `Y`:
  some placement `R` on `S` induces `Y` **and** satisfies the literal historical
  `I_s` (`HistoricalInformationFeasibleLiteral`).

A candidate can be read-realizable without being `I_s`-feasible, so the fibres
differ and each direction fails.

| statement | status | theorem |
|---|---|---|
| `ABAB` is `I_s`-promising at `Y = {AB, BA}` | kernel-checked | `isPromiseRS_abab_yabba` |
| `ABAB` and `AABB` both realize `Y = {AB, BA}`, in different orbits | kernel-checked | `realizable_abab_yabba`, `realizable_aabb_yabba`, `orbit_aabb_ne_abab` |
| Two different-orbit realizers refute `Unambiguous` | kernel-checked | `not_unambiguous_of_two_orbit_realizers` |
| **Direction 1** `I_s ⇏ Unambiguous` | **REFUTED** | `isPromiseRS_not_imp_unambiguous` |
| Direction-1 competitor `AABB` is realizable but **not** `I_s`-feasible | kernel-checked | `not_isPromiseRS_aabb_yabba` |
| Every realizer of `Y = {AA, BB}` is a rotation of `AABB` | kernel-checked | `realizable_yaabb_orbit` |
| `Y = {AA, BB}` is `Unambiguous` | kernel-checked | `unambiguous_yaabb` |
| `BBAA` is not `I_s`-promising at `Y = {AA, BB}` | kernel-checked | `not_isPromiseRS_bbaa_yaabb` |
| **Direction 2** `Unambiguous ⇏ I_s` | **REFUTED** | `unambiguous_not_imp_isPromiseRS` |
| Both observations have positive predictive probability | kernel-checked | `predictive_pos_yabba`, `predictive_pos_yaabb` |
| **Verdict: incomparable ("neither")** | kernel-checked | `isPromiseRS_unambiguous_incomparable` |

All endpoints depend only on `propext`, `Classical.choice`, `Quot.sound`
(`#print axioms` audit); no `sorry`, `admit`, `axiom`, or `native_decide`.

## 1. The model

A candidate is a length-`4` circular spelling over `Bit = Fin 2`; the observation
is the distinct read-string set `Finset (Fin 2 → Bit)`. The rotation class is
represented by the canonical rotation code `orbit g = min` of the base-`2`
encoding over the four rotations (`orbit_rot` records invariance). The prior is
uniform (`π ≡ 1`) and the likelihood is the read-realizable support indicator
`p g Y = 1` iff `Realizable g Y`, `0` otherwise.

## 2. Direction 1: `I_s` does not imply `Unambiguous`

The period-`2` genome `ABAB` (length `4`, read length `2`) is `I_s`-feasible at
the start set `{0,1}`: it has no maximal repeat and no triple occurrence, while
historical coverage is saturated; the induced read-string set is `Y = {AB, BA}`.
But `Y` is read-realizable by `14` genomes spanning `4` rotation classes — in
particular by `ABAB` and by `AABB` (`R = {1,3}`), which are in different orbits.
So `I_s` holds at `(ABAB, Y)` while `Unambiguous Y` fails.

This is a genuine refutation of the natural expectation "information-feasible
reads pin the orbit": the **literal historical `I_s` is not sufficient for
orbit-pinning in the read-realizable model**. It does **not** contradict the
external Shomorony--Kim--Courtade--Tse (2016) Not-So-Greedy guarantee, because
that guarantee constrains the `I_s`-**feasible** fibre
([`ConditionalIdentifiability.feasible_fibre_unique`](../AssemblyP1/ConditionalIdentifiability.lean)),
not the read-realizable fibre: the direction-1 competitor `AABB` is
read-realizable but **not** `I_s`-feasible (`not_isPromiseRS_aabb_yabba`), so no
feasible-fibre uniqueness is violated.

## 3. Direction 2: `Unambiguous` does not imply `I_s`

For `Y = {AA, BB}`, realizing both `AA` and `BB` on a length-`4` binary circle
forces an adjacent `00` pair and an adjacent `11` pair, hence the genome is a
rotation of `AABB`; the read-realizable support is exactly the four rotations of
`AABB` (`realizable_yaabb_orbit`), a single rotation class, so `Unambiguous`
holds. But the realizer `BBAA` is not `I_s`-promising at `Y`: its only placement
`{0,2}` fails historical coverage (position `1` is not within `L-1 = 1` of a
matching start).

## 4. Reconciliation with the external Not-So-Greedy premise

The verdict "neither" is exactly the statement that `Unambiguous` (a
read-realizable-support property) and `I_s` (a feasible-fibre property) are
different, incomparable constraints. The external 2016 decoder guarantee remains
an attributed premise and is neither asserted nor needed here. Nothing in this
module formalizes the source algorithm.

## 5. What remains genuinely OPEN

1. **`I_s` necessity for the specific 2016 Not-So-Greedy decoder.** Still OPEN
   and source-level; the order results here do not address it.
2. **Weakest source-defined bridging promise.** Still reduced by
   `weakest_admissible_iff_union` to whether the union of source-defined
   sufficient promises is itself source-defined and sufficient. OPEN.
3. **Decoder-level certainty endpoint.** Requires the external Not-So-Greedy
   guarantee; remains an attributed premise.

## 6. No duplication

* `FiniteBayesianSideInformation` (`Sufficient`, `Unambiguous`, `predictiveMass`,
  `jointMass`) is imported and reused unchanged.
* `FiniteSideInformationReadStringAdapter` (`isPromiseReadString`,
  `isPromiseReadStringSpelling`) is imported and reused unchanged; the module
  defines only a local concrete-model alias `isPromiseRS` with the bridge
  `isPromiseRS_iff_spelling : isPromiseRS w Y ↔ isPromiseReadStringSpelling 4 2 _ w Y`.
* The `FiniteReadStringIsVsUnambiguous` model (`Sp4`, `Realizable`, `p`, `orbit`)
  is new and does not modify any merged object. `#266`
  (`ConditionalIdentifiability`) and `#269` (`FiniteBayesDecision`) cores are
  neither imported nor modified.
