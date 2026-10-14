# Issue #272: the order of sufficient side-information promises

_Status: 2026-10-14. Mathematical formalization front. Extends the exact
posterior semantics of
[`AssemblyP1/FiniteBayesianSideInformation.lean`](../AssemblyP1/FiniteBayesianSideInformation.lean)
(merged as `b0a6e9f`) with a general, kernel-checked characterization of when a
**weakest** (least informative) sufficient promise exists and whether it is
unique. Companion Lean module:
[`AssemblyP1/FiniteSideInformationOrder.lean`](../AssemblyP1/FiniteSideInformationOrder.lean)._

This document does **not** re-derive the posterior-iff theorem; it reuses the
merged `Sufficient` / `Stronger` / `Unambiguous` objects unchanged and adds only
order-theoretic results. The exact posterior semantics
`π(g)·p_g(r)·1_E(g,r)` (conditioning the prior **and** the likelihood on the
supplied promise `E`) are inherited verbatim from the merged module.

## Epistemic status

| Component | Status | Where |
|---|---|---|
| Sufficiency invariant under logical equivalence | kernel-checked | `sufficient_congr` |
| Sufficiency downward-closed under strengthening | kernel-checked | `sufficient_of_stronger` |
| Empty promise is sufficient (trivial strongest event) | kernel-checked | `sufficient_false`, `false_strongest` |
| Conjunction of sufficient promises is sufficient | kernel-checked | `sufficient_and` |
| Nonempty pointwise conjunction of sufficient promises is sufficient | kernel-checked | `sufficient_iInter` |
| Weakest sufficient exists **iff** the union of all sufficient promises is sufficient | kernel-checked | `weakest_iff_union` |
| Weakest sufficient promise is unique up to equivalence | kernel-checked | `weakest_unique` |
| Family-relative existence/ uniqueness inside an equivalence-closed `Adm` | kernel-checked | `weakest_admissible_iff_union`, `weakest_admissible_unique` |
| Read-only family: unique weakest is `Unambiguous` | kernel-checked | `unambiguous_isWeakest_readonly`, `weakest_readonly_exists`, `weakest_readonly_unique` |
| Full truth-dependent family: no weakest (union insufficient) | kernel-checked | `NoWeakestProb.no_weakest_sufficient`, `NoWeakestProb.unionAllSufficient_not_sufficient` |
| Sufficiency is **not** closed under binary union | kernel-checked | `NoWeakestProb.union_e1_e2_not_sufficient` |
| `I_s` necessity for the specific Not-So-Greedy decoder | **OPEN** | §6 |
| Ordering of `I_s` against `Unambiguous` / arbitrary sufficient promises | **OPEN** | §6 |
| Weakest sufficient inside the source-defined bridging subfamily | **OPEN** (reduced to a concrete criterion) | §6 |

All results are proved with `autoImplicit` disabled and audited by
[`AssemblyP1/FiniteSideInformationOrderAudit.lean`](../AssemblyP1/FiniteSideInformationOrderAudit.lean);
every endpoint depends only on the three permitted axioms (`propext`,
`Classical.choice`, `Quot.sound`). No `sorry`, `admit`, or `axiom` is used.

## 1. The promise order

`Stronger E₁ E₂` (merged definition) means `E₁` implies `E₂`, i.e. `E₁` is the
stronger, more informative promise. It is a preorder (`Stronger.refl`,
`Stronger.trans`), and mutual implication is pointwise logical equivalence
(`stronger_antisymm`). A promise is **sufficient** (`Sufficient`, merged) when
conditioning on it makes the posterior on every positive-probability true orbit
equal to one — equivalently, when its positive joint-mass fibre is contained in
a single orbit class.

"**Weakest**" is the least informative sufficient promise: the *largest* event
among sufficient promises. The opposite extreme, the *strongest* event, always
exists trivially — the empty promise is sufficient (`sufficient_false`) and is
implied by everything (`false_strongest`) — but it supplies no information, so
the meaningful question is whether the **weakest** sufficient promise exists.

## 2. Sufficiency is a meet-semilattice

Two closure facts, both kernel-checked:

- **Downward closure.** If `E'` is sufficient and `E` is stronger than `E'`
  (`E ⇒ E'`), then `E` is sufficient (`sufficient_of_stronger`). Shrinking a
  sufficient promise keeps it sufficient. Hence the weakest sufficient promise,
  if it exists, is the largest sufficient event.
- **Conjunction.** The pointwise conjunction of two sufficient promises is
  sufficient (`sufficient_and`), and more generally the pointwise conjunction of
  a nonempty family of sufficient promises is sufficient (`sufficient_iInter`).

Sufficiency is therefore a **meet-semilattice** of promises.  It is *not* closed
under union: `NoWeakestProb.union_e1_e2_not_sufficient` exhibits two sufficient
promises on a fully specified finite model whose disjunction is insufficient.
The read-only family is the exception: it is closed under arbitrary unions,
because its total union is `Unambiguous` (`unionReadOnly_eq_unambiguous`), which
is itself sufficient (`unambiguous_sufficient`), and sufficiency is downward
closed.

## 3. When does a weakest sufficient promise exist?

Define the pointwise union of every sufficient promise

```
unionAllSufficient π p orbit g r := ∃ E, Sufficient π p orbit E ∧ E g r.
```

This is the largest event implied by any sufficient promise, hence the only
candidate for a weakest sufficient promise.

**Theorem (`weakest_iff_union`, kernel-checked).**

```
Sufficient π p orbit (unionAllSufficient π p orbit)
  ↔ ∃ W, Sufficient π p orbit W ∧ ∀ E, Sufficient π p orbit E → Stronger E W.
```

The forward direction is the union itself; the reverse identifies any weakest
sufficient promise with the union up to logical equivalence. Consequently a
weakest sufficient promise exists exactly when the disjunction of all sufficient
promises is again sufficient.

**Theorem (`weakest_unique`, kernel-checked).** Any two weakest sufficient
promises are pointwise logically equivalent. There is at most one weakest
sufficient promise up to equivalence.

This is the precise "minimum vs minimal" answer: the *minimum* (strongest,
empty) sufficient event always exists but is trivial, while the *weakest*
(maximum) sufficient event exists only under the union criterion above, and when
it does it is unique up to equivalence.

## 4. The criterion inside a structural family

For a family `Adm` of allowed (e.g. source-shaped) promises that is closed under
logical equivalence, define

```
unionAdmissible Adm π p orbit g r := ∃ E, Adm E ∧ Sufficient π p orbit E ∧ E g r.
```

**Theorem (`weakest_admissible_iff_union`, kernel-checked).**

```
(Adm (unionAdmissible Adm π p orbit) ∧ Sufficient π p orbit (unionAdmissible Adm π p orbit))
  ↔ ∃ W, IsWeakestAdmissible Adm π p orbit W,
```

with `IsWeakestAdmissible Adm W := Adm W ∧ Sufficient W ∧ ∀ E, Adm E → Sufficient E → Stronger E W`.
Uniqueness inside `Adm` is `weakest_admissible_unique`.

This reduces the source-level "weakest source-defined bridging promise" question
to a single concrete obligation: *is the union of all source-defined sufficient
promises itself a source-defined sufficient promise?* (Still OPEN, §6.)

## 5. Read-only family (criterion holds) vs full family (criterion fails)

**Read-only family (`AdmReadOnly`): a weakest exists.** Let `AdmReadOnly` be the
promises that do not depend on the unknown truth `g`, only on the observed read
`r` — the abstract form of a read-only structural side channel. Then
(`unionReadOnly_eq_unambiguous`) the union of all sufficient read-only promises
is exactly `Unambiguous`, and (`unambiguous_isWeakest_readonly`) `Unambiguous` is
the unique weakest admissible sufficient promise:

```
IsWeakestAdmissible AdmReadOnly π p orbit (fun _ r => Unambiguous π p orbit r).
```

So the read-only family satisfies the union criterion; its weakest sufficient
member is the merged `Unambiguous` (`weakest_readonly_exists`,
`weakest_readonly_unique`). This is a genuine **minimum**, not merely a minimal
element.

**Full truth-dependent family: no weakest exists.** On the merged `NoWeakest`
finite model (four candidates, two reads, confusability pairs `{0,1}` and
`{2,3}`, distinct orbits), realized by the unnormalized weights `π ≡ 1` and
`p g r = 1_{S(g,r)}`, `Sufficient` coincides with the merged support-restricted
`SufficientOn` (`NoWeakestProb.sufficient_iff_sufficientOn`). Hence the merged
counterexample transfers:

- `NoWeakestProb.no_weakest_sufficient` — no weakest sufficient promise exists;
- `NoWeakestProb.unionAllSufficient_not_sufficient` — the union of all
  sufficient promises is itself insufficient, so the criterion of §3 fails;
- `NoWeakestProb.union_e1_e2_not_sufficient` — two sufficient promises with an
  insufficient disjunction;
- `NoWeakestProb.order_failure_bundle` — the combined failure statement.

This is the requested small counterexample establishing that arbitrary
truth-revealing promises make "weakest side information" vacuous; the
meaningful structural restriction is the read-only (and, more generally,
equivalence-closed admissible) family.

## 6. Remaining open cases

1. **`I_s` necessity for the specific Not-So-Greedy decoder.** Whether the
   source predicate `I_s` is necessary for the *particular* 2016 decoder (as
   opposed to sufficient for certainty via the external guarantee) is OPEN and a
   source-level question. The order results here say nothing about it: `I_s` is
   one admissible promise, and sufficiency of one promise does not order it
   against another (§2, and the merged `Incomparable.sufficient_promises_incomparable`).
2. **Ordering of `I_s` against `Unambiguous` / arbitrary sufficient promises.**
   OPEN. Sufficiency alone imposes no ordering; the merged incomparability
   example (two normalized, positive-support sufficient promises that do not
   imply each other) is the kernel-checked obstruction to assuming one. No new
   implication is claimed here.
3. **Weakest source-defined bridging promise.** OPEN, but now reduced by
   `weakest_admissible_iff_union` to the single question of whether the union of
   all source-defined sufficient promises is itself source-defined and
   sufficient. The negative full-family result of §5 shows this cannot be
   discharged for the unrestricted family; the source-defined subfamily is not
   covered by either the negative or the positive result.
4. **Concrete historical read-string adapter.** OPEN. A kernel-checked
   instantiation of the posterior bridge on the full historical read-string
   model requires the external Not-So-Greedy guarantee; the abstract bridge is
   proved in the merged module, and the concrete endpoint remains attributed.
   This module adds no historical adapter.

## 7. Relationship to sibling fronts (no duplication)

- **#266** (conditional identifiability; branch
  `agent/67d2b06729ed-issue266-conditional-identifiability`, not merged) owns the
  conditional-identifiability / latent-placement core (`ReadModel`,
  `PlacementModel`, `placementJoint`). This module does **not** import or
  reprove any of it: its results are about the *lattice of promises*, not about
  the posterior theorem or the placement-weighted event mass.
- **#269** (`AssemblyP1/FiniteBayesDecision.lean`, merged) owns finite
  MAP/zero-one optimality. Not duplicated here.
- The merged `#272` module `AssemblyP1/FiniteBayesianSideInformation.lean` is
  imported and its `Sufficient`, `Stronger`, `Unambiguous`, and `NoWeakest`
  objects are reused unchanged.

## 8. Decision table

```
                                read-only (AdmReadOnly)   arbitrary truth-dependent
weakest sufficient exists?      yes (= Unambiguous)        iff union is sufficient
unique up to equivalence?       yes                        yes (when it exists)
strongest (empty) sufficient?   yes, trivial               yes, trivial
closed under conjunction?       yes                        yes
closed under union?             yes (union = Unambiguous)   no
```

The general criterion `weakest_iff_union` / `weakest_admissible_iff_union` is the
manuscript-ready answer to the "weakest conditioning" question of #272.
