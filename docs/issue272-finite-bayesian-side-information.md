# Issue #272: weakest side information for certain finite Bayesian recovery

_Status: 2026-10-14. Mathematical formalization front. Extends the support-only
`#164` abstraction (`AssemblyP1/FiniteSideInformationColoring.lean`) with
priors, generative likelihoods, and an exact posterior theorem. Companion Lean
module: [`AssemblyP1/FiniteBayesianSideInformation.lean`](../AssemblyP1/FiniteBayesianSideInformation.lean)._

## Epistemic status

| Component | Status | Where |
|---|---|---|
| Exact posterior-iff theorem for a promise event `E` | kernel-checked, no `sorry`/`axiom` | `posteriorMass_eq_one_iff` |
| Excluded-competitor form | kernel-checked | `posteriorMass_eq_one_iff_excluded` |
| Side-channel `Z` singleton-fibre form | kernel-checked | `posteriorMassZ_eq_one_iff` |
| a.s. vs pointwise equivalence | kernel-checked | `ae_certain_iff_pointwise` |
| Read-only vs promise separation, supplied-not-inferred | kernel-checked example | `TwoCandidate.side_information_needed` |
| Weakest read-only promise exists and is unique | kernel-checked | `unambiguous_unique_weakest_readonly` |
| No weakest truth-dependent promise (counterexample) | kernel-checked | `NoWeakest.no_weakest_sufficient` |
| Decoder-correctness ⇒ fibre uniqueness ⇒ posterior one | kernel-checked | `fibreUnique_of_decoder`, `conditional_certain_of_fibreUnique` |
| Two sufficient promises are incomparable (no ordering from sufficiency) | kernel-checked example | `Incomparable.sufficient_promises_incomparable` |
| Not-So-Greedy `I_s` ⇒ posterior one | external premise + the above bridge | §6 below |
| Minimal source-defined bridging promise | **iff `∀ r, Unambiguous`**; weakest = `True`, unique | [`FiniteSourceDefinedWeakest.lean`](../AssemblyP1/FiniteSourceDefinedWeakest.lean) §7 |

All Lean results are proved with `autoImplicit` disabled and audited by
`AssemblyP1/FiniteBayesianSideInformationAudit.lean`; the only axioms are the
three permitted ones (`propext`, `Classical.choice`, `Quot.sound`).

## 1. Setup and notation

Fix finite types:

- `Genome`, the finite candidate set;
- `Obs`, the finite read sample space `X`;
- `Θ`, the finite set of circular-rotation **orbit classes**;
- `orbit : Genome → Θ`, mapping each candidate to its rotation class.

A prior `π : Genome → ℝ` (`0 ≤ π`, optionally normalized `∑ π = 1`) and a
generative likelihood `p : Genome → Obs → ℝ` (`0 ≤ p g r`, optionally normalized
`∑_r p g r = 1`) describe the experiment `G ∼ π`, `R | G = g ∼ p_g`. The extra
information is a **truth-dependent promise** `E : Genome → Obs → Prop` (possibly
depending on the unknown truth `g`), or an observed **side channel** `Z` with
`q : Genome → Obs → Aux → ℝ`.

The joint mass used for inference is

```
jointMass π p E g r = π g · p_g(r) · 1_E(g,r),
predictiveMass π p E r = ∑_g jointMass π p E g r,
posteriorMass π p E orbit r θ = (∑_{g : orbit g = θ} jointMass π p E g r) / predictiveMass π p E r.
```

The indicator `1_E(g,r)` is part of the joint mass: the **prior and the
likelihood are both conditioned on `E`** by dividing by `predictiveMass`. No step
assumes `E` is a function of `R` alone.

**Normalization is an interpretation assumption, not a hypothesis of the
algebra.** Every theorem below uses only `0 ≤ π` and `0 ≤ p` (plus strict
positivity on the support of the fibre); it never uses `∑_g π g = 1`, `∑_r p_g(r)
= 1`, or `∑_z q_g(z|r) = 1`. Those normalizations are needed only to *read* `π`,
`p`, `q` as a prior, a likelihood, and a conditional pmf. The posterior-iff
criterion and the fibre-uniqueness bridge are statements about the unnormalized
masses `π g · p_g(r) · 1_E(g,r)` and hold with or without normalization.

## 2. The exact necessary-and-sufficient theorem

**Theorem (kernel-checked, `posteriorMass_eq_one_iff`).** Let `0 ≤ π`, `0 ≤ p`,
fix `r : Obs` with `predictiveMass π p E r > 0`, and fix `θ : Θ`. Then

```
posteriorMass π p E orbit r θ = 1
  ↔ ∀ h, 0 < π h → 0 < p h r → E h r → orbit h = θ.
```

Equivalently (`posteriorMass_eq_one_iff_excluded`), for the true class
`orbit g`,

```
posteriorMass π p E orbit r (orbit g) = 1
  ↔ ∀ h, 0 < π h → 0 < p h r → orbit h ≠ orbit g → ¬ E h r.
```

**Reading.** The conditional posterior is one exactly when the **supported
truth-fibre** `{h : π h > 0, p_h(r) > 0, E(h,r)}` is contained in a single
orbit class. The promise is *necessary* only on that fibre: candidates with zero
prior (`jointMass_eq_zero_of_prior_zero`) or zero read likelihood are irrelevant.

**Tie / zero-prior corner cases.** Because the statement is an iff for arbitrary
nonnegative `π`, `p`, it holds in the zero-prior and zero-likelihood corners:
those candidates simply do not enter the support. The positive-predictive-mass
hypothesis `predictiveMass > 0` is what rules out the degenerate `0/0` case.

## 3. Side channels

For a side channel `Z` with joint mass `π g · p_g(r) · q_g(z|r)`
(`jointMassZ`), the same argument gives

```
posteriorMassZ π p q orbit r z θ = 1
  ↔ ∀ h, 0 < π h → 0 < p h r → 0 < q h r z → orbit h = θ,
```

i.e. **the supported fibre of `(R, Z)` is a single orbit class**
(`posteriorMassZ_eq_one_iff`). This is the "supported fibre of `(R,Z)` is
singleton" formulation requested in #272.

## 4. Read-only certainty vs a supplied promise

Without any promise (`E ≡ True`), `readOnly_posterior_eq_one_iff` gives

```
posteriorMass π p (fun _ _ => True) orbit r θ = 1
  ↔ ∀ h, 0 < π h → 0 < p h r → orbit h = θ.
```

So a read-only decoder is certain at `r` iff the **read support alone** already
collapses to one orbit. The promise strictly enlarges the set of observations on
which certainty is possible, but it must be **supplied**. The smallest witness is
kernel-checked:

> `TwoCandidate.side_information_needed`: two equally likely candidates, one
> read. The read-only posterior on the true class is `1/2 ≠ 1`, the truth
> satisfies `E = (g = 0)`, and `posteriorMass π p E orbit r (orbit 0) = 1`.

Thus one may **not** infer `E` from `R`, and may not drop the conditioning: the
event `E = F(G,R)` is a joint property of truth and reads. This is the same
"truth-dependent event, not merely `R`" caveat as #266, now with the exact
posterior criterion attached.

## 5. Weakest conditioning

Order promises by implication: `E₁` is at least as strong as `E₂` when
`Stronger E₁ E₂` (`E₁ ⇒ E₂`). A promise is **sufficient** when conditioning on it
gives posterior one for every positive-probability truth (`Sufficient`, the
structural fibre condition of §2).

- **No weakest truth-dependent promise.** In a four-candidate, two-read model
  with confusability pairs `{0,1}` and `{2,3}` and distinct orbits, two
  sufficient promises `E1`, `E2` that each select one member of each pair are
  incomparable, and any promise containing both is insufficient. Hence no
  sufficient promise contains every sufficient promise
  (`NoWeakest.no_weakest_sufficient`): **there is no weakest / least informative
  sufficient truth-dependent promise.** (This mirrors, in the promise rather than
  label-partition setting, the `#164` "no common sufficient coarsening" result.)
- **Weakest read-only promise exists and is unique.** Among promises depending
  only on `r`, define `Unambiguous π p orbit r := ∀ g h, (positive prior and
  likelihood at r) → orbit g = orbit h`. Then `Unambiguous` is sufficient, and
  every sufficient read-only promise implies it
  (`unambiguous_unique_weakest_readonly`). So the read-only family has a genuine
  **minimum**, while the full truth-dependent family has only **minimal**
  elements and no minimum.

**Sufficiency does not order promises.** Sufficiency is a property of each
promise on its own; it does **not** by itself imply any inclusion between two
sufficient promises. In particular the read-only minimum `Unambiguous` is the
weakest member of the *read-only* family only, and it is **not shown** to be
ordered against arbitrary truth-dependent sufficient promises — nor is the
source `I_s` predicate (§6). A kernel-checked witness
(`Incomparable.sufficient_promises_incomparable`) exhibits two sufficient
promises that are genuinely incomparable on the positive support of a **fully
normalized** model (`∑ π = 1`, `∑_r p_g(r) = 1`): with `E(g,r) = (g = 0 ∧ r =
0)`, `E` holds at the positive pair `(0,0)` where `Unambiguous(0)` fails, so `E`
does not imply `Unambiguous`; and `Unambiguous` holds at read `1` (only
candidate `0` has positive likelihood there) while `E 0 1` fails at the positive
pair `(0,1)`, so `Unambiguous` does not imply `E`. Any claim that one sufficient
promise is weaker than another therefore needs a separate proof and is not a
consequence of sufficiency.

This is the precise "minimum vs minimal" distinction #272 asks for: an intrinsic
least *event* does not exist for arbitrary promises, but it does once the family
is restricted to read-only structural predicates.

## 6. Comparison with Shomorony et al. (2016)

Attribution is explicit: the Not-So-Greedy theorem/corollary of Shomorony et al.
is an **external premise**, not formalized here. Write `F(g,r)` for the exact
2016 read-*string* information-feasibility predicate `r ∈ I_g` (see
[`docs/source-notes/shomorony-ml-reference.md`](source-notes/shomorony-ml-reference.md)
and [`AssemblyP1/HistoricalCovers.lean`](../AssemblyP1/HistoricalCovers.lean)),
and let `A(r)` be the deterministic read-only reconstruction the source
supplies.

**Bridge (kernel-checked).** If `A` is correct on the `F`-support, i.e.
`∀ g r, F g r → orbit (A r) = orbit g`, then

```
fibreUnique_of_decoder : ∀ g h r, F g r → F h r → orbit g = orbit h,
conditional_certain_of_fibreUnique : posteriorMass π p F orbit r (orbit g) = 1
```

for any `0 ≤ π`, `0 ≤ p` and any positive-probability truth with `F g r`. This is
the exact #266 chain, now stated with probabilities and the posterior-iff
criterion. **Only the implication is proved here; the hypothesis is the published
guarantee.**

| Property | Implication for posterior singleton | Status / scope |
|---|---|---|
| `I_s` holds for the truth (coverage + bridged interleaved + triple repeats) | posterior one given `E = I_s`, via the external Not-So-Greedy guarantee + `conditional_certain_of_fibreUnique` | sufficient; external premise; same orientation, `2 ≤ L ≤ G`, observed read multiplicities, fixed candidate universe |
| Absence of a repeat-bridging obstruction | necessary for read-only certainty (else two orbits share the read support) | necessary only; formalized abstractly by §4, not as the 2016 predicate |
| Arbitrary fibre-unique `F` (separates confusable orbits) | posterior one given `E = F` | sufficient; **no ordering against `I_s` follows from sufficiency** (incomparable in general, §5) |
| Read-unambiguous (`Unambiguous`) | posterior one given `E = Unambiguous`; unique weakest **read-only** promise | sufficient, read-only; **not shown to be weaker or stronger than `I_s`** |

Here ``E = I_s`` means the event is actually included in the observation or
promise being conditioned on. Knowing only that the realized truth/read pair
satisfies `I_s(g,r)` does not change the read-only posterior: the event
indicator must occur in the conditioned joint law (or its information must be
reported by a side channel). In particular, the second row is an obstruction
to *read-only* certainty, not a claim that conditioning on an unobserved
truth-dependent event is available.

**Consequence.** `I_s` is a *sufficient* structural certificate. Sufficiency alone
does **not** establish that `I_s` is necessary, nor that it is the strongest or
the weakest sufficient promise: the ordering between `I_s` and other sufficient
promises (read-only or arbitrary truth-dependent) is not determined by the
posterior-iff theorem and is left OPEN (§7). The original necessity/sufficiency
statements remain attributed to the source.

## 7. Genuinely open cases

1. **Minimal source-defined bridging promise.** RESOLVED by
   [`AssemblyP1/FiniteSourceDefinedWeakest.lean`](../AssemblyP1/FiniteSourceDefinedWeakest.lean):
   for the source-defined family (promises built only from the observed read
   or only from the truth), a weakest sufficient promise exists **iff**
   `∀ r, Unambiguous π p orbit r`; when it exists, the weakest is `True`,
   unique up to equivalence.  On the ambiguous `TwoCandidate` model, the
   family has no weakest sufficient promise.
2. **`I_s` necessity for decoder-level certainty.** RESOLVED (negative) at the
   read-only-decoder level by
   [`AssemblyP1/FiniteIsNotNecessaryCertainty.lean`](../AssemblyP1/FiniteIsNotNecessaryCertainty.lean)
   (`is_not_necessary_for_readOnly_certainty`): a kernel-checked `L = 3` witness
   (`AAAB`, `R = {0,2}`, `Y = {AAA, ABA}`) fails the all-bridged-triple clause of
   `I_s` while a read-only decoder is certain at `Y`. **Algorithm-specific**
   necessity for the literal 2016 Not-So-Greedy decoder is OPEN (the algorithm is
   not formalized; it is the attributed external premise). See
   [`docs/source-notes/issue272-is-necessity.md`](source-notes/issue272-is-necessity.md).
3. **Concrete AssemblyP1 endpoint.** A kernel-checked instantiation of
   `conditional_certain_of_fibreUnique` on the full historical read-string model
   requires the external guarantee; the abstract bridge is proved, the concrete
   endpoint remains attributed/open.
4. **Ordering among sufficient promises.** Whether `I_s` implies, is implied by,
   or is incomparable with the read-only `Unambiguous` promise or with arbitrary
   truth-dependent sufficient promises is OPEN. Sufficiency alone yields no
   ordering, and `Incomparable.sufficient_promises_incomparable` shows two
   sufficient promises can be incomparable, so no such ordering may be assumed.

**Addendum (2026-10-14, `AssemblyP1/FiniteSideInformationOrder.lean`).** The
*existence and uniqueness* question behind items 3–4 is now settled at the level
of the promise order, without touching the posterior theorem: a weakest
sufficient promise exists **iff** the union of all sufficient promises is itself
sufficient (`weakest_iff_union`), and when it exists it is unique up to logical
equivalence (`weakest_unique`); the same criterion holds inside any
equivalence-closed structural family (`weakest_admissible_iff_union`). The
read-only family satisfies it with weakest member `Unambiguous`
(`unambiguous_isWeakest_readonly`), while the full truth-dependent family does
not (`NoWeakestProb.unionAllSufficient_not_sufficient`). The `I_s`-specific
   ordering of item 4, the necessity of item 2, and the concrete historical
   adapter of item 3 all remain OPEN. The source-defined weakest promise of
   item 1 is RESOLVED by
   [`AssemblyP1/FiniteSourceDefinedWeakest.lean`](../AssemblyP1/FiniteSourceDefinedWeakest.lean).
   See
   [`docs/issue272-side-information-order.md`](issue272-side-information-order.md)
   for the precise reduction and status.

## 8. Decision table

```
                                    read-only        promise E        side channel Z
certain at r (posterior = 1)?       support ⊆ orbit  E-support ⊆ orbit support(R,Z) ⊆ orbit
weakest sufficient object?          Unambiguous      none (only minimal)  --
tie/zero-prior corner               excluded from support; no effect
a.s. vs pointwise                   equal (ae_certain_iff_pointwise)
must be supplied (not inferred)?    --               yes                yes
```
