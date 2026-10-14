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
| Not-So-Greedy `I_s` ⇒ posterior one | external premise + the above bridge | §6 below |
| Minimal source-defined bridging promise | **OPEN** | §7 |

All Lean results are proved with `autoImplicit` disabled and audited by
`AssemblyP1/FiniteBayesianSideInformationAudit.lean`; the only axioms are the
three permitted ones (`propext`, `Classical.choice`, `Quot.sound`).

## 1. Setup and notation

Fix finite types:

- `Genome`, the finite candidate set;
- `Obs`, the finite read sample space `X`;
- `Θ`, the finite set of circular-rotation **orbit classes**;
- `orbit : Genome → Θ`, mapping each candidate to its rotation class.

A normalized prior `π : Genome → ℝ` (`0 ≤ π`, `∑ π = 1`) and a generative
likelihood `p : Genome → Obs → ℝ` (`0 ≤ p g r`, `∑_r p g r = 1`) describe the
experiment `G ∼ π`, `R | G = g ∼ p_g`. The extra information is a
**truth-dependent promise** `E : Genome → Obs → Prop` (possibly depending on the
unknown truth `g`), or an observed **side channel** `Z` with `q : Genome → Obs →
Aux → ℝ`.

The joint mass used for inference is

```
jointMass π p E g r = π g · p_g(r) · 1_E(g,r),
predictiveMass π p E r = ∑_g jointMass π p E g r,
posteriorMass π p E orbit r θ = (∑_{g : orbit g = θ} jointMass π p E g r) / predictiveMass π p E r.
```

The indicator `1_E(g,r)` is part of the joint mass: the **prior and the
likelihood are both conditioned on `E`** by dividing by `predictiveMass`. No step
assumes `E` is a function of `R` alone.

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
| Arbitrary fibre-unique `F` (separates confusable orbits) | posterior one given `E = F` | sufficient and **strictly weaker** than `I_s`; read-unambiguous is the weakest such promise |
| Read-unambiguous (`Unambiguous`) | posterior one given `E = Unambiguous`; the unique weakest read-only promise | sufficient, read-only, independent of `I_s` |

**Consequence.** `I_s` is a *sufficient* structural certificate, not a necessary
condition for certainty: there exist sufficient truth-dependent promises
strictly weaker than `I_s` (read-unambiguous is one, §5), so `I_s` is not
necessary for posterior singleton. The original necessity/sufficiency
statements remain attributed to the source.

## 7. Genuinely open cases

1. **Minimal source-defined bridging promise.** Whether there is a weakest
   sufficient promise within the family of *source-defined* predicates (e.g.
   minimal bridging sets built only from observed read strings), as opposed to
   arbitrary or read-only promises, is OPEN. The counterexample of §5 rules out
   an intrinsic least event for the full family; the source-defined subfamily is
   not covered by either the negative or the positive result.
2. **`I_s` necessity for the specific algorithm.** Whether `I_s` is necessary
   for the *particular* Not-So-Greedy decoder (as opposed to for any read-only
   decoder) is OPEN and is a source-level question.
3. **Concrete AssemblyP1 endpoint.** A kernel-checked instantiation of
   `conditional_certain_of_fibreUnique` on the full historical read-string model
   requires the external guarantee; the abstract bridge is proved, the concrete
   endpoint remains attributed/open.

## 8. Decision table

```
                                    read-only        promise E        side channel Z
certain at r (posterior = 1)?       support ⊆ orbit  E-support ⊆ orbit support(R,Z) ⊆ orbit
weakest sufficient object?          Unambiguous      none (only minimal)  --
tie/zero-prior corner               excluded from support; no effect
a.s. vs pointwise                   equal (ae_certain_iff_pointwise)
must be supplied (not inferred)?    --               yes                yes
```
