# Conditional identifiability from the Not-So-Greedy information-feasibility guarantee

_Status: 2026-10-14. Mathematical front for issue #266. Readable
theorem/proof/caveat for issue #265 to incorporate. The read-instance bridge
(Finset decoder versus the source's sampled read instances) is closed by the
duplicate-invariance adapter of §7._

## Epistemic status and trust boundary

- **External premise (source fact, not proved here).** The Not-So-Greedy
  theorem/corollary of Shomorony, Kim, Courtade, and Tse (2016),
  *Bioinformatics* 32(17):i494–i502, <https://doi.org/10.1093/bioinformatics/btw450>,
  guarantees that under the information-feasibility condition `I_s` a
  deterministic read-only reconstruction recovers the true circular genome up
  to cyclic shift. This is a cited external result. It is **not** formalized in
  this repository and is used below only as an explicit hypothesis.
- **Kernel-checked mathematics (this work).** The consequences in §2–§5 —
  feasible-fibre uniqueness, conditional posterior certainty, the constrained-MAP
  statement, the class-mass bound, and the latent-placement weighted-mass
  adapter — are proved from the external premise plus finite real algebra in
  `AssemblyP1/ConditionalIdentifiability.lean`. They introduce no `axiom`,
  `sorry`, or `admit`; the module's `#print axioms` output shows only Lean's
  three standard axioms (`feasible_fibre_unique` depends on none). The decoder
  interface of §6 is **not** formalized: it is a prose adapter whose correctness
  reduces to the external premise `(NSG)`.
- **Source-theorem choice.** The deterministic reconstruction used here is the
  **Corollary 1** statement (a graph with a *unique* Eulerian cycle spelling the
  truth up to rotation), not the weaker **Theorem 1** (existence of *some*
  Chinese-Postman cycle). Theorem 1 alone does not yield a read-only decoder or
  a unique compatible genome; see §7. This matches the primary-source checkpoint
  recorded on the board for #266.

## 1. Setup and notation

### 1.1 Observation model

Fix the candidate universe `Θ` (circular words of a fixed genome length `G`
over an alphabet), the read length `L`, the orientation convention, and the
rotation equivalence `≈` (cyclic shift for oriented reads; see §7 for the
reverse-complement molecule-class variant). An **observation** `r` is the data
the decoder is allowed to see — the observed read **strings**, i.e. the
historical read-string content, not the latent sampled positions.

### 1.2 Feasibility and the decoder

Let

- `F(g, r)` be the source-faithful information-feasibility predicate
  (`r ∈ I_g`), and
- `A(r)` be the deterministic read-only reconstruction supplied by the source
  theorem.

The published guarantee, taken as an external premise, is

```
∀ g r,  F(g, r)  →  A(r) ≈ g.        (NSG)
```

In the repository this is stated against the real §6.4 definitions as
`HistoricalEvent S L R := HistoricalCovers.HistoricalInformationFeasibleLiteral S L R`,
with the observation `observedTypes_ofFinset S L R` (the set of distinct
read strings) and `A : Finset (Fin L → α) → Genome α`. This decoder interface
is **not** a strengthening of the cited result: the manuscript explicitly
deduplicates read instances before assembly — "since the reads in `R` are
assumed to be all distinct from each other (which can be achieved by a
preprocessing step)" (author-hosted manuscript, §3.2, PDF p. 12) — its vertex
set is the set of distinct read strings `R = {st(v) : v ∈ V}`, and both the
§6.4 feasibility conditions and the §6.3 edge multiplicities are functions of
that set. §7 makes the deduplication adapter kernel-explicit. The remaining
trust boundary is the source guarantee `hNSG` itself (the algorithm is not
formalized), not the read-instance encoding; the source length/model
restrictions are recorded in `SourceRegime`.

## 2. Theorem 1 — feasible-fibre uniqueness

**Statement.** For all `g, h, r`, if `F(g, r)` and `F(h, r)` then `g ≈ h`.

**Proof.** From `F(g, r)` and `(NSG)`, `A(r) ≈ g`; from `F(h, r)` and `(NSG)`,
`A(r) ≈ h`. Symmetry and transitivity of `≈` give `g ≈ h`. ∎

Lean: `ReadModel.feasible_fibre_unique`, and for the real §6.4 predicate
`historical_feasible_fibre_unique`.

**Interpretation.** A fixed observation cannot be information-feasible for two
genomes in different rotation classes. This is uniqueness of the *feasible
fibre* `{g : F(g, r)}`, **not** uniqueness of ordinary maximum-likelihood
estimation over all candidates. The two are logically independent.

## 3. Theorem 2 — conditional posterior certainty

**Statement.** Let `J(g, r) = π(g) · P_g(r)` be any unnormalized joint mass
(prior times a valid generative finite-read likelihood), and let
`K(g, r) := J(g, r) · 1_{F(g,r)}` be its restriction to the truth-dependent
event `E := F(G, R)`. Then for every `r` with positive conditional mass
`∑_g K(g, r) > 0`,

```
P([G] = [A(r)] | R = r, E) = 1,
```

where `[·]` is the rotation class.

**Proof.** For any `g`, if `K(g, r) ≠ 0` then `F(g, r)` holds, so `(NSG)` gives
`A(r) ≈ g`, i.e. `g ∈ [A(r)]`. Hence the total conditional mass equals the mass
of the class `[A(r)]`:

```
∑_g K(g, r) = ∑_{g : g ≈ A(r)} K(g, r).
```

Dividing by the positive denominator gives `1`. ∎

Lean: `ReadModel.orbit_mass_eq_total` and
`ReadModel.conditional_posterior_eq_one`.

**Critical caveat.** The conditioning event is `E = F(G, R)`, a joint property
of the *unknown truth* and the reads. It is generally **not** a function of `r`
alone. Without conditioning on `E`, the posterior `P([G] = [A(r)] | R = r)` can
be strictly below `1`, because an infeasible competitor `h` with `P_h(r) > 0`
can explain the same reads. This is conditional identifiability, not
unconditional identifiability, and not a sample-wise maximum-likelihood
guarantee.

## 4. Theorem 3 — constrained MAP

**Statement.** Any maximizer `g*` of the constrained joint mass
`π(g) P_g(r) 1_{F(g,r)}` with positive value lies in `[A(r)]`, regardless of the
relative likelihoods.

**Proof.** If the constrained mass at `g*` is positive then `F(g*, r)` holds, so
`(NSG)` gives `A(r) ≈ g*`. The constraint alone pins the class; the likelihood
values never enter. ∎

Lean: `ReadModel.constrained_MAP_mem_orbit`.

**Distinctions.**

- *Ordinary MAP/ML* maximizes `π(g) P_g(r)` with no constraint. A competitor
  `h` with `¬ F(h, r)` and `P_h(r) > 0` has **zero** constrained mass
  (`ReadModel.infeasible_eventJoint_eq_zero`) but can have strictly larger
  ordinary mass. The concrete two-point witness `Example.ordinary_ML_prefers_infeasible`
  / `Example.constrained_kills_infeasible` exhibits exactly this: ordinary mass
  `2` versus `1` for the infeasible competitor, constrained mass `0` versus `1`.
- *Naive conditioning on `F`* would replace the prior by
  `P_g(F) = ∑_r P_g(r) 1_{F(g,r)}` and use `P_g(r | F)`. That is a different
  quantity; the correct constrained procedure restricts the **joint** mass and
  leaves the relative prior/likelihood structure intact inside the fibre.

## 5. Theorem 4 — no rule beats the decoder on `E`

**Statement.** For any reported class `c`, its conditional mass
`∑_{g : g ≈ c} K(g, r)` is at most the total conditional mass, with equality for
`c = A(r)`. Hence the conditional zero-one Bayes accuracy of `A` is `1`, and no
rule can exceed `1`.

**Proof.** Each summand is at most `K(g, r)` because `K ≥ 0`; equality at
`c = A(r)` is Theorem 2. ∎

Lean: the class-mass bound itself is `ReadModel.orbit_mass_le_total` (with the
nonnegativity hypothesis `0 ≤ J`); the equality — hence accuracy `1` — is
`ReadModel.orbit_mass_eq_total` / `ReadModel.conditional_posterior_eq_one`. The
`100%` accuracy is a corollary of those two, not an independent theorem.

**This is immediate given uniqueness.** The `100%` figure is a direct
consequence of Theorem 1 and is **not** a stronger finite-ML conjecture, and it
does **not** replace the independent population/P2 theorem.

## 6. Theorem 5 — decoder interface and inherited hypotheses

The abstract results require only a decoder `A` satisfying `(NSG)`. Two source
cases give such an `A`:

- **Case A — the source returns a sequence.** Then `A(r)` is the algorithm's
  output directly.
- **Case B — the source constructs a unique graph Eulerian cycle.** Then
  `A(r) := Spell(EulerianCycle(X_r))`, where `X_r` is the read-overlap graph
  built from `r`. This is well-defined **only** because Corollary 1 proves the
  Eulerian cycle is unique up to cyclic shift. If only existence is available
  (Theorem 1), the decoder needs a tie-break rule and the uniqueness guarantee
  is lost.

Hypotheses to verify against the source before the external premise is applied:
genome length `G` (external parameter or intrinsic), read model (read strings,
not sampled placements), orientation (oriented reads give cyclic-shift
equivalence; reverse-complement-collapsed molecule classes give a coarser
dihedral equivalence), error-free reads, and finite versus population sampling.
The graph `X_r` in Case B is built from the distinct read-string set after the
source's deduplication preprocessing (§7); `SourceRegime` records the
`2 ≤ L ≤ S.len` length regime and the error-free/circular assumptions.

## 7. Source-fidelity caveats

**Read-instance bridge (duplicate invariance).** The NSG manuscript states
the algorithm on a set of reads `R` and explicitly deduplicates read
instances as a preprocessing step (§3.2, PDF p. 12); the vertex set is the
distinct read strings, and the §6.3 edge multiplicities are computed by
Algorithm 6 from the graph *topology*, not from read-instance counts. The
repository's `observedTypes_ofFinset` is exactly that distinct-string set, and
`HistoricalInformationFeasibleLiteral` depends on the candidate only through
it. Section 7 of the Lean module makes this a kernel-checked adapter:
`list_toFinset_map` and `observedTypes_ofList_eq_toFinset` relate an instance
list to its support, `historicalEvent_dedup` shows feasibility is
duplicate-invariant, `exists_finset_decoder` factors any duplicate-invariant
instance decoder through the support, `nsg_instance_iff_finset` proves the
instance-level NSG premise is equivalent to the Finset premise, and
`historical_feasible_fibre_unique_of_instance_decoder` restates the historical
endpoint with a source-shaped instance-level decoder. The remaining trust
boundary is the external guarantee `hNSG` (the source algorithm is not
formalized), not the read-instance encoding. `SourceRegime` records the
`2 ≤ L ≤ S.len` length regime, error-free/circular hypotheses, and the
deduplication step.

1. **Latent placements and the likelihood marginal.** The repository's literal
   §6.4 predicate `HistoricalInformationFeasibleLiteral S L R` is determined by
   the candidate genome `S` and the *observed read-string set*
   `observedTypes_ofFinset S L R`; the sampled start set `R` enters only through
   that induced string set, and for a competitor of a different length the true
   genome's start labels cannot be reused. The *likelihood*, by contrast, is a
   function of the candidate-specific placement, and several placements can
   induce the same observed string set. When the source event is expressed at the
   placement level as a predicate `E(g,T)`, the correct event-weighted joint
   mass is therefore the weighted marginalization over compatible placements,

   ```
   L(g, Y) = ∑_{T : consistent(g,T,Y) ∧ E(g,T)} weight(g, T),
   ```

   rather than a single likelihood times an existential feasibility indicator
   `π(g) P_g(Y) · 1_{∃T …}`. `PlacementModel`, `placementJoint`,
   `placement_support_subset_orbit`, and `placement_posterior_certain` in the
   Lean module formalize this weighted-sum version; the string-level `ReadModel`
   is the clean abstraction stated by the issue, and the two are kept separate.
2. **`E` is truth-dependent and not observable.** The event `E = F(G, R)`
   depends on the unknown `G`; it does not become an `R`-observable event merely
   because it holds. Conditioning must multiply the joint by `1_E` with the
   changed conditional prior, not apply a fixed prior to `P_g(r | E)`.
3. **Sufficient, not necessary.** `I_s` is a sufficient condition for the
   Not-So-Greedy guarantee. Nothing here claims it is necessary for unique
   reconstruction, and no converse is asserted.
4. **Not the Medvedev–Brudno objective.** The 2016 paper explicitly cautions
   that reconstruction under its feasibility conditions does **not** show the
   true `s` optimizes the Medvedev–Brudno read-count maximum-likelihood
   objective. The constrained-MAP statement of §4 is about the *feasible fibre*,
   not about ordinary ML, and it does not close the 2016 open question.
5. **§§6.1/6.2 pseudo-likelihood.** The pseudo-likelihood/molecule-spectrum
   formulations of Medvedev–Brudno §§6.1/6.2 are a different objective from the
   finite read-string likelihood used here. No transfer between them is claimed.
6. **Oriented reads versus reverse-complement classes.** With oriented reads the
   equivalence is cyclic shift. If reads are collapsed with their reverse
   complements, the equivalence is the coarser dihedral relation and Theorem 1
   yields dihedral uniqueness instead. The Lean module takes the equivalence
   `orbit` as an explicit parameter precisely so neither reading is silently
   assumed.
7. **Not a new theorem and not a population replacement.** The result is a
   conditional consequence of the published guarantee; it does not assert that
   infinite-read/population uniqueness was unnecessary, and it does not replace
   the independent population/P2 theorem.

## 8. Trust-boundary summary

| Component | Status | Artifact |
|-----------|--------|----------|
| `(NSG)`: `F(g,r) → A(r) ≈ g` | External premise (Shomorony et al. 2016, Corollary 1) | not formalized; hypothesis `hNSG` |
| Theorem 1, feasible-fibre uniqueness | Kernel-checked from `(NSG)` | `ReadModel.feasible_fibre_unique`, `historical_feasible_fibre_unique` |
| Theorem 2, conditional posterior certainty | Kernel-checked | `ReadModel.orbit_mass_eq_total`, `ReadModel.conditional_posterior_eq_one` |
| Placement-level adapter (weighted event mass) | Kernel-checked | `placement_support_subset_orbit`, `placement_posterior_certain` |
| Theorem 3, constrained MAP | Kernel-checked | `ReadModel.constrained_MAP_mem_orbit` |
| Ordinary-ML non-implication | Kernel-checked witness | `Example.ordinary_ML_prefers_infeasible`, `Example.constrained_kills_infeasible` |
| Theorem 4, no rule exceeds the decoder | Kernel-checked | `ReadModel.orbit_mass_le_total` |
| Theorem 5, decoder interface | Stated; depends on source case | this document, §6 |
| Read-instance bridge (Finset decoder vs. source instances) | Kernel-checked adapter under the source's explicit deduplication (§3.2, p. 12) | `exists_finset_decoder`, `nsg_instance_iff_finset`, `historicalEvent_dedup`, `historical_feasible_fibre_unique_of_instance_decoder` |
| Source length/model regime | Kernel-checked structure; prose hypotheses | `SourceRegime` (this document, §7) |

## 9. What this is not

- It is **not** an unconditional ordinary maximum-likelihood guarantee.
- It is **not** a new biological or combinatorial theorem.
- It does **not** assert that infinite-read uniqueness was unnecessary.
- It does **not** claim to have formalized the Not-So-Greedy implementation;
  `(NSG)` remains a cited external premise with the trust boundary marked above.
