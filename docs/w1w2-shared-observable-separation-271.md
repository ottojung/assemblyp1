# W1/W2 conditional-Bayes vs ordinary-ML separation on ONE shared observable model (issue #271)

_Status: research comparison note. The two-sided separation on the historical
W1/W2 witnesses is Lean kernel-checked in
`AssemblyP1/W1W2SharedObservableSeparation.lean` on top of the exact read model
of `AssemblyP1/SameLengthSection62Counterexample.lean` (W1) and
`AssemblyP1/PerOccurrenceSameLengthCounterexample.lean` (W2). The (B)-side
alone (no (A)-side) was previously kernel-checked by reuse in
`AssemblyP1/W1W2SeparationCompatibility.lean`, which recorded that the
historical witness model carries no prior, no normalized observation pmf, and no
side event `E`, so the (A)-posterior was undefined there. This note's module
closes exactly that gap with the explicit concrete adapter the #271 kernel
standard demands; the abstract toy remains **not** a source-faithful genome
witness. Axiom audit: `AxiomAudit271.lean` (only `propext`,
`Classical.choice`, `Quot.sound`)._

## 1. The single shared observable model

For each witness (W1, W2) the SAME four objects serve both sides of the #271
comparison — the (A)-posterior and the (B)-ML rule are evaluated on one joint
model, not on two different ones:

| object | W1 | W2 |
| --- | --- | --- |
| candidate universe | `W1Cand = {truth, competitor}` (spectra `dS`, `dD : Fin 8 → ℕ`) | `W2Cand = {truth, competitor}` (spectra `dS`, `dD : Fin 64 → ℕ`) |
| prior | uniform `w1prior g = 1/2` (skewed `w1prior'` for ablation) | uniform `w2prior g = 1/2` |
| observation representation | two-point collapse `{obs, other}` of the read-count-vector space (`W1Obs`) | same collapse (`W2Obs`) |
| likelihood | exact multinomial pmf of the observed count vector, `n = 5` reads iid uniform over the `G = 6` cyclic starts | exact multinomial pmf, `n = 6` reads over the `G = 8` cyclic starts |
| side information | truth-dependent promise `E g r := (g = truth)` | same |

The likelihood is the genuine normalized observation model: with `obs` the
realized count vector, `p_d(obs) = (n! / ∏_c obs c!) · ∏_c (d c / G)^{obs c}`.
Unlike the §6.1 product of binomials (not a pmf over count vectors) and unlike
the unnormalized `exactLik` score kernel, this is a probability. The
candidate-independent multinomial coefficient `n! / ∏ obs c!` and the `G^n`
normalization cancel between the two candidates, so the multinomial likelihood
ratio equals the already-kernel-checked `exactLik` ratio (W1: `3`; W2: `3/2`):
the (B)-failure is inherited exactly, not re-proved.

The joint distribution is made explicit as `J(g, r) = π g · p_g(r) · 1_E(g, r)`
(`jointE`). Conditioning on `(r, E)` forms
`P(g | r, E) = J(g, r) / ∑_h J(h, r)` (`postE`), so conditioning touches both
the prior and the likelihood. Under the truth-dependent `E` the non-truth
candidate's joint mass vanishes (`jointE_eq_zero_of_ne`), the prior and
likelihood cancel in the ratio, and the posterior on the truth is `1`
(`postE_truth_eq_one`, instantiated as `w1_A`, `w2_A`); without `E` they do
not cancel and the posterior is `< 1` (`noE_post_lt_one`).

## 2. Where the two guarantees separate (kernel-checked)

* **(A) holds, (B) fails — the separation.** On the one shared model,
  conditional recovery under `E` is certain (`w1_A : postE … = 1`,
  `w2_A : postE … = 1`), while ordinary R-only ML strictly prefers the wrong
  candidate (`w1_B`, `w2_B : ¬ mlMax (fun g r => w1p g r) truth obs`), because
  the exact multinomial likelihood orders `5/216 < 5/72` (W1) and
  `135/8192 < 405/16384` (W2). Packaged: `w1_premise_sensitivity`,
  `w2_premise_sensitivity`.
* **E-ablation.** Without `E`, the ordinary posterior on the truth is not
  certain: `w1_noE_post = 1/4 ≠ 1`, `w2_noE_post = 2/5 ≠ 1`. The competitor
  retains positive prior and positive likelihood, adding positive denominator
  mass absent from the numerator. So `E` is doing the work for (A).
* **Prior-ablation.** The no-`E` posterior depends on the prior: under the
  uniform prior it is `1/4`, under the skewed prior `w1prior'` it is `1/10`
  (`w1_noE_post'`). The ML ranking (B) is prior-free: it is a statement about
  the likelihood alone, and the same (B)-failure is witnessed under every
  prior. The two guarantees therefore sit on different axes of the model: (A)
  is sensitive to the prior AND to `E`; (B) is sensitive to neither.
* **Maximizer vs unique maximizer.** The (B)-failure here is strong: the truth
  is not even a maximizer (the competitor is strictly better), so the
  unique-maximizer form of (B) fails a fortiori. Tie-semantics regressions at
  the toy level are kernel-checked separately in
  `AssemblyP1/ConditionalVsOrdinaryMLBoundary271.lean`.

## 3. What is NOT claimed

* This is an adapter on the historical W1/W2 witness spectra with an externally
  supplied truth-dependent `E`. It is **not** a claim that the §6.1
  product-of-binomials objective is a pmf over count vectors, and **not** a
  claim that any source-faithful side predicate (e.g. the latent-start
  information-feasible predicate of
  `AssemblyP1/ConditionalVsMLGenomeAdapter271.lean`) is ML-sound: the truth
  here is not an ML maximizer at the observed read, so `E` holds at a read
  where ordinary ML fails. Per the merged #271 refinement
  (`AssemblyP1/ConditionalBayesEImpliesB271`), conditional recovery implies
  ordinary ML recovery exactly when the side information is ML-sound
  (`condCertain_iff`); this `E` is deliberately NOT ML-sound
  (`not_MLsound_of_witness`), so no (A)-implies-(B) theorem is available or
  claimed for it.
* The observation representation is the **reverse-complement-collapsed
  molecule-class count vector** of the historical witnesses, as the witness
  modules themselves state: `SameLengthSection62Counterexample` reads the
  vertices of the bidirected read-overlap graph as read *DNA molecules* (a word
  and its reverse complement are one vertex), and both witnesses index the
  observable `obs` and the spectra `dS`, `dD` by the molecule class
  `cls w = min (code w) (code (rc w))` (`Fin 8` for W1, `Fin 64` for W2; MB09
  §3.1/§4.1). This is the same molecule-class observable as the #260
  full-overlap molecule layer, not an oriented single-strand read-string
  observable. The oriented single-strand model of `#88`/`#261`
  (`docs/oriented-same-length-ml-88.md`: "Read types are oriented single-strand
  length-`L` circular windows; there is no reverse-complement collapse") is a
  **different observable with a different likelihood**, and the two are not
  mixed here: this module makes no separation claim for the oriented model.
  The historical coverage-predicate variants (`HistoricalCovers` matched read
  strings vs `SourceFaithfulIs.InformationFeasible` latent starts) do not
  affect this module either: its statements concern the molecule-class count
  vector `obs`, not coverage.

## 4. Relation to the other #271 artifacts

* `AssemblyP1/ConditionalVsOrdinaryMLSeparation.lean` — the abstract
  incomparability witness (toy level).
* `AssemblyP1/W1W2SeparationCompatibility.lean` — the (B)-side W1/W2
  instantiation by reuse (binomial and exact objectives); states the
  structural absence of the (A)-side and defers it to the adapter in this note.
* `AssemblyP1/ConditionalVsMLGenomeAdapter271.lean` — genome-level adapter in
  the exact finite circular read model with the source-faithful
  information-feasibility predicate; separation (A ∧ ¬B) and converse
  (B ∧ ¬A) at the genome level.
* `AssemblyP1/ConditionalBayesEImpliesB271.lean` — the (A)-implies-(B)
  boundary: exactly ML-sound `E`.
* `AssemblyP1/ConditionalVsOrdinaryMLBoundary271.lean` — tiny-table
  regressions: ties, zero-likelihood competitors, MAP vs ML.
