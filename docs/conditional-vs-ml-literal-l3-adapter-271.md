# Oriented adapter at read length `3` with the **literal** §6.4 event (#271)

_Status: research comparison note. All Lean statements referenced below are
kernel-checked in `AssemblyP1/ConditionalVsMLLiteralL3Adapter271.lean` and
audited in `AxiomAudit271.lean` (only `propext`, `Classical.choice`,
`Quot.sound`). This closes the read-length-`≥3` item that the merged
[`conditional-vs-ml-genome-adapter-271.md`](conditional-vs-ml-genome-adapter-271.md)
handoff left open._

## 1. What is instantiated, exactly

The abstract separation of
`AssemblyP1/ConditionalVsOrdinaryMLSeparation.lean` (#271) and the general
orbit-class boundary `AssemblyP1.FiniteBayesianSideInformation.posteriorMass_eq_one_iff`
(#272) are instantiated on a concrete finite circular read model at **read length
`3`**, with the **literal** historical event:

| axis | choice in this adapter |
| --- | --- |
| alphabet | `Sym = Fin 2` (binary) |
| genome length | `G = 4`; circular genome `ZMod 4 → Sym` |
| read length | `L = 3`; oriented read string `Read = Fin 3 → Sym` |
| candidate universe | six rotation-**orbit classes**: `0000`, `0001`, `0011`, `0101`, `0111`, `1111` up to rotation (`rep`, `orbit`) |
| observation model | `p i w = orbitReadPmf (G:=4) (L:=3) (orbit i) w = #{starts spelling w in g} / 4`; normalized (`p_sum_one`) and nonnegative (`p_nonneg`) |
| observation representation | oriented one-strand windows; **no** reverse-complement quotient (per #269/#260 and the merged `W1W2RcOrientedRepresentation271`) |
| prior | uniform `1/6` over the six orbit classes (`prior`), normalized (`prior_sum_one`) |
| likelihood objective | exact single-read pmf (the iid product is its `n`-fold power); **not** the MB09 fixed-`N` product-binomial and **not** the §6.2 feasible-flow objective |
| side information | candidate-specific **literal** §6.4 event `E i r := ∃ T, (∃ s ∈ T, window (genOf i) 3 s = r) ∧ HistoricalInformationFeasibleLiteral (genOf i) 3 T` |
| rotation | the genuine rotation action on `ZMod 4`; `readPmf` is rotation invariant (`readPmf_rotWord`), so `p` descends to orbits |

## 2. The literal event is non-degenerate at read length `3`

The merged `AssemblyP1/ConditionalVsMLFullReadSet271` proved that at read length
`2` the literal historical event is **degenerate**: literal feasibility forces
coverage, coverage forces the whole window-type image (cardinality `≥ 2`) into
the observed read set, so the literal weighted placement mass vanishes at
**every** single-read observation (`fullJoint_singleton_eq_zero`).

At read length `3` that degeneracy disappears. The truth orbit `1` (`0001`)
satisfies the literal §6.4 event at the **single** observed read string `000`
via the **non-saturated** placement `{0,1,3}`:

```
literalFeasible_nonsaturated :
  HistoricalInformationFeasibleLiteral (genOf 1) 3 {0,1,3}
nonsaturated_card : ({0,1,3} : Finset (Fin 4)).card = 3
E_one_000 : E 1 (r3 0 0 0)
```

The non-saturated placement has three of the four positions; read length `3`
bridges the length-`1` three-occurrence repeats (the `bridgesCopy_length`
obstruction `e + 2 ≤ L` is `3 ≤ 3`, attainable). The literal event pins the
truth orbit at `000`:

```
E_iff_at_000 : ∀ i : Fin 6, E i (r3 0 0 0) ↔ i = 1
```

## 3. The two kernel-checked endpoints

### (A ∧ ¬B) — separation

Truth orbit `1` (`0001`), observed read string `000`.

* **(A) conditional recovery is certain.**
  `sep_posteriorMass_one :
  posteriorMass prior p E orbit (r3 0 0 0) (orbit 1) = 1`,
  established by the general #272 theorem `posteriorMass_eq_one_iff`: at read
  `000` the only candidate of positive prior and positive likelihood satisfying
  the literal event `E` is the truth orbit `1`. The excluded-competitor form is
  `sep_posteriorMass_one_excluded`.
* **(B) ordinary ML prefers the wrong orbit.** `p 1 (000) = 1/4 < 1 = p 0 (000)`
  (`sep_ml_strict`), so the truth orbit `1` is not an ML maximizer
  (`sep_truth_not_ml`); the wrong orbit `0` (`0000`) is.
* **the ordinary posterior is not certain.**
  `sep_ordinary_not_certain :
  posteriorMass prior p (fun _ _ => True) orbit (r3 0 0 0) (orbit 1) ≠ 1`.

Packaged as `separation_genome`.

### (B ∧ ¬A) — converse

Truth orbit `0` (`0000`), observed read string `000`.

* **(B) ordinary ML uniquely selects the truth.** `p 0 (000) = 1` beats
  `p 1 (000) = 1/4` and the zero-likelihood others (`conv_ml_strict`), and `0` is
  the *unique* maximizer (`conv_ml_unique`).
* **(A) the ordinary posterior is not certain.**
  `conv_ordinary_not_certain :
  posteriorMass prior p (fun _ _ => True) orbit (r3 0 0 0) (orbit 0) ≠ 1`.

Packaged as `converse_genome`.

Both endpoints use **one and the same** generative read model: the same `p`, the
same orbit universe, and the same uniform prior. The only additional ingredient
in (A) is the literal source event `E`.

## 4. Relation to the merged #271 modules (reuse, no fork)

* **Placement-based adapter (read length `2`).**
  `AssemblyP1/ConditionalVsMLGenomeAdapter271.lean` uses the placement-based
  `SourceFaithfulIs.InformationFeasible` at the two-start placement `{0,2}`. The
  present module uses the **literal** §6.4 predicate
  `HistoricalInformationFeasibleLiteral` (coverage + all three-occurrence repeats
  bridged + interleaved repeats bridged) at a non-saturated placement, and
  exhibits the first **non-degenerate single-read literal** witness.
* **Full-read-set literal mass.** `AssemblyP1/ConditionalVsMLFullReadSet271.lean`
  computes the literal weighted placement mass over the full observed read set;
  its `fullJoint_singleton_eq_zero` is the read-length-`2` degeneracy that the
  present read-length-`3` witness escapes.
* **Rotation descent.** The source predicate is rotation invariant
  (`SourceFaithfulIs.informationFeasible_rotGenome`, merged PR #354), so `p`
  descends to orbit classes; the present `E` is stated at the chosen
  representatives exactly as the read-length-`2` adapter's is.
* **W1/W2 representation warning.** The oriented observable is not the
  reverse-complement-collapsed molecule observable; that separation is the merged
  `AssemblyP1/W1W2RcOrientedRepresentation271.lean`. This adapter does not
  identify the two.
* **Classification.** The ordinary-ML classification (#255/#258/#259/#261) is
  untouched; `MLMax` is the read-model instance of the prior-free, `E`-free
  maximizer predicate.

## 5. Open items (labelled, not claimed)

1. **`E → B`.** Still not claimed; refuted here (`sep_truth_not_ml`). The uniform
   orbit prior does not create the (A)-side collapse — the literal event does.
   The general refinement (`E` ML-sound) is the merged
   `AssemblyP1/ConditionalBayesEImpliesB271`.
2. **General `L`, `G`.** This is a bounded finite witness at `L = 3`, `G = 4`; no
   general-`L` theorem is asserted.
3. **Full iid-product objective.** The adapter uses the exact single-read pmf;
   the `n`-fold iid product is its power, and it is not identified with the
   fixed-`N` product-binomial (merged
   `GenomeOrbitAdapter.ExactVsSurrogate.exact_ne_productBinomial`).

## 6. Manuscript-safe wording (for #265/#268, non-competing)

> At read length three, the oriented finite circular read model admits a
> single-read observation at which the **literal** §6.4 historical
> information-feasibility event holds for the true rotation class through a
> **non-saturated** placement, while ordinary maximum likelihood strictly prefers
> a wrong class: conditioning on the literal event yields posterior certainty on
> the truth, but the R-only ML rule does not recover it. This complements the
> read-length-two placement-based witness, where the literal event is degenerate.
