# Oriented same-length ML at the model boundary (issue #88)

This note records what `AssemblyP1/OrientedSameLengthML.lean` states and proves,
which modeling choices it makes, and exactly what it does **not** prove. The Lean
module is imported by `AssemblyP1.lean`, so every theorem listed here is
kernel-checked by `lake build` and free of `sorry`/`admit`/`axiom`
(`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`).

## 1. What is kernel-checked

The module has three independent jobs.

### 1.1 Support and read-nodes to `genomeNodes` (the bridge)

| theorem | content |
| --- | --- |
| `genomeNodes_eq_image_winPrefix` | the `(L-1)`-window node set of a circular word is the image of `winPrefix` on its own window support |
| `genomeNodes_of_support_eq` | equal window support implies equal node set |
| `mem_support_iff_window` | a word is in the support iff it is some window |
| `specCount_pos_iff` | a word's spectrum is positive exactly on the support |

`genomeNodes_of_support_eq` is the only piece needed to move the truth's balance
equation from a *candidate's* node set to the truth's node set. It is applied in
`candidate_circulation_hypotheses` via `genomeNodes_of_support_eq hG D S hsup`
followed by rewriting with `hsup`.

### 1.2 A same-length spelled candidate into the existing rigidity hypotheses

| theorem | content |
| --- | --- |
| `IsSameLengthSpelledCandidate` | restricted candidate universe: support `D` = support `S`, and every observed read type is spelled by `D` |
| `candidate_circulation_hypotheses` | the candidate's own spectrum `specCount hG D` is a positive balanced circulation of total mass `G` on the **truth's** support |
| `same_length_candidate_spectrum_eq` | therefore `specCount hG D = specCount hG S`, by `OrientedFinal.oriented_same_length_spectrum_rigidity` |

`candidate_circulation_hypotheses` is an exact interface statement: the three
hypotheses it returns are literally the three hypotheses
`OrientedFinal.oriented_same_length_spectrum_rigidity` consumes
(`hBsup`, `hBbal`, `hBtot`), in the same order and with no strengthening and no
weakening. No new abstract hypothesis is introduced and none is dropped.

### 1.3 Spectrum into the actual objective and maximizer endpoint

Two objectives are defined, kept strictly separate, and neither is advertised as
*the* objective the 2016 sentence denotes
(`docs/source-notes/shomorony-mb-formulation-referent-reconciliation.md`):

* `exactLik` — the oriented same-length exact Medvedev–Brudno multinomial
  likelihood `∏_w (d_D w / G)^{x w}`, with the candidate-intrinsic
  `N(D) = G` (`docs/ml-formalization-contract.md` Variant E);
* `binomialLik` — the §6.1 separable approximation `∏_w Binomial(n, d_D w / N)`,
  with the external genome-size estimate `N` as an explicit argument and
  `n = totalReads x` taken from the observation.

| theorem | content |
| --- | --- |
| `exactLik_congr_of_specCount_eq`, `binomialLik_congr_of_specCount_eq` | the objectives factor through the spectrum |
| `exactLik_scale_congr`, `exactLik_scale_pos`, `exactLik_scale_le_iff` | reinserting the observation-only multinomial coefficient `n! / ∏_w x w!` provably does not change any comparison between candidates |
| `same_length_exactLik_maximizer` | the truth is a maximizer of `exactLik` over the spelled same-length candidate class |
| `same_length_binomialLik_maximizer` | the same for the §6.1 objective |
| `same_length_ML_maximizer_both` | both objectives at `N = G` in one statement |
| `exactLik_eq_zero_of_unspelled_observed`, `exactLik_le_of_unspelled_observed` | a candidate missing an observed read type has likelihood `0`, hence is dominated — with **no** spelledness and **no** support assumption |
| `same_length_unique_up_to_rotation_of_bbt` | the uniqueness-up-to-rotation schema, conditional on the external complete-spectrum (BBT) premise |
| `same_length_maximality_and_rotation_uniqueness_of_bbt` | both conclusion schemas together, as a quantification over candidates |
| `spelled_observed_or_unsounded`, `same_length_exactLik_maximizer_or_residual_gap` | the exact characterization of the candidate space — see §3 |

The maximizer-only and the uniqueness-up-to-equivalence readings are separate
propositions, as `docs/ml-formalization-contract.md` constraint 7 requires.
Neither is designated as *the* published conjecture.

## 2. Modeling choices, with their justification

* **Orientation.** Read types are oriented single-strand length-`L` circular
  windows; there is no reverse-complement collapse. Genome equivalence is
  `OrientedFinal.IsCyclicShift`, rotation only. The two choices are coupled: see
  `docs/source-notes/equivalence-and-tie-wellposedness.md`.
* **Candidate length is a type, not a hypothesis.** A candidate is
  `Fin G → α`, so it is a circular genome of the same length as the truth. This
  is a **restricted candidate universe** in the sense of the contract, and every
  theorem name says so (`…_same_length_…`, `IsSameLengthSpelledCandidate`).
* **Observation vs. realization.** The objective consumes only the read-type
  multiplicity `x : (Fin L → α) → ℕ`. A `Finset` of latent starts is never used
  as the observation, and repeated starts are counted repeatedly
  (`objective_depends_only_on_observation`, `totalReads_congr`). The
  realization-level layer that *builds* `x` is **not** formalized here; the
  observable consequence of draws from the truth appears only as the explicit
  premise `hobs` of `truth_is_spelled_candidate`.
* **Alphabet.** The theorems are quantified over a finite decidable alphabet
  `[Fintype α] [DecidableEq α]`, matching the finite DNA alphabet of the model.
* **Sample size.** `n` is `totalReads x`, not a free parameter, so the likelihood
  is a function of the observation and the candidate only.

## 3. The residual gap, stated rather than hidden

`IsSameLengthSpelledCandidate` requires **equality of the whole window
supports**, which no observation can certify: a candidate may spell every
observed read type and still have a different support. The module therefore does
*not* prove maximality over all circular candidates, and it does not claim to.
Instead it proves the exact dichotomy:

`spelled_observed_or_unsounded`: every same-length candidate either spells every
observed read type, or misses one of them (and then has exact likelihood `0`);

`same_length_exactLik_maximizer_or_residual_gap`: for **any** same-length
candidate `D`, either the truth maximises `exactLik` over `D`, or `D` spells
every observed read type while having a different window support from the truth.

The second disjunct is the residual gap. For such a candidate:

* `genomeNodes_of_support_eq` does not apply, so the balance equation cannot be
  moved to the truth's node set, and the rigidity chain's hypotheses are not
  available;
* the graph-theoretic claim that a spelled circuit of the read-overlap graph has
  the truth's support is **not** formalized (§6.2, single-strand reading);
* no theorem in this repository settles it.

## 4. What this does not prove

* Not that bridging conditions (`I_s`) imply the no-long-triple-repeat premise.
  That implication is source-supported (note §3, Fact D) but is **not**
  formalized anywhere in the repository. `hno` is therefore an explicit premise
  of every theorem here and is never hidden. This module defines no `I_s`, and
  issue #90 owns the source-faithful `I_s` layer; the seam here is deliberately
  narrow — one premise of the form `¬ RepeatAdapter.HasLongTripleRepeat hG S L`
  — so that #90's layer can be imported above this module after merge.
* Not that the candidate universe is all circular words of length `G` (§3).
* Not uniqueness of the maximizer. The BBT complete-spectrum step is external
  and appears only as the premise `hBBT`; see
  `docs/exact-same-length-spectrum-fibre-count.md`.
* Not that the exact or the §6.1 objective is the objective the 2016 sentence
  denotes, and not that the maximum-likelihood formulation refers to a
  particular candidate referent. Both remain open per
  `docs/source-notes/mb-formulation-referent-reconciliation.md`.
* Not that the two objectives have the same maximizers. They get separate
  definitions, separate congruence lemmas, and separate maximizer theorems; no
  theorem relates them.

## 5. Reproduction

```
lake build
```

`AssemblyP1.lean` imports this module, so the theorems are checked by the
default build. To re-check the trust boundary:

```
lake env lean - <<'EOF'
import AssemblyP1
#print axioms AssemblyP1.OrientedSameLengthML.same_length_ML_maximizer_both
#print axioms AssemblyP1.OrientedSameLengthML.same_length_exactLik_maximizer_or_residual_gap
EOF
```

Both must report only `propext`, `Classical.choice`, `Quot.sound`.
