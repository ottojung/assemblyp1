# Short finite-read ML counterexamples: true circular genome lengths 2, 3, 4

_Status: kernel-checked Lean certificate + exact-rational arithmetic, 2026-10-15,
for board issue #300. Companion module:
[`AssemblyP1/ShortFiniteMLCounterexamples.lean`](../../AssemblyP1/ShortFiniteMLCounterexamples.lean)._

## 0. Verdict at a glance

Under the **source-faithful oriented single-strand** convention already used by
[`oriented-variable-length-se62.md`](oriented-variable-length-se62.md) — read
*types* are the oriented length-`L` circular windows of the truth (no
reverse-complement collapse), candidate length is a free parameter, and the
§6.2 feasibility constraint is the literal per-vertex lower bound `1` — there are
concrete finite-read witnesses with true circular genome lengths **2, 3, and 4**
in which the truth satisfies the full information-feasibility predicate `I_s`,
the competitor is a genuine §6.2-feasible candidate, and the competitor has
**strictly greater ordinary exact read likelihood**.

| `G` | `L` | truth `S` | competitor `D` | observed reads | `P(R|D)/P(R|S)` |
|---|---|---|---|---|---|
| 2 | 1 | `AT` | `AAT` | `A, A, T` | `32/27 > 1` |
| 3 | 2 | `AAT` | `AAAT` | `AA, AA, AT, TA` | `81/64 > 1` |
| 4 | 3 | `AAAT` | `AAAAT` | `AAA, AAA, AAT, ATA, TAA` | `4096/3125 > 1` |

No minimality is claimed or proved: this note and the module only exhibit the
three witnesses and compute their exact ratios.

## 1b. The three witnesses sit in an infinite family (verifier-checked)

The tabulated instances are the `G = 2, 3, 4` slice of the family truth
`S = A^{G-1}T` vs competitor `D = A^{G}T` at read length `L = G - 1`, with one
read per true start plus one extra read from start `0`. For every `G ≥ 2` the
competitor spectrum is the truth spectrum plus exactly one extra `A^L` window,
so the exact likelihoods have the closed forms `P(R|S) = (1/G)^{G+1}` and
`P(R|D) = 4/(G+1)^{G+1}`, i.e. ratio `4·G^{G+1}/(G+1)^{G+1} > 1`. The extended
independent verifier (`scripts/verify_short_finite_ml_300.py`,
`check_general_family(2, 8)`) re-derives from scratch, for each `G = 2, …, 8`:
full `I_s` for the truth, the spectrum pattern, both candidates' three §6.2
readings (per-vertex, spelled support, closed overlap circuit with the cyclic
window order as the walk), the closed-form likelihoods and strict ratio
(reproducing `32/27`, `81/64`, `4096/3125` at `G = 2, 3, 4`), and the shared
multinomial-count ratio. The Lean module certifies only the `G = 2, 3, 4`
slice; the wider family is Python-checked, not kernel-checked.

## 1. Assumptions, stated exactly

- **Alphabet and read types.** Alphabet `{A, T}`. A read type is the *oriented*
  length-`L` circular window of a genome, with no reverse-complement collapse.
  [source fact for the oriented single-strand convention: Shomorony et al. 2016
  §2; the *choice* to study the oriented type space is inherited from the
  variable-length front.]
- **Genomes.** Truths `AT`, `AAT`, `AAAT` (`G = 2, 3, 4`); competitors
  `AAT`, `AAAT`, `AAAAT` (`|D| = G + 1`). Every genome is a circular word, and
  its length is intrinsic to the Lean `Genome` object. [mathematical fact]
- **Sampling.** The observation is **one read from every true starting position,
  plus one extra read from start `0`**: `[0,1,0]`, `[0,1,2,0]`, `[0,1,2,3,0]`
  for `G = 2, 3, 4`. Reads are distinguished by their actual strings.
  [source fact: reads are sampled from uniformly chosen starts, MB09 §6.1]
- **Likelihood (E), exact ordered-read.** `P(R | X) = ∏_{w ∈ R} d_X(w)/|X|`,
  where `d_X(w)` is the number of starts of `X` whose length-`L` window is `w`
  and `|X|` is the candidate's intrinsic length. This is the probability that
  the observed ordered list of read strings is produced by independent uniform
  start sampling; the multinomial coefficient `n!/∏_w x_w!` of the read-count
  objective is common to all candidates and cancels in any ratio.
  [source fact: MB09 §6.1]
- **Bridging hypothesis `I_s`.** The Shomorony et al. (2016) Eq. (1)
  information-feasible set, transcribed with Bresler et al. (2013) repeat
  definitions and kernel-checked in
  [`SourceFaithfulIs.lean`](../../AssemblyP1/SourceFaithfulIs.lean): coverage,
  every maximal triple repeat all-bridged, every interleaved pair of repeats
  bridged. It is a predicate on the **set** of realized starts, not on sample
  multiplicities. [source fact; transcription in
  [`../bridging-source-semantics.md`](../bridging-source-semantics.md)]
- **§6.2 feasibility.** Three readings are certified for every candidate: (F1)
  the literal per-vertex lower bound `1`; (F3) the stronger spelled
  support-equality form; (F4) the flow/circuit form — the candidate is realized
  by a closed walk of the oriented read-overlap graph whose per-type counts equal
  its spectrum. [F1 is source fact; F3 and F4 are source-supported strengthenings]

## 2. The witnesses

For `G = 2, 3, 4` the truth is `S = A^{G-1}T` and the competitor is
`D = A^{G}T`, the truth with one extra `A` inserted inside its maximal `A`-run.
Inserting one `A` into the maximal `A^{G-1}` run adds exactly one `AAA…A`
window and preserves every other length-`L = G-1` window, so the competitor's
spectrum equals the observation `spec_L(S) + e_{A^L}`. [verified computation;
kernel-checked by `spec_*` and `lik_*` below]

The observed spectra and likelihoods:

| `G` | truth spectrum | competitor spectrum | `P(R|S)` | `P(R|D)` |
|---|---|---|---|---|
| 2 | `A:1, T:1` | `A:2, T:1` | `1/8` | `4/27` |
| 3 | `AA:1, AT:1, TA:1` | `AA:2, AT:1, TA:1` | `1/81` | `1/64` |
| 4 | `AAA:1, AAT:1, ATA:1, TAA:1` | `AAA:2, AAT:1, ATA:1, TAA:1` | `1/1024` | `4/3125` |

## 3. The `L = 1` and `L = 2` edge cases, stated precisely

The issue requires that the two shortest instances not be mislabelled as
refuting a theorem that assumes a larger `L`.

- `SourceFaithfulIs.BridgesCopy` bridges a length-`e` copy only when a single
  read contains a base strictly before and strictly after the copy, so
  `SourceFaithfulIs.bridgesCopy_length` forces `e + 2 ≤ L` for any bridged copy.
  Hence for `L = 1` and `L = 2` **no** copy of length `e ≥ 1` can be bridged,
  and a truth carrying a maximal triple repeat could not be
  information-feasible. The `G = 2` truth `AT` and the `G = 3` truth `AAT` carry
  no maximal triple repeat at all, so their triple-repeat and interleaved-repeat
  clauses are **vacuous** and `InformationFeasible` reduces to coverage. This
  module proves that vacuity explicitly (`no_triple_repeat_2/3`,
  `no_interleaved_2/3/4`) *in addition to* discharging the full predicate by
  `decide`. [kernel-checked]
- The `G = 4` truth `AAAT` *does* carry a maximal triple repeat — the length-`1`
  triple of `A`s at starts `0, 1, 2` — and the module proves it and its
  all-bridged certificate (`triple_repeat_4`, `triple_repeat_all_bridged_4`);
  here the bridging bound `e + 2 = L` is tight. [kernel-checked]
- The repository's same-length rigidity theorem
  (`AssemblyP1.OrientedSameLengthML`, hypothesis `2 ≤ L ≤ G`) does **not** apply
  to the `G = 2, L = 1` instance (`L < 2`); and in any case that theorem is about
  *same-length* candidates, whereas these witnesses are variable-length
  (`|D| = G + 1 ≠ G`). Nothing here is claimed to refute a same-length or
  `L ≥ 2` statement. The witnesses settle the **variable-candidate-length**
  question in the oriented, per-vertex-§6.2, source-faithful model. [scope]

## 4. Exact Lean theorem names

Module `AssemblyP1.ShortFiniteMLCounterexamples`:

- full `I_s`: `truth_information_feasible_2`, `truth_information_feasible_3`,
  `truth_information_feasible_4`;
- vacuity / bridging detail: `no_triple_repeat_2`, `no_interleaved_2`,
  `no_triple_repeat_3`, `no_interleaved_3`, `triple_repeat_4`,
  `triple_repeat_all_bridged_4`, `no_interleaved_4`;
- §6.2 feasibility (per-vertex, spelled, circuit):
  `truth_perVertex_2/3/4`, `competitor_perVertex_2/3/4`,
  `truth_spelled_2/3/4`, `competitor_spelled_2/3/4`,
  `truth_section62_2/3/4`, `competitor_section62_2/3/4`, with circuits
  `circuit_S2`, `circuit_D2`, `circuit_S3`, `circuit_D3`, `circuit_S4`,
  `circuit_D4` and count theorems `counts_S2 … counts_D4`;
- exact likelihoods: `lik_truth_2`, `lik_competitor_2`, `lik_truth_3`,
  `lik_competitor_3`, `lik_truth_4`, `lik_competitor_4`;
- strict ratios: `ratio_2` (`32/27`), `ratio_3` (`81/64`), `ratio_4`
  (`4096/3125`), and `candidate_strictly_better_2/3/4`;
- multinomial objective shares the ratio: `multinomLik_ratio`, with instance
  corollaries `multinom_ratio_2/3/4`;
- endpoints: `short_finite_ml_counterexample_2/3/4` (each bundles `I_s`, both
  §6.2 certificates, both candidate-intrinsic lengths, and the strict ratio).

## 5. Verification map

| Claim | Certificate |
|---|---|
| `I_s` at full strength for each truth | Lean `truth_information_feasible_2/3/4` (`decide` on `SourceFaithfulIs.InformationFeasible`), axiom-clean |
| Repeat-clause vacuity / bridging | Lean `no_triple_repeat_2/3`, `no_interleaved_2/3/4`, `triple_repeat_4`, `triple_repeat_all_bridged_4` |
| §6.2 feasibility, all three readings | Lean `*_perVertex_*`, `*_spelled_*`, `*_section62_*` (closed walks `walkS2…walkD4`) |
| Exact likelihoods and strict ratios | Lean `lik_*`, `ratio_*`, `candidate_strictly_better_*` |
| Independent exact-rational re-derivation | [`scripts/verify_short_finite_ml_300.py`](../../scripts/verify_short_finite_ml_300.py) (imports no repository or Lean output; `fractions.Fraction` throughout) |
| Multinomial-count ratio | Lean `multinomLik_ratio`, `multinom_ratio_2/3/4` |
| No `sorry`/`axiom`/`admit`/`native_decide` | `grep` over the module returns no matches |
| Axioms | `#print axioms` on the endpoint theorems returns exactly `[propext, Classical.choice, Quot.sound]` |

## 6. Scope

This note settles the **oriented single-strand variable-candidate-length**
question for the three specific short witnesses, under the source per-vertex
§6.2 reading (and the stronger spelled and circuit readings), with `I_s` at full
strength. It does not settle which Medvedev–Brudno object the Shomorony et al.
(2016) sentence intends, does not address the bidirected / reverse-complement
sub-case, does not touch the fixed-length rigidity theorem, and does not claim
that these witnesses are minimal.
