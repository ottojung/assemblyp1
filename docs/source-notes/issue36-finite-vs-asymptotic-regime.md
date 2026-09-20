# Issue #36: the finite-sample / high-coverage regime fork

_Status: independent source reading + mathematical analysis for issue #36,
2026-09-20. This note records one thing the existing issue-#36 notes do not:
the published sentence is quantified **per read set** and the kernel-checked
witnesses settle only that reading, not the high-coverage (consistency) reading,
under which the fixed-length answer is opposite. Source facts, mathematical
proofs, and interpretation are labelled separately. It does not re-derive the
§6.2 packet or the witness arithmetic._

## 0. Result

1. **Source fact.** The 2016 question is phrased as a per-instance guarantee over
   the information-feasible set `I_s`, and the paper uses explicit
   "with high probability" language elsewhere but not in the open question.
   The literal reading is therefore *for every read set `R ∈ I_s`*.
2. **Mathematical fact (new here).** Under the high-coverage reading with the
   true genome length `G` fixed, the truth's `L`-mer spectrum is, almost surely
   for all sufficiently large `n`, the **unique** maximizer of both determinate
   Medvedev–Brudno §6.1 objectives. With the repository's circular spectrum
   uniqueness bridge this makes the ML sequence the truth up to cyclic shift.
   With arbitrary-length competitors the strong conclusion fails outright at
   every `n`: `S^k` has *exactly* the same exact-multinomial likelihood as `S`
   for every sample (`k ≥ 2`), because the normalized window distribution is
   unchanged.
3. **Consequence.** The kernel-checked same-length witnesses are *low-coverage*
   phenomena: for large `n` a.s. the competitor in each witness is missing an
   observed read type and has likelihood zero, while the truth's likelihood
   dominates. The witnesses therefore settle the published question only under
   the finite-sample/per-instance reading, not under the high-coverage reading.
4. **Interpretation.** The regime is a third source choice, alongside the
   probability model and length/tie conventions. It does not by itself overturn
   a negative settlement, because the "otherwise nearly trivial" argument in §7
   favours the per-instance reading; but it must be recorded so the negative
   settlement is not stated unconditionally.

## 1. Source facts: what the sentence quantifies over

### 1.1 The open question (accepted text, printed p. i501, §5 Discussion)

> "The maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009), on
> the contrary, seems to be robust to these issues, and thus a good candidate
> for the 'correct' formulation. Understanding whether bridging conditions can
> be used to guarantee that the maximum-likelihood sequence is the true sequence
> is currently an open question."

No sample-size, coverage-depth, or limiting qualifier occurs in the sentence.
[source fact]

### 1.2 `I_s` is a set of *read sets* (accepted text, printed p. i497, Eq. (1))

The paper defines

> "`I_s ≜ { R : R covers s; triple repeats in s are all-bridged; interleaved
> repeats in s are bridged }`"

and says the set "nearly matches the set of information-feasible instances of
the AP (for most genomes considered)." The quantified object of the question is
therefore a *realized* read set `R`, not an asymptotic ensemble. [source fact]

### 1.3 The paper's own "guarantee" language is deterministic

Theorem 1 (accepted text, printed p. i497) is a deterministic implication from
`R` and `s`: "If `R` covers `s` and all triple repeats in `s` are all-bridged,
NOT-SO-GREEDY produces a read-overlap graph …". By contrast, where the paper
means a probabilistic statement it says so explicitly (Introduction, printed
p. i494–i495):

> "… with high probability the true sequence corresponds to a path on the
> graph as long as we are in the information-theoretic feasibility region …"

The open question avoids that qualifier. [source fact + interpretation: the
literal reading is the per-instance one.]

## 2. The two determinate §6.1 probability models (recap of the locators)

Medvedev–Brudno (2009), *J. Comput. Biol.* 16(8):1101–1116; §6 begins on journal
p. 1110.

- **Exact global read-count multinomial, candidate-intrinsic length.** MB09
  §6.1 (journal p. 1110): for a circular candidate `D` of length `N(D)`, with
  `d_D(i)` the number of length-`L` windows of type `i` and observed counts
  `x_i` over `n` reads,
  `L_exact(D|x) = n!/∏_i x_i! · ∏_i (d_D(i)/N(D))^{x_i}`. [source fact]
- **Separable product of binomial marginals, externally fixed length.** MB09
  §6.1 (journal pp. 1110–1111): `N(D)` is replaced by the known actual genome
  length `N`, giving per-type cost
  `c_i(d_i) = −x_i log d_i − (n − x_i) log(N − d_i)`. [source fact]
- **§6.2** is MB09's *algorithm* (journal p. 1111), whose output is a
  "(non-contiguous) assembly", not a sequence. [source fact]

Both §6.1 objectives are sequence-valued once a spectrum is fixed: for fixed
length they depend on the candidate only through its window counts `d_D(·)`.
This is the repository's existing reading; it is repeated only to fix notation.
See [`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md),
[`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md),
[`se62-feasibility-necessity-determination.md`](se62-feasibility-necessity-determination.md).

## 3. The regime fork

Fix the truth `S` (circular, length `G`) and the read length `L`. Let
`p(i) = d_S(i)/G` be the truth's window distribution.

- **Regime F (per-instance / finite sample).** For a fixed realized read set
  `R ∈ I_s` with counts `x`, ask whether `S` maximizes the likelihood over the
  candidate class. This is what the published sentence literally quantifies
  over (§1.2).
- **Regime H (high coverage / consistency).** Draw `n` i.i.d. reads from `S`;
  ask whether, almost surely, the ML sequence equals `S` for all sufficiently
  large `n` (with coverage/bridging holding a.s. eventually).

Regime F is a universal statement over `R ∈ I_s`; Regime H is an a.s. eventual
statement over the sampling process. Neither implies the other. The source
selects neither. [interpretation]

## 4. Mathematical analysis of Regime H

All uses of "`n` reads" below mean i.i.d. uniform length-`L` windows of `S`, so
`x_i/n → p(i)` almost surely (law of large numbers). [mathematical proof]

### 4.1 Exact multinomial, fixed candidate length `G`

For a length-`G` candidate `D` with `q_D(i) = d_D(i)/G` (a probability vector on
the finite type set),

`(1/n) log L_exact(D|x) = (1/n) log(n!/∏_i x_i!) + Σ_i (x_i/n) log q_D(i)`.

The first term is independent of `D` and tends to `H(p)` (Stirling). Hence

`(1/n) log L_exact(D|x) → H(p) + Σ_i p(i) log q_D(i) = −KL(p ‖ q_D)`,

which is `≤ 0`, with equality **iff** `q_D = p`, i.e. `d_D(i) = d_S(i)` for
every type `i`. The type set is finite and `Σ_i d_D(i) = G`, so the candidate
spectra are finite and the convergence is uniform over candidates. Therefore,
for almost every sampling sequence, the truth's spectrum is the unique exact-ML
spectrum for all sufficiently large `n`.

**Consequence (fixed length).** `d_S` is the unique maximizer and any length-`G`
competitor maximizing it has the truth's `L`-mer spectrum. Under the repository's
circular spectrum-uniqueness bridge (bridging excludes the `(L−1)`-mer
interleaved/triple obstructions; see
[`../literature/substring-spectrum-identifiability-2026-09-20.md`](../literature/substring-spectrum-identifiability-2026-09-20.md)),
that competitor is `S` up to cyclic shift. So in Regime H the answer to the
fixed-length question is **yes**, not no. [mathematical proof + analysis,
conditional on spectrum uniqueness]

### 4.2 Exact multinomial, arbitrary candidate length

Now `q_D(i) = d_D(i)/N(D)` is a probability vector for every nonempty circular
`D`, and the same limit `−KL(p ‖ q_D)` holds. The maximum `0` is
attained **iff** `q_D = p`. For every `k ≥ 1`, the `k`-fold repetition `S^k` has
`d_{S^k}(i) = k·d_S(i)` and `N(S^k) = kG`, hence `q_{S^k} = p`. In fact the
equality is exact at every finite `n`, not only in the limit:

`∏_i (d_{S^k}(i)/N(S^k))^{x_i} = ∏_i (k·d_S(i)/(kG))^{x_i} = ∏_i (d_S(i)/G)^{x_i}`,

so `L_exact(S^k) = L_exact(S)` for **every** observed sample and every `k ≥ 1`.
Therefore, whenever arbitrary-length competitors are admitted, `S^2` is a
maximizer with the same likelihood as `S` yet is not `S`, so the strong
conclusion "every maximizer is the truth" fails outright (no asymptotics
needed, and independently of any repeat or bridging condition). Whether the
weak conclusion "the truth is *a* maximizer" holds for large `n` is a separate,
uniform-in-`D` question and is not needed here. [mathematical proof]

### 4.3 The §6.1 binomial approximation

Here `q_D(i) = d_D(i)/N` uses the fixed external length `N`, not `N(D)`. The
per-type limiting term is `p(i) log q_D(i) + (1−p(i)) log(1−q_D(i))`, whose
unique per-type maximizer is `q_D(i) = p(i)`, i.e. `d_D(i) = d_S(i)` when
`N = G`. Since `Σ_i d_D(i) = N(D)`, attaining this forces `N(D) = G`. So unlike
the candidate-intrinsic exact case, the scaling tie `S^k` does **not** occur
here: the §6.1 binomial's asymptotic optimizer has length `G` and spectrum
`d_S`, and under spectrum uniqueness it is `S`. The arbitrary-length
non-uniqueness of §4.2 is therefore specific to the candidate-intrinsic
`N(D)` exact multinomial. (As in §4.2, turning "the limit objective is
uniquely maximized at `d_S`" into "`S` is a global maximizer for every large
`n`" needs a uniform-over-`D` argument, which is not made here.) [mathematical
proof]

## 5. Which regime the kernel-checked witnesses address

The witnesses are finite read multisets: `AAABB` with reads `{AAA, AAB, BAA}`
(#31, exact) and `AAACC` with reads `{AAA, AAC, CAA}` (#32, binomial), both
`n = 3`, `L = 3`, `G = 5`. In both, the winning competitor (`AAAAB`
respectively `AAAAC`) **omits** read types that the truth contains (e.g. `ABB`
and `BBA` for `S = AAABB`). Such a competitor has likelihood zero as soon as any
omitted truth type is observed, which happens with probability tending to one as
`n` grows. So the witnesses are genuine Regime-F counterexamples and say nothing
against Regime H. [source fact + mathematical observation]

This is consistent with §4: the finite-sample failure is a large-deviation
event of the sampling process, while the high-coverage limit favours the truth.

## 6. Determination for issue #36

1. **Most faithful literal reading.** Regime F, per-instance over `R ∈ I_s`
   (§1). Under Regime F the kernel-checked same-length witnesses refute the
   "truth is ML" conclusion for both determinate §6.1 models, and candidate-set
   inclusion transfers that to arbitrary-length candidates; §6.2 feasibility is
   not an additional necessary obligation. This is the branch's existing
   negative settlement, and it is correct for Regime F. [source fact + math]
2. **Not settled.** The published sentence does not exclude Regime H. In Regime
   H with fixed length and the spectrum-uniqueness bridge, the answer is
   *positive*; with arbitrary length it is weak-positive/strong-negative.
   Because these are opposite to the Regime-F answers, the witnesses do **not**
   settle the question unconditionally. [math + interpretation]
3. **Residual source choices** are therefore three, not two: the probability
   model (§6.1 exact vs binomial), the length/tie convention, and the
   regime/quantifier (per-instance vs high-coverage). The existing
   [`se62-feasibility-necessity-determination.md`](se62-feasibility-necessity-determination.md)
   §9 lists one fewer; the regime choice should be added.

## 7. Why Regime F is probably the intended reading

If the authors had meant Regime H (consistency of the MLE), then for fixed
candidate length the answer is immediate from the law of large numbers, the
finiteness of the candidate-spectrum set, and the classical spectrum
characterization — it would be surprising to call such a statement "currently an
open question." The nontrivial content the sentence can carry is the
per-instance Regime-F statement, which `I_s` controls directly. This supports
the repository's negative settlement as source-faithful, while still requiring
the regime caveat of §6.2. [interpretation]

## 8. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| Open question has no sample-size/coverage qualifier | source fact | accepted text p. i501 |
| `I_s` is a set of realized read sets | source fact | accepted text Eq. (1), p. i497 |
| Paper uses "with high probability" explicitly elsewhere | source fact | accepted text Introduction, p. i494–i495 |
| Literal reading is per-instance (Regime F) | interpretation | §1 |
| Regime H fixed-length truth spectrum is unique asymptotic maximizer | mathematical proof | §4.1, Gibbs/KL |
| Regime H arbitrary-length: weak true, strong false (`S^k`) | mathematical proof | §4.2 |
| Binomial objective shares the Regime-H conclusion | mathematical proof | §4.3 |
| Witnesses are Regime-F only; competitors die for large `n` | source fact + math | §5, witness data |
| Regime H fixed-length answer is yes (given spectrum uniqueness) | analysis, conditional | §4.1 |
| Regime H is probably not the intent | interpretation | §7 |

## 9. Locators

- I. Shomorony, S. H. Kim, T. A. Courtade, D. N. C. Tse, "Information-optimal
  genome assembly via sparse read-overlap graphs," *Bioinformatics* 32(17)
  (2016) i494–i502, DOI `10.1093/bioinformatics/btw450`; Eq. (1) and Theorem 1
  printed p. i497; open question printed p. i501; "with high probability"
  Introduction p. i494–i495.
- P. Medvedev, M. Brudno, "Maximum Likelihood Genome Assembly," *J. Comput.
  Biol.* 16(8) (2009) 1101–1116, §6.1 (journal p. 1110), §6.1 approximation
  (journal pp. 1110–1111), §6.2 (journal p. 1111).
- Repository witnesses: [`../fixed-length-exact-counterexample.md`](../fixed-length-exact-counterexample.md),
  [`../fixed-length-binomial-counterexample.md`](../fixed-length-binomial-counterexample.md).
- Circular spectrum-uniqueness bridge:
  [`../literature/substring-spectrum-identifiability-2026-09-20.md`](../literature/substring-spectrum-identifiability-2026-09-20.md)
  and `mathematics/bridging-and-spectrum-uniqueness.md` (Conjecture 4).
