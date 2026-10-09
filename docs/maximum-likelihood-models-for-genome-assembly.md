# Maximum-likelihood models for genome assembly

This note synthesizes the current AssemblyP1 research state. It deliberately separates the published Shomorony–Medvedev/Brudno question from two later repaired models introduced by this project. It is the repository-oriented companion to the LaTeX white paper (GitHub issue #51) and the Beamer talk (GitHub issue #56).

## 1. Why maximum likelihood is not enough by itself

A tempting starting point is simple: noiseless reads were sampled from the true circular genome, so the true genome ought to maximize their likelihood.

That intuition ignores identifiability. A tiny example already shows the problem. Take circular genomes

- `S = AAABAB`, and
- `D = AABAAB`,

with read length `L=2`. They are not cyclic rotations of one another, but both have exactly the same circular 2-mer spectrum:

- `AA` occurs twice;
- `AB` occurs twice;
- `BA` occurs twice;
- `BB` never occurs.

Thus even the complete noiseless 2-mer information cannot distinguish `S` from `D`; under the corresponding uniform-start read model they induce the same read distribution. This is a structural ambiguity, not a failure caused by unlucky finite sampling or by a particular likelihood optimizer.

This is why the repeat/read-length boundary comes first. Shomorony et al. formulate an information-feasibility condition `I_s`: the reads cover the genome, every triple repeat is all-bridged, and every interleaved pair of repeats is bridged in the required sense. Their Not-So-Greedy construction recovers the circular sequence under this condition. The 2016 Discussion then asks whether such bridging conditions also guarantee that the maximum-likelihood sequence is the true sequence, referring to the maximum-likelihood assembly formulation of Medvedev and Brudno (2009).

The question is therefore not whether arbitrary read sets identify arbitrary genomes. It is whether maximum likelihood inherits the recovery guarantee after the structural repeat obstruction has been removed.

## 2. The 2016 question is not one model

The 2016 sentence asks whether bridging makes "the maximum-likelihood sequence" the true sequence, but the sources do not pin down the referent of that phrase. The distinctions below are not pedantry; each one changes the answer, and collapsing them is the historical ambiguity this project repairs.

First, Shomorony's theoretical model is an oriented single circular sequence with oriented length-`L` reads, whereas Medvedev–Brudno also use reverse-complement-collapsed molecular read types and a bidirected graph representation. These representations must not be silently identified.

Second, Medvedev–Brudno's externally supplied genome-size parameter `N` is not a restriction that every candidate assembly have length `N`. In the §6.1 approximation, `N` is used in the probability model; the §6.2 flow constraints do not thereby impose a fixed total candidate flow. Thus

- knowing or supplying `N=G` to the likelihood, and
- restricting every candidate `D` to `|D|=G`

are different assumptions.

Third, the conclusion can mean either that the truth is *a* maximizer or that every maximizer is the truth up to the appropriate circular-genome equivalence. These differ whenever a wrong candidate ties the truth.

Fourth, the ML object itself differs between the two Medvedev–Brudno formulations. §6.1 is a product of binomial marginals over read types with fixed external `N`. §6.2 optimizes vertex throughputs of a bidirected flow and says its output "represents a (non-contiguous) assembly"; a flow optimum is not automatically an ML *sequence* without a flow-to-sequence rule. The #214 front makes this explicit: the general §6.2 candidate universe contains possibly-non-contiguous flows, and whether a flow optimum can be called an ML sequence at all is a separate question.

Accordingly, finite results below are stated with their assumption surface rather than being collapsed into a single yes/no answer.

## 3. Finite results

### 3.1 A strong positive slice: oriented, spelled, same length

Under strict oriented single-strand read types, Shomorony `I_s`, the §6.2 spelled-candidate support condition, and the additional candidate restriction `|D|=G`, the truth spectrum is rigid: `spec_L(S)` is the unique positive circulation of total `G` on the relevant de Bruijn support.

Consequently every feasible same-length spelled candidate has exactly the same length-`L` spectrum as the truth. Any objective depending only on that spectrum and the observed read counts therefore gives every such candidate the same score as the truth.

This is a genuine positive finite theorem for the **maximizer** conclusion. It does not by itself establish uniqueness of the maximizing circular sequence. That uniqueness reading — can distinct tied maximizing circular genomes exist under the same oriented same-length `I_s` assumptions? — is the #211 question, and it remains externally conditional on the Bresler–Bresler–Tse complete-spectrum theorem (see §6.1). The positive slice also depends essentially on the same-length candidate restriction; that restriction is not supplied merely by Medvedev–Brudno's known-`N` parameter.

### 3.2 Remove the candidate-length restriction: finite ML fails

The length restriction is a real mathematical boundary. In the same oriented setting, let

- truth `S = AAATT`, with `G=5`;
- competitor `D = AAAATT`, of length `6`;
- read length `L=3`.

The truth satisfies the relevant information-feasibility condition and the competitor contains every observed read type. With a realized sample containing one additional `AAA` observation (`n=6`), the longer competitor strictly beats the truth under both the candidate-intrinsic exact multinomial objective and the fixed-`N` §6.1 binomial objective.

The mechanism is general, not a census accident (#210). If a feasible sample from `S` is realized and `D` assigns higher probability to some observed truth read type `w`, then adding `m` further observations of `w` multiplies the exact likelihood ratio by `(p_D(w)/p_S(w))^m` and the §6.1 ratio by an explicit computable factor; for `AAATT → AAAATT` at external `N=5` the exact ratio goes from `3125/3888` at `M=0` to `15625/11664 > 1` at `M=1`, and the §6.1 ratio from `81/128` to `81/64`. A kernel-checked finite instance of the same witness is on main: `AssemblyP1.Section62BridgingCounterexample` checks the literal §6.2 bidirected-flow feasibility of both candidates at realized starts `(0,1,4)` (`n=3`, external `N=5`) and gives the §6.1 ratio `9/8 > 1`.

Thus the finite positive theorem does not extend from same-length candidates to unrestricted candidate length.

### 3.3 Reverse-complement molecular representation

The repository also contains strict counterexamples for the reverse-complement-collapsed Medvedev–Brudno representation, including the integrated `AAATAT → AAAAAT` witness (kernel-checked on main in `AssemblyP1.SameLengthSection62Counterexample`: exact ratio `3`, §6.1 ratio `5`). These results are important, but their hypothesis must be described carefully: the established witness checks Shomorony's single-strand `I_s` while evaluating an MB09 reverse-complement molecular likelihood/flow representation. It should therefore not be advertised as a theorem about a separately strengthened double-strand bridging condition.

The source-faithful lesson is narrower and sufficient: the representation map between Shomorony's theoretical read instance and the chosen MB09 likelihood object is part of the model, not notation to suppress.

### 3.4 Per-occurrence feasibility is a project repair, not a source fact (#212)

A second bidirected witness strengthens the feasibility requirement from MB09's per-vertex `1` to per-observation `d_w >= x_w`: truth `S = ATATACAC`, competitor `D = ATACACAC`, both of length `G=8`, read length `L=3`, external `N=8`. Both are per-occurrence feasible (tight at `ACA`/`TGT`), and `D` beats `S` under both objectives (exact ratio `3/2`, §6.1 ratio `9/5`). The witness is kernel-checked in `AssemblyP1.PerOccurrenceSameLengthCounterexample` on the #212 front branch (commits `6aeb95e..4afaade`; not merged to main as of this writing). The earlier `AAATAT → AAAAAT` refutation only covers per-vertex feasibility — there the truth itself is not per-occurrence feasible (`d_S(AAA)=1 < x_AAA=2`) — so the two refutations are logically independent.

The per-occurrence reading must be labeled as a project-level strengthening of MB09 §6.2, not a source fact.

### 3.5 The general flow domain: integral, half-integral, and the flow-to-sequence gap (#214)

MB09 §6.2's genuine target is possibly-non-contiguous feasible bidirected flows, not circular spelled genomes. The #214 front (`AssemblyP1.Section62NonSpelledFlow`, on the #214 branch) kernel-checks the integral argmax: among integer flows the existing strict spelled-circuit witnesses are feasible and optimal, so dominance fails in the full flow optimizer. But MB09 §5.1 discusses half-integral biflows as an algorithmic relaxation, and the binomial objective extended to half-integral throughputs strictly beats the integral optima: for the tied integer flows with throughputs `(2,1,1)` and `(3,1,1)`, the half-integral average at `(5/2,1,1)` improves the `AAA` marginal by `625/576 > 1`. Three levels must be kept separate: (i) the original integer genomics domain (§5.2), (ii) the half-integral biflow approximation (§5.1), (iii) an optional continuously-extended likelihood on relaxed flows. No automatic transfer of optimality or interpretation between them.

This is also where the flow-to-sequence gap lives: a flow optimum is not automatically an ML sequence without a flow-to-sequence rule, so a theorem about ML flows is not automatically a theorem about *the* ML sequence.

## 4. Why fixed true candidate length is an unsatisfying repair

The same-length theorem shows that a strong extra axiom can make the finite problem behave well. But `|D|=G` gives the candidate class privileged access to the true target length. That may be unavailable operationally, and it is stronger than merely supplying a genome-size parameter to an objective.

This motivates a first *new* model, not a reinterpretation of the historical papers: replace true-length knowledge with candidate-intrinsic structural checks.

The project considered repeat/read-length predicates intrinsic to each candidate, together with primitiveness where needed. A particularly strong test is P1: no repeated `(L-1)`-mer. P1 is stronger than the proposed P2/Ukkonen-style repeat condition, so failure under P1 also rules out the weaker structural repair as a general finite theorem.

## 5. Intrinsic structural checks still do not repair finite sampling

The decisive finite witness is

- truth `S = AABBC`, `L=3`;
- realized starts `(0,3)`, giving reads `{AAB,BCA}`;
- competitor `D = AABC`.

Both circular genomes are primitive and satisfy P1. The realized sample satisfies the truth-side information-feasibility condition. Yet under the candidate-intrinsic exact multinomial likelihood,

`L(D) / L(S) = (5/4)^2 = 25/16 > 1`.

This failure is qualitatively different from repeat ambiguity. The wrong genome wins because the finite sample happened to include only reads to which the shorter candidate assigns probability `1/4`, while the truth assigns probability `1/5`. Structural admissibility has not failed; empirical frequencies have fluctuated in favor of the wrong candidate.

This is the point at which a second repair becomes justified. Strengthening the repeat axioms again would target the wrong mechanism.

## 6. Population ML removes the remaining sampling failure

Let `d_S(w)` be the number of cyclic occurrences of the oriented length-`L` word `w` in `S`, and define the population read distribution

`p_S(w) = d_S(w) / |S|`.

For a candidate `D`, define `p_D` similarly. The per-read population log likelihood is

`ell_S(D) = sum_w p_S(w) log p_D(w)`,

with value `-infinity` when a truth-positive word has zero probability under `D`. Then

`ell_S(D) - ell_S(S) = -KL(p_S || p_D) <= 0`.

Therefore the truth is a population maximum-likelihood genome over **any** candidate class containing it. No repeat condition is required for this maximizer statement. Equality holds exactly when `p_D=p_S`, so uniqueness is no longer a statistical question: it is normalized-spectrum identifiability inside the chosen candidate class.

For the project's **oriented, primitive P2** candidate class, that identifiability step is also available, and it is now fully kernel-checked. The unrestricted claim --- primitivity plus normalized-spectrum equality implies ordinary-spectrum equality --- is **false**: at `L=2`, the primitive words `S = AAB` (`|S|=3`) and `D = AAABAB` (`|D|=6`) have `spec_2(S) = (AA:1, AB:1, BA:1)` and `spec_2(D) = (AA:2, AB:2, BA:2)`, hence identical normalized spectra `p_S = p_D = (1/3, 1/3, 1/3)` but distinct ordinary spectra. So primitivity alone is insufficient; the repair below uses P2 essentially.

The P2-specific argument runs as follows. Let `S` be a primitive P2 genome with `L <= |S|` and integer spectrum vector `c = spec_L(S)`; let `g = gcd{c(w) : c(w) > 0}`. Suppose `g > 1`. In the order-`(L-1)` de Bruijn graph, `c` is a balanced (in-degree equals out-degree at every vertex) and weakly connected edge multiset on its support, because `S` spells an Eulerian circuit using every edge once. Dividing every multiplicity by `g` gives `c' = c/g`, still integer-valued: balance is a homogeneous linear condition so it survives division, and the support is unchanged (`c'(w) > 0` iff `c(w) > 0`), so weak connectivity on the support survives too. Hence `c'` spells an Eulerian closed trail `W` with `spec_L(W) = c'` and `|W| = |S|/g`. Then `W^g` has length `|S|` and `spec_L(W^g) = g * spec_L(W) = c = spec_L(S)`, since each cyclic length-`L` window of `W` lifts to exactly `g` windows of `W^g`. The complete-spectrum uniqueness step (below) applied to `S` — which satisfies P2 — forces `S ~ W^g` up to rotation, contradicting primitivity, since `W^g` is a nontrivial whole-genome power and primitivity is rotation-invariant. Uniqueness is applied only to `S`; nothing requires `W^g` itself to satisfy P2. Therefore every primitive P2 spectrum has `g = 1`.

If primitive P2 genomes `S, D` satisfy `p_S = p_D`, then `|S| spec_L(D) = |D| spec_L(S)`, so their integer spectrum vectors are proportional; both have gcd `1`, hence they are equal (indeed `|S|` divides `|D|` and vice versa, so `|S| = |D|`).

The remaining step — equal complete `L`-spectra plus P2 force rotation equivalence — is the step an earlier version of this note left as an external Bresler–Bresler–Tse (2013) Theorem 3 premise. It is now a kernel-checked theorem of this repository, in two halves:

- **Short window (`K <= L-1`).** `AssemblyP1.Issue94Split.bbtCompleteSpec_of_short_window` proves rotation equivalence for arbitrary words at genome lengths below the read length; no P2, no primitivity, no Ukkonen is needed.
- **Long window (`K >= L`).** `AssemblyP1.Issue94ConcreteAntiderivative.concrete_p2LongUnique` proves the `P2`-restricted long-range uniqueness directly, by the concrete component-antiderivative construction. It consumes no external premise.

The end-to-end endpoint is the merged module `AssemblyP1.Issue94Complete`:

> **Population uniqueness theorem (oriented primitive P2), kernel-checked.** For `L >= 2`, a primitive P2 truth `S` of any positive length `G`, and **any** positive-length candidate `W` with `IsPrimitive W ∧ P2 W` (`AdmClass`): the population log likelihood of `W` is at most the truth's, and a tie forces `|W| = |S|` and `W` a cyclic rotation of `S`.

The proof chain is: the Gibbs/KL tie characterization (`AssemblyP1.PopulationGibbs`: `popLogLik_le_self'`, `popTie_iff` — the project's own formalization of Cover–Thomas, not an assumed premise); the P2-specific gcd-one/division argument and the normalized-to-ordinary step (`AssemblyP1.PopulationReduction`, issue #70); the short- and long-window spectrum uniqueness (`Issue94Split`, `Issue94ConcreteAntiderivative`); and the end-to-end wiring (`Issue94Complete.population_unique_ML`, which composes the proved `concrete_p2LongUnique` with `population_unique_ML_of_p2LongUnique`). The kernel-checker records

```
#print axioms AssemblyP1.Issue94Complete.population_unique_ML
-- [propext, Classical.choice, Quot.sound]
```

— only the three standard axioms, with no BBT or Eulerian-cycle premise appearing anywhere (full-CI leanchecker log, build 9051 jobs, 2026-10-09; merged in PR #117 at main `e9fcf01`). The older conditional route `AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation` (issues #73/#89) retains its `hPevzner : EulerianCycleObstruction` premise; it is the explicitly-conditional path, retained for the audit trail, and is now superseded by the concrete proof.

### 6.1 Do not conflate with the finite same-length uniqueness question (#211)

The population theorem above is **not** the finite oriented same-length `I_s` rotation-uniqueness question, and the two have different proof status. The finite question — can distinct tied maximizing circular genomes exist under oriented single-strand `I_s`, `|D|=|S|`, and the exact finite objective? — is source-backed but **Lean-conditional**: `AssemblyP1.BBTEulerian.bbtCompleteSpec_of_obstruction` consumes `EulerianCycleObstruction` as a hypothesis, `AssemblyP1.BBTCondense.spectrum_unique_of_P1` covers only the stronger P1 class (no repeated `(L-1)`-mer), and the #211 front's `SameLength62TieUniqueness` consumes the BBT input as an explicit `hBBT` hypothesis. The population theorem's uniqueness is kernel-checked; the finite `I_s` same-length uniqueness is not. Recording the stronger status for the population result does not promote the finite one.

This result is for the oriented spectrum model. It should not be silently transferred to reverse-complement-collapsed molecule classes, whose representation changes the observation object.

## 7. What the sequence of results teaches us

There are two distinct failure modes and therefore two distinct repairs.

**Structural/model failure.** Without a repeat/read-length boundary, the genome need not be identifiable. Bridging/Ukkonen-style conditions repair that structural ambiguity. A fixed-true-length candidate class can additionally create finite spectrum rigidity, but requiring the true length is stronger than the source's external likelihood parameter and may be operationally unrealistic. In the repaired oriented population model, P2 plus primitivity is enough for uniqueness by the kernel-checked theorem of §6.

**Finite-sampling failure.** Even primitive candidates satisfying strong intrinsic repeat restrictions can beat the truth because empirical read frequencies fluctuate. The `AABBC → AABC` example isolates this mechanism. Population ML removes it by replacing empirical frequencies with the true read distribution.

The resulting conceptual progression is therefore

> naive ML intuition
> → structural repeat obstruction
> → repeat/read-length boundary
> → finite boundary-conditioned ML
> → positive same-length slice but negative variable-length neighbors
> → replace privileged true-length knowledge by intrinsic candidate checks
> → finite failure survives because of sampling frequencies
> → population ML removes frequency noise
> → P2 plus primitivity restores oriented circular uniqueness (kernel-checked).

This ordering matters. Population data is not introduced to patch repeat ambiguity, and intrinsic candidate checks are not introduced as historical assumptions of Shomorony or Medvedev–Brudno. They repair different weaknesses exposed in sequence.

## 8. Epistemic and source boundary

The source-faithful historical question and the repaired models must remain visibly distinct.

- Shomorony et al. supply the single-strand shotgun model, bridging/information-feasibility condition, and the published open-question sentence.
- Medvedev–Brudno supply the ML formulations and graph/flow machinery whose exact referent must be stated for each result.
- Bresler–Bresler–Tse supply the complete-spectrum/Ukkonen uniqueness theorem. In the repaired oriented population result this input is now discharged by the repository's own kernel-checked proof (`concrete_p2LongUnique`); in the finite same-length `I_s` uniqueness question it remains an explicit external premise. The two statuses must not be conflated.
- The fixed-candidate-length theorem is a mathematical result under an extra candidate restriction, not a consequence of MB09's known-`N` parameter.
- P1/P2 candidate-intrinsic admissibility, primitiveness, and the population objective are project-level repaired formulations motivated by the finite analysis, not assumptions retrofitted into the literature.
- Counterexamples and proofs should continue to be labeled according to whether they are mathematical proofs, computational evidence, source interpretations, or kernel-checked Lean results.

The published question is therefore best understood not as one theorem that merely awaited a proof, but as an interface between a bridging hypothesis and an ML formulation whose candidate and representation choices matter. The repaired population model gives a cleaner positive result: the Gibbs/KL layer removes finite-frequency noise at the maximizer level, and P2, primitivity, and the repository's own complete-spectrum uniqueness proof recover uniqueness for oriented circular genomes — kernel-checked end to end. The source-faithful finite ML question remains distinct from that later repair.
