# Maximum-likelihood models for genome assembly

This note synthesizes the current AssemblyP1 research state. It deliberately separates the published Shomorony–Medvedev/Brudno question from two later repaired models introduced by this project.

It is the repository-oriented companion to two living publication artifacts: the LaTeX white paper (GitHub issue #51, in [`paper/`](../paper/)) and the Beamer talk for microbiology-lab software developers (GitHub issue #56, in [`talk/`](../talk/)). Both GitHub issues are closed; that closure was queue migration, not editorial completion, and both artifacts continue to evolve with the mathematics.

Statements carry epistemic tags: **[F]** source fact (a claim with a cited primary source), **[M]** mathematical theorem (human-readable proof with explicit assumptions and conclusion), **[K]** kernel-checked Lean result (no `sorry`, `admit`, or new axioms), **[K-conditional]** Lean-checked only with an explicit undischarged premise. Unmarked passages are model choices, exact computations, or source interpretation.

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

## 2. The finite boundary-conditioned question is not one model

The source interface leaves several distinctions that materially affect the answer.

First, Shomorony's theoretical model is an oriented single circular sequence with oriented length-`L` reads, whereas Medvedev–Brudno also use reverse-complement-collapsed molecular read types and a bidirected graph representation. These representations must not be silently identified.

Second, Medvedev–Brudno's externally supplied genome-size parameter `N` is not a restriction that every candidate assembly have length `N`. In the §6.1 approximation, `N` is used in the probability model; the §6.2 flow constraints do not thereby impose a fixed total candidate flow. Thus

- knowing or supplying `N=G` to the likelihood, and
- restricting every candidate `D` to `|D|=G`

are different assumptions.

Third, the conclusion can mean either that the truth is *a* maximizer or that every maximizer is the truth up to the appropriate circular-genome equivalence. These differ whenever a wrong candidate ties the truth.

Accordingly, finite results below are stated with their assumption surface rather than being collapsed into a single yes/no answer.

The Antonina board fronts #208–#217 fixed the terminology this note now uses. The finite readings of the 2016 sentence form a 64-cell universe: **objective layer** (4) × **representation panel** (2) × **candidate universe** (4) × **conclusion schema** (2). The objective layer separates the exact multinomial `E` (candidate-intrinsic `N(D)`), the fixed-`N` binomial `A` (external, assumed-known length), the §6.2 bidirected flow `F`, and the unspecified general principle `P`. The representation panel couples read types to genome equivalence: oriented reads force cyclic-shift-only equivalence; reverse-complement molecule classes force dihedral equivalence. The candidate universes run from all circular candidates (`U1`), to true-length candidates (`U2`), to §6.2 spelled candidates (`U3`), to general flows (`U4`). The conclusion schema is either `W` (the truth is a maximizer) or `S` (every maximizer is the truth up to the equivalence). No primary source selects a cell: the 2016 text names Medvedev–Brudno by bibliography only, with no formula, candidate class, tie rule, or competitor length. The finite results in §3 live in specific cells of this grid; the population theorem in §6 is a repaired model outside it, not another cell.

## 3. Finite results

### 3.1 A strong positive slice: oriented, spelled, same length

Under strict oriented single-strand read types, Shomorony `I_s`, the §6.2 spelled-candidate support condition, and the additional candidate restriction `|D|=G`, the truth spectrum is rigid: `spec_L(S)` is the unique positive circulation of total `G` on the relevant de Bruijn support.

Consequently every feasible same-length spelled candidate has exactly the same length-`L` spectrum as the truth. Any objective depending only on that spectrum and the observed read counts therefore gives every such candidate the same score as the truth.

This is a genuine positive finite theorem for the **maximizer** conclusion. It does not by itself establish uniqueness of the maximizing circular sequence. It also depends essentially on the same-length candidate restriction; that restriction is not supplied merely by Medvedev–Brudno's known-`N` parameter.

The finite uniqueness half — under source-faithful `I_s`, is the truth the unique same-length maximizer up to cyclic rotation? — is a separate, *conditional* result (classification row R9, board front #211): on `main` it is Lean-checked only with the complete-spectrum uniqueness input as an explicit premise, which is not discharged. Do not conflate it with the population uniqueness theorem of §6, which is kernel-checked without that premise.

### 3.2 Remove the candidate-length restriction: finite ML fails

The length restriction is a real mathematical boundary. In the same oriented setting, let

- truth `S = AAATT`, with `G=5`;
- competitor `D = AAAATT`, of length `6`;
- read length `L=3`.

The truth satisfies the relevant information-feasibility condition and the competitor has the same oriented support. With a realized sample containing one additional `AAA` observation (`n=6`), the longer competitor strictly beats the truth under both the candidate-intrinsic exact multinomial objective and the fixed-`N` §6.1 binomial objective.

Thus the finite positive theorem does not extend from same-length candidates to unrestricted candidate length.

### 3.3 Reverse-complement molecular representation

The repository also contains strict counterexamples for the reverse-complement-collapsed Medvedev–Brudno representation, including the integrated `AAATAT → AAAAAT` witness. These results are important, but their hypothesis must be described carefully: the established witness checks Shomorony's single-strand `I_s` while evaluating an MB09 reverse-complement molecular likelihood/flow representation. It should therefore not be advertised as a theorem about a separately strengthened double-strand bridging condition.

The source-faithful lesson is narrower and sufficient: the representation map between Shomorony's theoretical read instance and the chosen MB09 likelihood object is part of the model, not notation to suppress.

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

For the project's **oriented, primitive P2** candidate class, that identifiability step is also available, via a P2-specific gcd argument. The unrestricted claim --- primitivity plus normalized-spectrum equality implies ordinary-spectrum equality --- is **false**: at `L=2`, the primitive words `S = AAB` (`|S|=3`) and `D = AAABAB` (`|D|=6`) have `spec_2(S) = (AA:1, AB:1, BA:1)` and `spec_2(D) = (AA:2, AB:2, BA:2)`, hence identical normalized spectra `p_S = p_D = (1/3, 1/3, 1/3)` but distinct ordinary spectra. So primitivity alone is insufficient; the repair below uses P2 essentially.

The correct P2-specific argument runs as follows. Let `S` be a primitive P2 genome with `L <= |S|` and integer spectrum vector `c = spec_L(S)`; let `g = gcd{c(w) : c(w) > 0}`. Suppose `g > 1`. In the order-`(L-1)` de Bruijn graph, `c` is a balanced (in-degree equals out-degree at every vertex) and weakly connected edge multiset on its support, because `S` spells an Eulerian circuit using every edge once. Dividing every multiplicity by `g` gives `c' = c/g`, still integer-valued: balance is a homogeneous linear condition so it survives division, and the support is unchanged (`c'(w) > 0` iff `c(w) > 0`), so weak connectivity on the support survives too. Hence `c'` spells an Eulerian closed trail `W` with `spec_L(W) = c'` and `|W| = |S|/g`. Then `W^g` has length `|S|` and `spec_L(W^g) = g * spec_L(W) = c = spec_L(S)`, since each cyclic length-`L` window of `W` lifts to exactly `g` windows of `W^g`. Applying complete-spectrum uniqueness at `K=L-1` to `S` (which satisfies P2, hence Ukkonen's condition) forces `S ~ W^g` up to rotation --- contradicting primitivity, since `W^g` is a nontrivial whole-genome power and primitivity is rotation-invariant. Uniqueness is applied only to `S`; nothing requires `W^g` itself to satisfy P2. Therefore every primitive P2 spectrum has `g = 1`.

If primitive P2 genomes `S, D` satisfy `p_S = p_D`, then `|S| spec_L(D) = |D| spec_L(S)`, so their integer spectrum vectors are proportional; both have gcd `1`, hence they are equal (indeed `|S|` divides `|D|` and vice versa, so `|S| = |D|`). Complete-spectrum uniqueness then gives rotation uniqueness.

The complete-spectrum uniqueness step is the classical Bresler–Bresler–Tse (2013), Theorem 3. Their theorem constructs the `K`-mer graph from the complete `(K+1)`-spectrum and, under Ukkonen's condition—no triple or interleaved repeats of length at least `K`—gives a unique Eulerian cycle corresponding to the genome. Their repeat objects use the maximal-repeat convention, and the length of an interleaved pair is the shorter constituent. Setting `K=L-1` therefore matches P2's threshold: maximal triple repeats have length at most `L-2`, and every interleaved maximal-repeat pair has a constituent of length at most `L-2`. [F]

> **Population uniqueness theorem (oriented primitive P2).** For `L >= 2`, among primitive P2-admissible oriented circular candidates, the true genome is the unique population maximum-likelihood genome up to cyclic rotation.

The proof chain is: KL/Gibbs characterizes population ties by normalized-spectrum equality; the P2-specific gcd-one/division argument plus primitivity reduces such a tie to ordinary-spectrum equality; complete-spectrum uniqueness at `K=L-1` — the content of Bresler–Bresler–Tse (2013) Theorem 3 under Ukkonen's condition — then gives circular spectrum identifiability. [M]

**Status: fully kernel-checked, no external premises.** `AssemblyP1.Issue94Complete.population_unique_ML` (root-imported by `AssemblyP1.lean` on `main` at `e9fcf01`) proves the whole chain under exactly four hypotheses — `0 < G`, `L >= 2`, `S` primitive, `S` P2 — and **both** conclusion halves: (i) population log-likelihood dominance, `ell_S(W) <= ell_S(S)` for every admissible candidate `W` of any positive length; and (ii) unique recovery, `ell_S(W) = ell_S(S)` implies `|W| = |S|` and `W` a cyclic rotation of `S`. The theorem depends only on `[propext, Classical.choice, Quot.sound]`. In particular, the Gibbs/KL tie characterization is the project's own formalization of Cover–Thomas (`AssemblyP1.PopulationGibbs`, issue #89), and the complete-spectrum uniqueness step is *proved inside the repository* for the P2 class by the Issue94 stack's concrete P2 long-uniqueness construction (`concrete_p2LongUnique`, discharging the `P2LongUnique` input of `Issue94LongWindowSplit.population_unique_ML_of_p2LongUnique`). Neither the Gibbs/KL layer nor the BBT uniqueness step remains an external premise. [K]

**Keep this distinct from the finite same-length rotation uniqueness.** The finite question of §3.1's uniqueness half (classification row R9, board front #211) is Lean-checked on `main` only as `OrientedSameLengthML.same_length_unique_up_to_rotation_of_bbt`, which carries the complete-spectrum uniqueness input as the explicit premise `hBBT`; that premise is not discharged. The #211 module `SameLength62TieUniqueness` (board branch, not yet on `main`) supplies the `I_s ⇒ no interleaved long repeats` adapter and refutes the BBT premise's antecedent on a concrete `G=6, L=2` instance, but the finite uniqueness conclusion remains Lean-conditional on the external input. Only the population theorem above is kernel-checked without it. [K-conditional for R9; K for the population theorem]

What changed: the P2-class instance of the complete-spectrum uniqueness step is now proved inside the repository (Issue94 stack), so the population theorem no longer cites the Bresler–Bresler–Tse theorem as a premise. [K]

This theorem bypasses the repository's attempted direct matching/cycle proof. The latter still has a genuine maximal-extension gap (see the [audit of the direct circular P2 proof](audit-p2-direct-proof-maximal-extension-2026-09-21.md)); that gap invalidates that alternative proof route, not the theorem above.

This result is for the oriented spectrum model. It should not be silently transferred to reverse-complement-collapsed molecule classes, whose representation changes the observation object.

## 7. What the sequence of results teaches us

There are two distinct failure modes and therefore two distinct repairs.

**Structural/model failure.** Without a repeat/read-length boundary, the genome need not be identifiable. Bridging/Ukkonen-style conditions repair that structural ambiguity. A fixed-true-length candidate class can additionally create finite spectrum rigidity, but requiring the true length is stronger than the source's external likelihood parameter and may be operationally unrealistic. In the repaired oriented population model, P2 plus primitivity is enough for uniqueness by the spectrum theorem above — now kernel-checked end to end, with no external uniqueness premise.

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
> → P2 plus primitivity restores oriented circular uniqueness.

This ordering matters. Population data is not introduced to patch repeat ambiguity, and intrinsic candidate checks are not introduced as historical assumptions of Shomorony or Medvedev–Brudno. They repair different weaknesses exposed in sequence.

## 8. Epistemic and source boundary

The source-faithful historical question and the repaired models must remain visibly distinct.

- Shomorony et al. supply the single-strand shotgun model, bridging/information-feasibility condition, and the published open-question sentence.
- Medvedev–Brudno supply the ML formulations and graph/flow machinery whose exact referent must be stated for each result.
- Bresler–Bresler–Tse supply the complete-spectrum/Ukkonen uniqueness theorem, a source fact about the general complete-spectrum problem. For the repaired oriented population result, the P2-class instance of that step is now proved inside the repository (Issue94 stack), so the population theorem carries no external uniqueness premise; the *finite* same-length uniqueness (R9, #211) still cites the general theorem as a premise and remains Lean-conditional. Neither settles the finite 2016 ML question by itself.
- The fixed-candidate-length theorem is a mathematical result under an extra candidate restriction, not a consequence of MB09's known-`N` parameter.
- P1/P2 candidate-intrinsic admissibility, primitiveness, and the population objective are project-level repaired formulations motivated by the finite analysis, not assumptions retrofitted into the literature.
- Counterexamples and proofs should continue to be labeled according to whether they are mathematical proofs, computational evidence, source interpretations, or kernel-checked Lean results.

The published question is therefore best understood not as one theorem that merely awaited a proof, but as an interface between a bridging hypothesis and an ML formulation whose candidate and representation choices matter. The repaired population model gives a cleaner positive result, now fully kernel-checked: KL/Gibbs removes finite-frequency noise at the maximizer level, while P2, primitivity, and internally proved complete-spectrum uniqueness recover oriented circular uniqueness with no external premise. The source-faithful finite ML question remains distinct from that later repair.

This is also why the synthesis does not claim the historical readings solved prematurely. The #208–#217 classification resolves every *determinate, source-supported* finite interpretation — the negative rows under both sequence-nameable objectives (exact multinomial and fixed-`N` binomial), the §6.2 flow readings under molecule types, the oriented variable-length reading, and the one narrow positive same-length slice (maximizer unconditional, uniqueness Lean-conditional). It explicitly does **not** extend the claim to: the referent question, which no primary source settles; the publisher's supplementary material, which remains uninspected; the Bresler doubled-strand `2G` concatenation convention, a different paper's model whose row is open in both directions; or the unspecified general principle, which is not a determinate proposition. Historical closure of the publication issues (#51 paper, #56 talk) was queue migration, not editorial completion; the artifacts in [`paper/`](../paper/) and [`talk/`](../talk/) remain living documents.
