# Maximum-likelihood models for genome assembly

This note synthesizes the current AssemblyP1 research state. It deliberately separates the published Shomorony–Medvedev/Brudno question from two later repaired models introduced by this project.

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

## 3. Finite results

### 3.1 A strong positive slice: oriented, spelled, same length

Under strict oriented single-strand read types, Shomorony `I_s`, the §6.2 spelled-candidate support condition, and the additional candidate restriction `|D|=G`, the truth spectrum is rigid: `spec_L(S)` is the unique positive circulation of total `G` on the relevant de Bruijn support.

Consequently every feasible same-length spelled candidate has exactly the same length-`L` spectrum as the truth. Any objective depending only on that spectrum and the observed read counts therefore gives every such candidate the same score as the truth.

This is a genuine positive finite theorem for the **maximizer** conclusion. It does not by itself establish uniqueness of the maximizing circular sequence. It also depends essentially on the same-length candidate restriction; that restriction is not supplied merely by Medvedev–Brudno's known-`N` parameter.

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

## 6. Population ML removes exactly the remaining sampling failure

Let `d_S(w)` be the number of cyclic occurrences of the oriented length-`L` word `w` in `S`, and define the population read distribution

`p_S(w) = d_S(w) / |S|`.

For a candidate `D`, define `p_D` similarly. The per-read population log likelihood is

`ell_S(D) = sum_w p_S(w) log p_D(w)`,

with value `-infinity` when a truth-positive word has zero probability under `D`. Then

`ell_S(D) - ell_S(S) = -KL(p_S || p_D) <= 0`.

Therefore the truth is a population maximum-likelihood genome over **any** candidate class containing it. No repeat condition is required for this maximizer statement. Equality holds exactly when `p_D=p_S`, so uniqueness is no longer a statistical question: it is exactly normalized-spectrum identifiability inside the chosen candidate class.

For primitive P2-admissible circular candidates, the current uniqueness argument reduces normalized-spectrum equality to ordinary spectrum equality and then uses the Ukkonen/Bresler–Bresler–Tse spectrum-identifiability condition at `K=L-1`. Primitivity removes non-unit whole-genome scaling. Under that candidate class, the resulting repaired theorem is:

> For `L >= 2`, among primitive P2-admissible circular candidates, the true genome is the unique population maximum-likelihood genome up to cyclic rotation.

The statistical KL statement and the combinatorial uniqueness statement should remain separate in any formalization: the first is general, while the second depends on the structural candidate class.

## 7. What the sequence of results teaches us

There are two distinct failure modes and therefore two distinct repairs.

**Structural/model failure.** Without a repeat/read-length boundary, the genome need not be identifiable. Bridging/Ukkonen-style conditions address this. A fixed-true-length candidate class can additionally create finite spectrum rigidity, but requiring the true length is stronger than the source's external likelihood parameter and may be operationally unrealistic.

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
> → structural identifiability supplies uniqueness.

This ordering matters. Population data is not introduced to patch repeat ambiguity, and intrinsic candidate checks are not introduced as historical assumptions of Shomorony or Medvedev–Brudno. They repair different weaknesses exposed in sequence.

## 8. Epistemic and source boundary

The source-faithful historical question and the repaired models must remain visibly distinct.

- Shomorony et al. supply the single-strand shotgun model, bridging/information-feasibility condition, and the published open-question sentence.
- Medvedev–Brudno supply the ML formulations and graph/flow machinery whose exact referent must be stated for each result.
- The fixed-candidate-length theorem is a mathematical result under an extra candidate restriction, not a consequence of MB09's known-`N` parameter.
- P1/P2 candidate-intrinsic admissibility and the population objective are project-level repaired formulations motivated by the finite analysis, not assumptions retrofitted into the literature.
- Counterexamples and proofs should continue to be labeled according to whether they are mathematical proofs, computational evidence, source interpretations, or kernel-checked Lean results.

The published question is therefore best understood not as one theorem that merely awaited a proof, but as an interface between a bridging hypothesis and an ML formulation whose candidate and representation choices matter. The repaired population theorem is a separate positive statement explaining how the attractive ML intuition can be recovered once both structural ambiguity and finite-frequency noise are controlled.
