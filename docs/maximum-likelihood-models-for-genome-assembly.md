# Maximum-likelihood models for genome assembly

This note synthesizes the current AssemblyP1 research state. It deliberately separates the published Shomorony–Medvedev/Brudno question from two later repaired models introduced by this project. It is the repository-oriented companion to two living publication artifacts: the LaTeX white paper (GitHub issue #51, in [`paper/`](../paper/)) and the Beamer talk for microbiology-lab software developers (GitHub issue #56, in [`talk/`](../talk/)). Both GitHub issues are closed; that closure was queue migration, not editorial completion, and both artifacts continue to evolve with the mathematics.

**Epistemic tags.** Every substantive claim below carries one of: **[source]** source fact (a claim with a cited primary source); **[model]** model choice (a modelling decision no source forces); **[compute]** exact computation (a finite arithmetic verification); **[theorem]** mathematical theorem (a human-readable proof with explicit assumptions and conclusion); **[lean]** Lean check (kernel-checked with no `sorry`, `admit`, or new axioms); **[lean?]** Lean check conditional on an explicit undischarged premise.

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

Thus even the complete noiseless 2-mer information cannot distinguish `S` from `D`; under the corresponding uniform-start read model they induce the same read distribution. This is a structural ambiguity, not a failure caused by unlucky finite sampling or by a particular likelihood optimizer. [compute]

This is why the repeat/read-length boundary comes first. Shomorony et al. formulate an information-feasibility condition `I_s`: the reads cover the genome, every triple repeat is all-bridged, and every interleaved pair of repeats is bridged in the required sense. Their Not-So-Greedy construction recovers the circular sequence under this condition. The 2016 Discussion then asks whether such bridging conditions also guarantee that the maximum-likelihood sequence is the true sequence, referring to the maximum-likelihood assembly formulation of Medvedev and Brudno (2009). [source]

The question is therefore not whether arbitrary read sets identify arbitrary genomes. It is whether maximum likelihood inherits the recovery guarantee after the structural repeat obstruction has been removed.

## 2. The 2016 question is not one model

The 2016 sentence asks whether bridging makes "the maximum-likelihood sequence" the true sequence, but the sources do not pin down the referent of that phrase. The distinctions below are not pedantry; each one changes the answer, and collapsing them is the historical ambiguity this project repairs. [source]

First, Shomorony's theoretical model is an oriented single circular sequence with oriented length-`L` reads, whereas Medvedev–Brudno also use reverse-complement-collapsed molecular read types and a bidirected graph representation. These representations must not be silently identified: a reverse-complement molecule and its source are different observation objects, and the natural genome equivalence changes with them (cyclic shift alone under oriented reads; dihedral, i.e. cyclic shift together with reverse complement, under molecule classes). [source + model]

Second, Medvedev–Brudno's externally supplied genome-size parameter `N` is not a restriction that every candidate assembly have length `N`. In the §6.1 approximation, `N` is used in the probability model; the §6.2 flow constraints do not thereby impose a fixed total candidate flow. Thus

- knowing or supplying `N=G` to the likelihood, and
- restricting every candidate `D` to `|D|=G`

are different assumptions. [source + model]

Third, the conclusion can mean either that the truth is *a* maximizer or that every maximizer is the truth up to the appropriate circular-genome equivalence. These differ whenever a wrong candidate ties the truth. [source]

Fourth, the ML object itself differs between the two Medvedev–Brudno formulations. §6.1 is a product of binomial marginals over read types with fixed external `N`. §6.2 optimizes vertex throughputs of a bidirected flow and says its output "represents a (non-contiguous) assembly"; a flow optimum is not automatically an ML *sequence* without a flow-to-sequence rule. The #214 front makes this explicit: the general §6.2 candidate universe contains possibly-non-contiguous flows, and whether a flow optimum can be called an ML sequence at all is a separate question. [source]

The Antonina board fronts #208–#217 fixed the terminology this note now uses. The #208 source audit enumerates the source-supported readings of the 2016 sentence as a finite **64-cell universe**: objective layer (4) × representation panel (2) × candidate universe (4) × conclusion schema (2). The objective layer separates the exact multinomial `E` (candidate-intrinsic `N(D)`), the fixed-`N` binomial `A` (external, assumed-known length), the §6.2 bidirected flow `F`, and the unspecified general principle `P`. The representation panel couples read types to genome equivalence: oriented reads force cyclic-shift-only equivalence; reverse-complement molecule classes force dihedral equivalence. The candidate universes run from all circular candidates (`U1`), to true-length candidates (`U2`), to §6.2 spelled candidates (`U3`), to general flows (`U4`). The conclusion schema is either `W` (the truth is a maximizer) or `S` (every maximizer is the truth up to the equivalence). No primary source selects a cell: the 2016 text names Medvedev–Brudno by bibliography only, with no formula, candidate class, tie rule, or competitor length. [source]

The #217 META synthesis integrates the leaf fronts #208–#216 into a row matrix. The finite results below are its rows; the repaired population theorem of §6 is a project-level model *outside* the 64-cell grid, not another cell. [source + model]

## 3. Finite results

### 3.1 A strong positive slice: oriented, spelled, same length

Under strict oriented single-strand read types, Shomorony `I_s`, the §6.2 spelled-candidate support condition, and the additional candidate restriction `|D|=G`, the truth spectrum is rigid: `spec_L(S)` is the unique positive circulation of total `G` on the relevant de Bruijn support. [theorem]

Consequently every feasible same-length spelled candidate has exactly the same length-`L` spectrum as the truth. Any objective depending only on that spectrum and the observed read counts therefore gives every such candidate the same score as the truth. [theorem]

This is a genuine positive finite theorem for the **maximizer** conclusion. It does not by itself establish uniqueness of the maximizing circular sequence. The positive slice also depends essentially on the same-length candidate restriction; that restriction is not supplied merely by Medvedev–Brudno's known-`N` parameter. [theorem]

The finite uniqueness half — under source-faithful `I_s`, is the truth the *unique* same-length maximizer up to cyclic rotation? — is a separate, conditional result (classification row R9, board front #211), treated in §6.2. It must not be conflated with the population uniqueness theorem of §6, which is kernel-checked without an external premise. [lean?]

### 3.2 Remove the candidate-length restriction: finite ML fails

The length restriction is a real mathematical boundary. In the same oriented setting, let

- truth `S = AAATT`, with `G=5`;
- competitor `D = AAAATT`, of length `6`;
- read length `L=3`.

The truth satisfies the relevant information-feasibility condition and the competitor contains every observed read type. With a realized sample containing one additional `AAA` observation (`n=6`), the longer competitor strictly beats the truth under both the candidate-intrinsic exact multinomial objective and the fixed-`N` §6.1 binomial objective. [theorem]

The mechanism is general, not a census accident (front #210). If a feasible sample from `S` is realized and `D` assigns higher probability to some observed truth read type `w`, then adding `m` further observations of `w` multiplies the exact likelihood ratio by `(p_D(w)/p_S(w))^m` and the §6.1 ratio by an explicit computable factor. For `AAATT → AAAATT` at external `N=5` the exact ratio goes from `3125/3888` at `M=0` to `15625/11664 > 1` at `M=1`, and the §6.1 ratio from `81/128` to `81/64`. [theorem + compute] These are the first instances of three infinite families of strict counterexamples proved in [`docs/source-notes/oriented-variable-length-se62.md`](source-notes/oriented-variable-length-se62.md); the strongest (growing competitor `D_M = A^{3+M}TT`) has exact ratio `(5/(5+M))^{5+M}·(1+M)^{1+M} > 1` for every `M ≥ 1`. [theorem]

A kernel-checked finite instance of the same witness is on `main`: [`AssemblyP1.OrientedVariableLengthSe62`](../AssemblyP1/OrientedVariableLengthSe62.lean) discharges the full-strength `I_s` predicate by `decide`, checks the literal §6.2 flow feasibility of both candidates, and certifies the strict exact ratios `15625/11664` (`M=1`) and `2109375/823543` (`M=2`) with axioms `[propext, Classical.choice, Quot.sound]` only. [lean]

Thus the finite positive theorem does not extend from same-length candidates to unrestricted candidate length. [theorem]

### 3.3 Reverse-complement molecular representation

The repository also contains strict counterexamples for the reverse-complement-collapsed Medvedev–Brudno representation. The integrated `AAATAT → AAAAAT` witness is kernel-checked on `main` in [`AssemblyP1.SameLengthSection62Counterexample`](../AssemblyP1/SameLengthSection62Counterexample.lean): the truth is single-strand `I_s`-feasible, the candidates are evaluated in the MB09 molecular likelihood/flow representation, and the competitor wins with exact ratio `3` and §6.1 ratio `5`. [lean]

A second, same-length bidirected witness strengthens the feasibility requirement from MB09's per-vertex bound `1` to the per-observation rule `d_w >= x_w`: truth `S = ATATACAC`, competitor `D = ATACACAC`, both of length `G=8`, read length `L=3`, external `N=8`; both are per-occurrence feasible, and `D` beats `S` under both objectives (exact ratio `3/2`, §6.1 ratio `9/5`). It is kernel-checked in `AssemblyP1.PerOccurrenceSameLengthCounterexample` on the #212 front branch (not merged to `main` as of this writing). The earlier `AAATAT → AAAAAT` refutation covers only per-vertex feasibility — there the truth itself is not per-occurrence feasible — so the two refutations are logically independent. [lean]

The per-occurrence rule `d_w >= x_w` is a project-level strengthening of MB09 §6.2, not a source fact; the source's literal §6.2 bound is per-vertex. [source + model]

### 3.4 The general §6.2 flow domain

MB09 §6.2's genuine target is possibly-non-contiguous feasible bidirected flows, not circular spelled genomes. The #214 front kernel-checks the integral argmax: among integer flows the existing strict spelled-circuit witnesses are feasible and optimal, so dominance fails in the full flow optimizer. But MB09 §5.1 discusses half-integral biflows as an algorithmic relaxation, and the binomial objective extended to half-integral throughputs strictly beats the integral optima: for the tied integer flows with throughputs `(2,1,1)` and `(3,1,1)`, the half-integral average at `(5/2,1,1)` improves the `AAA` marginal by `625/576 > 1`. Three levels must be kept separate: (i) the original integer genomics domain, (ii) the half-integral biflow approximation, (iii) an optional continuously-extended likelihood on relaxed flows. No automatic transfer of optimality or interpretation between them. [theorem + model] These results are on the #214 branch (`AssemblyP1.Section62NonSpelledFlow`), not yet on `main`. [lean]

This is also where the flow-to-sequence gap lives: a flow optimum is not automatically an ML sequence without a flow-to-sequence rule, so a theorem about ML flows is not automatically a theorem about *the* ML sequence. [model]

### 3.5 What the finite classification settles, and what it leaves open

The #217 META synthesis reports that every *determinate, source-supported* finite interpretation is resolved: eleven negative rows under the sequence-nameable objectives (nine kernel-checked: R1, R2, R5, R6, R10–R14; two exact-arithmetic: R3, R4), together with the narrow positive slice of §3.1 (maximizer kernel-checked, uniqueness Lean-conditional, row R9). The oriented variable-length reading (§3.2, #210) and the bidirected per-occurrence readings (#212 same-length, #213 variable-length) are resolved as negative witnesses; #214 resolves the general non-spelled flow domain; #215 classifies the oriented ↔ double-strand transfer as an exact non-equivalence off a precise compatibility locus; #216 records the implication lattice and its uncommitted Part 6 is superseded by the kernel-checked #210 result. [source + lean]

The classification explicitly does **not** close three residues. R16 is the Bresler doubled-strand `2G`-concatenation convention — a different paper's project-level convention, not a determinate source row; its known witness is kernel-checked *inadmissible* under the remap, and it is open in both directions. R17 is the unspecified general ML principle, which is not a determinate proposition (the 2016 text names no objective). R18 is a disclosed project-level duplex model (two disjoint circles `S`, `rc(S)`), not a source row. [source + model + lean]

## 4. Why fixed true candidate length is an unsatisfying repair

The same-length theorem shows that a strong extra axiom can make the finite problem behave well. But `|D|=G` gives the candidate class privileged access to the true target length. That may be unavailable operationally, and it is stronger than merely supplying a genome-size parameter to an objective. [model]

This motivates a first *new* model, not a reinterpretation of the historical papers: replace true-length knowledge with candidate-intrinsic structural checks. [model]

The project considered repeat/read-length predicates intrinsic to each candidate, together with primitiveness where needed. A particularly strong test is P1: no repeated `(L-1)`-mer. P1 is stronger than the proposed P2/Ukkonen-style repeat condition, so failure under P1 also rules out the weaker structural repair as a general finite theorem. [model + theorem]

## 5. Intrinsic structural checks still do not repair finite sampling

The decisive finite witness is

- truth `S = AABBC`, `L=3`;
- realized starts `(0,3)`, giving reads `{AAB,BCA}`;
- competitor `D = AABC`.

Both circular genomes are primitive and satisfy P1. The realized sample satisfies the truth-side information-feasibility condition. Yet under the candidate-intrinsic exact multinomial likelihood,

`L(D) / L(S) = (5/4)^2 = 25/16 > 1`.

[theorem + compute]

This failure is qualitatively different from repeat ambiguity. The wrong genome wins because the finite sample happened to include only reads to which the shorter candidate assigns probability `1/4`, while the truth assigns probability `1/5`. Structural admissibility has not failed; empirical frequencies have fluctuated in favor of the wrong candidate. [theorem]

This is the point at which a second repair becomes justified. Strengthening the repeat axioms again would target the wrong mechanism. [model]

## 6. Population ML removes the remaining sampling failure

Let `d_S(w)` be the number of cyclic occurrences of the oriented length-`L` word `w` in `S`, and define the population read distribution

`p_S(w) = d_S(w) / |S|`.

For a candidate `D`, define `p_D` similarly. The per-read population log likelihood is

`ell_S(D) = sum_w p_S(w) log p_D(w)`,

with value `-infinity` when a truth-positive word has zero probability under `D`. Then

`ell_S(D) - ell_S(S) = -KL(p_S || p_D) <= 0`.

[theorem]

Therefore the truth is a population maximum-likelihood genome over **any** candidate class containing it. No repeat condition is required for this maximizer statement. Equality holds exactly when `p_D=p_S`, so uniqueness is no longer a statistical question: it is normalized-spectrum identifiability inside the chosen candidate class. [theorem]

### 6.1 The kernel-checked population theorem (oriented, primitive P2)

For the project's **oriented, primitive P2** candidate class, the identifiability step is now fully kernel-checked. The unrestricted claim — primitivity plus normalized-spectrum equality implies ordinary-spectrum equality — is **false**: at `L=2`, the primitive words `S = AAB` (`|S|=3`) and `D = AAABAB` (`|D|=6`) have `spec_2(S) = (AA:1, AB:1, BA:1)` and `spec_2(D) = (AA:2, AB:2, BA:2)`, hence identical normalized spectra `p_S = p_D = (1/3, 1/3, 1/3)` but distinct ordinary spectra. So primitivity alone is insufficient; the repair uses P2 essentially. [compute]

The P2-specific argument runs as follows. Let `S` be a primitive P2 genome with `L <= |S|` and integer spectrum vector `c = spec_L(S)`; let `g = gcd{c(w) : c(w) > 0}`. Suppose `g > 1`. In the order-`(L-1)` de Bruijn graph, `c` is a balanced (in-degree equals out-degree at every vertex) and weakly connected edge multiset on its support, because `S` spells an Eulerian circuit using every edge once. Dividing every multiplicity by `g` gives `c' = c/g`, still integer-valued: balance is a homogeneous linear condition so it survives division, and the support is unchanged (`c'(w) > 0` iff `c(w) > 0`), so weak connectivity on the support survives too. Hence `c'` spells an Eulerian closed trail `W` with `spec_L(W) = c'` and `|W| = |S|/g`. Then `W^g` has length `|S|` and `spec_L(W^g) = g * spec_L(W) = c = spec_L(S)`, since each cyclic length-`L` window of `W` lifts to exactly `g` windows of `W^g`. Complete-spectrum uniqueness applied to `S` (which satisfies P2, hence Ukkonen's condition) forces `S ~ W^g` up to rotation — contradicting primitivity, since `W^g` is a nontrivial whole-genome power and primitivity is rotation-invariant. Uniqueness is applied only to `S`; nothing requires `W^g` itself to satisfy P2. Therefore every primitive P2 spectrum has `g = 1`. [theorem]

If primitive P2 genomes `S, D` satisfy `p_S = p_D`, then `|S| spec_L(D) = |D| spec_L(S)`, so their integer spectrum vectors are proportional; both have gcd `1`, hence they are equal (indeed `|S|` divides `|D|` and vice versa, so `|S| = |D|`). Complete-spectrum uniqueness then gives rotation uniqueness. [theorem]

The remaining step — equal complete `L`-spectra plus P2 force rotation equivalence — was left as an external Bresler–Bresler–Tse (2013) Theorem 3 premise in earlier versions of this note. It is now a kernel-checked theorem of this repository, in two halves: [theorem + lean]

- **Short window (`K <= L-1`).** `AssemblyP1.Issue94Split.bbtCompleteSpec_of_short_window` proves rotation equivalence for arbitrary words at genome lengths below the read length; no P2, no primitivity, no Ukkonen is needed. [lean]
- **Long window (`K >= L`).** `AssemblyP1.Issue94ConcreteAntiderivative.concrete_p2LongUnique` proves the P2-restricted long-range uniqueness directly, by the concrete component-antiderivative construction. It consumes no external premise. [lean]

The end-to-end endpoint is the merged module [`AssemblyP1.Issue94Complete`](../AssemblyP1/Issue94Complete.lean):

> **Population uniqueness theorem (oriented primitive P2), kernel-checked.** For `L >= 2`, a primitive P2 truth `S` of any positive length `G`, and **any** positive-length candidate `W` with `IsPrimitive W ∧ P2 W` (`AdmClass`): the population log likelihood of `W` is at most the truth's, and a tie forces `|W| = |S|` and `W` a cyclic rotation of `S`. [lean]

`AssemblyP1.Issue94Complete.population_unique_ML` proves this under exactly four hypotheses — `0 < G`, `L >= 2`, `S` primitive, `S` P2 — and **both** conclusion halves: (i) population log-likelihood dominance over any-length admissible candidates; and (ii) unique recovery, a tie implying equal length and cyclic rotation. The Gibbs/KL tie characterization is the project's own formalization of Cover–Thomas (`AssemblyP1.PopulationGibbs`: `popLogLik_le_self'`, `popTie_iff`), and the complete-spectrum uniqueness step is proved inside the repository for the P2 class. **Neither the Gibbs/KL layer nor the BBT uniqueness step remains an external premise.** [lean]

The kernel-checker records

```
#print axioms AssemblyP1.Issue94Complete.population_unique_ML
-- [propext, Classical.choice, Quot.sound]
```

— only the three standard axioms, with no BBT or Eulerian-cycle premise appearing anywhere (build `9010` jobs, 2026-10-09, re-measured on `main` at `d7bd160`). The older conditional route `AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation` (issues #73/#89) retains its `hPevzner : EulerianCycleObstruction` premise; it is the explicitly-conditional path, retained for the audit trail, and is now superseded by the concrete proof. [lean]

This theorem bypasses the repository's attempted direct matching/cycle proof. The latter still has a genuine maximal-extension gap (see the [audit of the direct circular P2 proof](audit-p2-direct-proof-maximal-extension-2026-09-21.md)); that gap invalidates that alternative proof route, not the theorem above. [theorem]

This result is for the oriented spectrum model. It should not be silently transferred to reverse-complement-collapsed molecule classes, whose representation changes the observation object. [model]

### 6.2 Do not conflate with the finite same-length uniqueness question (#211)

The population theorem above is **not** the finite oriented same-length `I_s` rotation-uniqueness question (classification row R9), and the two have different proof status. On `main`, the finite uniqueness half is Lean-checked only as `AssemblyP1.OrientedSameLengthML.same_length_unique_up_to_rotation_of_bbt`, which carries the complete-spectrum uniqueness input as the explicit premise `hBBT` (equal length-`L` spectrum implies cyclic shift); that premise is **not discharged**. [lean?]

The #211 front sharpens the residue. Its module `SameLength62TieUniqueness` (board branch, not merged to `main`) shows that the *unconditional* form of the external premise is false in general — `bbt_premise_refuted_G6_L2` exhibits two length-`6` binary circular words with equal length-`2` spectra that are not cyclic shifts — and isolates the source-conditioned residue as the fibre-rigidity proposition `SupportRigidity` / `FibreFreedomForcesLongRepeat`, which `I_s` is expected to force but which is not formalized. `AssemblyP1.BBTEulerian.bbtCompleteSpec_of_obstruction` consumes `EulerianCycleObstruction` as a hypothesis, and `AssemblyP1.BBTCondense.spectrum_unique_of_P1` covers only the stronger P1 class (no repeated `(L-1)`-mer). [lean?]

So the finite same-length `I_s` uniqueness is source-backed but Lean-conditional on an external complete-spectrum input, while the population theorem's uniqueness is kernel-checked without it. Recording the stronger status for the population result does not promote the finite one. [lean?]

## 7. What the sequence of results teaches us

There are two distinct failure modes and therefore two distinct repairs.

**Structural/model failure.** Without a repeat/read-length boundary, the genome need not be identifiable. Bridging/Ukkonen-style conditions repair that structural ambiguity. A fixed-true-length candidate class can additionally create finite spectrum rigidity, but requiring the true length is stronger than the source's external likelihood parameter and may be operationally unrealistic. In the repaired oriented population model, P2 plus primitivity is enough for uniqueness by the kernel-checked theorem of §6.1. [model + theorem]

**Finite-sampling failure.** Even primitive candidates satisfying strong intrinsic repeat restrictions can beat the truth because empirical read frequencies fluctuate. The `AABBC → AABC` example isolates this mechanism. Population ML removes it by replacing empirical frequencies with the true read distribution. [theorem]

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

This ordering matters. Population data is not introduced to patch repeat ambiguity, and intrinsic candidate checks are not introduced as historical assumptions of Shomorony or Medvedev–Brudno. They repair different weaknesses exposed in sequence. [model]

## 8. Epistemic and source boundary

The source-faithful historical question and the repaired models must remain visibly distinct.

- Shomorony et al. supply the single-strand shotgun model, the bridging/information-feasibility condition, and the published open-question sentence. [source]
- Medvedev–Brudno supply the ML formulations and graph/flow machinery whose exact referent must be stated for each result. [source]
- Bresler–Bresler–Tse supply the complete-spectrum/Ukkonen uniqueness theorem, a source fact about the general complete-spectrum problem. In the repaired oriented population result this input is now discharged by the repository's own kernel-checked proof (`concrete_p2LongUnique`); in the finite same-length `I_s` uniqueness question it remains an explicit external premise. The two statuses must not be conflated. [source + lean + lean?]
- The fixed-candidate-length theorem is a mathematical result under an extra candidate restriction, not a consequence of MB09's known-`N` parameter. [model + theorem]
- P1/P2 candidate-intrinsic admissibility, primitiveness, and the population objective are project-level repaired formulations motivated by the finite analysis, not assumptions retrofitted into the literature. [model]
- Counterexamples and proofs are labeled according to whether they are mathematical theorems, exact computations, source interpretations, or kernel-checked Lean results. [model]

The published question is therefore best understood not as one theorem that merely awaited a proof, but as an interface between a bridging hypothesis and an ML formulation whose candidate and representation choices matter. The repaired population model gives a cleaner positive result: the Gibbs/KL layer removes finite-frequency noise at the maximizer level, and P2, primitivity, and the repository's own complete-spectrum uniqueness proof recover uniqueness for oriented circular genomes — kernel-checked end to end, with no external premise. The source-faithful finite ML question remains distinct from that later repair. [model + lean]

This is also why the synthesis does not claim the historical readings solved prematurely. The #208–#217 classification resolves every *determinate, source-supported* finite interpretation — the negative rows under both sequence-nameable objectives (exact multinomial and fixed-`N` binomial), the §6.2 flow readings under molecule types, the oriented variable-length reading, and the one narrow positive same-length slice (maximizer unconditional, uniqueness Lean-conditional). It explicitly does **not** extend the claim to: the referent question, which no primary source settles; the publisher's supplementary material, which remains uninspected; the Bresler doubled-strand `2G` concatenation convention, a different paper's model whose row is open in both directions; the disclosed two-disjoint-circles duplex model; or the unspecified general principle, which is not a determinate proposition. Historical closure of the publication issues (#51 paper, #56 talk) was queue migration, not editorial completion; the artifacts in [`paper/`](../paper/) and [`talk/`](../talk/) remain living documents. [source + model]
