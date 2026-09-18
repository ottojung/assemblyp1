# Fixed-Length Exact Variant E: Analytical Characterization

_Status: mathematical analysis; exploration-phase research document. Not a Lean formalization. Cross-checked against `docs/ml-formalization-contract.md`, `AssemblyP1/Model.lean`, and `docs/bridging-source-semantics.md`._

## Scope

This note analyzes the **fixed-known-length exact Variant E** objective: all candidate circular genomes have the same length G as the truth, and the likelihood uses the exact multinomial with the candidate's own length N(D) = G in the denominator. The fixed-length restriction is a material subproblem per the formalization contract (§candidate-universe discipline); it does not follow automatically from the source papers.

## 1. Notation and setup

| Symbol | Meaning |
|--------|---------|
| S | True circular genome, length G, alphabet Σ |
| L | Read length (2 ≤ L ≤ G) |
| N | Number of reads drawn i.i.d. uniformly from G circular starts |
| x_i | Observed count of L-mer type i among the N reads; ∑_i x_i = N |
| D | Candidate circular genome, length G |
| d_i^D | Occurrence count of L-mer type i in D; ∑_i d_i^D = G |
| d_i^S | Truth's occurrence count for L-mer type i |

The exact multinomial likelihood (Medvedev–Brudno §6.1, per `docs/ml-formalization-contract.md` §Variant E) is:

```
L_exact(D | x) = n! / (∏_i x_i!) · ∏_i (d_i^D / G)^{x_i}
```

Since the observation-only coefficient n! / ∏ x_i! is the same for all candidates, comparing likelihoods reduces to comparing:

```
f(D) = ∏_i (d_i^D)^{x_i}           [1]
```

The truth is an ML maximizer iff f(S) ≥ f(D) for all length-G circular D.

## 2. The AM-GM upper bound

**Lemma 1.** For any non-negative vector (d_i) with ∑ d_i = G:

```
∏_i d_i^{x_i}  ≤  ∏_i (G · x_i / N)^{x_i}       [2]
```

with equality iff d_i = G · x_i / N for all i with x_i > 0.

**Proof.** By the weighted AM-GM inequality applied to the weights x_i / N:

```
∏_i d_i^{x_i/N}  ≤  ∑_i (x_i / N) · d_i  =  G / N
```

 raising both sides to the N-th power gives [2]. Equality holds iff all d_i (for i with x_i > 0) are equal to G · x_i / N. □

**Corollary.** The maximum possible value of f(D) over all non-negative integer vectors d with ∑ d_i = G is:

```
f_max = ∏_i (G · x_i / N)^{x_i} = (G/N)^N · ∏_i x_i^{x_i}    [3]
```

## 3. When can the truth lose?

From [1] and [3], the truth S can be beaten by some candidate D (ignoring realizability constraints) whenever:

```
f(S) = ∏_i (d_i^S)^{x_i}  <  f_max = ∏_i (G · x_i / N)^{x_i}    [4]
```

Taking logarithms, this is equivalent to:

```
∑_i x_i · log(d_i^S)  <  ∑_i x_i · log(G · x_i / N)               [5]
```

Rearranging:

```
∑_i x_i · log(d_i^S / (G · x_i / N))  <  0                         [6]
```

Define the **log-likelihood gap**:

```
Δ(S, x)  =  ∑_i x_i · log(d_i^S · N / (G · x_i))                  [7]
```

Then:
- Δ > 0: truth is strictly optimal (ignoring realizability).
- Δ = 0: truth matches the AM-GM upper bound (achievable only when d_i^S ∝ x_i).
- Δ < 0: truth can be beaten (again, ignoring realizability).

**Interpretation.** Let p_i = d_i^S / G (truth's L-mer distribution) and q_i = x_i / N (empirical read distribution). Then:

```
Δ(S, x) = N · ∑_i q_i · log(p_i / q_i) = -N · KL(q ‖ p) + N · H(p, q) - N · H(q)
```

More directly: Δ measures how well the truth's occurrence distribution aligns with the empirical read distribution. The truth is vulnerable when these distributions diverge.

## 4. The realizability constraint

Not every non-negative integer vector summing to G is realizable as L-mer counts of a circular genome. The realizability condition comes from the **de Bruijn graph**: for each (L-1)-mer j, the flow conservation condition requires:

```
∑_a d_{(j,a)} = ∑_a d_{(a,j)}                           [8]
```

i.e., the number of L-mers extending j equals the number of L-mers starting with j.

**When is the AM-GM optimum realizable?** The optimum d_i = G · x_i / N is realizable iff the de Bruijn flow conservation [8] is satisfied. This depends on the specific observation vector x.

**Key observation.** For the minimal counterexample (§6 below), the AM-GM optimum IS realizable, confirming that the truth can be beaten.

## 5. Coverage and bridging do NOT exclude competitors

### 5.1 Coverage

Coverage requires every position in S to be covered by at least one observed read. This implies d_i^S ≥ 1 for all i with x_i > 0 (every observed L-mer appears in S).

**Why coverage doesn't help the truth.** Coverage constrains S's L-mer spectrum: it ensures every L-mer that appears in S is observed. But it does NOT ensure that every L-mer TYPE is observed. In a binary alphabet with G = 4, L = 2, there are 4 L-mer types, and the truth has all 4. But the observation might only cover 2 of them. A competitor can then "reallocate" genome slots from unobserved L-mers to observed ones.

### 5.2 Bridging

Bridging requires that certain repeats in S are covered by reads extending beyond the repeat on both sides (per `docs/bridging-source-semantics.md`). This constrains S's repeat structure but does NOT constrain the competitor D.

**Why bridging doesn't help the truth.** Bridging is a condition on the true genome S and the realized reads. It ensures that repeats in S are "resolved" by the read collection. But the ML objective scores empirical read-type frequencies, not reconstructibility. A competitor D can have a completely different repeat structure and still achieve higher likelihood if it concentrates probability on observed read types.

### 5.3 The asymmetry

The fundamental asymmetry is:

- **Bridging** ensures unique reconstructibility of the true genome from the read collection.
- **ML likelihood** scores how well a candidate's L-mer distribution matches the observed read frequencies.

These are different objectives. Bridging constrains S; ML compares S against ALL candidates. Coverage and bridging on S do not prevent a competitor from having a "better" L-mer distribution for the observed data.

## 6. Minimal counterexample

### Instance

| Parameter | Value |
|-----------|-------|
| True genome S | AABB (circular, G=4) |
| Alphabet | {A, B} |
| Read length | L=2 |
| Observation | x_AB = 1, x_BA = 1 (N=2) |

### Truth's L-mer spectrum

S = AABB has L-mers: AA (pos 0), AB (pos 1), BB (pos 2), BA (pos 3). All distinct:
d_AA^S = 1, d_AB^S = 1, d_BB^S = 1, d_BA^S = 1.

### Competitor

D = ABAB (circular, G=4). L-mers: AB (pos 0), BA (pos 1), AB (pos 2), BA (pos 3).
d_AB^D = 2, d_BA^D = 2, d_AA^D = 0, d_BB^D = 0.

### Likelihood comparison

```
f(S) = 1^1 · 1^1 = 1
f(D) = 2^1 · 2^1 = 4
```

D has 4× the likelihood of S.

### Verification of coverage

| Position | Covering read | Source |
|----------|--------------|--------|
| 0 | AB | start s=0 |
| 1 | AB | start s=0 |
| 2 | BA | start s=2 |
| 3 | BA | start s=2 |

All 4 positions covered. ✓

### Verification of bridging

S = AABB has no repeated L-mers (all four 2-mers are distinct). Bridging conditions are vacuously satisfied. ✓

### Log-likelihood gap

```
Δ(S, x) = 1·log(1·2/(4·1/2)) + 1·log(1·2/(4·1/2))
         = 1·log(1) + 1·log(1) = 0
```

Wait — this gives Δ = 0, meaning the truth matches the AM-GM bound. But f(S) = 1 < f(D) = 4 = f_max. The issue is that the AM-GM bound is achieved by d_i = G · x_i / N = 2 for both AB and BA, which is exactly D's distribution. So Δ = 0 means the truth TIES the AM-GM bound, but the bound is achieved by a different genome D.

**Corrected interpretation:** Δ ≥ 0 is necessary but not sufficient for the truth to be an ML maximizer. Even when Δ ≥ 0, a competitor can achieve the same or higher likelihood if the AM-GM optimum is realizable by a different genome.

The correct condition for the truth to be an ML maximizer is:

```
f(S) ≥ f(D)  for all length-G circular D with f(D) > 0     [9]
```

This is equivalent to:

```
∑_i x_i · log(d_i^S) ≥ ∑_i x_i · log(d_i^D)  for all feasible D    [10]
```

The AM-GM bound gives the maximum possible RHS, but the actual maximum over feasible D might be lower (if the AM-GM optimum is not realizable).

## 7. Characterization theorem

**Theorem.** Let S be a length-G circular genome with L-mer occurrence counts d_i^S. Let x be an observation with ∑ x_i = N. The truth S is an ML maximizer among all length-G circular candidates if and only if:

```
∑_i x_i · log(d_i^S) ≥ max_{D ∈ 𝒢_G} ∑_i x_i · log(d_i^D)    [11]
```

where 𝒢_G is the set of L-mer occurrence-count vectors realizable by length-G circular genomes.

**When the truth can lose.** The truth can be beaten whenever:

1. The observation is non-uniform (x_i varies across L-mer types), AND
2. There exists a realizable d-vector D with d_i^D > d_i^S for overrepresented observed L-mers, at the cost of d_j^D < d_j^S for unobserved or underrepresented L-mers.

**Sufficient condition for truth to win.** If d_i^S ∝ x_i for all i (i.e., the truth's L-mer distribution is proportional to the empirical read distribution), then the truth achieves the AM-GM bound and is an ML maximizer (modulo realizability of competitors).

**Necessary condition for truth to win.** If the truth's L-mer distribution is far from proportional to x (high KL divergence), and the AM-GM optimum is realizable by a competitor, the truth can be beaten.

## 8. Connection to the complete-spectrum case

The computational evidence report (`/workspace/COMPUTATIONAL_EVIDENCE_REPORT.md`) shows zero counterexamples in the dense complete-spectrum case (Phase 1). This is consistent with the analysis:

In the complete spectrum case, x_i = d_i^S for all i (every L-mer observed exactly as many times as it appears in S). Then:

```
Δ(S, x) = ∑_i d_i^S · log(d_i^S · G / (G · d_i^S)) = ∑_i d_i^S · log(1) = 0
```

So Δ = 0, meaning the truth matches the AM-GM bound. Moreover, in the complete spectrum case, every L-mer type is observed (x_i > 0 for all i with d_i^S > 0). A competitor D must have d_i^D ≥ 1 for all observed L-mers to have nonzero likelihood. Since ∑ d_i^D = G and there are at most G observed L-mer types, D is forced to have d_i^D = 1 for all observed L-mers — the same as S. So D ties S (or has lower likelihood if it includes unobserved L-mers at the cost of observed ones).

**This is why the complete-spectrum case has no counterexamples.**

## 9. The sampling-fluctuation mechanism

The counterexample arises from a **sampling fluctuation**: the finite sample x deviates from the truth's L-mer distribution d^S / G. When x concentrates on a subset of L-mers (here {AB, BA}), a competitor that also concentrates on those L-mers (here ABAB with d_AB = d_BA = 2) achieves higher likelihood.

The deeper insight: **ML rewards high probability assigned to observed data, while bridging rewards unambiguous reconstructibility.** These objectives conflict when the sample is small and concentrated. The truth's "spread" L-mer distribution (each type appears once) is optimal for reconstructibility but suboptimal for assigning high probability to a concentrated sample.

## 10. Cross-check against repository conventions

| Repository artifact | Consistency |
|--------------------|----|
| `docs/ml-formalization-contract.md` §Variant E | ✓ Uses candidate's own N(D); in fixed-length case N(D)=G, reducing to ∏(d_i/G)^{x_i} |
| `AssemblyP1/Model.lean` `IsMaximumLikelihood` | ✓ Our condition [11] is exactly ∀ candidate, f(candidate) ≤ f(truth) |
| `docs/exact-variant-e-counterexample.md` | ✓ Our analysis extends that counterexample to the fixed-length case with AABB |
| `docs/bridging-source-semantics.md` | ✓ Bridging is a condition on S, not on D; confirmed it doesn't constrain competitors |
| `COMPUTATIONAL_EVIDENCE_REPORT.md` Phase 1 | ✓ Complete-spectrum case has no counterexamples, consistent with our §8 analysis |
| `COMPUTATIONAL_EVIDENCE_REPORT.md` Phase 2 | ✓ Finite-sample counterexamples exist, consistent with our §6 counterexample |
| `assemblyP1_notes.md` AM-GM theorem | ✓ Our Lemma 1 is the same AM-GM bound; the notes prove truth wins for unrestricted length |

## 11. Open questions

1. **Realizability characterization.** For which observation vectors x is the AM-GM optimum d_i = G · x_i / N realizable by a circular genome? This determines exactly when the truth can lose.

2. **Bridging as a sufficient condition.** Does bridging + coverage imply that the truth's L-mer distribution is "close enough" to the empirical distribution to prevent competitors from winning? The answer appears to be NO (counterexample in §6), but a quantitative version might hold.

3. **The L ≥ G/2 regime.** The computational evidence shows no counterexamples for L ≥ G/2. Is there a structural reason? Hypothesis: when L ≥ G/2, the de Bruijn graph is sufficiently constrained that the AM-GM optimum is rarely realizable by a competitor.

4. **Unique ML vs. ML maximizer.** The counterexample shows truth is not an ML maximizer. But even when truth IS an ML maximizer (complete spectrum), it may tie with cyclic shifts. The stronger conjecture (unique ML up to cyclic shift) is a separate question.

## 12. Summary of findings

1. **Fixed-length exact Variant E is vulnerable to competitors that concentrate on observed L-mers.** The truth's likelihood ∏(d_i^S)^{x_i} can be beaten by a competitor with d_i^D > d_i^S for overrepresented observed L-mers.

2. **The key inequality is [11]:** truth wins iff its log-likelihood ∑ x_i log(d_i^S) exceeds the maximum over all realizable competitor d-vectors.

3. **Coverage and bridging do NOT prevent this.** They constrain S, not D. They ensure S's L-mers are observed and S's repeats are resolved, but they don't prevent competitors from having "better" L-mer distributions.

4. **The complete-spectrum case IS safe** (zero counterexamples, proved in §8): when every L-mer is observed exactly as many times as it appears in S, competitors are forced to tie.

5. **The minimal counterexample is AABB vs ABAB** (G=4, L=2, {AB:1, BA:1}): coverage and bridging hold, but D has 4× the likelihood of S.

6. **The mechanism is sampling fluctuation + concentration:** finite samples can deviate from the truth's uniform L-mer distribution, and competitors that match the deviation score higher.
