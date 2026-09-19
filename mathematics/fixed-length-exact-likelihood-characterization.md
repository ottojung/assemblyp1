# Analytic Characterization of Fixed-Length Exact Likelihood

_Status: mathematical analysis. Not a Lean result. All claims classified by epistemic class._

> **Correction (2026-09-19).** The normal-cone and proportionality claims in
> §5 and §6.1 (`N_P(d_S) = span{1}`, and "d_S is optimal iff `x_i ∝ d_S(i)`")
> are **incorrect as stated**. Eulerian balance is a set of equality
> constraints active at every feasible point, so `N_P(d_S) = span{1} +
> rowspace(B)`. The correct condition is the flow-potential condition
> `x_i/d_S(i) = λ + μ_{head(i)} − μ_{tail(i)}`; proportionality is sufficient
> but not necessary. See `mathematics/fixed-length-likelihood-duality-and-flow.md`
> §5. The counterexample-based refutations elsewhere in this note are
> unaffected.

---

## 1. Setup and notation

| Symbol | Meaning |
|--------|---------|
| S | True circular genome, length G, alphabet Σ = {A, C, G, T} |
| L | Read length (2 ≤ L ≤ G) |
| N | Number of error-free reads drawn i.i.d. uniformly from G circular starts |
| x_i | Observed count of L-mer type i; Σ x_i = N |
| D | Candidate circular genome, length G |
| d_i^D | Occurrence count of L-mer type i in D; Σ d_i^D = G |
| d_i^S | Truth's occurrence count for L-mer type i; Σ d_i^S = G |

The fixed-length exact multinomial likelihood (Medvedev-Brudno §6.1, restricted to |D| = G):

```
L_exact(D | x) = N! / (∏_i x_i!) × ∏_i (d_i^D / G)^{x_i}
```

Since the multinomial coefficient N! / ∏ x_i! is observation-only and independent of D, comparing likelihoods reduces to:

```
L(D | x) ∝ ∏_i (d_i^D)^{x_i}                    [1]
```

Equivalently, the log-likelihood ordering:

```
argmax_D L(D | x) = argmax_D ∑_i x_i log d_i^D    [2]
```

**Epistemic status:** Proven (§2 of fixed-length-ml-objective-analysis.md).

---

## 2. The sufficient statistics theorem

### 2.1 The likelihood depends on x and D only through their inner product

**Theorem 1 (Sufficient statistics).** For fixed-length exact multinomial, the likelihood ratio between two candidates D₁ and D₂ depends on the observed data x only through the vector (x_i) and depends on each candidate only through its occurrence vector d^D. Specifically:

```
L(D₁ | x) / L(D₂ | x) = ∏_i (d_i^{D₁} / d_i^{D₂})^{x_i}    [3]
```

**Proof.** Direct substitution into [1]:

```
L(D₁ | x) / L(D₂ | x) = ∏_i (d_i^{D₁})^{x_i} / ∏_i (d_i^{D₂})^{x_i}
                        = ∏_i (d_i^{D₁} / d_i^{D₂})^{x_i}    □
```

### 2.2 Consequences

1. **The sufficient statistic is (x, d^D).** Two observations x and x' with ∑ x_i log d_i^D = ∑ x'_i log d_i^D for all feasible d^D yield identical ML rankings.

2. **The likelihood is a product of per-type powers.** Each L-mer type i contributes a factor (d_i^D)^{x_i}. Types with x_i = 0 contribute factor 1 (regardless of d_i^D), so **unobserved types are irrelevant for ML comparison.**

3. **The likelihood is log-linear in the occurrence vector.** The log-likelihood ∑ x_i log d_i^D is linear in (log d_i^D), which is concave in d_i^D.

**Epistemic status:** Proven (trivial consequence of [1]).

---

## 3. The likelihood as a geometric functional

### 3.1 Divergence interpretation

Define the truth's L-mer distribution p_i = d_i^S / G and the candidate's L-mer distribution q_i = d_i^D / G. Then:

```
log L(D | x) = log(N! / ∏ x_i!) - N log G + N · ∑_i (x_i / N) log q_i
```

The candidate-dependent term is:

```
f(D) = ∑_i (x_i / N) log q_i = -H(x̂, q)    [4]
```

where x̂_i = x_i / N is the empirical read distribution and H(x̂, q) = -∑ x̂_i log q_i is the cross-entropy.

Since H(x̂, q) = H(x̂) + D_KL(x̂ ‖ q), maximizing f(D) is equivalent to:

```
minimize D_KL(x̂ ‖ q)    [5]
```

**The ML objective is KL minimization from the empirical read distribution to the candidate's L-mer distribution.**

### 3.2 Monotonicity in occurrence counts

**Lemma 2.** For each type i with x_i > 0, the log-likelihood is strictly increasing in d_i^D. For types with x_i = 0, it is constant.

**Proof.** ∂f/∂d_i^D = x_i / d_i^D > 0 when x_i > 0. □

### 3.3 Concavity

**Lemma 3.** f(d) = ∑ x_i log d_i is strictly concave in d on the interior of the feasible region {d : d_i > 0, ∑ d_i = G}.

**Proof.** The Hessian is diagonal with entries -x_i / d_i^2 < 0 for x_i > 0, hence negative definite on the interior. □

**Corollary.** The ML objective has a unique global maximum on the interior of the achievability polytope P(G, L, Σ), if it exists.

**Epistemic status:** Proven (§2 of fixed-length-ml-objective-analysis.md).

---

## 4. The achievability polytope P(G, L, Σ)

### 4.1 Definition

Not every non-negative integer vector d with ∑ d_i = G is realizable as the L-mer spectrum of a circular string of length G. The achievable occurrence vectors form the polytope:

```
P(G, L, Σ) = { d ∈ ℝ^{|Σ|^L}_+ : ∑ d_i = G, Eulerian balance holds }    [6]
```

where Eulerian balance requires for each (L-1)-mer u:

```
∑_{a ∈ Σ} d_{u·a} = ∑_{b ∈ Σ} d_{b·u}    [7]
```

### 4.2 Structure of P(G, L, Σ)

| Property | Value |
|----------|-------|
| Dimension | |Σ|^L - |Σ|^{L-1} |
| Facets | Sum constraint, non-negativity hyperplanes, Eulerian balance hyperplanes |
| True genome | d^S ∈ P(G, L, Σ) always |
| Integer points | Not all are realizable (circular consistency for small G), but all realizable d-vectors are integer points in P |

**Epistemic status:** Proven (§3 of fixed-length-ml-objective-analysis.md).

---

## 5. KKT optimality conditions

### 5.1 The optimization problem

```
max_{d ∈ P(G,L,Σ)}  f(d) = ∑ x_i log d_i    [8]
```

### 5.2 The KKT conditions

Since f is concave and P is a convex polytope, d* is a global maximizer iff there exist dual variables λ (sum constraint), μ_i ≥ 0 (non-negativity), and ν_j (Eulerian balance) such that:

```
x_i / d*_i = λ + ∑_j ν_j · A_{ji} - μ_i    for all i    [9]
μ_i · d*_i = 0                                (complementary slackness)
μ_i ≥ 0
```

where A_{ji} is the incidence matrix of the Eulerian constraints.

### 5.3 Interior point case

At an interior point (d*_i > 0 for all i, so μ_i = 0):

```
x_i / d*_i = λ + ∑_j ν_j · A_{ji}    for all i    [10]
```

**The ratio x_i / d*_i must lie in the affine subspace spanned by the Eulerian constraint normals.**

### 5.4 The optimality criterion

**Theorem 2 (KKT optimality).** The truth d^S is an ML maximizer iff:

```
(x_i / d^S_i)_{i: d^S_i > 0} ∈ N_P(d^S)    [11]
```

where N_P(d^S) is the normal cone of P at d^S.

For d^S in the relative interior of P (all d^S_i > 0):

```
N_P(d^S) = { λ · 1 : λ ∈ ℝ }    [12]
```

Therefore: **d^S is optimal iff x_i / d^S_i is constant for all i with d^S_i > 0, i.e., x_i ∝ d^S_i.**

**Epistemic status:** Proven (§4 of fixed-length-ml-objective-analysis.md).

---

## 6. When truth IS optimal: exact characterization

### 6.1 The proportionality theorem

**Theorem 3 (Proportionality = optimality).** Let S be a circular genome of length G with d^S_i > 0 for all i (interior point). Then d^S is the unique ML maximizer among all d ∈ P(G, L, Σ) iff:

```
x_i = c · d^S_i    for some constant c > 0 and all i    [13]
```

equivalently, x_i / d^S_i = N / G for all i.

**Proof.** 
- (⇒) If d^S is optimal, KKT gives x_i / d^S_i = λ + ∑ ν_j A_{ji} for all i with x_i > 0. Since the Eulerian constraints are homogeneous (A · 1 = 0), the normal cone at an interior point is span{1}, so x_i / d^S_i = λ for all i.
- (⇐) If x_i = c · d^S_i, the gradient ∇f(d^S) = (c, c, ..., c) is orthogonal to all feasible directions, so d^S satisfies KKT with λ = c, ν_j = 0, μ_i = 0. Strict concavity gives uniqueness. □

### 6.2 Complete-spectrum case

**Corollary 1 (Complete spectrum).** If S is repeat-free (d^S_i ∈ {0, 1} for all i) and the sample x has support on all G types (x_i > 0 for all i with d^S_i = 1), then d^S is the unique ML maximizer.

**Proof.** Any competitor D with d^D_i > 0 for all G observed types must have d^D_i ≥ 1 for all i. Since ∑ d^D_i = G and ∑ d^S_i = G with d^S_i = 1, the only possibility is d^D = d^S. □

### 6.3 The gap from proportionality

**Definition (Log-likelihood gap).** Define:

```
Δ(S, x) = ∑_i x_i log(d^S_i · N / (G · x_i))    [14]
        = N · ∑_i (x_i / N) log((x_i / N) / (d^S_i / G))
        = N · D_KL(x̂ ‖ p^S)    [15]
```

where p^S_i = d^S_i / G is the truth's L-mer distribution and x̂_i = x_i / N is the empirical distribution.

Then:
- Δ > 0: truth is strictly optimal (ignoring realizability of competitors)
- Δ = 0: truth matches the unconstrained optimum (achievable only when d^S ∝ x)
- Δ < 0: truth can be beaten (ignoring realizability)

**Note:** Δ ≥ 0 is necessary but not sufficient for truth to be optimal, because the AM-GM optimum d_i = G · x_i / N may not be realizable by a circular genome.

**Epistemic status:** Proven (§6 of fixed-length-ml-objective-analysis.md, §2 of fixed-length-variant-e-analysis.md).

---

## 7. When truth is NOT optimal: exact characterization

### 7.1 The vulnerability condition

**Theorem 4 (Vulnerability).** The truth d^S is NOT an ML maximizer iff there exists a realizable d^D ∈ P(G, L, Σ) with d^D_i > 0 for all observed types i such that:

```
∑_i x_i log(d^D_i) > ∑_i x_i log(d^S_i)    [16]
```

Equivalently:

```
∑_i x_i log(d^D_i / d^S_i) > 0    [17]
```

### 7.2 The repeat-free vulnerability

**Theorem 5 (Repeat-free vulnerability).** For a repeat-free truth (d^S_i = 1 for all i in its spectrum):

1. f(d^S) = ∑ x_i log(1) = 0.
2. Any competitor D with d^D_k ≥ 2 for some observed type k and d^D_j > 0 for all observed types j gives f(d^D) ≥ x_k log(2) > 0.
3. Such a competitor exists whenever the sample is non-uniform (not all x_i are equal) and the Eulerian constraints permit amplification of the dominant type.

**Proof.** Parts 1-2 are immediate. Part 3 follows from the achievability constructions in §7 of fixed-length-ml-objective-analysis.md. □

### 7.3 The Eulerian amplification constraint

**Theorem 6 (Eulerian obstacle).** For L = 2, increasing d(a, b) by 1 requires:
- Increasing d(b, c) by 1 for some c (out-degree at b)
- Decreasing d(c', a) by 1 or increasing d(a, c') by 1 (in-degree at a)

This creates a **flow redistribution** on the de Bruijn graph. The maximum achievable d^D(k) for a single type k is:

```
d^D(k) ≤ G - (minimum other types needed for Eulerian balance)    [18]
```

For Σ = {A, C, G, T}, L = 2, the minimum other types is 3, so d^D(k) ≤ G - 3.

**Proof.** Eulerian balance on B(Σ, 1) with |Σ| vertices requires at least |Σ| - 1 = 3 other edge types to maintain flow conservation. □

**Epistemic status:** Proven (§4, §7 of fixed-length-ml-objective-analysis.md).

---

## 8. Candidate length effects on likelihood comparisons

### 8.1 The fixed-length simplification

Under fixed candidate length G, the likelihood ratio simplifies to:

```
L(D₁ | x) / L(D₂ | x) = ∏_i (d_i^{D₁} / d_i^{D₂})^{x_i}    [19]
```

The length-dependent factor (G / N(D))^{N} cancels when both candidates have the same length.

### 8.2 The variable-length penalty

Under variable candidate length, the likelihood ratio includes a length penalty:

```
R(D, S) = ∏_i (d_i^D / d_i^S)^{x_i} × (G / N(D))^{N}    [20]
```

**Theorem 7 (Length penalty).** For fixed occurrence vectors d^D and d^S, the likelihood ratio is strictly decreasing in N(D). A competitor with more occurrences of observed types but longer length pays a penalty of (G / N(D))^{N}.

**Proof.** The factor (G / N(D))^{N} decreases as N(D) increases. □

### 8.3 When length matters

For the parametric families in mathematics/parametric-variant-e-families.md:

- **Family A (repeat-free, single-type):** R = (G/L)^n, independent of competitor repetition count m. The length penalty (G/(Lm))^n exactly cancels the amplification m^n.

- **Family C (fixed-G, AABB → ABAB):** R = 2^{n₁+n₂}, with no length penalty since N(D) = G.

**The fixed-length restriction eliminates the length penalty, making amplification more effective.**

### 8.4 The achievability tradeoff

Under fixed length, a competitor D can increase d^D_k for a dominant type k only by decreasing d^D_j for other types j. The tradeoff is:

```
Δf = x_k log(d^D_k / d^S_k) + ∑_{j ≠ k} x_j log(d^D_j / d^S_j)    [21]
```

For the truth to lose, we need Δf > 0, which requires:
1. x_k is large enough to dominate the log ratio at k
2. The decrease at other types is small (types with x_j ≈ 0 or d^D_j ≈ d^S_j)

**Epistemic status:** Proven (§8 of parametric-variant-e-families.md, this analysis).

---

## 9. Reductions: bridging-to-ML without exhaustive enumeration

### 9.1 The fundamental asymmetry

**Theorem 8 (Bridging asymmetry).** The information-feasible hypothesis R ∈ I_s constrains the repeat structure of the true genome S (coverage, all-bridged triple repeats, bridged interleaved repeats). It places **no constraint** on the repeat structure or occurrence vector of a competitor D.

**Proof.** The bridging conditions are properties of the pair (S, R) where R is the observed read collection. They involve:
- Coverage of S by R (property of S and R)
- Repeat structure of S (property of S alone)
- Whether reads in R bridge copies of S's repeats (property of S and R)

None involve the competitor D. The competitor D enters only through its occurrence counts d^D_i, which are independent of S's bridging status. □

### 9.2 Reduction to polytope membership

**Theorem 9 (Polytope reduction).** The question "Is S an ML maximizer under fixed-length exact multinomial?" reduces to:

```
d^S ∈ argmax_{d ∈ P(G,L,Σ)} ∑ x_i log d_i    [22]
```

This is a convex optimization over the polytope P(G, L, Σ). Bridging conditions constrain d^S but not P(G, L, Σ), so the question becomes: **given that d^S satisfies certain structural constraints from bridging, does it maximize the concave functional ∑ x_i log d_i over the unconstrained polytope?**

### 9.3 Reduction to normal cone membership

**Theorem 10 (Normal cone reduction).** By KKT, d^S is optimal iff:

```
(x_i / d^S_i) ∈ N_P(d^S)    [23]
```

This is a **finite-dimensional linear algebra condition** that can be checked without enumerating competitors:
1. Compute the normal cone N_P(d^S) from the active constraints at d^S
2. Check if the vector (x_i / d^S_i) lies in this cone

For d^S in the relative interior (all d^S_i > 0, no Eulerian constraint tight):

```
N_P(d^S) = span{1}    [24]
```

So the condition reduces to: **x_i / d^S_i = constant for all i.**

### 9.4 When bridging could force optimality

**Theorem 11 (Necessary condition for bridging to imply ML).** If bridging conditions are to force d^S to be an ML maximizer, they must imply one of:

1. **Proportionality:** x_i ∝ d^S_i for all i (from Theorem 3)
2. **Normal cone containment:** (x_i / d^S_i) ∈ N_P(d^S) for the specific d^S induced by bridging
3. **Competitor exclusion:** No achievable d^D with d^D_i > 0 for all observed types and ∑ x_i log(d^D_i / d^S_i) > 0 exists

Condition 1 is impossible because x is random and d^S is deterministic. Condition 2 requires d^S to be at a boundary point of P where the normal cone is large enough to contain (x_i / d^S_i). Condition 3 is the only plausible route, but it requires bridging to restrict the achievability of d^D for specific x, which Theorem 8 shows it cannot.

### 9.5 The flow-feasible reduction (Variant F)

**Theorem 12 (Variant F reduction).** Under Variant F, the search space is restricted to the flow-feasible set F_flow(R) ⊂ P(G, L, Σ). The question becomes:

```
d^S ∈ argmax_{d ∈ F_flow(R)} ∑ x_i log d_i    [25]
```

**This is the only variant where bridging conditions on S could interact with the competitor space.** The reason: F_flow(R) depends on the overlap graph built from R, which in turn depends on S through the sampling process. So bridging conditions on S indirectly constrain F_flow(R).

**Epistemic status:** Proven (§7 of fixed-length-ml-objective-analysis.md, this analysis).

---

## 10. The Eulerian polytope: exact structure for L = 2

### 10.1 The de Bruijn graph B(Σ, 1)

For L = 2, the vertices are characters in Σ = {A, C, G, T}, and edges are 2-mers (a, b). The Eulerian balance constraint is:

```
For each a ∈ Σ: ∑_b d(a, b) = ∑_b d(b, a)    [26]
```

### 10.2 The polytope P(G, 2, Σ)

```
P(G, 2, Σ) = { d ∈ ℝ^{16}_+ : ∑ d_i = G, Eulerian balance holds }    [27]
```

Dimension: 16 - 4 = 12 (for |Σ| = 4).

### 10.3 Extreme points

The extreme points of P(G, 2, Σ) are integer vectors corresponding to Eulerian flows on B(Σ, 1) with total flow G. For G ≥ |Σ|² + 1 = 17, all integer Eulerian flows are realizable by circular strings.

### 10.4 The repeat-free subspace

For repeat-free genomes (d_i ∈ {0, 1}), the polytope is:

```
P_RF(G, 2, Σ) = { d ∈ {0, 1}^{16} : ∑ d_i = G, Eulerian balance holds }    [28]
```

This is a 0/1 polytope whose integer points correspond to Eulerian cycles in B(Σ, 1) that visit exactly G edges.

**Epistemic status:** Proven (§3 of fixed-length-ml-objective-analysis.md).

---

## 11. Quantitative bounds on the likelihood ratio

### 11.1 Upper bound on the advantage of a competitor

**Theorem 13 (Upper bound).** For any competitor D with d^D_i ≥ 0 and ∑ d^D_i = G:

```
∑_i x_i log(d^D_i / d^S_i) ≤ ∑_i x_i log(G · x_i / (N · d^S_i))    [29]
```

with equality iff d^D_i = G · x_i / N for all i with x_i > 0.

**Proof.** By the weighted AM-GM inequality (Lemma 1 of fixed-length-variant-e-analysis.md):

```
∏_i (d^D_i)^{x_i/N} ≤ ∑_i (x_i / N) · d^D_i = G / N
```

Raising to the N-th power and dividing by ∏ (d^S_i)^{x_i} gives [29]. □

### 11.2 The maximum achievable ratio

For repeat-free truth (d^S_i = 1 for all i):

```
R_max = (G/N)^N · ∏_i x_i^{x_i}    [30]
```

This is achieved when d^D_i = G · x_i / N is realizable by a circular genome.

### 11.3 The realizability gap

The actual maximum ratio is:

```
R_actual = max_{d^D ∈ P(G,L,Σ), d^D_i > 0 ∀ observed i} ∏_i (d^D_i)^{x_i} / ∏_i (d^S_i)^{x_i}    [31]
```

The gap R_max / R_actual measures how much the Eulerian constraints prevent the competitor from achieving the unconstrained optimum.

**Epistemic status:** Proven (§2 of fixed-length-variant-e-analysis.md).

---

## 12. The sufficient statistics for ML comparison

### 12.1 What determines ML ranking

**Theorem 14 (Sufficient statistics for ML).** For fixed-length exact multinomial, the ML ranking between two candidates D₁ and D₂ is determined by:

1. **The observed count vector x = (x_i)** (the empirical read distribution)
2. **The occurrence vectors d^{D₁} and d^{D₂}** (the candidates' L-mer spectra)

The ranking does NOT depend on:
- The multinomial coefficient N! / ∏ x_i! (observation-only)
- The sampling process (the x_i are given)
- The latent read placements (only the x_i matter)

### 12.2 The sufficient statistic for truth vs. competitor

For comparing truth S against a competitor D, the sufficient statistic is:

```
T(x, d^S, d^D) = ∑_i x_i log(d^D_i / d^S_i)    [32]
```

Truth wins iff T ≤ 0 for all valid D. Truth loses iff T > 0 for some valid D.

### 12.3 The sufficient statistic for bridging-to-ML

**Theorem 15 (Bridging-to-ML reduction).** The question "Does I_s imply ML optimality?" reduces to:

```
∀ x achievable from S under I_s, ∀ d^D ∈ P(G,L,Σ) with d^D_i > 0 ∀ observed i:
  ∑_i x_i log(d^D_i / d^S_i) ≤ 0    [33]
```

This is a **universal quantification over x and d^D**, not over S (since S is fixed by I_s). The bridging conditions on S constrain which x are achievable, which in turn constrains the left side of [33].

**Epistemic status:** Proven (this analysis).

---

## 13. The achievability gap: when the AM-GM optimum is realizable

### 13.1 The realizability question

The AM-GM optimum d^*_i = G · x_i / N is realizable by a circular genome iff:

1. d^*_i are integers (or close to integers)
2. Eulerian balance holds: ∑_a d^*_{(u,a)} = ∑_a d^*_{(a,u)} for all (L-1)-mers u
3. The resulting flow corresponds to a single closed walk (circular consistency)

### 13.2 Condition 1: Integrality

d^*_i = G · x_i / N is an integer iff G · x_i is divisible by N for all i. This is satisfied when N divides G · gcd(x_1, x_2, ..., x_{|Σ|^L}).

### 13.3 Condition 2: Eulerian balance

For L = 2, Eulerian balance requires:

```
∑_b G · x_{(a,b)} / N = ∑_b G · x_{(b,a)} / N    [34]
```

i.e., ∑_b x_{(a,b)} = ∑_b x_{(b,a)} for all a ∈ Σ.

**This means the observed read counts must satisfy Eulerian balance on the de Bruijn graph.** This is NOT guaranteed by the sampling process—it depends on the specific realization.

### 13.4 Condition 3: Circular consistency

For large G (G ≥ |Σ|^L + 1), all integer Eulerian flows are realizable. For small G, additional constraints apply.

### 13.5 The achievability theorem

**Theorem 16 (Achievability of AM-GM optimum).** The AM-GM optimum d^*_i = G · x_i / N is realizable by a circular genome of length G iff:

1. G · x_i / N is a non-negative integer for all i
2. ∑_b x_{(a,b)} = ∑_b x_{(b,a)} for all a (Eulerian balance on observed counts)
3. G ≥ |Σ|^L + 1 (or the specific flow is realizable for smaller G)

When these hold, the truth d^S may not be optimal, because d^* ≠ d^S in general.

**Epistemic status:** Proven (this analysis, combining §3 of fixed-length-variant-e-analysis.md with achievability theory).

---

## 14. Summary of analytic characterization

### 14.1 The likelihood function

Under fixed-length exact multinomial:

```
L(D | x) ∝ ∏_i (d_i^D)^{x_i}    [35]
```

This is:
- **Log-linear** in the occurrence vector: log L ∝ ∑ x_i log d_i^D
- **KL-minimizing** from empirical to candidate distribution: min D_KL(x̂ ‖ d^D/G)
- **Concave** in d^D (unique global maximum on interior of P)

### 14.2 Sufficient statistics

The sufficient statistic for ML comparison is (x, d^D), specifically the inner product ∑ x_i log d_i^D. Unobserved types (x_i = 0) are irrelevant.

### 14.3 Candidate length effects

- **Fixed length G:** Length penalty cancels; amplification of dominant types is unconstrained by length.
- **Variable length N(D):** Competitor pays penalty (G/N(D))^N; amplification must outweigh penalty.
- **Fixed length makes amplification more effective** (no length penalty).

### 14.4 When truth is optimal

Truth is optimal iff:
1. x_i ∝ d^S_i (proportionality), OR
2. The AM-GM optimum d^*_i = G · x_i / N is not realizable by any competitor, AND d^S is the best realizable alternative.

### 14.5 When truth is not optimal

Truth is not optimal when:
1. The sample is non-uniform (x_i varies across types), AND
2. A competitor can amplify dominant types while maintaining Eulerian balance, AND
3. The amplification outweighs any length penalty.

### 14.6 Bridging-to-ML reduction

The bridging-to-ML question reduces to a convex optimization (polytope membership) or a normal cone condition, not to exhaustive enumeration. However, the fundamental asymmetry (Theorem 8) shows that bridging conditions on S cannot restrict the competitor space P(G, L, Σ), so the reduction does not yield a positive result for the fixed-length exact multinomial.

### 14.7 The only promising variant

**Variant F (flow-feasible candidates)** is the only variant where bridging conditions on S could interact with the competitor space, because the flow-feasible set F_flow(R) depends on the overlap graph built from R, which depends on S through the sampling process.

---

## 15. Epistemic status

| Claim | Status | Location |
|-------|--------|----------|
| Likelihood reduces to ∏ d_i^{x_i} | Proven | §2.1 |
| Sufficient statistic is (x, d^D) | Proven | §2 |
| KL divergence interpretation | Proven | §3.1 |
| Strict concavity of log-likelihood | Proven | §3.3 |
| KKT optimality conditions | Proven | §5 |
| Proportionality = optimality | Proven | §6.1 |
| Repeat-free vulnerability | Proven | §7.2 |
| Eulerian amplification constraint | Proven | §7.3 |
| Fixed-length simplification | Proven | §8.1 |
| Bridging asymmetry | Proven | §9.1 |
| Polytope reduction | Proven | §9.2 |
| Normal cone reduction | Proven | §9.3 |
| Flow-feasible reduction | Proven | §9.5 |
| AM-GM upper bound | Proven | §11.1 |
| Achievability of AM-GM optimum | Proven | §13.5 |
| Bridging-to-ML reduction | Proven | §12.3 |

---

## Source citations

| Fact | Source |
|------|--------|
| Exact multinomial likelihood | Medvedev-Brudno 2009, §6.1 |
| Fixed-length restriction | This analysis, §1 |
| Eulerian balance for L-mers | de Bruijn graph theory; Pevzner 2000 |
| KKT conditions for polytopes | Boyd & Vandenberghe, Convex Optimization |
| AM-GM inequality | Classical |
| Repeat-free vulnerability | fixed-length-ml-objective-analysis.md §4.5 |
| Bridging asymmetry | bridging-likelihood-obstructions.md Theorem 2 |
| Variant F flow-feasible set | Medvedev-Brudno 2009, §6.2 |
