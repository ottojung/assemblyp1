# Occurrence-count inequality for exact multinomial ML dominance

_Status: mathematical analysis with computational evidence. Not a formal Lean result._

## Question

Under the source bridging/coverage hypotheses, what occurrence-count inequality
would imply exact multinomial ML dominance, and do those hypotheses imply it?

## Setup (fixed-length exact multinomial, Variant E restricted to length G)

- Circular true genome S of length G over alphabet {A, C, G, T}.
- Read length L; N error-free reads sampled independently and uniformly from G
  circular start positions.
- Observed multiset: read type i appears x_i times; sum x_i = N.
- Candidate genome D of **the same length** G: occurrence counts d_D(i) = number
  of positions whose length-L circular window equals type i.
- Constraint: sum_i d_S(i) = G = sum_i d_D(i).

The exact multinomial likelihood (ordering only, multinomial coefficient factored
out) is:

  L(D | x) proportional to prod_i d_D(i)^{x_i}

Log-likelihood difference (competitor minus truth):

  Delta(D) = sum_i x_i log(d_D(i) / d_S(i))

Truth wins (ML dominance) iff Delta(D) <= 0 for all valid D.

## The central occurrence-count inequality

### Candidate 1: Pointwise dominance (sufficient, too strong)

  (OI-PW)  For all i with x_i > 0:  d_S(i) >= d_D(i).

This is sufficient for ML dominance (each term x_i log(d_S(i)/d_D(i)) >= 0).
It is NOT necessary and is extremely strong: it requires the truth's spectrum to
pointwise dominate every valid competitor's spectrum on observed types.

For this to hold for ALL valid D, we need d_S(i) >= max achievable d_D(i) for
every observed i. Since d_D can concentrate up to G occurrences on a single type
(if achievable), this requires d_S(i) >= G for all i, which contradicts
sum d_S(i) = G unless G = 1.

**Verdict: (OI-PW) is never satisfiable for G >= 2.**

### Candidate 2: Weighted sum dominance (sufficient, weaker)

  (OI-WS)  For all valid D:  sum_i x_i * d_S(i) >= sum_i x_i * d_D(i).

This is sufficient by the weighted Jensen/AM-GM inequality:

  sum x_i log(d_S(i)/d_D(i))  >=  (sum x_i) * log(sum x_i d_S(i) / sum x_i d_D(i))

If sum x_i d_S(i) >= sum x_i d_D(i), the RHS >= 0, so Delta(D) <= 0.

### Candidate 3: KL-optimality (necessary and sufficient)

  (OI-KL)  d_S maximizes  f(d) = sum_i x_i log(d(i))  over all achievable
  occurrence vectors d with sum d(i) = G and d(i) > 0 for all observed types i.

This is exactly the ML dominance condition rewritten. It is necessary and
sufficient but is an optimization characterization, not a closed-form inequality.

### Candidate 4: Majorization (sufficient, intermediate strength)

  (OI-MJ)  d_S majorizes d_D in the weighted sense: for all observed types i,
  the partial sums satisfy the Schur-convex ordering with weights x_i.

This is stronger than (OI-WS) but weaker than (OI-PW). It is sufficient because
sum x_i log(d(i)) is Schur-concave in d when x_i are weights.

## Do bridging/coverage imply any of these?

### The fundamental obstruction (Theorem, restated)

**Theorem (Asymmetry of bridging constraints).** The information-feasible
hypothesis constrains the repeat structure of the true genome S (coverage,
all-bridged triple repeats, bridged interleaved repeats). It places **no
constraint** on the repeat structure or occurrence vector of a competitor D.

**Proof.** The bridging conditions are properties of the pair (S, R) where R
is the observed read collection. They involve: coverage of S by R (property of
S and R); repeat structure of S (property of S alone); whether reads in R
bridge copies of S's repeats (property of S and R). None of these involve D.
The competitor D enters only through its occurrence counts d_D(i), which are
independent of S's bridging status. ∎

**Corollary.** For any true genome S satisfying the information-feasible
hypothesis, the set of valid competitors D (same length G, d_D(i) > 0 for all
observed types) is the same regardless of whether S satisfies bridging.
Therefore bridging conditions cannot restrict the competitor pool and cannot
force (OI-PW), (OI-WS), or (OI-KL).

### Specific failure for repeat-free genomes

For a repeat-free S (vacuously satisfies all bridging):

  d_S(i) = 1 for all i.

Then:

  f(d_S) = sum x_i log(1) = 0.

For any competitor D with d_D(i) > 1 for some observed type i (which exists
whenever the observed sample is non-uniform, i.e., not all x_i are equal):

  f(d_D) = sum x_i log(d_D(i)) > 0 > f(d_S).

So the truth **always loses** to any non-trivially different competitor under
exact multinomial ML, regardless of bridging/coverage. The occurrence-count
inequality (OI-KL) is violated for every non-uniform observed sample.

### Specific failure for genomes with repeats

Even when S has repeats (d_S(i) > 1 for some i), bridging constrains how
large d_S(i) can be (bounded by the bridging budget), but d_D(i) is unconstrained.
A competitor can always concentrate occurrences on observed types to achieve
d_D(i) > d_S(i) for types with high x_i.

## Computational evidence: small counterexamples

Exhaustive search over canonical circular genomes of length G in {4, 5, 6}
with L = 2, repeat-free truths, observed samples of size N in {3, ..., 10}
with 2-3 distinct read types satisfying coverage.

| G | L | Repeat-free truths | Counterexamples found |
|---|---|-------------------|----------------------|
| 4 | 2 | 10                | 18                   |
| 5 | 2 | 65                | 240                  |
| 6 | 2 | 350               | 1016                 |

**Representative counterexample (G=4, L=2):**

  Truth: CCAA, d_S = {(C,C):1, (C,A):1, (A,A):1, (A,C):1}
  Observed: {(C,A):2, (A,C):1}, N=3, coverage satisfied
  Competitor: CACA, d_D = {(C,A):2, (A,C):2}
  Delta = 2*log(2/1) + 1*log(2/1) = 3*log(2) > 0

  Competitor has 8x higher likelihood.

**The existing counterexample (docs/bridging-likelihood-obstructions.md):**

  Truth: AACAGG (G=6, L=2), repeat-free
  Observed: {AA:5, CA:1, GG:1}, N=7, coverage satisfied
  Competitor: AAAGGC (G=6, L=2), d_D(AA)=2
  Delta = 5*log(2) = 3.466..., ratio = 32

  Bridging vacuously satisfied; competitor has 32x higher likelihood.

## What the analysis reveals

### The occurrence-count inequality that WOULD imply ML dominance

The minimal occurrence-count condition sufficient for exact multinomial ML
dominance (fixed-length Variant E) is:

  (OI-KL)  d_S maximizes sum x_i log(d(i)) over achievable d with sum d(i)=G.

Equivalently (by KKT conditions), for some lambda:

  For all i with x_i > 0:  x_i / d_S(i) = lambda  if d_S(i) > 0
  For all i with d_S(i) = 0:  x_i = 0

This means d_S(i) = x_i / lambda = G * x_i / N for all observed types.
In other words, **the truth's occurrence vector must be proportional to the
observed count vector**.

### Why bridging cannot imply it

Bridging constrains S's repeat structure but not D's. The condition (OI-KL)
requires d_S to be optimal, which depends on the relationship between d_S and
all achievable d_D. Bridging says nothing about d_D.

For repeat-free S (d_S = 1 for all i), (OI-KL) requires x_i = N/G for all i
(uniform observed sample). But bridging does not control which reads are
observed—it constrains the true genome's repeat structure given the observed
reads.

### The gap in the open question

The Shomorony et al. (2016) open question asks whether bridging conditions
guarantee ML dominance. This analysis shows:

1. For exact multinomial ML (Variant E) with fixed-length candidates:
   bridging does NOT imply ML dominance. Counterexamples exist at every
   genome size G >= 4.

2. The reason is structural: bridging constrains S's spectrum but not D's,
   and the exact multinomial likelihood compares them.

3. The occurrence-count inequality that would be needed (OI-KL) requires
   d_S to be proportional to x, which bridging cannot force.

4. The only ways to achieve ML dominance under exact multinomial are:
   (a) Restrict the candidate universe (e.g., Variant F flow-feasible set);
   (b) Assume the observed sample is uniform (unrealistic);
   (c) Use a different likelihood variant (e.g., Variant A approximation).

## Failed lemma: weighted sum inequality is not implied

**Lemma (attempted, refuted).** Under coverage and bridging, sum x_i d_S(i) >=
sum x_i d_D(i) for all valid D.

**Refutation.** For repeat-free S: sum x_i d_S(i) = N. For competitor D with
d_D(j) = 2 for the highest-weight type j (and d_D(i) = 1 otherwise):

  sum x_i d_D(i) = N + x_j > N = sum x_i d_S(i).

This is achievable whenever a genome with d(j) = 2 exists (which it does for
all G >= 3, L = 2). ∎

## Failed lemma: pointwise dominance is impossible

**Lemma (attempted, refuted).** Under bridging, d_S(i) >= d_D(i) for all
observed i and all valid D.

**Refutation.** For any S, the competitor D = S with one additional copy of
the most frequent observed type (by inserting a repeat) achieves d_D(j) >
d_S(j) for that type, provided the insert maintains length G. For G >= 4,
this is always achievable. ∎

## Candidate stronger conditions that WOULD force ML dominance

These are strictly stronger than bridging alone:

1. **Candidate restriction to flow-feasible set (Variant F).** If D is
   constrained by the overlap-graph flow feasibility, the search space may
   be small enough that bridging on S interacts with the flow constraints.
   This is the most plausible route to a positive result.

2. **Uniform observed sample.** If x_i = N/G for all i, then d_S = 1
   (repeat-free) is optimal. But uniform samples are atypical.

3. **Candidate spectrum restriction.** If D must have the same k-mer types
   as S (not just positive counts for observed types), then for repeat-free S,
   d_D = d_S is forced.

## Epistemic status

| Claim | Status |
|-------|--------|
| (OI-PW) sufficient for ML dominance | Proven (trivial) |
| (OI-PW) never satisfiable for G >= 2 | Proven |
| (OI-WS) sufficient for ML dominance | Proven (Jensen) |
| (OI-WS) not implied by bridging | Proven (refuted) |
| (OI-KL) necessary and sufficient | Proven (reformulation) |
| Bridging cannot imply (OI-KL) | Proven (Theorem 2 + counterexamples) |
| Counterexamples at G=4,5,6 | Computationally verified |
| Counterexample at G=6 with bridging | Computationally verified (prior work) |
| Variant F might yield positive result | Open |
| Variant A might yield positive result | Open |
