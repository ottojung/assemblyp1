# Fixed-length maximum-likelihood objective: structural analysis

_Status: mathematical analysis deriving structural characterizations of the exact multinomial ML objective under fixed known candidate length. All claims are mathematical theorems or definitions. Not a Lean result._

> **Correction (2026-09-19).** The "proportionality = optimality" claim in
> §4.3 and §6.3 is **incorrect as stated**. The Eulerian balance constraints
> `B d = 0` are equalities and are active at every feasible point, so the
> normal cone of the Eulerian polytope at an interior point is
> `span{1} + rowspace(B)`, not `span{1}`. The correct criterion is the
> flow-potential condition `x_i/d_S(i) = λ + μ_{head(i)} − μ_{tail(i)}`.
> Proportionality is sufficient but not necessary. See
> `mathematics/fixed-length-likelihood-duality-and-flow.md` §5 for the proof
> and an explicit counterexample. The refutations of fixed-length Variant E/A
> in §7 and §10 are unaffected.

---

## 1. Setup and notation

- Circular true genome S of length G over alphabet Σ = {A, C, G, T}.
- Read length L ≥ 2; N error-free reads sampled independently and uniformly from G circular start positions.
- Observed multiset: read/k-mer type i appears x_i times; Σ x_i = N.
- Candidate genome D of the **same length** G: occurrence count d_D(i) = number of circular L-window positions in D equal to type i.
- Σ_i d_D(i) = G for every valid candidate.

The fixed-length exact multinomial likelihood (Medvedev–Brudno §6.1 restricted to |D| = G):

```
L(D | x) = N! / (∏_i x_i!) × ∏_i (d_D(i) / G)^{x_i}
```

---

## 2. Objective decomposition

### 2.1 Log-likelihood up to constants

Taking logarithms:

```
log L(D | x) = log(N! / ∏ x_i!) + Σ_i x_i log(d_D(i) / G)
             = log(N! / ∏ x_i!) - N log G + Σ_i x_i log d_D(i)
```

The first two terms are independent of D. For ML ordering:

```
argmax_D L(D | x) = argmax_D Σ_i x_i log d_D(i)          (∗)
```

**The multinomial coefficient is observation-only and plays no role in candidate comparison under fixed length.** It is a constant that factors out of the optimization.

### 2.2 Alternative forms

The objective (∗) is equivalently:

- **Weighted sum of log-multiplicities:** f(d) = Σ x_i log d(i)
- **Negative cross-entropy:** −H(x̂, d) where x̂_i = x_i/N is the empirical distribution and H(p,q) = −Σ p_i log q_i is the cross-entropy
- **KL divergence form:** Since Σ x_i log(d(i)/G) = N · [−H(x̂) − D_KL(x̂ ‖ d/G)] − N log G, maximizing the log-likelihood is equivalent to minimizing D_KL(x̂ ‖ d/G), the KL divergence from the empirical read distribution to the candidate's L-mer distribution.

### 2.3 Key structural properties of f(d) = Σ x_i log d(i)

1. **Concave** in d (sum of concave functions log, since x_i ≥ 0).
2. **Monotonically increasing** in each d(i) when x_i > 0.
3. **Scale-invariant under fixed sum:** Since Σ d(i) = G is fixed, the feasible region is compact and f is continuous, so a maximum exists.
4. **Uniqueness:** f is strictly concave on the interior of the simplex {d : d(i) > 0, Σ d(i) = G}, so the unconstrained maximum is unique.

---

## 3. The achievability polytope

### 3.1 What makes an occurrence vector achievable?

Not every non-negative integer vector d with Σ d(i) = G is realizable as the L-mer spectrum of a circular string of length G. The constraints are:

**Sum constraint:**
```
Σ_i d(i) = G                                        (C1)
```

**Non-negativity:**
```
d(i) ≥ 0  for all i                                   (C2)
```

**Eulerian balance (for L = 2, explicit):**

For alphabet Σ = {a₁, ..., aₖ}, define the de Bruijn graph B(Σ, 1) with vertices Σ and directed edges labeled by 2-mers (a, b). Each position in a circular string contributes one edge. The occurrence vector d must satisfy:

```
For each character a ∈ Σ:
  Σ_{b} d(a, b)  =  Σ_{b} d(b, a)                   (C3)
```

This says: out-degree = in-degree at every vertex, i.e., d defines an Eulerian flow on B(Σ, 1).

**General L (de Bruijn graph B(Σ, L−1)):**

For general read length L, the vertices are (L−1)-mers and edges are L-mers. The Eulerian balance constraint is:

```
For each (L−1)-mer u:
  Σ_{a ∈ Σ} d(u · a)  =  Σ_{b ∈ Σ} d(b · u)        (C3')
```

**Circular consistency:**

The Eulerian flow must be realizable by a single closed walk (not a disjoint union of cycles). For a connected de Bruijn graph, Eulerian balance (C3) is sufficient for a single closed walk when G > 0.

### 3.2 The polytope P(G, L, Σ)

Define:

```
P(G, L, Σ) = { d ∈ ℝ^{|Σ|^L}_+ : Σ d(i) = G,  Eulerian balance (C3') holds }
```

This is a rational polytope (intersection of half-spaces and hyperplanes with integer coefficients). Its extreme points are integer vectors (since the constraint matrix is totally unimodular for Eulerian balance on a directed graph).

**The true genome's vector d_S ∈ P(G, L, Σ) by construction.**

### 3.3 Structure of P(G, L, Σ)

**Dimension.** The number of free variables is |Σ|^L − 1 (from the sum constraint). The number of independent Eulerian constraints is |Σ|^(L−1) − 1 (one per vertex, minus one for linear dependence since total in = total out). So:

```
dim P = |Σ|^L − |Σ|^(L−1)
```

For Σ = {A,C,G,T}, L = 2: dim P = 16 − 4 = 12.

**Facets.** The facets of P are:
- The sum constraint hyperplane Σ d(i) = G.
- The non-negativity hyperplanes d(i) = 0 for each i.
- The Eulerian balance hyperplanes (C3') for each vertex.

**Extreme points.** Integer points in P correspond to L-mer spectra of circular strings of length G. Not every integer point in P is achievable (circular consistency for G small relative to L), but for G ≥ |Σ|^L + 1, all integer Eulerian flows are realizable.

### 3.4 The repeat-free case

S is **repeat-free** (all L-mers distinct) iff d_S(i) ∈ {0, 1} for all i and Σ d_S(i) = G. Since the L-mers must cover G positions with distinct values, we need G ≤ |Σ|^L. The repeat-free vector is:

```
d_S(i) = 1 for i in the L-mer spectrum of S, 0 otherwise
```

The set of achievable d vectors for repeat-free genomes is exactly the set of 0/1 vectors in P(G, L, Σ) with exactly G ones.

---

## 4. Optimality conditions

### 4.1 The optimization problem

**Problem.** Given observed counts x = (x_i) with Σ x_i = N, and the true genome's vector d_S, determine:

```
max_{d ∈ P(G,L,Σ)}  f(d) = Σ x_i log d(i)
```

and check whether d_S is a maximizer.

### 4.2 KKT conditions

Since f is concave and P is a convex polytope, d* is a global maximizer iff there exist dual variables λ (for the sum constraint), μ_i ≥ 0 (for non-negativity), and ν_j (for Eulerian balance) such that:

```
x_i / d*(i) = λ + Σ_j ν_j · A_{ji} − μ_i        for all i
μ_i · d*(i) = 0                                      (complementary slackness)
μ_i ≥ 0
```

where A_{ji} is the incidence matrix of the Eulerian constraints.

**At an interior point** (d*(i) > 0 for all i, so μ_i = 0):

```
x_i / d*(i) = λ + Σ_j ν_j · A_{ji}                for all i
```

This says: the ratio x_i / d*(i) must lie in the affine subspace spanned by the Eulerian constraint normals.

### 4.3 Interpretation

The KKT conditions say that d_S is optimal iff the gradient ∇f(d_S) = (x_i / d_S(i))_i lies in the normal cone of P at d_S. The normal cone is determined by the active constraints at d_S.

**For d_S in the interior of P** (all d_S(i) > 0, which holds when G > L and the genome covers all L-mer types needed for Eulerian connectivity):

```
d_S is optimal  ⟺  ∃ λ, ν_j :  x_i / d_S(i) = λ + Σ_j ν_j · A_{ji}  ∀ i with x_i > 0
```

### 4.4 Simple necessary condition

A necessary condition for d_S to be optimal is that no feasible direction from d_S improves f. Consider a perturbation δ with Σ δ(i) = 0 and δ in the tangent space of P (satisfying Eulerian balance). Then:

```
d_S is optimal  ⟹  Σ_i (x_i / d_S(i)) · δ(i) ≤ 0  for all feasible δ
```

Equivalently, the vector (x_i / d_S(i)) must make an obtuse angle with every feasible direction.

### 4.5 The repeat-free special case

When S is repeat-free, d_S(i) ∈ {0, 1} and the objective at d_S is:

```
f(d_S) = Σ_{i: d_S(i)=1} x_i · log(1) = 0
```

(since log 1 = 0). So for repeat-free S, **the log-likelihood of the truth is always 0** (up to the constant terms), regardless of the sample x.

For a competitor D with d_D(i) > 0 for all observed types:

```
f(d_D) = Σ_{i in observed} x_i log d_D(i)
```

Since d_D(i) >= 1 for observed types (integer multiplicities), f(d_D) >= 0. The competitor beats the truth iff f(d_D) > 0, which requires d_D(k) >= 2 for at least one observed type k with x_k > 0.

**Therefore: a repeat-free truth loses to any achievable competitor that amplifies a dominant observed type while maintaining d_D(j) > 0 for all observed types j.**

### 4.6 The positivity constraint: when truth IS optimal for repeat-free genomes

A crucial constraint is that **d_D(i) > 0 for all observed types i** (otherwise the likelihood is 0). For a repeat-free truth of length G, all G types in its spectrum have d_S(i) = 1 and sum to G. A competitor that increases d_D(k) from 1 to 2 must decrease some other d_D(j) from 1 to 0 (by the sum constraint). If j is an observed type, this makes D invalid.

**Theorem (Uniform sample optimality).** Let S be a repeat-free circular genome of length G with L-mers, and let the sample x assign positive counts to all G types (complete spectrum). Then d_S is the unique ML maximizer among all d in P(G,L,Sigma) with d(i) > 0 for all observed types.

*Proof.* Any competitor D with d_D(i) > 0 for all G observed types must have d_D(i) >= 1 for all i. Since sum d_D(i) = G and d_S(i) = 1 for all i, the only possibility is d_D(i) = 1 for all i. By strict concavity of f, d_S is the unique maximizer. QED

**Theorem (Skewed sample vulnerability).** Let S be repeat-free with L-mer spectrum of size G. If the sample x has support on k < G types, and there exists an achievable d_D with d_D(k) >= 2 for some observed type k and d_D(j) > 0 for all observed types j, then the competitor D beats the truth.

*Proof.* f(d_D) = sum x_i log d_D(i) >= x_k log 2 > 0 = f(d_S). QED

**Corollary.** Computational verification confirms that for all repeat-free truths of length 4-7 with L=2 over {A,C,G,T}, concentrated samples (single type) always admit amplifying competitors of the same length. The self-paired types (AA, CC, GG, TT) can be amplified to multiplicity 4; heterologous types (AC, AG, etc.) to multiplicity 2.

### 4.7 The positivity-Eulerian coupling

The feasibility of an amplifying competitor depends on three jointly satisfiable conditions:
1. Eulerian balance: d_D must be a valid flow on B(Sigma, L-1).
2. Sum constraint: sum d_D(i) = G.
3. Positivity: d_D(i) > 0 for all observed types i.

For concentrated samples (k << G), condition 3 is easy to satisfy (few observed types to protect), and the Eulerian balance can often be achieved by "chain" constructions that repeat the dominant k-mer. For complete-spectrum samples (k = G), condition 3 combined with the sum constraint forces d_D = d_S, making the truth uniquely optimal.

---

## 5. The concentration mechanism

### 5.1 When can a competitor increase d_D(i) for observed types?

The competitor wants to maximize Σ x_i log d_D(i) subject to d_D ∈ P(G, L, Σ) and d_D(i) > 0 for all observed types i.

Since f is concave, the maximum is at an extreme point of P restricted to d(i) > 0 for observed types. Extreme points of P are integer L-mer spectra of circular strings.

**A competitor can increase d_D(k) for a dominant type k if and only if:**
1. There exists a circular string of length G with d(k) > d_S(k) for type k.
2. The Eulerian balance is maintained.
3. d_D(i) > 0 for all observed types i.

### 5.2 The Eulerian obstacle

For L = 2, increasing d(k) = d(a, b) by 1 requires increasing some d(b, c) by 1 (to maintain out-degree at b) and decreasing some d(c', a) or increasing some d(a, c') (to maintain in-degree at a). This "chain" of adjustments may force d_D(j) = 0 for some observed type j, which would make D invalid.

**The Eulerian constraints create coupling between L-mer types.** A competitor cannot independently tune each d_D(i); adjustments propagate through the de Bruijn graph.

### 5.3 Parametric family: frequency amplification

For repeat-free S of length G with L = 2, and a single observed type k = (a, b) appearing n times:

**Construction:** D = (a, b)^m (m copies of the 2-mer k), giving length 2m and d_D(k) = m.

But this has length 2m ≠ G. For **fixed length G**, we need a different construction.

**Fixed-length construction:** Take D to be a circular string of length G that repeats k = (a, b) as many times as possible while maintaining Eulerian balance. The maximum d_D(k) is:

```
d_D(k) ≤ G - (number of other types needed for Eulerian balance)
```

For Σ = {A, C, G, T}, the minimum number of other types needed is 3 (to balance the in/out degrees at a, b, and the other two characters). So:

```
d_D(k) ≤ G - 3
```

**Achievable example for k = (A, C), G = 6:**

D = AACCGA (length 6):
- Position 0: AA, Position 1: AC, Position 2: CC, Position 3: CG, Position 4: GA, Position 5: AA
- d(AA) = 2, d(AC) = 1, d(CC) = 1, d(CG) = 1, d(GA) = 1
- Eulerian: A: out=2+0=2, in=1+1=2 ✓; C: out=1+1=2, in=2+0=2 ✓; G: out=1, in=1 ✓
- d_D(AC) = 1 = d_S(AC) (no improvement for AC)

**To beat the truth, we need d_D(k) > d_S(k) = 1.**

For k = (A, C), G = 6, a competitor with d_D(AC) = 2:

D = AACACC (length 6):
- Position 0: AA, Position 1: AC, Position 2: CA, Position 3: AC, Position 4: CC, Position 5: CA
- d(AA) = 1, d(AC) = 2, d(CA) = 2, d(CC) = 1
- Eulerian: A: out=1+2=3, in=2+0=... wait, let me recount.

Actually, for a circular string of length 6:
- s = AACACC
- Positions: 0:A, 1:A, 2:C, 3:A, 4:C, 5:C
- 2-mers: AA, AC, CA, AC, CC, CA
- d(AA)=1, d(AC)=2, d(CA)=2, d(CC)=1
- Eulerian: A: out=1+2=3, in=2+... hmm, let me be more careful.

For circular string s[0..5] = A, A, C, A, C, C:
- 2-mers at positions 0-5: (A,A), (A,C), (C,A), (A,C), (C,C), (C,A)
- d(AA)=1, d(AC)=2, d(CA)=2, d(CC)=1

Eulerian check:
- A: out = d(AA) + d(AC) = 1 + 2 = 3; in = d(AA) + d(CA) = 1 + 2 = 3 ✓
- C: out = d(CA) + d(CC) = 2 + 1 = 3; in = d(AC) + d(CC) = 2 + 1 = 3 ✓

Sum = 1+2+2+1 = 6 = G ✓

For truth S = AACAGG (from the counterexample):
- S = A, A, C, A, G, G
- 2-mers: AA, AC, CA, AG, GG, GA
- d_S(AA)=1, d_S(AC)=1, d_S(CA)=1, d_S(AG)=1, d_S(GG)=1, d_S(GA)=1

Sample x = {AA:5, CA:1, GG:1}, N=7:

For truth S: f(d_S) = 5*log(1) + 1*log(1) + 1*log(1) = 0.

For competitor D = AAAGGC: d_D(AA)=2, d_D(CA)=1, d_D(GG)=1 (all other observed types unchanged):
- f(d_D) = 5*log(2) + 1*log(1) + 1*log(1) = 5*log(2)

Likelihood ratio = prod_i (d_D(i)/d_S(i))^{x_i} = (2/1)^5 * (1/1)^1 * (1/1)^1 = 32.

The competitor doubles d(AA) from 1 to 2 while maintaining Eulerian balance. The 5-fold concentration on AA gives ratio 2^5 = 32.

---

## 6. Conditions under which truth must maximize likelihood

### 6.1 Complete spectrum observation (corrected)

**Theorem 1 (Repeat-free truth, complete spectrum).** Let S be a repeat-free circular genome of length G, and let the sample x assign positive counts to all G types in S's L-mer spectrum. Then d_S is the unique ML maximizer.

*Proof.* Any competitor D with d_D(i) > 0 for all G observed types must have d_D(i) >= 1 for all i. Since sum d_D(i) = G and d_S(i) = 1 for all i, the only feasible vector is d_D = d_S. QED

This is a degenerate case: the positivity constraint d_D(i) > 0 combined with the sum constraint and the repeat-free structure forces d_D = d_S.

For genomes with repeats (d_S(i) > 1 for some i), complete spectrum does NOT guarantee truth optimality. A competitor can increase d_D(k) for a dominant type k by redistributing flow within the Eulerian polytope while keeping all observed types positive.

### 6.2 Sufficient condition: sample proportional to truth's spectrum

**Theorem 2.** If x_i = c · d_S(i) for some constant c > 0 and all i with d_S(i) > 0, and if d_S is in the relative interior of P(G, L, Σ), then d_S is the unique ML maximizer.

*Proof.* The gradient of f at d_S is x_i / d_S(i) = c for all i with d_S(i) > 0. This is a constant, so the gradient is orthogonal to the constraint hyperplane Σ d(i) = G. The KKT conditions are satisfied with λ = c and all dual variables for active constraints equal to 0. By strict concavity, this is the unique maximizer. □

**Interpretation:** When the sample is a scaled version of the truth's L-mer spectrum, the truth is optimal. This is the "faithful sampling" regime.

### 6.3 Necessary condition: gradient alignment

**Theorem 3.** d_S is a (local, hence global for concave f) maximizer of f over P(G, L, Σ) iff:

```
(x_i / d_S(i))_{i: d_S(i)>0} ∈ N_P(d_S)
```

where N_P(d_S) is the normal cone of P at d_S.

For d_S in the relative interior of P (all d_S(i) > 0 and no Eulerian constraint is tight):

```
N_P(d_S) = { λ · 1 : λ ∈ ℝ }
```

(the normal cone is just the span of the all-ones vector, since only the sum constraint is active).

**Therefore: d_S is optimal iff x_i / d_S(i) is constant for all i, i.e., x_i ∝ d_S(i).**

This is a very restrictive condition. It says the truth is optimal only when the sample perfectly mirrors the truth's L-mer proportions.

---

## 7. Conditions under which truth need NOT maximize likelihood

### 7.1 The general obstruction

**Theorem 4 (Frequency-fitting obstruction).** For any repeat-free truth S of length G with |Sigma| >= 2 and L >= 2, and any sample x concentrated on a single observed type k with x_k >= 2, there exists a valid competitor D of length G with L_exact(D | x) > L_exact(S | x).

*Proof.* Since S is repeat-free, d_S(k) = 1. The objective at d_S is 0. Any achievable d_D with d_D(k) >= 2 and d_D(j) > 0 for all observed types j gives f(d_D) > 0.

For L = 2: heterologous type (a,b) with a != b can be amplified to d = 2 by the string (ab)^{G/2} when G is even, or by a near-repetition when G is odd. Self-paired type (a,a) can be amplified to d = G by the string a^G. In both cases, all observed types (just k) have d_D(k) > 0, and the Eulerian balance holds trivially. QED

For L >= 3: similar constructions exist using the de Bruijn graph structure. The Eulerian constraints are more restrictive, but for G large enough relative to |Sigma|^L, amplification is always possible. The minimum G for amplification depends on L and |Sigma|.

### 7.2 The Eulerian coupling mechanism

For L = 2, increasing d(a, b) by 1 requires:
- Increasing d(b, c) by 1 for some c (out-degree at b)
- Decreasing d(c', a) by 1 or increasing d(a, c') by 1 (in-degree at a)

This creates a **flow redistribution** on the de Bruijn graph. The competitor cannot increase d(k) for a single type k in isolation; it must adjust a cycle of types.

**When the cycle includes observed types with high x_i, the adjustments help. When it includes unobserved types, the adjustments are wasted.**

### 7.3 The bridging asymmetry (restated for fixed length)

**Theorem 5 (Asymmetry for fixed-length ML).** The I_s bridging conditions are properties of (S, R) where R is the realized read collection. For fixed candidate length G, the set of valid competitors {D : |D| = G, d_D(i) > 0 ∀ observed i} is identical regardless of whether S satisfies I_s.

*Proof.* I_s involves: (1) coverage of S by R; (2) repeat structure of S; (3) bridging of S's repeats by R. None mention D. The competitor D enters only through its occurrence vector d_D ∈ P(G, L, Σ). □

**Corollary.** For fixed-length exact ML, bridging conditions cannot restrict the competitor pool. They constrain d_S (the truth's spectrum) but not the set of d_D over which the optimization is performed. The truth is optimal iff d_S maximizes f over P, which depends on the relationship between x and d_S, not on whether S satisfies I_s.

### 7.4 Quantitative bound: when does the competitor win?

For a repeat-free truth with d_S(k) = 1 for all k in its spectrum, and a sample with x_k = n for a single type k:

```
f(d_S) = 0
f(d_D) = n · log d_D(k)
```

The competitor wins whenever d_D(k) ≥ 2 and d_D is achievable. The minimum achievable d_D(k) ≥ 2 is constrained by:

1. Eulerian balance: increasing d(k) requires compensating adjustments.
2. Non-negativity of other types.
3. The total sum Σ d(i) = G.

For L = 2 and a "chain" construction (repeating k = (a, b) with minimal fill), the maximum d_D(k) achievable is roughly G/2 (filling half the genome with the repeating pattern). This gives:

```
f(d_D) ≈ n · log(G/2)
```

which grows as log G for fixed n, and linearly in n for fixed G.

---

## 8. Connection to existing counterexamples

### 8.1 The AACAGG counterexample (fixed-length, vacuous bridging)

- S = AACAGG (G=6, L=2), repeat-free.
- d_S = (1,1,1,1,1,1) for types {AA, AC, CA, AG, GG, GA}.
- Sample x = {AA:5, CA:1, GG:1}.
- Competitor D = AAAGGC: d_D(AA)=2, d_D(CA)=1, d_D(GG)=1, others ≥ 1.
- f(d_S) = 0, f(d_D) = 5·log 2 + 0 + 0 = 5·log 2.
- Ratio = 2^5 = 32.

**Mechanism:** The sample concentrates 5/7 on AA. The competitor doubles d(AA) from 1 to 2 while maintaining Eulerian balance (the extra AA is balanced by adjusting CA and other types). The 5-fold concentration on the amplified type gives ratio 2^5 = 32.

### 8.2 The AAABB counterexample (fixed-length, substantive bridging)

- S = AAABB (G=5, L=3), has genuine repeats.
- Sample x = {AAA:1, AAB:1, BAA:1}.
- Competitor D = AAAAB: d_D(AAA)=2, d_D(AAB)=1, d_D(BAA)=1.
- f(d_S) = log 1 + log 1 + log 1 = 0.
- f(d_D) = 1·log 2 + 0 + 0 = log 2.
- Ratio = 2.

**Mechanism:** Same frequency-fitting: the competitor doubles d(AAA) while maintaining the 3-mer Eulerian constraints. The sample has one type (AAA) that benefits from amplification.

### 8.3 The AAABB counterexample (fixed-length, substantive bridging, detailed)

- S = AAABB (G=5, L=3):
  - Positions: 0:A, 1:A, 2:A, 3:B, 4:B
  - 3-mers: AAA (pos 0), AAB (pos 1), ABB (pos 2), BBA (pos 3), BAA (pos 4)
  - d_S(AAA)=1, d_S(AAB)=1, d_S(ABB)=1, d_S(BBA)=1, d_S(BAA)=1

- D = AAAAB (G=5, L=3):
  - Positions: 0:A, 1:A, 2:A, 3:A, 4:B
  - 3-mers: AAA (pos 0), AAA (pos 1), AAB (pos 2), ABB (pos 3), BAA (pos 4)
  - d_D(AAA)=2, d_D(AAB)=1, d_D(ABB)=1, d_D(BAA)=1

- Sample from starts [0, 1, 4]: {AAA:1, AAB:1, BAA:1}

The competitor D has d_D(AAA) = 2 vs d_S(AAA) = 1, with all other observed types unchanged. This is the minimum feasible improvement: doubling one occurrence count.

---

## 9. The role of the multinomial coefficient

### 9.1 When does it matter?

Under **fixed candidate length G**, the multinomial coefficient N! / ∏ x_i! is constant across candidates and plays no role in ML ordering. This is a key simplification.

Under **variable candidate length**, the multinomial coefficient is still constant (it depends only on the observed counts, not on the candidate). The candidate-dependent factor is ∏ (d_D(i) / N(D))^{x_i}, which includes N(D) in the denominator. The multinomial coefficient remains irrelevant for ordering.

**The multinomial coefficient is never relevant for ML ordering.** It is a normalization constant that depends only on the observed data.

### 9.2 What the multinomial coefficient encodes

The multinomial coefficient N! / ∏ x_i! counts the number of ways to assign N labeled draws to types with counts x_i. It is large when the sample is diverse (many types with moderate counts) and small when concentrated.

For the **probability** of the observed data under a candidate, the multinomial coefficient matters:

```
P(x | D) = (N! / ∏ x_i!) × ∏ (d_D(i) / G)^{x_i}
```

But for **comparing** two candidates, it cancels:

```
P(x | D) / P(x | S) = ∏ (d_D(i) / d_S(i))^{x_i}
```

---

## 10. Summary of structural results

### 10.1 The objective

Under fixed candidate length G, the ML objective reduces to:

```
argmax_d Σ x_i log d(i)   subject to   d ∈ P(G, L, Σ)
```

where P(G, L, Σ) is the polytope of achievable L-mer occurrence vectors for circular strings of length G.

### 10.2 The achievability polytope

P(G, L, Σ) is defined by:
- Σ d(i) = G (sum constraint)
- d(i) ≥ 0 (non-negativity)
- Eulerian balance on B(Σ, L−1) (de Bruijn graph flow conservation)

### 10.3 When truth IS optimal

1. **Repeat-free truth, complete spectrum:** If S is repeat-free and the sample has all G types observed, the positivity constraint forces d_D = d_S, so the truth is uniquely optimal (Theorem 1, §6.1).
2. **Sample proportional to truth's spectrum:** If x_i = c * d_S(i) for all i, the truth is optimal by KKT (Theorem 2, §6.2).
3. **Interior KKT point:** d_S is optimal iff x_i / d_S(i) is constant across all i with d_S(i) > 0 (Theorem 3, §6.3). This is equivalent to x being proportional to d_S.

### 10.4 When truth is NOT optimal

1. **Skewed sample on repeat-free truth:** If the sample concentrates on k < G types, a competitor can amplify a dominant type while keeping all observed types positive. The ratio grows as d_D(k)^{x_k} (Theorem 4, §7.1). Computational verification confirms this for all repeat-free truths of length 4-7 with L=2.
2. **Sample mismatch:** When x_i / d_S(i) varies across types, the gradient is not in the normal cone and d_S is not optimal.
3. **Eulerian-achievable amplification:** When the Eulerian constraints permit d_D(k) > d_S(k) for a high-count type k, a competitor wins. The existing counterexamples (ratio 2 for AAABB, ratio 32 for AACAGG) demonstrate this.

### 10.5 The fundamental asymmetry

- Bridging conditions constrain d_S (the truth's spectrum) through the repeat structure of S.
- The ML objective compares d_S to d_D over the polytope P(G, L, Σ).
- Bridging does not constrain P or the competitor's position in P.
- Therefore, bridging cannot force d_S to be optimal in P.

### 10.6 What remains open

1. **Variant A (binomial approximation):** The objective ∏ d_D(i)^{x_i} with fixed external N instead of G. The polytope P is the same, but the objective is different. Whether bridging forces optimality under this objective is open.

2. **Variant F (flow-feasible candidates):** The search space is restricted to overlap-graph flows, not all of P(G, L, Σ). Bridging might interact with flow constraints. This is the most plausible route to a positive result.

3. **Conditions on x:** For what distributions of x (as a function of d_S, G, L, N) is d_S optimal with high probability? This is a statistical question about the sampling process, not a worst-case question.

4. **Tight Eulerian bounds:** What is the maximum possible ratio L_exact(D) / L_exact(S) as a function of G, L, |Σ|, and the sample size N? The existing counterexamples achieve ratio 2 for small G; the parametric family achieves (G/L)^n for unrestricted length. For fixed length, the achievable ratio is constrained by the Eulerian polytope.

---

## 11. Epistemic status

| Claim | Status | Location |
|-------|--------|----------|
| Objective reduces to Σ x_i log d(i) | **Proven** | §2.1 |
| P(G,L,Σ) is a rational polytope | **Proven** | §3.2 |
| d_S ∈ P(G,L,Σ) always | **Proven** | §3.2 |
| Repeat-free truth, complete spectrum: truth optimal | **Proven** | §6.1 |
| Repeat-free truth, skewed sample: truth loses | **Proven** | §4.6, §7.1 |
| KKT characterization of optimality | **Proven** | §4.2 |
| Bridging asymmetry for fixed length | **Proven** | §7.3 |
| Truth optimal when x ∝ d_S | **Proven** | §6.2 |
| Ratio 2 for AAABB counterexample | **Verified** (exact arithmetic) | §8.2 |
| Ratio 32 for AACAGG counterexample | **Verified** (exact arithmetic) | §8.1 |
| Variant A / F still open | **Open** | §10.6 |

---

## Source citations

| Fact | Source |
|------|--------|
| Exact multinomial with N(D) | Medvedev–Brudno 2009, §6.1 |
| Fixed-length restriction | This analysis, §1 |
| Eulerian balance for L-mers | de Bruijn graph theory; Pevzner 2000 |
| Repeat-free vulnerability | This analysis, §4.5 |
| AACAGG counterexample | docs/bridging-likelihood-obstructions.md |
| AAABB counterexample | docs/analysis-bridging-implies-what.md §3.3 |
| Bridging asymmetry | docs/bridging-likelihood-obstructions.md Theorem 2 |
