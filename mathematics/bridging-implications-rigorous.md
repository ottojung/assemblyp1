# Rigorous implications of the published bridging/information-feasibility conditions

_Status: mathematical analysis. Not a Lean result. All claims classified by epistemic class._

---

## 0. Scope and the invalid inference pattern

This note answers a precise question: **what do the source-faithful Shomorony repeat-bridging conditions I_s actually imply about (a) the observed fixed-length read multiset x and (b) the set of competitor genomes D?**

The analysis is organized around one central caution. A frequent informal argument runs:

> "I_s is a hypothesis about S (the truth) and R (the realized reads). It does not mention D (the competitor). Therefore I_s cannot constrain D. Therefore I_s cannot force ML optimality."

This reasoning contains a valid step and an invalid step:

- **Valid**: I_s does not directly mention D, so I_s does not directly constrain d_D (the competitor's occurrence vector). This is the *asymmetry theorem* (Theorem 1 below), which is proven and correct.
- **Invalid**: from "I_s does not directly constrain D" to "I_s cannot force ML." The invalid step ignores that I_s constrains x (the observed read multiset), which constrains the ML objective, which determines whether d_S is optimal. Moreover, under Variant F the candidate universe F_flow(R) depends on R, which depends on S through sampling, creating a coupling chain that the informal argument misses.

The rigorous content below separates what is proven from what is open, and identifies exactly where the invalid inference would need to be rescued (or refuted) to settle the open question.

---

## 1. The I_s conditions: precise content

**Definition (I_s).** R ∈ I_s iff:
1. R covers S (every genome position lies in at least one read);
2. every maximal triple repeat in S is all-bridged (each selected copy is bridged);
3. every pair of interleaved maximal repeats in S is bridged (at least one constituent repeat is bridged).

A read [r, r+L) bridges a copy at position t with length l iff r < t and t + l < r + L.

*Source:* Shomorony et al. 2016, Eq. (1); Bresler et al. 2013. Definitions at `docs/bridging-source-semantics.md:53-61`.

---

## 2. Valid lemmas: what I_s implies about the read multiset x

### Lemma 1 (I_s constrains support, not concentration)

I_s constrains the *support* supp(x) = {i : x_i > 0} but places no upper bound on any individual count x_k.

**Proof.** I_s requires reads from specific start positions (bridging intervals and coverage positions). Each such start produces an L-mer type that must appear in supp(x). However, I_s constrains only *which* start positions must appear in R, not *how many times* each start is sampled. Under i.i.d. uniform sampling, any valid start position can be sampled arbitrarily many times. Formally, for any R satisfying I_s and any valid start position p, the modified collection R' with one additional read from p also satisfies I_s (coverage and bridging are monotone in R). Therefore x_k can be arbitrarily large for any k in supp(x). □

**Epistemic status:** Proven (immediate from monotonicity of coverage and bridging in R).

**Implication for ML:** The ML objective f(d) = Σ x_i log d_i depends on concentration, not just support. A sample with support on many types but concentration on one type (x_k ≫ x_j for j ≠ k) is fully compatible with I_s. This is the mechanism by which counterexamples are constructed.

### Lemma 2 (Coverage forces observed-type presence in d_S)

If I_s holds, then d_S(i) ≥ 1 for every L-mer type i with x_i > 0.

**Proof.** A read of type i starting at position p implies S[p..p+L) = i, so d_S(i) ≥ 1. □

**Epistemic status:** Proven.

### Lemma 3 (Bridging bounds repeat length in S)

Under I_s, every maximal repeat in S has length l ≤ L − 2.

**Proof.** A repeat of length l requires bridging: a read [r, r+L) with r < t and t + l < r + L. This gives L > l + 1, i.e., l ≤ L − 2. □

**Epistemic status:** Proven.

### Lemma 4 (I_s implies concentration is achievable under sampling)

For any S satisfying I_s, any L-mer type k with d_S(k) ≥ 1, and any integer M ≥ 1, there exists a sample x achievable under i.i.d. uniform sampling from S with x_k ≥ M and x satisfying I_s.

**Proof.** Under i.i.d. uniform sampling, the number of reads starting at any given position follows a Binomial(N, 1/G) distribution. Taking N large enough and conditioning on coverage (which holds w.h.p. for N ≥ c·G·log G), we can make x_k arbitrarily large while maintaining coverage. I_s is satisfied because S's repeat structure is fixed (independent of sampling) and coverage is maintained. □

**Epistemic status:** Proven (standard concentration bounds for i.i.d. sampling).

---

## 3. Valid lemma: the asymmetry theorem (what I_s does NOT imply)

### Theorem 1 (Bridging asymmetry for fixed-length ML)

Let S be a circular genome of length G satisfying I_s. The set of valid competitors

C(x) = { D : |D| = G, d_D(i) > 0 for all i with x_i > 0 }

is independent of whether S satisfies I_s.

**Proof.** The bridging conditions I_s are properties of the pair (S, R). They involve:
1. Coverage of S by R (property of S and R);
2. Repeat structure of S (property of S alone);
3. Whether reads in R bridge copies of S's repeats (property of S and R).

None of these involve the competitor D. The competitor D enters only through its occurrence vector d_D ∈ P(G, L, Σ). Therefore C(x) depends on x and G, but not on I_s. □

**Epistemic status:** Proven (Theorem 2 of `docs/bridging-likelihood-obstructions.md:148-155`; Theorem 1 of `mathematics/deterministic-vs-likelihood-separation.md`).

**What this correctly implies:** For Variant E (exact multinomial over all length-G circular genomes), the RHS of the ML dominance condition

max_{d_D ∈ P(G,L,Σ), d_D(i) > 0 ∀ observed i} Σ_i x_i log d_D(i)

is independent of I_s. Therefore I_s cannot force the inequality Σ_i x_i log d_S(i) ≥ RHS to hold by restricting the competitor set.

**What this does NOT imply:** That I_s cannot constrain ML under *any* variant. The theorem applies to variants where the competitor universe is defined independently of R. Under Variant F, the competitor universe is F_flow(R), which *does* depend on R, and therefore *does* depend on I_s through the coupling chain (Theorem 3 below).

---

## 4. The invalid inference, stated precisely

**The invalid inference is the following syllogism:**

(P1) I_s is a property of (S, R), not of D. [True, by Theorem 1]
(P2) Therefore I_s cannot constrain the set of valid competitors. [True for Variants E, A; FALSE for Variant F]
(C) Therefore I_s cannot force ML optimality. [Does not follow]

The syllogism is invalid because:
- (P2) is false under Variant F, where the competitor universe F_flow(R) depends on R, which depends on S through sampling.
- Even under Variants E, A where (P2) is true, (C) does not follow: I_s constrains *which x are achievable*, which constrains *the likelihood objective*, which determines whether d_S is optimal. The correct statement is: "I_s constrains x, and x determines ML optimality; I_s does not independently constrain the competitor set."

**The valid version of the argument for Variants E, A is:**

(V1) I_s constrains d_S (Lemmas 3-4) but not P(G, L, Σ) (Theorem 1). [True]
(V2) ML optimality requires d_S to maximize Σ x_i log d_i over P(G, L, Σ). [True by definition]
(V3) Whether d_S is optimal depends on the relationship between x and d_S (KKT conditions), not on whether S satisfies I_s. [True: for d_S in the relative interior of P, optimality requires x_i ∝ d_S(i), which is a property of x, not of I_s]
(C') Therefore I_s cannot force ML optimality under Variants E, A. [Valid conclusion from V1-V3]

The critical distinction: V3 is the actual mathematical reason, not the informal "I_s doesn't mention D."

---

## 5. The Variant F coupling chain: where the invalid inference breaks

### Theorem 2 (Variant F coupling chain)

Under Variant F (flow-feasible candidates, Medvedev-Brudno §6.2), the candidate universe is F_flow(R), which depends on R. Since R depends on S through sampling, I_s on S indirectly constrains F_flow(R):

I_s → S's repeat structure → R composition → G(R) → F_flow(R)

**Proof.** 
1. I_s constrains S's repeat structure (Lemma 3: repeat length ≤ L − 2; bridging intervals of size L − l − 1).
2. S's repeat structure determines which start positions produce which L-mers.
3. I_s requires reads from specific start positions (bridging intervals, coverage positions). This constrains the set of possible R.
4. R determines the overlap graph G(R) (vertices are reads, edges are overlaps).
5. G(R) determines F_flow(R) (genomes reconstructible from R via overlap-graph flow).

Each step is a deterministic function of the previous. Therefore I_s propagates through the chain to constrain F_flow(R). □

**Epistemic status:** Proven (structural argument; Theorem 3 of `docs/bridging-flow-feasibility-lemma.md:149-175`).

**What is NOT proven:** Whether the coupling is *strong enough* to force d_S to be optimal over F_flow(R). This is the genuinely open question (Lemmas I and J of `mathematics/bridging-combinatorial-implications-for-fixed-length.md:198-204`).

### The overlap graph rigidity theorem (positive case)

**Theorem 3 (Overlap-graph rigidity for distinct reads).** For repeat-free S with L ≥ 3, if all reads in R are distinct, then G(R) is a directed cycle and F_flow(R) = {S}. ML is trivially satisfied.

**Proof.** Since S is repeat-free, every length-L circular substring is distinct, so each L-mer type appears at most once. For L ≥ 3, each (L-1)-mer prefix/suffix appears as prefix/suffix of at most one L-mer, giving in-degree ≤ 1 and out-degree ≤ 1 at every vertex of G(R). The circular structure forces a single Hamiltonian cycle, hence a unique flow. □

**Epistemic status:** Proven (Theorem 1 of `docs/bridging-flow-feasibility-lemma.md:68-104`).

**Limitation:** Applies only when all reads are distinct (N ≤ G for repeat-free S). When N > G, repeated reads create parallel vertices enabling alternative flows.

### The vulnerability to repeated reads (negative case)

**Theorem 4 (Repeated reads enable competitors).** For repeat-free S, if x_k ≥ 2 for some type k, G(R) has parallel vertices enabling alternative flows with d_D(k) ≥ 2. I_s does not prevent x_k ≥ 2.

**Proof.** Two reads of the same type from different starts are distinct vertices with identical neighborhoods. Parallel vertices in an Eulerian multigraph enable alternative circuits. I_s for repeat-free S reduces to coverage, which does not bound multiplicities. □

**Epistemic status:** Proven (Theorem 2 of `docs/bridging-flow-feasibility-lemma.md:107-146`).

---

## 6. Counterexamples that correctly separate what is refuted

### Counterexample 1 (Variant E, unrestricted length, kernel-checked)

- Truth: S = ACGT (G = 4, L = 2)
- Observed: R = {AC:2, GT:1} (starts [0, 0, 2])
- Competitor: D = ACACGT (length 6 ≠ G)
- I_s satisfied (repeat-free, coverage holds)
- L_exact(D | x) / L_exact(S | x) = 64/54 > 1

*Source:* `docs/exact-variant-e-counterexample.md`. Kernel-checked in Lean.

**What this refutes:** Variant E with unrestricted competitor length. D has length 6 ≠ G = 4.

### Counterexample 2 (Variant E, fixed length, exact arithmetic)

- Truth: S = AACAGG (G = 6, L = 2), repeat-free
- Observed: x = {AA:5, CA:1, GG:1} (N = 7)
- Competitor: D = AAAGGC (G = 6, d_D(AA) = 2)
- I_s satisfied (vacuously: repeat-free)
- Ratio: 32

*Source:* `docs/bridging-likelihood-obstructions.md:88-144`. Exact rational arithmetic.

**What this refutes:** Fixed-length Variant E. The competitor has the same length G = 6.

### Counterexample 3 (Variant E, fixed length, substantive bridging)

- Truth: S = AAABB (G = 5, L = 3)
- Triple repeat of A at positions (0,1,2): all-bridged
- Observed: x = {AAA:3, AAB:1, BAA:1} (N = 5)
- Competitor: D = AAAAB (d_D(AAA) = 2)
- I_s satisfied substantively (bridging is non-vacuous)
- Ratio: 8

*Source:* `docs/exhaustive-small-instance-search-v2.md:53-59`. Exact rational arithmetic.

**What this refutes:** Fixed-length Variant E even with substantive (non-vacuous) bridging.

### What these counterexamples do NOT refute

- **Variant F (flow-feasible candidates):** The competitor D must be checked for flow-feasibility w.r.t. R. If the overlap graph G(R) does not support the flow needed for D, then D ∉ F_flow(R) and the counterexample does not apply.
- **The statement "I_s implies ML under some variant not yet tested":** The counterexamples are specific to the variants they test.

---

## 7. The KKT characterization: when truth IS optimal (for any variant)

### Theorem 5 (Proportionality = optimality)

Let S be a circular genome of length G with d_S(i) > 0 for all i (interior point of P(G, L, Σ)). Then d_S is the unique ML maximizer among all d ∈ P(G, L, Σ) iff:

x_i = c · d_S(i) for some constant c > 0 and all i

**Proof.** By KKT conditions at an interior point, the normal cone is span{1}, so optimality requires x_i / d_S(i) = constant. □

**Epistemic status:** Proven (`mathematics/fixed-length-exact-likelihood-characterization.md:199-209`).

**Implication:** For the truth to be optimal under any variant where the competitor universe includes all of P(G, L, Σ), the sample must be proportional to d_S. Under i.i.d. sampling, this is a measure-zero event (除非 d_S is uniform and the sample is exactly uniform). This is why Variant E is universally refuted.

### Theorem 6 (Complete-spectrum trivial case)

If the sample x assigns positive counts to all G types in S's L-mer spectrum (complete spectrum), then d_S is the unique ML maximizer, regardless of I_s or flow-feasibility.

**Proof.** Any competitor with d_D(i) > 0 for all G types must have d_D(i) ≥ 1 for all i. Since Σ d_D(i) = G = Σ d_S(i) with d_S(i) = 1, the only possibility is d_D = d_S. □

**Epistemic status:** Proven.

---

## 8. What remains genuinely open

### The Variant F question

**Open Question.** Does I_s + flow-feasibility imply ML optimality for any nontrivial class of (S, L, G)?

**What would a positive proof require:**
1. For every S satisfying I_s with repeats of length l ≤ L − 2,
2. For every valid R satisfying I_s (with starts constrained to bridging intervals),
3. For every flow-feasible D ∈ F_flow(R) with d_D(i) > 0 for all observed i,
4. Σ_i x_i log(d_D(i)/d_S(i)) ≤ 0.

**What would a negative counterexample require:**
1. An S satisfying I_s with specific repeats,
2. A valid R satisfying I_s,
3. A flow-feasible D ∈ F_flow(R) with d_D(k) > d_S(k) for some observed k,
4. Such that D is reconstructible from R via overlap-graph flow.

**Assessment:** The coupling chain (Theorem 2) is proven. The overlap-graph rigidity (Theorem 3) handles the distinct-reads case. The vulnerability to repeated reads (Theorem 4) shows the mechanism of failure. The open question is whether, for S *with* repeats (where I_s is substantive), the bridging-start coupling constrains the overlap graph enough to prevent competitors. No proof or counterexample exists.

### The key parameter: bridging-interval coverage ratio

Define ρ(S, L) = |union of bridging intervals for all repeats in S| / G.

When ρ is large, F_flow(R) is tightly constrained. When ρ is small, F_flow(R) may include competitors.

**Open conjecture.** For S with ρ(S, L) > 1/2, F_flow(R) = {S} for all R satisfying I_s.

*Epistemic status:* Conjecture. The structural coupling is proven; the quantitative threshold is open.

---

## 9. Summary: what I_s implies, validly

| Statement | Status | Notes |
|-----------|--------|-------|
| I_s constrains support of x, not concentration | **Proven** | Lemma 1 |
| I_s forces d_S(i) ≥ 1 for observed types | **Proven** | Lemma 2 |
| I_s bounds repeat length ≤ L − 2 | **Proven** | Lemma 3 |
| I_s does not directly constrain d_D | **Proven** | Theorem 1 (asymmetry) |
| I_s cannot force ML under Variant E (fixed-length) | **Proven** | Theorems 1 + 5 + counterexamples |
| I_s cannot force ML under Variant E (unrestricted) | **Proven** | Counterexample 1 |
| I_s cannot force ML under Variant A (fixed-length) | **Proven** | Same as Variant E |
| I_s constrains F_flow(R) through coupling chain | **Proven** | Theorem 2 |
| I_s forces ML under Variant F (distinct reads, repeat-free) | **Proven** | Theorem 3 |
| I_s forces ML under Variant F (S with repeats) | **OPEN** | No proof or counterexample |
| ρ > 1/2 implies F_flow(R) = {S} | **OPEN** | Conjecture |
| "I_s doesn't mention D, therefore I_s cannot force ML" | **INVALID** | Fails under Variant F; even for E, the real reason is KKT, not the informal argument |

---

## 10. Source citations

| Fact | Primary source | Repository anchor |
|------|---------------|-------------------|
| I_s definition | Shomorony et al. 2016, Eq. (1) | `docs/bridging-source-semantics.md:53-61` |
| Asymmetry theorem | Proven in repository | `docs/bridging-likelihood-obstructions.md:148-155` |
| Overlap-graph rigidity | Proven in repository | `docs/bridging-flow-feasibility-lemma.md:68-104` |
| Vulnerability to repeated reads | Proven in repository | `docs/bridging-flow-feasibility-lemma.md:107-146` |
| Bridging constrains overlap graph | Proven in repository | `docs/bridging-flow-feasibility-lemma.md:149-175` |
| KKT optimality | Classical convex optimization | `mathematics/fixed-length-exact-likelihood-characterization.md:144-191` |
| Eulerian polytope | de Bruijn graph theory | `docs/eulerian-edge-count-formulation.md:66-83` |
| AACAGG counterexample | Exact rational arithmetic | `docs/bridging-likelihood-obstructions.md:88-144` |
| AAABB counterexample | Exact rational arithmetic | `docs/exhaustive-small-instance-search-v2.md:53-59` |
| ACGT counterexample | Kernel-checked (Lean) | `docs/exact-variant-e-counterexample.md` |
| Exhaustive search | Exact rational arithmetic | `docs/exhaustive-small-instance-search-v2.md` |
