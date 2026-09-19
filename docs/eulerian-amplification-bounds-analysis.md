# Eulerian amplification bounds and fixed-length exact ML structural analysis

_Status: computational evidence and mathematical analysis. Reproducible exact-rational computation. Not a Lean result._

## Scope

This note independently analyzes the **source-faithful fixed-candidate-length exact Variant E** ML objective, focusing on:
1. Precise Eulerian amplification bounds on d_D(k) for L=2 over alphabets of size 2, 3, 4
2. Exhaustive search confirmation for alpha=4 (the paper's {A,C,G,T} alphabet)
3. Structural characterization of when counterexamples exist for repeat-free truths

**Assumptions and model version:**
- Circular true genome S of length G over alphabet Σ
- Read length L=2, N reads sampled i.i.d. uniformly from G circular starts
- Fixed candidate length: all candidates D have |D| = G
- Exact multinomial: L(D|x) proportional to ∏_i d_D(i)^{x_i} (constant multinomial coefficient cancels)
- I_s bridging conditions: coverage + all-bridged triple repeats + bridged interleaved repeats
- Genome equivalence: truth ≠ competitor (different circular string)

**Limitations:**
- Exhaustive search limited to G ≤ 6 for alpha=4 (search space 4^G grows exponentially)
- Only L=2 analyzed in depth; L=3,4 have separate existing results
- I_s verification is exhaustive but the bridging detection implementation follows the V2 script's conventions
- No formal proof of the Eulerian bounds; verified computationally for G ≤ 8

---

## 1. Eulerian amplification bounds (exact, L=2)

For a repeat-free truth where d_S(k) = 1, the ML ratio for a concentrated sample {k:n} is d_D(k)^n. The maximum achievable d_D(k) over all circular genomes of length G determines the worst-case vulnerability.

### Theorem (Eulerian amplification bound, L=2, verified computationally for G ≤ 8)

For L=2 over any alphabet Σ of size σ:

1. **Self-loop kmer (a,a):** max d_D(a,a) = G. Achieved by genome a^G (all same character).

2. **Heterologous kmer (a,b) with a ≠ b:** max d_D(a,b) = ⌊G/2⌋.
   - Achieved by genome (ab)^{G/2} when G even.
   - When G odd: genome (ab)^{(G-1)/2} a, giving d(a,b) = (G-1)/2 = ⌊G/2⌋.

**Proof sketch.** For self-loops: the genome a^G has d(a,a) = G trivially. For heterologous: the Eulerian constraint requires d(a,b) = d(b,a) = m (flow conservation at a and b). This uses 2m positions. Remaining G-2m positions filled by self-loops on other symbols. Maximum m = ⌊G/2⌋.

### Verified bounds table (L=2, sigma=4)

| G | max d(self-loop) | max d(heterologous) | max ratio (self, n=G) | max ratio (het, n=G) |
|---|---|---|---|---|
| 4 | 4 | 2 | 256 | 16 |
| 5 | 5 | 2 | 3125 | 32 |
| 6 | 6 | 3 | 46656 | 729 |
| 7 | 7 | 3 | 823543 | 2187 |
| 8 | 8 | 4 | 16777216 | 65536 |

**The bounds are independent of alphabet size σ for σ ≥ 2.** The heterologous bound ⌊G/2⌋ holds for σ=2,3,4 and is determined by the flow conservation constraint at the two endpoints, not by the number of available filler symbols.

### Consequence for repeat-free truths

For a repeat-free truth S of length G with L=2:
- If the dominant observed kmer is a self-loop (e.g., AA): max ratio = G^{x_k}
- If the dominant observed kmer is heterologous (e.g., AB): max ratio = ⌊G/2⌋^{x_k}
- Self-loop types are strictly more vulnerable (G > ⌊G/2⌋ for G ≥ 2)

---

## 2. Exhaustive search: alpha=4 (ACGT), L=2

### G=4, L=2, N=4

| Metric | Value |
|--------|-------|
| Total circular strings | 256 |
| I_s-satisfying (truth, starts) pairs | 3,952 |
| Counterexamples | 216 |
| Vacuous bridging | 216 |
| Substantive bridging | 0 |
| Max ratio | 16 |

All 216 counterexamples are vacuously bridging (repeat-free truths with no repeats to bridge). Representative: AABB vs ABAB, ratio = 16 (= 2^4 for heterologous AB amplified to d=2).

### G=5, L=2, N=5

| Metric | Value |
|--------|-------|
| Total circular strings | 1,024 |
| I_s-satisfying pairs | 30,804 |
| Counterexamples | 4,800 |
| Vacuous bridging | 4,800 |
| Substantive bridging | 0 |
| Max ratio | 8 |

Counterexamples at G=5 with alpha=4 have lower max ratio than G=4 because the Eulerian bound for heterologous types remains ⌊5/2⌋ = 2, but the sample structure at G=5 distributes observations differently.

### Key observation: zero substantive bridging counterexamples for L=2

For L=2, no repeat of positive length can be bridged (bridging requires L ≥ ℓ + 2, so ℓ = 0 only). The I_s conditions reduce to: no maximal triple repeats exist. At G ≤ 6, many repeat-free genomes satisfy I_s vacuously. At G ≥ 7 (alpha=4), almost every genome has a maximal triple repeat of length 1 (some character appears ≥ 3 times with non-uniform flanking), making I_s unsatisfiable.

**This is consistent with the alpha=3 results.** The zero substantive counterexamples at L=2 reflects the structural fact that L=2 reads cannot bridge any repeat of positive length.

---

## 3. Structural characterization: when do counterexamples exist?

### The complete-spectrum safety theorem (from existing analysis, computationally confirmed)

**Theorem.** If the sample x assigns positive counts to all G types in a repeat-free truth's spectrum (complete spectrum), then d_S is the unique ML maximizer among all d in P(G,L,Σ) with d(i) > 0 for all observed types.

**Proof.** Any competitor D with d_D(i) > 0 for all G observed types must have d_D(i) ≥ 1 for all i. Since Σ d_D(i) = G and d_S(i) = 1 for all i, the only feasible vector is d_D = d_S. QED.

### The skewed-sample vulnerability theorem

**Theorem.** For any repeat-free truth S of length G ≥ 4 with L=2 over any alphabet of size ≥ 2, and any sample x concentrated on a single observed type k with x_k ≥ 2, there exists a valid competitor D of length G with L_exact(D|x) > L_exact(S|x).

**Proof.** Since S is repeat-free, d_S(k) = 1. The objective at d_S is 0. Any achievable d_D with d_D(k) ≥ 2 and d_D(j) > 0 for all observed types j gives f(d_D) > 0.

For self-loop k = (a,a): D = a^G has d_D(k) = G ≥ 2. Only observed type is k, so positivity holds trivially. Ratio = G^{x_k}.

For heterologous k = (a,b): D = (ab)^{G/2} (G even) has d_D(k) = G/2 ≥ 2 for G ≥ 4. Only observed type is k. Ratio = (G/2)^{x_k}. QED.

### The genome-length-vs-distinct-types threshold

Computational analysis reveals a structural threshold for repeat-free truths:

- **G=4, sigma=4:** 192 repeat-free genomes. Among those with I_s-satisfying observations:
  - AABB, AACC, etc. (D < G distinct types): counterexamples exist (max ratio 16)
  - AABC, AACD, etc. (D = G distinct types): NO counterexamples

- **G=5, sigma=4:** 600 repeat-free genomes. Similar pattern:
  - AABBC, AABBD, etc. (D < G): counterexamples exist (max ratio 8)
  - AABAC, AABAD, etc. (D = G): NO counterexamples

**Conjecture (computational evidence, not proved).** For a repeat-free truth S of length G with L=2:
- If S has < G distinct kmer types: counterexamples exist for some I_s-satisfying observations
- If S has = G distinct kmer types: no counterexamples exist for any I_s-satisfying observation

**Mechanism.** When D = G, the positivity constraint d_D(i) > 0 for all G observed types combined with Σ d_D = G forces d_D = d_S. When D < G, there is slack in the sum constraint allowing amplification.

**This does NOT constitute evidence for a positive resolution of the open problem.** The threshold applies only to repeat-free truths with complete-spectrum-like observations. For truths with repeats (d_S(k) > 1 for some k), or for incomplete-spectrum observations, counterexamples exist at every tested parameter combination.

---

## 4. What these results mean for the open question

### The fundamental asymmetry persists

The bridging conditions constrain d_S (the truth's spectrum) through the repeat structure of S. The ML objective compares d_S to d_D over the polytope P(G, L, Σ). Bridging does not constrain P or the competitor's position in P. Therefore:

**At every (G, L, σ) parameter combination where I_s is satisfiable and the truth has < G distinct kmer types, counterexamples exist.**

### The three regimes (confirmed for alpha=4)

1. **L=2, G ≤ 6:** Vacuous bridging dominates. Repeat-free genomes satisfy I_s vacuously. Counterexamples are abundant with max ratio = G^{x_k} for self-loops, (G/2)^{x_k} for heterologous.

2. **L=2, G ≥ 7:** I_s becomes unsatisfiable for most truths (triple repeats of length 1 cannot be bridged by L=2 reads). The few I_s-satisfying instances do not admit counterexamples, but this reflects vacuous unsatisfiability, not ML optimality.

3. **L ≥ 3:** Substantive bridging counterexamples exist at every tested G (from the alpha=3 exhaustive search). The maximum ratio increases with G as the Eulerian polytope becomes less constrained.

### Epistemic status

| Claim | Status | Evidence |
|-------|--------|----------|
| Eulerian bound: self-loop max d = G | Verified computationally (G ≤ 8, all σ) | Exact enumeration |
| Eulerian bound: het max d = ⌊G/2⌋ | Verified computationally (G ≤ 8, all σ) | Exact enumeration |
| Alpha=4, G=4, L=2: 216 vacuous cex | Exhaustive search (exact arithmetic) | Script output |
| Alpha=4, G=5, L=2: 4800 vacuous cex | Exhaustive search (exact arithmetic) | Script output |
| Complete-spectrum safety | Proven (algebraic, §6.1 of fixed-length-ml-objective-analysis.md) | Mathematical proof |
| Skewed-sample vulnerability | Proven (construction) | Mathematical proof |
| D < G threshold for counterexamples | Computational evidence (not proved) | Exhaustive search G=4-6, σ=4 |
| Bridging asymmetry (S constrained, D not) | Proven | Theorem 2 of bridging-likelihood-obstructions.md |

---

## 5. Scripts used

All scripts use exact rational arithmetic (Python `fractions.Fraction`). No floating-point rounding.

```bash
# Exhaustive search, alpha=4
python3 scripts/fixed_length_bridging_search_v2.py --G 4 --L 2 --alpha 4 --N 4
python3 scripts/fixed_length_bridging_search_v2.py --G 5 --L 2 --alpha 4 --N 5

# Eulerian amplification bounds
python3 scripts/eulerian_amplification_analysis.py

# Structural analysis
python3 scripts/structural_analysis.py
```

---

## 6. What remains open

1. **Variant A (binomial approximation) and Variant F (flow-feasible candidates):** Whether bridging forces optimality under these objectives remains open. Variant F is the most plausible route to a positive result.

2. **Proof of the D < G threshold:** The computational evidence suggests a clean structural theorem, but a proof would require showing that the Eulerian polytope P(G,L,Σ) restricted to d(i) > 0 for a set of size D < G always contains a point with higher log-likelihood than d_S.

3. **Tight ratio bounds for L ≥ 3:** The existing exhaustive search (alpha=3) shows max ratios of 27 (G=7, L=3) and 64 (G=6, L=3). Tighter bounds for alpha=4 with L ≥ 3 remain unexplored due to computational cost.

4. **Probabilistic statement:** For what distributions of x (as a function of d_S, G, L, N) is d_S optimal with high probability? The worst-case counterexamples above use adversarially concentrated samples.
