# ML ambiguity audit: exact findings from primary sources

_Status: resolved source note, 2026-09-18. Settles the factual question of what each primary source actually defines. Does not settle the open problem itself._

## Scope

Audit the primary genome-assembly sources underlying `ottojung/assemblyp1`—specifically Shomorony et al. (2016) and Medvedev–Brudno (2009)—to determine exactly which maximum-likelihood objective and candidate-genome length convention the published open problem refers to. Distinguish exact multinomial ML from approximations and flow. All claims below cite exact sections, equations, or passages.

---

## 1. Shomorony et al. (2016) — what the open question actually says

**Paper:** Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse, "Information-optimal genome assembly via sparse read-overlap graphs," *Bioinformatics* 32(17), 2016, i494–i502. DOI: [10.1093/bioinformatics/btw450](https://doi.org/10.1093/bioinformatics/btw450).

### The open-question sentence

Section 5 (Discussion), final paragraph:

> "Understanding whether bridging conditions can be used to guarantee that **the maximum-likelihood sequence is the true sequence** is currently an open question."

### What Shomorony et al. say *before* that sentence

Section 5 first says that Theorem 1 (their bridging theorem) reconstructs the true sequence but does not guarantee that this sequence solves an optimization-based assembly formulation. It cites Nagarajan–Pop (2009) and **Medvedev–Brudno (2009)** as examples of such formulations. It then contrasts parsimony-based formulations (which can over-collapse repeats) with "the maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009)."

### What Shomorony et al. do *not* say

The 2016 paper does **not**, in the open-question passage or anywhere else in the main text:

1. Reproduce the Medvedev–Brudno multinomial likelihood formula.
2. Mention the binomial/separable approximation.
3. Mention the Section 6.2 overlap-graph flow feasible set.
4. State that candidate genome length is fixed to the true length G.
5. State a candidate-genome universe for the ML comparison.
6. Provide a theorem/equation/section pointer inside Medvedev–Brudno that selects one of those objects.

### Author-hosted version (23-page manuscript)

Available at <https://web.stanford.edu/~gkamath/nsgIlan.pdf>. Its first two pages give more historical context than the accepted Introduction but still do not write the likelihood formula, identify exact versus approximate likelihood, fix a candidate-genome class, or say that all competitors have the true genome length. The appended Supplementary Material (beginning at PDF p. 18) develops the Not-So-Greedy implementation/proofs and the Bresler et al. bridging conditions but does not define the Medvedev–Brudno optimization target.

### Conclusion for Shomorony et al.

**Source ambiguity confirmed.** The phrase "the maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009)" is a bare bibliographic reference. It does not select among the three materially different ML objects defined in the Medvedev–Brudno paper (see §2 below).

---

## 2. Medvedev & Brudno (2009) — the three distinct ML objects

**Paper:** Paul Medvedev and Michael Brudno, "Maximum Likelihood Genome Assembly," *Journal of Computational Biology* 16(8), 2009, 1101–1116. DOI: [10.1089/cmb.2009.0047](https://doi.org/10.1089/cmb.2009.0047). Open full text: [PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/).

### Object 1: Exact global read-count likelihood (Section 6.1)

**Section 6.1, "Maximizing the global read-count likelihood"** defines:

- **D** = a circular genome of length **N(D)** (candidate-dependent length).
- **d_i** = number of times k-molecule type *i* appears in D.
- **n** = total number of sampled reads; **x_i** = observed count of type *i*.

The sampling model: in each of *n* independent trials, a position is uniformly sampled from D; the outcome is the k-molecule beginning at that position. The probability of type *i* in a single trial is **d_i / N(D)**.

The joint distribution is **exactly multinomial** (equation in Section 6.1):

> P(X_1=x_1, …, X_{4^k}=x_{4^k}) = n! / (∏_i x_i!) · ∏_i (d_i / N(D))^{x_i}

The likelihood of parameters (d_i) given observed counts (x_i) is the **global read-count likelihood**:

> **L_exact(D | x) = n! / (∏_i x_i!) · ∏_i (d_i / N(D))^{x_i}**

**Key fact:** The candidate's own length N(D) appears in every denominator. The paper states: "we attempt to assemble the genome with the maximum global read-count likelihood." No restriction to fixed candidate length is imposed at this point.

### Object 2: Binomial/separable approximation (Section 6.1, second half)

Still in Section 6.1, the authors explain that the exact multinomial objective is **not separable** in the d_i variables (because of the constraint Σ_i d_i = N(D)), which prevents direct use of convex-cost flow. They then write:

> "However, as the number of trials goes to infinity, the X_i random variables become independent. Because the number of trials (sampled k-molecules) is typically large, we can approximate the multinomial distribution as the product of the individual binomial distributions of each X_i."

At this point they **replace N(D) by N**, the length of the actual genome:

> "Since in the binomial approximation the length of the genome N(D) is a constant that is independent of each d_i, we can replace it by N, which is the length of the actual genome from which the reads were sampled. The approximate length of the actual genome can be ascertained through one of a number of biological experiments, or through an Expectation-Maximization type approach. For our experiments, we assume that the genome size is known."

The resulting approximate likelihood is:

> **L_approx(D | x) ∝ ∏_i (d_i / N)^{x_i}**

where N is a **fixed external constant** (the true or estimated genome length), not the candidate's own length.

**Key fact:** This approximation is a **different mathematical object** from the exact multinomial. The length semantics change: candidate-dependent N(D) → fixed external N.

### Object 3: Section 6.2 overlap-graph flow optimization

Section 6.2 ("Putting it all together") constructs a transitively reduced bidirected overlap graph from the observed reads. Each read vertex has a lower bound of 1 (every observed read must be represented). The flow encodes read copy counts. The feasible objects are **flows in this specific graph** with explicit lower bounds, not arbitrary circular genomes.

**Key fact:** The feasible set searched by the algorithm is a constrained subset of all possible genomes. A result about feasible flows is not automatically a result about all circular candidate genomes.

---

## 3. Exact multinomial vs. approximation vs. flow — precise distinction

| Property | Object 1 (exact multinomial) | Object 2 (binomial approx.) | Object 3 (flow optimization) |
|---|---|---|---|
| **Section** | 6.1 (first half) | 6.1 (second half) | 6.2 |
| **Likelihood formula** | Multinomial with d_i/N(D) | Product of binomials with d_i/N | Depends on flow decomposition |
| **Candidate length** | N(D) — candidate's own | N — fixed external constant | Implicit in graph construction |
| **Search space** | All circular genomes D | All circular genomes D | Feasible flows in overlap graph |
| **Separable in d_i?** | No (Σ d_i = N(D) constraint) | Yes | N/A (flow constraints) |
| **Used for algorithm?** | No (intractable) | Yes (convex-cost flow) | Yes (bidirected network flow) |

---

## 4. What the open problem *can* refer to — and what it *cannot*

Given the primary-source evidence:

### What is settled

1. **Shomorony et al. cite Medvedev–Brudno by name** but provide no formula, equation, section number, or disambiguation among the three objects.

2. **Medvedev–Brudno define the exact multinomial likelihood** with candidate-dependent N(D) in Section 6.1 as the primary statistical objective. The binomial approximation and flow algorithm are presented as computational aids, not as redefinitions of the statistical goal.

3. **The binomial approximation is explicitly introduced as an approximation**, not as the exact likelihood. Medvedev–Brudno say "we can approximate the multinomial distribution as the product of the individual binomial distributions." The word "approximate" signals a departure from the exact objective.

4. **The flow feasible set is an algorithmic search space**, not the universe of all circular genomes.

### What remains genuinely ambiguous

1. **Which ML object Shomorony et al. intend** by "the maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009)":
   - The **strongest textual reading** favors Object 1 (exact multinomial), since that is the primary statistical objective that Medvedev–Brudno introduce and name. The approximation and flow are presented as means to compute it.
   - However, Shomorony et al. provide **no evidence** that they distinguished the three objects. The bare citation is compatible with any of them.

2. **Whether "the maximum-likelihood sequence is the true sequence"** means:
   - **(a) truth is a maximizer**: L_exact(truth) ≥ L_exact(D) for all admissible D, or
   - **(b) uniqueness up to equivalence**: truth is the *unique* maximizer (up to cyclic shift or other genome equivalence).

   The English singular "the maximum-likelihood sequence" most naturally suggests uniqueness (reading (b)), but this is not a mathematical definition and could be informal prose for (a).

3. **Whether candidates must have length G** (the true genome length):
   - The exact multinomial (Object 1) does **not** require this; candidates of any length contribute their own N(D).
   - The binomial approximation (Object 2) **does** fix length to external N.
   - The flow algorithm (Object 3) implicitly constrains length via the graph.
   - Shomorony et al.'s Section 2 fixes the true sequence to length G for their sampling model but does not say that ML competitors must also have length G.

---

## 5. Formalization consequence

The repository should continue to preserve three explicitly named ML variants:

1. **Variant E (exact multinomial):** Candidate D contributes its own N(D). No fixed competitor length. This is the primary statistical objective defined in Medvedev–Brudno Section 6.1.

2. **Variant A (binomial approximation):** Length fixed to external constant N. This is explicitly an approximation introduced for computational tractability.

3. **Variant F (flow optimization):** Feasible flows in the read-derived overlap graph. This is an algorithmic search space, not interchangeable with either likelihood definition without a correspondence theorem.

Any eventual settlement of the open problem must:
- State which variant it proves;
- Justify why that variant corresponds to the 2016 question (via the bare citation or additional analysis);
- State whether the conclusion is maximizer-only or uniqueness-up-to-equivalence.

---

## 6. Summary of the audit

| Question | Answer | Primary source |
|---|---|---|
| Does Shomorony et al. reproduce the ML formula? | No | Section 5, full text |
| Does Shomorony et al. fix candidate length? | No | Section 2 (fixes true-sequence length only) |
| Does Shomorony et al. distinguish exact vs. approx. ML? | No | Full text search |
| What is the exact ML objective in Medvedev–Brudno? | Multinomial with d_i/N(D) | Section 6.1, equation |
| What is the approximation? | Binomial with d_i/N (fixed N) | Section 6.1, second half |
| What is the flow optimization? | Feasible flows in overlap graph | Section 6.2 |
| Are the three objects mathematically equivalent? | No | Different search spaces, different objectives |
| Is the ambiguity resolved? | **No** — source ambiguity remains | This note |
