# Issue #266: Conditional identifiability from the Not-So-Greedy information-feasibility guarantee

_Status: 2026-10-12. Mathematical formalization front. Source-faithful read-string model. This document provides a readable theorem/proof/caveat that #265 can incorporate._

## Epistemic status

- **External premise (source fact, not proved here):** The Not-So-Greedy theorem/corollary of Shomorony et al. (2016) guarantees that under the information-feasibility condition $I_s$, a deterministic read-only reconstruction $A(r)$ recovers the true circular genome up to cyclic shift. This is a cited external result, not formalized in this repository.
- **Mathematical proof (this document):** All five derivations below — fibre uniqueness, conditional posterior, constrained MAP, Bayes accuracy, and the decoder interface — are proved rigorously from the external premise plus standard probability theory. No new biological or combinatorial conjecture is introduced.
- **Trust boundary:** The external premise is used as a black box. If the source theorem requires extra input (e.g., genome length $G$ as an external parameter, or a stronger read model), this is stated explicitly in the hypotheses. If the source theorem only constructs a unique graph Eulerian cycle rather than an algorithm returning a sequence, the exact derived decoder interface is stated and verified.

## 1. Setup and notation

### 1.1 The source-faithful observation model

We work in the exact source-faithful finite-read model of Shomorony et al. (2016), supplement §6.4. The key definitions, already formalized in `AssemblyP1/HistoricalCovers.lean`:

- **Genome:** A circular word $S$ of length $G$ over a finite alphabet $\Sigma$. The candidate universe is the set $\mathcal{G}$ of all circular words of length $G$ (or a specified subclass; see §5).
- **Read length:** $L$ with $2 \le L \le G$.
- **Read realization:** A multiset $R$ of start positions in $\{0, \dots, G-1\}$. The observed read *strings* are the length-$L$ windows $W_t(S)$ for $t \in R$.
- **Observed read-string set:** $\mathcal{W}(R, S) = \{W_t(S) : t \in R\}$, the set of distinct observed read strings.
- **Match starts:** $\mathrm{MatchStarts}(S, L, \mathcal{W}) = \{t : W_t(S) \in \mathcal{W}\}$, the saturated set of positions at which some observed read string matches.

### 1.2 The information-feasibility predicate

The historical information-feasibility predicate $I_s^{\mathrm{match}}$ (Definition 1 of §6.4, formalized as `HistoricalInformationFeasibleLiteral` in Lean) requires:

1. **Historical coverage:** For every position $t$, there exists $\delta \in \{0, \dots, L-2\}$ such that $W_{(t+\delta) \bmod G}(S) \in \mathcal{W}$.
2. **Literal triple-repeat bridging:** Every three-occurrence repeat of $S$ is all-bridged (every copy is strictly straddled by some observed read string matched at a position in the source's straddling interval).
3. **Interleaved-pair bridging:** Every interleaved pair of maximal repeats is bridged.

We define the feasibility predicate:

$$F(g, r) := \text{"} r \in I_g^{\mathrm{match}} \text{"}$$

where $r$ is a read realization (multiset of start positions) and $g$ is a candidate genome. This is the source-faithful read-string predicate, NOT the alternative latent-start coverage proxy.

### 1.3 The reconstruction map

Let $A(r)$ denote the deterministic read-only genome reconstruction supplied by the original Not-So-Greedy theorem/corollary, under all its exact hypotheses. The published guarantee is:

$$\forall g, r: \quad F(g, r) \implies A(r) \approx g$$

where $\approx$ denotes cyclic-shift equivalence (the natural genome equivalence for oriented reads on a circular genome).

### 1.4 What we prove

We derive five consequences of the published guarantee:

1. **Fibre uniqueness** (§2): $\forall g, h, r: F(g,r) \wedge F(h,r) \implies g \approx h$
2. **Conditional posterior** (§3): $P([G] = [A(r)] \mid R = r, E) = 1$ for positive-probability $r, E$
3. **Constrained MAP** (§4): The constrained joint-posterior MAP recovers the unique feasible rotation class on $E$
4. **Bayes accuracy** (§5): Zero-one-loss conditional Bayes accuracy reaches 100% on $E$
5. **Decoder interface** (§6): Exact statement of the derived decoder

## 2. Theorem 1 (Feasible-fibre uniqueness)

**Statement.** Fix the candidate universe $\mathcal{G}$, genome length $G$, read length $L$, orientation convention, and the observation $r$ drawn from the source-faithful read-string model. Let $F(g,r) := (r \in I_g^{\mathrm{match}})$. Let $A(r)$ be the deterministic reconstruction under the Not-So-Greedy guarantee. Then:

$$\forall g, h \in \mathcal{G}, \forall r: \quad F(g, r) \wedge F(h, r) \implies g \approx h$$

**Proof.** By the published guarantee $\forall g, r: F(g,r) \implies A(r) \approx g$:

- From $F(g, r)$: $A(r) \approx g$.
- From $F(h, r)$: $A(r) \approx h$.
- By transitivity of $\approx$: $g \approx h$. $\square$

**Interpretation.** This is uniqueness of the *feasible fibre* given a fixed observed $r$. It says: among all candidate genomes $g$ that could have produced the observation $r$ under the information-feasibility condition, all are cyclic shifts of each other. This is NOT a claim about unique maximum-likelihood estimation over all candidates. The feasible fibre is the set $\{g : F(g, r)\}$; the theorem says this fibre contains exactly one rotation class.

**Distinction from unique ML.** Unique ML over all candidates would say: $\arg\max_g P_g(r) = \{g : g \approx S\}$ (the truth is the unique maximizer). Feasible-fibre uniqueness says something different: the set of candidates *consistent with the feasibility condition* is a single rotation class. These are logically independent statements:
- Feasible-fibre uniqueness does NOT imply unique ML (a candidate outside the fibre could have higher likelihood).
- Unique ML does NOT imply feasible-fibre uniqueness (the ML maximizer could be unique while other feasible candidates exist).

## 3. Theorem 2 (Conditional posterior)

**Statement.** Let $\pi$ be any prior distribution on $\mathcal{G}$ with positive mass on the true genome $S$ (i.e., $\pi(S) > 0$). Let $P_g(r)$ be any valid generative finite-read likelihood: the probability of observing read realization $r$ given that the true genome is $g$. Under the joint law of $(G, R)$ where $G \sim \pi$ and $R \mid G = g \sim P_g$, define the event:

$$E := F(G, R)$$

Then for any observation $r$ with $P(R = r, E) > 0$:

$$P([G] = [A(r)] \mid R = r, E) = 1$$

where $[g]$ denotes the cyclic-rotation equivalence class of $g$.

**Proof.** We compute the conditional probability directly:

$$P([G] = [A(r)] \mid R = r, E) = \frac{P([G] = [A(r)], R = r, E)}{P(R = r, E)}$$

The denominator is positive by hypothesis. For the numerator:

$$P([G] = [A(r)], R = r, E) = \sum_{g \in [A(r)]} \pi(g) P_g(r) \cdot \mathbf{1}_{F(g, r)}$$

By the published guarantee, $F(g, r) \implies A(r) \approx g$, i.e., $g \in [A(r)]$. So for any $g \in [A(r)]$, if $F(g, r)$ holds then $g \in [A(r)]$ (tautologically). Thus:

$$P([G] = [A(r)], R = r, E) = \sum_{g \in [A(r)]} \pi(g) P_g(r) \cdot \mathbf{1}_{F(g, r)}$$

The denominator:

$$P(R = r, E) = \sum_{g \in \mathcal{G}} \pi(g) P_g(r) \cdot \mathbf{1}_{F(g, r)}$$

By Theorem 1 (fibre uniqueness), if $F(g, r)$ and $F(h, r)$ both hold, then $g \approx h$. Since $A(r) \approx g$ for all $g$ with $F(g, r)$, all such $g$ are in $[A(r)]$. Therefore:

$$P(R = r, E) = \sum_{g \in [A(r)]} \pi(g) P_g(r) \cdot \mathbf{1}_{F(g, r)} = P([G] = [A(r)], R = r, E)$$

Hence the ratio is 1. $\square$

**Critical caveat.** This is conditioned on the *additional, truth-dependent event* $E = F(G, R)$, NOT merely on $R = r$. The event $E$ depends on the true genome $G$ through the feasibility predicate. Without conditioning on $E$, the posterior $P([G] = [A(r)] \mid R = r)$ can be strictly less than 1: there may be candidates $h \notin [A(r)]$ with $P_h(r) > 0$ that produced the same observation but violate the feasibility condition. The event $E$ is a *filter* that removes all candidates except those in the feasible fibre, and by Theorem 1 the feasible fibre is a single rotation class.

**What this does NOT say.** This does NOT say that ordinary (unconditioned) maximum-likelihood estimation always recovers truth. The conditional posterior equals 1 only after conditioning on $E$. Without the $E$ filter, the posterior may assign positive mass to wrong genomes.

## 4. Theorem 3 (Constrained MAP)

**Statement.** Under the same setup as Theorem 2, consider the constrained joint-posterior MAP estimator:

$$\hat{g}_{\mathrm{MAP}}(r) := \arg\max_{g \in \mathcal{G}} \; \pi(g) \cdot P_g(r) \cdot \mathbf{1}_{F(g, r)}$$

Then on the event $E$ (i.e., when the true genome $G$ satisfies $F(G, R)$), with probability 1:

$$\hat{g}_{\mathrm{MAP}}(r) \in [A(r)]$$

That is, the constrained MAP recovers the unique feasible rotation class.

**Proof.** The constrained objective is:

$$J(g, r) = \pi(g) \cdot P_g(r) \cdot \mathbf{1}_{F(g, r)}$$

For any $g$ with $F(g, r) = \mathrm{false}$, $J(g, r) = 0$. For any $g$ with $F(g, r) = \mathrm{true}$, $J(g, r) = \pi(g) \cdot P_g(r) > 0$ (since $\pi(g) > 0$ for all $g$ in the support of the prior, and $P_g(r) > 0$ for $r$ with positive probability).

By Theorem 1, all $g$ with $F(g, r) = \mathrm{true}$ are in $[A(r)]$. Therefore the argmax is over a subset of $[A(r)]$, and any maximizer is in $[A(r)]$. $\square$

**Distinction from ordinary MAP.** The ordinary (unconstrained) MAP:

$$\hat{g}_{\mathrm{ordinary}}(r) := \arg\max_{g \in \mathcal{G}} \; \pi(g) \cdot P_g(r)$$

can select a candidate outside $[A(r)]$, because the constraint $\mathbf{1}_{F(g, r)}$ is removed. The constraint is essential: it restricts the search to the feasible fibre, which by Theorem 1 is a single rotation class.

**Distinction from naive conditioning on $F$.** A naive approach might condition on $F$ by computing $P_g(r \mid F(g, r))$ and then applying a uniform prior. This is different from the constrained MAP above:
- The constrained MAP uses the *joint* objective $\pi(g) P_g(r) \mathbf{1}_{F(g, r)}$, which is the posterior restricted to the fibre.
- The naive approach computes the *conditional* likelihood $P_g(r \mid F(g, r))$, which requires computing $P_g(F)$, the probability that genome $g$ produces a feasible observation. This is a different quantity and generally does not recover the same answer.

The constrained MAP is the correct procedure because it directly restricts the posterior to the feasible set, which is exactly the set of candidates consistent with the feasibility condition.

## 5. Theorem 4 (Bayes accuracy)

**Statement.** Under the same setup, define the zero-one loss for genome reconstruction:

$$\ell(\hat{g}, g) = \mathbf{1}_{[\hat{g}] \neq [g]}$$

The conditional Bayes accuracy of any decision rule $\delta(r, E)$ (which may use the observation $r$ and the knowledge that $E$ occurred) is:

$$\mathrm{Acc}(\delta) = P(\ell(\delta(R, E), G) = 0 \mid E)$$

The optimal decision rule is the conditional Bayes rule:

$$\delta^*(r) = [A(r)]$$

which achieves:

$$\mathrm{Acc}(\delta^*) = 1$$

No other rule can exceed this accuracy (since 1 is the maximum possible).

**Proof.** By Theorem 2, $P([G] = [A(r)] \mid R = r, E) = 1$ for all $r$ with $P(R = r, E) > 0$. Therefore:

$$\mathrm{Acc}(\delta^*) = P([G] = [A(R)] \mid E) = \sum_{r : P(R=r, E) > 0} P(R = r \mid E) \cdot P([G] = [A(r)] \mid R = r, E) = \sum_{r} P(R = r \mid E) \cdot 1 = 1$$

For any other rule $\delta$:

$$\mathrm{Acc}(\delta) = P([\delta(R, E)] = [G] \mid E) \le 1$$

with equality if and only if $\delta(r, E) \in [G]$ for almost all $(r, E)$. By Theorem 1, $\delta(r, E) \in [A(r)]$ is necessary for equality. $\square$

**This is immediate given uniqueness.** The 100% Bayes accuracy is a direct consequence of fibre uniqueness (Theorem 1). It is NOT a stronger finite-ML conjecture, and it does NOT replace the independent population/P2 theorem. It is a statement about the *conditional* distribution given $E$, not about the unconditional distribution.

**No unconditional guarantee.** Without conditioning on $E$, the Bayes accuracy can be strictly less than 1. The event $E$ is essential: it is the filter that removes all non-feasible candidates, leaving only the true rotation class.

## 6. Theorem 5 (Decoder interface and hypotheses)

**Statement.** The exact decoder interface depends on the form of the Not-So-Greedy theorem:

**Case A: The source theorem returns a sequence.** If the Not-So-Greedy theorem/corollary provides an algorithm $\mathcal{A}$ that maps the observed read realization $r$ to a circular genome $\mathcal{A}(r)$, then the derived decoder is:

$$\mathrm{Decode}(r) = \mathcal{A}(r)$$

with the guarantee that $F(g, r) \implies \mathcal{A}(r) \approx g$.

**Case B: The source theorem constructs a unique graph Eulerian cycle.** If the source theorem only proves that a certain graph $X_r$ (constructed from the observed reads) has a unique Eulerian cycle spelling the true genome, then the derived decoder requires an additional step:

1. Construct the graph $X_r$ from the observed reads (the exact construction depends on the source's definitions; for the §6.2 model, this is the read-overlap graph).
2. Find the Eulerian cycle in $X_r$ (e.g., using Hierholzer's algorithm).
3. Spell the genome from the Eulerian cycle.

The decoder is then:

$$\mathrm{Decode}(r) = \mathrm{Spell}(\mathrm{EulerianCycle}(X_r))$$

**Verification of the decoder interface.** The key requirement is that the Eulerian cycle is *unique* up to cyclic shift. If the source theorem proves uniqueness of the Eulerian cycle in the graph, then the decoder is well-defined. If the source theorem only proves existence, the decoder requires a tie-breaking rule, and the uniqueness guarantee is lost.

**Hypotheses inherited from the source theorem.** The following hypotheses must be verified against the source:

1. **Genome length $G$:** Is $G$ assumed known (external parameter) or intrinsic to the reconstruction? If external, the decoder requires $G$ as input.
2. **Read model:** Is the read model exactly the source-faithful read-string model of §6.4, or does the source theorem assume a stronger model (e.g., placement-based coverage)?
3. **Orientation:** Are reads oriented (single strand) or reverse-complement collapsed? The oriented model forces only cyclic-shift equivalence; the RC-collapsed model forces dihedral equivalence.
4. **Error model:** Are reads error-free? The source assumes error-free reads.
5. **Finite vs. infinite:** Is the theorem stated for a finite sample (finite number of reads) or in the population limit?

## 7. Summary of trust boundaries

| Component | Status | Source |
|-----------|--------|--------|
| Not-So-Greedy guarantee $\forall g, r: F(g,r) \implies A(r) \approx g$ | External premise | Shomorony et al. (2016), cited |
| Fibre uniqueness (Theorem 1) | Proved here | From external premise |
| Conditional posterior (Theorem 2) | Proved here | From Theorem 1 + probability theory |
| Constrained MAP (Theorem 3) | Proved here | From Theorem 1 + optimization |
| Bayes accuracy (Theorem 4) | Proved here | From Theorem 2 |
| Decoder interface (Theorem 5) | Stated here | Depends on source theorem form |

## 8. Caveats for #265

1. **This is NOT a claim that ordinary ML always recovers truth.** The conditional posterior equals 1 only after conditioning on $E = F(G, R)$. Without this conditioning, the posterior can assign positive mass to wrong genomes.

2. **This is NOT a stronger finite-ML conjecture.** The 100% Bayes accuracy is a direct consequence of fibre uniqueness, not a new conjecture about ML estimation.

3. **This does NOT replace the population/P2 theorem.** The population theorem (Theorem 5.1 of the paper) establishes uniqueness of the population ML maximizer for primitive P2 genomes. The conditional identifiability result here is a different statement about the *finite-sample* conditional distribution given the feasibility event.

4. **The event $E$ is truth-dependent.** The conditioning event $E = F(G, R)$ depends on the true genome $G$. This is not a property of the observation $R$ alone; it is a joint property of $(G, R)$. This is why the result is "conditional identifiability" rather than "unconditional identifiability."

5. **The feasible-fibre uniqueness is NOT unique ML.** The feasible fibre $\{g : F(g, r)\}$ is a single rotation class, but this does not mean that the ML maximizer is unique or correct. A candidate outside the fibre could have higher likelihood.

6. **The source-faithful read-string model is essential.** The result is stated for the historical $I_s^{\mathrm{match}}$ predicate of §6.4, not the placement-based proxy. The two are incomparable (Proposition 4.2 of the paper).

7. **The decoder interface must be verified against the source.** If the source theorem only constructs a unique graph Eulerian cycle, the decoder requires an explicit algorithm to extract the sequence from the cycle. This is stated in Case B of Theorem 5.
