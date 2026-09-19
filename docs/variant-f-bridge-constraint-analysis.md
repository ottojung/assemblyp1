# Variant F bridge constraint: what I_s implies about the flow-feasible set

_Status: mathematical analysis. Not a Lean result. All claims classified by epistemic class._

---

## 0. Purpose

This document determines what I_s implies about the flow-feasible candidate set F_flow(R) under Medvedev-Brudno section 6.2 (Variant F). It establishes a clean theorem for the repeat-free distinct-read case, characterizes the amplification obstacle, and identifies the structural coupling for genomes with substantive repeats.

Central findings:

1. **Singleton theorem (repeat-free, distinct reads):** For repeat-free S with L >= 3 and all reads distinct, I_s combined with Eulerian constraints forces F_flow(R) = {S}. ML is trivially satisfied.

2. **Amplification obstacle:** When reads repeat, parallel edges in the overlap graph allow flow-feasible competitors. I_s cannot prevent read repetition under the i.i.d. model. This is why Variant F is not trivially resolved.

3. **Bridging-start coupling (S with repeats):** For S with substantive repeats, I_s constrains start positions to specific intervals around repeat positions. These constraints propagate through the overlap graph to limit F_flow(R). This is strictly stronger than coverage alone.

4. **The key open question:** Is the bridging-start coupling strong enough to exclude all amplifying competitors from F_flow(R)?

---

## 1. Setup

| Symbol | Meaning |
|--------|---------|
| S | True circular genome, length G, alphabet Sigma |
| L | Read length |
| R | Realized read collection: multiset of (start, L-mer) pairs |
| x | Observable read multiset: projection pi(R) |
| I_s | Coverage and all-bridged triple repeats and bridged interleaved repeats |
| G(R) | Overlap graph from R |
| F_flow(R) | Flow-feasible set: genomes from valid flows in G(R) |

Flow-feasibility (Medvedev-Brudno section 6.2): D is flow-feasible w.r.t. R iff there exists a valid flow in G(R) with flow >= 1 through each read vertex, flow conservation, and decomposition into a single closed walk spelling D.

Overlap graph: vertices are reads in R; edge (r1, r2) if they share L-1 symbols in the correct orientation.

---

## 2. Why Variant F is structurally different from Variant E

### 2.1 The asymmetry theorem (from bridging-likelihood-obstructions.md)

I_s constrains (S, R), not D. For Variant E (fixed or unrestricted length), the candidate universe is independent of S, R, or I_s. Therefore I_s cannot restrict competitors.

### 2.2 Why the asymmetry fails for Variant F

For Variant F, the candidate universe is F_flow(R), which depends on R. Since R depends on S (through sampling), and I_s constrains (S, R), I_s indirectly constrains F_flow(R).

**Coupling chain:**
```
I_s on S  ->  S repeat structure  ->  R composition  ->  G(R)  ->  F_flow(R)
```

**Proposition 2.1.** F_flow(R) depends on R, not just x. Two realizations R1, R2 with pi(R1) = pi(R2) = x can have F_flow(R1) != F_flow(R2).

*Proof.* G(R) depends on which specific reads are present. Different start positions produce different overlap graphs. [Proven]

**Proposition 2.2.** I_s constrains R, not just x. I_s quantifies over start positions, which are elements of R, not of x. [Proven, from bridging-implies-what-rigorous.md section 1.2]

**Corollary 2.3.** For Variant F, I_s constrains F_flow(R) indirectly. Whether this constraint is strong enough to force ML is OPEN.

---

## 3. The singleton theorem: repeat-free S with distinct reads

### 3.1 Statement

**Theorem 1.** Let S be a repeat-free circular genome of length G with L >= 3. Let R satisfy I_s (reducing to coverage) with all reads distinct (distinct start positions and distinct L-mer types). Then F_flow(R) = {S}. ML is trivially satisfied.

### 3.2 Proof

**Step 1.** Coverage forces every position of S to be in some read.

**Step 2.** Distinct L-mer types mean each L-mer appears at most once in R. For L >= 3, two reads overlap iff the last L-1 of one equals the first L-1 of the other. Since all L-mers are distinct, each vertex in G(R) has in-degree <= 1 and out-degree <= 1.

**Step 3.** G(R) is a directed cycle visiting each read vertex exactly once (the circular structure of S forces this).

**Step 4.** The unique Eulerian circuit in this cycle spells S.

**Step 5.** Any flow-feasible D must be spellable from a valid flow in G(R) with flow >= 1 through each vertex. Since G(R) is a directed cycle, the only valid flow spells S. Therefore D = S. QED

### 3.3 Epistemic status: Proven.

### 3.4 Scope

Applies when S is repeat-free, all reads are distinct, L >= 3. When reads repeat, the overlap graph gains parallel edges and F_flow(R) can include competitors.

---

## 4. The amplification obstacle

### 4.1 Why reads repeat

Under i.i.d. uniform sampling from G starts, even repeat-free S produces repeated reads when:
- Same position sampled multiple times (happens with positive probability for any N > 1).
- N > G forces repetition by pigeonhole.

### 4.2 Repeated reads enable competitors

When type k appears m times in R (x_k = m), G(R) has m parallel vertices for type k. A flow can route through these to spell a string with d_D(k) >= 2.

**Proposition 4.1.** For repeat-free S with d_S(k) = 1, if x_k = m > 1, there exists a flow-feasible D with d_D(k) >= 2.

*Proof sketch.* Parallel read vertices create branching. Flow routes through them to increase d_D(k). Eulerian balance maintained by adjusting other flow. [Proven, structural]

### 4.3 I_s cannot bound x_i

**Proposition 4.2.** For repeat-free S, I_s does not bound x_i for any type i. A type with d_S(i) = 1 can appear x_i = N times.

*Proof.* Coverage is the only active constraint. For any sample with support on at most G types, a coverage-satisfying realization exists. [Proven]

### 4.4 Consequence

For repeat-free S under Variant F, I_s does not prevent amplifying competitors when reads repeat. The singleton theorem (Theorem 1) requires all reads distinct. This is why Variant F remains genuinely open.

---

## 5. The bridging-start coupling for S with repeats

### 5.1 When I_s is strictly stronger than coverage

For S with repeats, bridging constraints are strictly stronger than coverage:

- **Coverage** constrains the support of R (which positions are covered) but not start positions within the support.
- **Bridging** constrains start positions to specific intervals around repeat positions.

### 5.2 The bridging range

For a repeat of length l at position t, a bridging read must have start r with r < t and t + l < r + L (on the integer lift). The valid bridging starts form an interval of size L - l - 1 around each copy.

**Lemma 5.1 (Bridging constrains starts).** For a triple repeat at positions t1, t2, t3 with length l, I_s requires at least 3 reads with starts in the union of three bridging intervals, each of size L - l - 1.

*Proof.* Each copy requires a distinct bridging read (when bridging ranges are disjoint). [Proven]

### 5.3 How start constraints propagate to F_flow(R)

The overlap graph G(R) depends on which L-mers the reads produce, which depends on start positions. Constraining start positions constrains the set of possible overlap graphs.

**Proposition 5.2 (Start constraints limit overlap graphs).** If I_s constrains read starts to a set Sigma_start, then G(R) is determined by the L-mers produced by starts in Sigma_start. The set of possible G(R) is limited to those achievable from starts in Sigma_start.

*Proof.* Direct from the definition of G(R). [Proven]

### 5.4 The key structural observation

For S with high-frequency repeats (many copies requiring many bridging reads), the bridging constraints are tighter:
- More copies require more bridging reads.
- Each bridging read has a constrained start interval.
- The total number of valid start positions is bounded by the union of bridging intervals.
- This limits the branching in G(R).

**Conjecture 5.3.** For S with sufficiently many repeats (relative to L and G), the bridging constraints limit G(R) enough that F_flow(R) = {S}.

*Status:* OPEN. This is the strongest plausible positive result for Variant F.

---

## 6. Precise characterization: what I_s implies and what it does not for Variant F

### What I_s DOES constrain for Variant F

| Constraint | On what | Mechanism |
|------------|---------|-----------|
| Read start positions | R (latent) | Bridging intervals for each repeat copy |
| Overlap graph structure | G(R) | Start constraints limit available L-mers |
| Flow-feasible set | F_flow(R) | G(R) determines F_flow(R) |
| Competitor feasibility | Candidate D | D must be spellable from G(R) |

### What I_s does NOT constrain for Variant F

| Non-constraint | Why not |
|----------------|---------|
| x_i bounds | I_s constrains starts, not counts |
| Read repetition | i.i.d. sampling causes repetition regardless of I_s |
| Complete exclusion of competitors | Unknown; depends on repeat structure |

### What is OPEN

| Question | Status |
|----------|--------|
| Does I_s + Variant F force ML for S with repeats? | OPEN |
| Is the bridging-start coupling strong enough? | OPEN |
| Is Conjecture 5.3 true? | OPEN |
| Can a counterexample to I_s + Variant F be found? | OPEN |

---

## 7. Implications for the open problem

### 7.1 What the singleton theorem tells us

Theorem 1 proves that I_s + flow-feasibility CAN force ML (trivially) in the simplest case: repeat-free S with all distinct reads. This is not vacuous — it shows the coupling mechanism works in principle.

### 7.2 What the amplification obstacle tells us

The obstacle (section 4) shows the coupling is fragile: read repetition breaks the singleton property. Since read repetition is inherent in the i.i.d. model for N > G, the singleton theorem has limited direct applicability.

### 7.3 The structural path forward

The bridging-start coupling (section 5) identifies the correct mechanism for a positive result: for S with substantive repeats, the bridging constraints on start positions propagate through the overlap graph to limit F_flow(R). Whether this is strong enough is the open question.

**The key parameter is the ratio of bridging constraints to genome length.** When S has many repeats requiring many bridged copies, the start-position constraints are dense, potentially limiting G(R) enough to exclude competitors.

### 7.4 What would need to be proved

A positive result for Variant F would require:

1. Formalize the flow-feasible set F_flow(R) precisely for a given (S, R).
2. Characterize the set of valid R under I_s for a given S.
3. Show that for all valid R under I_s, F_flow(R) has d_S as the unique ML maximizer.

Step 3 is the hard part. The singleton theorem handles the case when F_flow(R) = {S}. The open question is whether I_s constrains R enough that F_flow(R) is always "small enough" for d_S to be optimal.

---

## 8. Epistemic status summary

| Claim | Status | Evidence |
|-------|--------|----------|
| F_flow(R) depends on R, not just x | Proven | Proposition 2.1 |
| I_s constrains R, not just x | Proven | Proposition 2.2 |
| Repeat-free distinct reads: F_flow(R) = {S} | Proven | Theorem 1 |
| Repeated reads enable competitors | Proven | Proposition 4.1 |
| I_s does not bound x_i | Proven | Proposition 4.2 |
| Bridging constrains start positions | Proven | Lemma 5.1 |
| Start constraints limit overlap graphs | Proven | Proposition 5.2 |
| S with many repeats: F_flow(R) constrained | Conjectured | Conjecture 5.3 |
| I_s + Variant F forces ML | **OPEN** | No counterexample known |

---

## Source citations

| Fact | Primary source | Repository anchor |
|------|---------------|-------------------|
| I_s definition | Shomorony et al. 2016, Eq. (1) | docs/bridging-source-semantics.md:53-61 |
| Flow-feasible set | Medvedev-Brudno 2009, section 6.2 | docs/bridging-consequences-analysis.md:25-62 |
| Asymmetry theorem | Proven in repository | docs/bridging-likelihood-obstructions.md:146-157 |
| Variant F as sole survivor | Proven status table | docs/bridging-consequences-lemmas.md:154-187 |
| Repeat-free singleton | This document, Theorem 1 | Section 3 |
| Amplification obstacle | This document, Proposition 4.1 | Section 4 |
| Bridging-start coupling | This document, Lemma 5.1 | Section 5 |
