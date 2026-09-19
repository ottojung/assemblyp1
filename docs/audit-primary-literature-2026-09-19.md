# Independent Audit: Primary Literature vs Repository Definitions

_Status: independent audit, 2026-09-19. Read-only verification against independently fetched primary sources. No Lean edits._

## Scope

Independently audit the AssemblyP1 repository against the exact published genome-assembly maximum-likelihood open problem from the primary literature. Focus areas: candidate length assumptions, circularity, likelihood normalization/multinomial terms, coverage and bridging predicates. Compare precisely with current repository definitions. Preserve any material mismatch as durable notes.

## Primary Sources Independently Fetched and Verified

1. **Medvedev & Brudno (2009)** — "Maximum Likelihood Genome Assembly," *J. Computational Biology* 16(8), 1101–1116. PMC3154397. **Verified from PMC full text.**
2. **Shomorony et al. (2016)** — "Information-optimal genome assembly via sparse read-overlap graphs," *Bioinformatics* 32(17), i494–i502. DOI: 10.1093/bioinformatics/btw450. **DOI fetched; accepted-article text confirmed.**
3. **Bresler et al. (2013)** — "Optimal assembly for high throughput shotgun sequencing," *BMC Bioinformatics* 14(Suppl 5):S18. PMC3706340. **Verified from PMC full text.**

---

## 1. Candidate Length Assumptions

### Primary source (independently verified from PMC3154397)

Medvedev–Brudno §6.1:

> "Let D be a circular genome of length N(D), and let di denote the number of times the k-molecule i appears in D."

The exact multinomial likelihood uses candidate-dependent `N(D)` in every denominator. **No restriction to fixed candidate length is imposed at this point.** The binomial approximation (still §6.1, second half) explicitly replaces `N(D)` by `N`:

> "Since in the binomial approximation the length of the genome N(D) is a constant that is independent of each di, we can replace it by N, which is the length of the actual genome from which the reads were sampled."

### Repository state

- **`Model.lean:14`:** Abstract `Genome : Type` with no length constraint. Correctly preserves ambiguity.
- **`ExactVariantECounterexample.lean:63–65`:** `IsMaximumLikelihood` quantifies over all nonempty `List DNA` with no length restriction. Competitor `ACACGT` (length 6) beats truth `ACGT` (length 4).
- **`bridging-likelihood-obstructions.md`:** Fixed-length counterexample `AACAGG` vs `AAAGGC` (both length 6) with prose-verified exact rational arithmetic.

### Verdict: NO MISMATCH

The repository correctly preserves unrestricted-length exact multinomial as the source-faithful default, with fixed-length as a named alternative. The abstract `Model.lean` correctly does not bake in a candidate-length restriction.

### Sub-finding: Shomorony §2 does not constrain competitor length

Shomorony et al. §2 fix the true circular genome to length `G` for the data-generating model but **do not say** that ML competitors must also have length `G`. The phrase "the maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009)" is a bare bibliographic reference. Transferring `|D| = G` to every ML competitor would be an additional modeling decision not justified by the 2016 text. **Confirmed: no mismatch with repository's treatment.**

---

## 2. Circularity

### Primary source (independently verified)

- **Medvedev–Brudno §6.1:** "Let D be a circular genome of length N(D)." The sampling model says positions are uniformly sampled from D; since D is circular, there are exactly N(D) starting positions.
- **Shomorony et al. §2:** "We work with a circular sequence s of length G. A sequencing experiment produces N error-free reads of common length L; reads are drawn independently and uniformly from the G possible length-L substrings of s, with circular indexing."
- **Medvedev–Brudno §3.1:** Defines "k-circular" strings and molecules; the bidirected de Bruijn graph construction (§4.1) uses circular walks.

### Repository state

- **`ExactVariantECounterexample.lean:11–12`:** `base g i := g[i % g.length]!` implements circular indexing via modular arithmetic. The `dinucleotideCount` function iterates positions `0..g.length` and accesses `base g (i+1)`, which wraps via modulo.
- **`Model.lean:16`:** Abstract `genomeEquiv : Setoid Genome` with doc comment mentioning cyclic shifts.

### Verdict: NO MISMATCH

Modular indexing faithfully implements circular window access. The abstract model correctly defers circularity to instantiation.

### Risk: `genomeEquiv` not yet constrained

The `genomeEquiv` setoid is abstract. For a circular-genome instantiation, it must eventually identify cyclic shifts. The doc comment at `Model.lean:32` says this is "expected," but the setoid is not yet constrained. **Low severity** — correctly documented as deferred.

---

## 3. Likelihood Normalization / Multinomial Terms

### Primary source (independently verified from PMC3154397 §6.1)

Medvedev–Brudno define the exact global read-count likelihood:

- **Sampling model:** In each of n independent trials, a position is uniformly sampled from D; the outcome is the k-molecule beginning at that position.
- **Per-type probability:** `P(type i in single trial) = d_i / N(D)`
- **Joint distribution (exactly multinomial):**

  ```
  P(X_1=x_1, ..., X_{4^k}=x_{4^k}) = n! / (∏_i x_i!) · ∏_i (d_i / N(D))^{x_i}
  ```

- **Likelihood:** "For the assembly problem, D is not known but the results of the n trials are known. Thus, we can consider the likelihood of the parameters of the distribution (di) given the outcome of the trials (xi), which we call the global read-count likelihood."

The exact multinomial contains:
1. The multinomial coefficient `n! / (∏_i x_i!)` — observation-only, factors out of ML ordering.
2. The per-type probability `d_i / N(D)` — candidate-dependent.
3. The product `∏_i (d_i / N(D))^{x_i}` — the essential likelihood factor.

### Repository state

- **`ExactVariantECounterexample.lean:26–28`:**

  ```lean
  def sampleLikelihood (g : Genome) : ℚ :=
    3 * ((dinucleotideCount g .A .C : ℚ) / (g.length : ℚ)) ^ 2 *
      ((dinucleotideCount g .G .T : ℚ) / (g.length : ℚ))
  ```

  - Constant `3 = 3!/(2!·1!)` — correct multinomial coefficient for observation `{AC:2, GT:1}`.
  - Each read probability: `(occurrences in candidate) / (candidate length)` — correct.
  - Candidate-dependent denominator `N(D) = g.length` — correct for exact Variant E.

- **`ml-formalization-contract.md:55–57`:** Explicitly notes: "For maximum-likelihood ordering, the observation-only multinomial coefficient can be factored out by a proved lemma. It must not simply be deleted from a definition advertised as the exact probability without documenting that distinction."

### Independent numerical verification

```
Truth (ACGT, length 4): AC_count=1, GT_count=1
  L = 3 × (1/4)² × (1/4) = 3/64 = 0.046875

Competitor (ACACGT, length 6): AC_count=2, GT_count=1
  L = 3 × (2/6)² × (1/6) = 3 × (1/9) × (1/6) = 3/54 = 1/18 ≈ 0.055556

Ratio: (1/18)/(3/64) = 64/54 = 32/27 ≈ 1.1852
```

Kernel-checked: `truth_likelihood : sampleLikelihood truth = 3 / 64` ✓
Kernel-checked: `competitor_likelihood : sampleLikelihood competitor = 1 / 18` ✓
Kernel-checked: `competitor_beats_truth : sampleLikelihood truth < sampleLikelihood competitor` ✓

### Verdict: NO MISMATCH

The likelihood formula faithfully implements the exact multinomial from §6.1. The multinomial coefficient is correctly included (observation-only, cancels for ML ordering). The candidate-dependent denominator `N(D)` is correctly used.

---

## 4. Coverage

### Primary source (independently verified)

- **Shomorony et al. Eq. (1):** `R` covers `s` — every base of the circular sequence is read by at least one read.
- **Bresler et al. §Lower bounds:** Coverage analysis uses Lander-Waterman: "the number of reads NLW required to cover the entire DNA sequence with probability at least 1 − ε."
- **Coverage is a property of (S, R):** the true genome and the realized sequencing (latent start positions). It is not a property of the observable read multiset alone.

### Repository state

- **`ExactVariantECounterexample.lean:36,39–42`:**

  ```lean
  private def starts : List Nat := [0, 0, 2]
  private def covered : Prop :=
    (List.range truth.length).all (fun i =>
        starts.any (fun s =>
          (List.range 2).any (fun d => i == (s + d) % truth.length))) = true
  ```

  Latent starts `[0, 0, 2]` with read length 2:
  - Position 0: covered by read at start 0
  - Position 1: covered by read at start 0
  - Position 2: covered by read at start 2
  - Position 3: covered by read at start 2

  Kernel-checked: `truth_covered : covered` ✓

### Verdict: NO MISMATCH

Coverage is correctly verified using latent start positions. The separation between latent starts (for coverage/bridging) and observable counts (for likelihood) is correctly maintained.

---

## 5. Repeats and Bridging Predicates

### Primary source (independently verified from PMC3706340)

Bresler et al. define:

- **Repeat of length ℓ:** Two start positions `t₁, t₂` with equal length-ℓ windows, **maximal on both sides**: `s(t₁ - 1) ≠ s(t₂ - 1)` and `s(t₁ + ℓ) ≠ s(t₂ + ℓ)`. (Bresler et al., Results section, "We take a moment to carefully define the various types of repeats.")
- **Triple repeat of length ℓ:** Three start positions `t₁, t₂, t₃` with equal length-ℓ windows, and the three-copy maximality condition: neither `s(t₁ - 1) = s(t₂ - 1) = s(t₃ - 1)` nor `s(t₁ + ℓ) = s(t₂ + ℓ) = s(t₃ + ℓ)` holds. (Bresler et al., same paragraph.)
- **Note:** "a subsequence that is repeated f times gives rise to (2f choose 2) repeats and (3f choose 3) triple repeats." Triple repeat should not be modeled as "a substring whose total multiplicity is exactly three."
- **Bridging a copy:** "A subsequence s[t..t+ℓ] is bridged if and only if there exists at least one read which covers at least one base on both sides of the subsequence, i.e. the read arrives in the preceding length L−ℓ−1 interval." (Bresler et al., Figure 5 caption and preceding paragraph.)
- **Bridged repeat:** "For brevity, we will call a repeat or a triple repeat bridged if at least one copy of the repeat is bridged."
- **Bridged interleaved pair:** "a pair of interleaved repeats bridged if at least one of the repeats is bridged."
- **Interleaved repeats:** Two repeats (each with two copies), one at positions `t₁, t₃` with `t₁ < t₃` and the second at positions `t₂, t₄` with `t₂ < t₄`, interleaved if `t₁ < t₂ < t₃ < t₄` or `t₂ < t₁ < t₄ < t₃`.
- **MultiBridging (Theorem 6):** Sufficient conditions for reconstruction: (a) all interleaved repeats are bridged; (b) all triple repeats are all-bridged (every copy bridged); (c) the sequence is covered by the reads.

Shomorony et al. Eq. (1) uses exactly these conditions in `I_s`, explicitly attributing the repeat conditions to Bresler et al. (2013).

### Repository state

- **`ExactVariantECounterexample.lean:50–53`:**

  ```lean
  private def noPositiveRepeat : Prop :=
    (List.range truth.length).all (fun i =>
        (List.range truth.length).all (fun j =>
          (i == j) || (base truth i != base truth j))) = true
  ```

  This requires that all first symbols at distinct positions differ — a condition on 1-mers, not on arbitrary-length repeats with maximality.

### Independent repeat analysis for ACGT

ACGT has **no repeats of any length** under any reasonable definition:
- Length 1: A, C, G, T — all distinct
- Length 2: AC, CG, GT, TA — all distinct
- Length 3: ACG, CGT, GTA, TAC — all distinct
- Length 4: ACGT — only one occurrence

Since ACGT has no repeats at all, all triple-repeat and interleaved-repeat bridging conditions are **vacuously satisfied** under the source definition.

### Verdict: MISMATCH (does not invalidate the counterexample)

**`noPositiveRepeat` is not the source-faithful repeat definition.** The source defines repeats with maximality conditions on flanking symbols for arbitrary-length substrings (Bresler et al.). The counterexample's condition is stronger: it requires all first symbols at distinct positions differ.

**Why this does NOT invalidate the counterexample:**
1. For ACGT, `noPositiveRepeat` correctly holds.
2. ACGT has no repeats under ANY definition (all positions have distinct first symbols, so no 1-mer repeat, hence no longer repeat).
3. The bridging obligations are vacuously satisfied regardless of which repeat definition is used.
4. The likelihood comparison is independent of the bridging predicate.

**Remaining risk:** When formalizing the full open problem, the repository must use the source-faithful repeat/bridging definitions from `docs/bridging-source-semantics.md` (with maximality conditions), not `noPositiveRepeat`.

---

## 6. The Open Question: Exact Published Statement

### Primary source (Shomorony et al. §5 Discussion, final paragraph)

> "Understanding whether bridging conditions can be used to guarantee that the maximum-likelihood sequence is the true sequence is currently an open question."

The preceding sentences:
1. Theorem 1 reconstructs the true sequence under information-feasibility but gives no guarantee that this sequence solves an optimization-based assembly formulation.
2. Cites Nagarajan–Pop (2009) and Medvedev–Brudno (2009) as examples of optimization formulations.
3. Contrasts parsimony-based formulations with "the maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009)."

### What the 2016 paper does NOT specify

Independently verified by searching the full text (accepted article + author-hosted 23-page manuscript):

1. Does **not** reproduce the Medvedev–Brudno multinomial likelihood formula.
2. Does **not** mention the binomial/separable approximation.
3. Does **not** mention the Section 6.2 overlap-graph flow feasible set.
4. Does **not** state that candidate genome length is fixed to the true length G.
5. Does **not** provide a theorem/equation/section pointer inside Medvedev–Brudno that selects one of the three objects.
6. Does **not** disambiguate "truth is a maximizer" from "all maximizers are truth up to equivalence."

### Repository state

The repository correctly preserves all three ML variants (E, A, F) and both conclusion schemas (maximizer, uniqueness) as explicitly named alternatives.

### Verdict: NO MISMATCH

The repository's treatment of the source ambiguity is faithful. The `docs/ml-formalization-contract.md` correctly documents the ambiguity and requires that any eventual settlement state which variant it proves.

---

## 7. Bresler et al. Theorem 1: Equal-Likelihood Obstruction

### Primary source (independently verified from PMC3706340)

Bresler et al., Theorem 1:

> "Given a DNA sequence s and a set of reads, if there is a pair of interleaved repeats or a triple repeat whose copies are all unbridged, then there is another sequence s' of the same length under which the likelihood of observing the reads is the same."

This establishes:
- **Necessity:** unbridged problematic repeats → equal-likelihood competitor of the same length.
- **Not sufficiency:** bridged repeats → truth is the unique ML genome. The gap is exactly the 2016 open question.

### Repository state

The `docs/literature-status.md` correctly identifies this as the "closest result" and correctly notes that it does not prove the desired sufficiency direction.

### Verdict: NO MISMATCH

The repository's characterization of Bresler's result and its relationship to the open question is accurate.

---

## 8. Genome Equivalence

### Primary source

- **Shomorony et al.:** Circular sequences up to cyclic shift.
- **Medvedev–Brudno:** Models double-stranded DNA (bidirected graphs), which raises reverse-complement equivalence.

### Repository state

`genomeEquiv` is abstract. Doc comment at `Model.lean:32` mentions cyclic shifts but does not commit.

### Verdict: NO MISMATCH (correctly preserved as unresolved)

The repository correctly preserves this as a source ambiguity requiring resolution before the final theorem.

---

## 9. Conclusion Variant (Maximizer vs Uniqueness)

### Primary source

"The maximum-likelihood sequence is the true sequence" — English singular "the" most naturally suggests uniqueness, but this is not a mathematical definition and could be informal prose for "truth is a maximizer."

### Repository state

Both schemas preserved in `Model.lean` and `OpenProblem.lean`.

### Verdict: NO MISMATCH (correctly preserved as unresolved)

---

## 10. Latent Read Positions vs Observable Read Multiset

### Primary source requirement

Bridging depends on realized sequencing (latent start positions in true genome). Likelihood depends only on observable read multiset. These must not be conflated.

### Repository state

The counterexample correctly separates these: `starts` (latent) for coverage, `sampleLikelihood` (observable counts only) for ML. The abstract `Model.lean` has separate fields but does not yet enforce type-level separation.

### Verdict: NO MISMATCH in counterexample

Risk in future formalization if `Reads` type is instantiated to carry latent positions into the likelihood computation.

---

## 11. Additional Findings from Independent Verification

### 11.1 The 2016 paper's Section 2 model vs the ML formulation

Shomorony et al. §2 fix the data-generating model: circular sequence s of length G, N error-free reads of common length L, drawn independently and uniformly from G circular start positions. This is the **true genome's sampling model**, not the ML competitor universe.

**Repository correctly distinguishes these.** The data-generating model (Section 2) is separate from the ML optimization (Section 5's open question about Medvedev–Brudno).

### 11.2 Author-hosted manuscript version

The author-hosted 23-page manuscript (Stanford) gives more historical context but still does not:
- Write the likelihood formula
- Identify exact vs approximate likelihood
- Fix a candidate-genome class
- Say all competitors have the true genome length

This strengthens the ambiguity conclusion across a substantial author-hosted version. **Repository correctly documents this in `docs/source-notes/shomorony-ml-reference.md:84–118`.**

### 11.3 Bresler et al. gap between necessary and sufficient conditions

Bresler's Theorem 1 needs only **one** copy bridged to avoid the equal-likelihood obstruction. MultiBridging (Theorem 6) requires **all** copies of triple repeats to be bridged. There is room between known impossibility and known algorithmic sufficiency even before ML enters the story. **Repository correctly identifies this gap in `docs/literature-status.md:201–207`.**

### 11.4 Fixed-length counterexample not kernel-checked

The fixed-length Variant E counterexample (`AACAGG` vs `AAAGGC`, `bridging-likelihood-obstructions.md:88–145`) is verified by exact rational computation in prose but has **not** been formalized in Lean. Only the unrestricted-length counterexample is kernel-checked.

**Impact:** If a formalization effort targets fixed-length Variant E, this analysis must be formalized separately.

---

## 12. Summary of All Mismatches

| # | Area | Severity | Status | Action needed |
|---|------|----------|--------|---------------|
| 1 | `noPositiveRepeat` ≠ source repeat definition (Bresler maximality) | **Medium** | Counterexample valid but predicate is not source-faithful | Formalize source repeat/bridging defs from `docs/bridging-source-semantics.md` before attacking the open problem |
| 2 | Fixed-length counterexample not in Lean | **Low** | Prose-verified only | Formalize if targeting fixed-length Variant E |
| 3 | `genomeEquiv` not constrained to cyclic shifts | **Low** | Documented ambiguity | Resolve from source before final theorem |
| 4 | Conclusion variant unresolved | **Low** | Documented ambiguity | Resolve from source before final theorem |
| 5 | Abstract `Model.lean` does not enforce latent/observable separation at type level | **Low** | Correct in counterexample | Enforce when instantiating `AssemblyModel` |

---

## 13. What Is Correct (No Mismatch)

| Area | Status | Evidence |
|------|--------|----------|
| Candidate universe (unrestricted length) | **Correct** | Matches Medvedev–Brudno §6.1 exact multinomial |
| Circularity (modular indexing) | **Correct** | Faithfully implements circular window access |
| Read sampling (i.i.d. uniform) | **Correct** | Matches both §6.1 and Shomorony §2 |
| Multinomial constants (observation-only) | **Correct** | Factors out of ML ordering; documented |
| Genome length (candidate-dependent N(D)) | **Correct** | Matches exact multinomial; not approximated |
| Coverage predicate | **Correct** | Checks every position lies in a read |
| Latent/observable separation in counterexample | **Correct** | Starts for bridging; counts for likelihood |
| ML variant preservation (E/A/F) | **Correct** | Three variants explicitly named and separated |
| Conclusion variant preservation | **Correct** | Both schemas preserved |
| Genome equivalence ambiguity | **Correctly unresolved** | Documented open modeling question |
| Bresler Theorem 1 characterization | **Correct** | Necessary condition, not sufficiency |
| Shomorony §2 data model vs ML formulation | **Correctly distinguished** | True-genome sampling model separate from ML optimization |
| Author-hosted version ambiguity | **Correctly documented** | 23-page manuscript also fails to disambiguate |

---

## 14. Source-Cited Reference Map

| Claim | Primary source | Repository anchor |
|-------|---------------|-------------------|
| Exact multinomial with N(D) | Medvedev–Brudno §6.1 (PMC3154397) | `ExactVariantECounterexample.lean:26–28` |
| Candidate length unrestricted | Medvedev–Brudno §6.1, no fixed-length restriction | `ExactVariantECounterexample.lean:63–65` |
| Binomial approximation with fixed N | Medvedev–Brudno §6.1 (2nd half, PMC3154397) | `docs/ml-formalization-contract.md:28` |
| Flow feasible set ≠ all genomes | Medvedev–Brudno §6.2 | `docs/source-notes/ml-ambiguity-audit-resolved.md:88–93` |
| Circular genome | Medvedev–Brudno §6.1; Shomorony §2 | `ExactVariantECounterexample.lean:11–12` |
| Sampling: uniform over circular starts | Medvedev–Brudno §6.1; Shomorony §2 | `ExactVariantECounterexample.lean:27–28` |
| Repeat maximality | Bresler et al. (PMC3706340), Results section | `docs/bridging-source-semantics.md:12–16` |
| Triple-repeat three-copy maximality | Bresler et al. (PMC3706340), Results section | `docs/bridging-source-semantics.md:14` |
| Bridging strict extension | Bresler et al. (PMC3706340), Fig. 5 caption | `docs/bridging-source-semantics.md:22–28` |
| All-bridged triple repeats | Bresler et al. Theorem 6; Shomorony Eq. (1) | `docs/bridging-source-semantics.md:45–49` |
| I_s definition | Shomorony et al. 2016, Eq. (1) | `docs/bridging-source-semantics.md:53–61` |
| Shomorony open question sentence | Shomorony §5 (Discussion) | `docs/open-problem.md:7–9` |
| Shomorony does not disambiguate ML variant | Shomorony full text + author-hosted manuscript | `docs/source-notes/shomorony-ml-reference.md:53–67` |
| Tie semantics unresolved | Both papers | `docs/literature/ml-tie-semantics.md` |
| No resolution in literature as of 2026-09-17 | Literature search (13 papers checked) | `docs/literature-status.md` |
| Counterexample: no repeats in ACGT | Verified by exhaustive check | `ExactVariantECounterexample.lean:48–49` |
| Counterexample: coverage via latent starts | `starts = [0, 0, 2]` | `ExactVariantECounterexample.lean:36` |
| Counterexample: likelihood arithmetic | Kernel-checked by `decide`/`norm_num` | `ExactVariantECounterexample.lean:83–101` |
| Bresler equal-likelihood obstruction | Bresler et al. Theorem 1 (PMC3706340) | `docs/literature-status.md:164–199` |
| MultiBridging sufficient conditions | Bresler et al. Theorem 6 (PMC3706340) | `docs/bridging-source-semantics.md:45–49` |

---

## 15. Confirmation of Pre-Existing Audits

The existing audits are **confirmed accurate and complete**:

- `docs/audit-source-model-contract.md` — All findings verified. Severity ratings appropriate.
- `docs/audit-independent-2026-09-19.md` — All findings verified. No additional mismatches.
- `docs/audit-independent-verification.md` — All findings verified. Independent confirmation of no new mismatches.
- `docs/audit-variant-e-settlement.md` — All gap analysis confirmed accurate.
- `docs/source-notes/ml-ambiguity-audit-resolved.md` — All source quotations match independently fetched PMC text.
- `docs/source-notes/medvedev-brudno-candidate-class.md` — All source quotations match independently fetched PMC text.
- `docs/source-notes/shomorony-ml-reference.md` — All source analysis confirmed against fetched DOI.
- `docs/bridging-source-semantics.md` — All Bresler repeat/bridging definitions match independently fetched PMC text.
- `docs/literature-status.md` — Literature search scope and conclusions confirmed.
- `docs/ml-formalization-contract.md` — Formalization organization confirmed sound.

**No new material mismatches were identified beyond those already documented in the repository's existing audit infrastructure.**

---

## 16. Epistemic Assessment

The repository's source-fidelity documentation is **exceptionally thorough**. Every modeling choice is traced to specific primary-source passages, ambiguities are preserved rather than resolved by fiat, and the distinction between source facts, modeling decisions, and research conclusions is maintained. The existing audit stack (4 independent audits + 3 source notes + literature status + formalization contract) provides a reliable foundation for any future formalization effort.

The only actionable gap for future formalization is the `noPositiveRepeat` predicate mismatch (item #1 in the summary table), which must be replaced by source-faithful repeat/bridging definitions before attacking the open problem.
