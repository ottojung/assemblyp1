# Independent literature search: independent verification (2026-09-19)

_Search method: independent web search via websearch tool, cross-referencing with existing repository literature files._
_Scope: papers citing Shomorony et al. (2016), papers on bridging conditions and ML assembly, post-2016 assembly theory._

## Executive conclusion

**The exact 2016 open question remains unsettled.** No published paper proves or disproves that the Shomorony et al. bridging conditions guarantee that the maximum-likelihood genome is the true sequence under the Medvedev–Brudno formulation. This conclusion is consistent with all existing repository literature documents (`literature-status.md`, `literature-search-post2016-durable.md`, `literature-search-independent-2026-09-19.md`).

This is a literature-search conclusion, not a proof of absence. The search was conducted via independent web search queries covering exact wording, author names, terminology variants, and recent assembly theory. Scholarly search systems are not exhaustive.

## Papers examined in this search

### 1. Ali, Narayanan, Krishnan — Converse for shotgun sequencing channel with erasures (2025)

- **Citation:** ITW 2025. DOI: [10.1109/ITW62417.2025.11240437](https://doi.org/10.1109/ITW62417.2025.11240437)
- **Key result (source fact):** Converse bound for the capacity of the shotgun sequencing channel with erasures.
- **Relationship to the open question:** Information-theoretic result in the sequencing channel model. Addresses capacity bounds, not the bridging→ML implication.
- **Epistemic status:** Source fact. Does not resolve the open question.

### 2. Pflughaupt, Sahakyan — Prior knowledge on context-driven DNA fragmentation (2025)

- **Citation:** *BMC Bioinformatics* 26:245, 2025.
- **Key result (source fact):** Uses breakage propensity scores to improve assembly of ultrashort fragments. Probabilistic framework for scoring assemblies.
- **Relationship to the open question:** Applies ML-like scoring to assembly evaluation, but in a different model (fragmentation probabilities, not read-count likelihood). Does not address the bridging→ML question.
- **Epistemic status:** Source fact. Does not resolve the open question.

### 3. Díaz-Domínguez, Martinello, Onodera, Puglisi, Salmela — Contig model for variable-order de Bruijn graphs (2026)

- **Citation:** WABI 2026, LIPIcs 390, 4:1–4:19.
- **Key result (source fact):** Extends SAMA's probabilistic correctness model to variable-order de Bruijn graphs.
- **Relationship to the open question:** Extends the correctness/probability estimation line, not the bridging→ML line.
- **Epistemic status:** Source fact. Does not resolve the open question.

### 4. Zhu, Liu, Liu — Eulerian reconstruction conditions (2026)

- **Citation:** *Mathematics* 14(5):832, 2026. DOI: [10.3390/math14050832](https://doi.org/10.3390/math14050832)
- **Key result (source fact):** Studies reconstruction from the complete k-mer spectrum. Derives sharp transitions as a function of k and genome length.
- **Relationship to the open question:** Complete-spectrum model (no sampling), different from finite shotgun-read setting. Does not address ML.
- **Epistemic status:** Source fact. Does not resolve the open question.

### 5. pHapCompass — Polyploid haplotype assembly (2025)

- **Citation:** arXiv:2512.04393, 2025.
- **Key result (source fact):** Probabilistic framework for polyploid haplotype assembly with uncertainty quantification.
- **Relationship to the open question:** Haplotype assembly problem, not genome assembly from reads. Different problem entirely.
- **Epistemic status:** Source fact. Does not resolve the open question.

### 6. Bankevich — Supregraph (2026)

- **Citation:** arXiv:2604.21951, 2026.
- **Key result (source fact):** Introduces supregraphs, a new class of assembly graphs that perfectly preserve information from error-free read sets. Correct representation exists (Theorem 17). Under natural assumptions, provides foundation for theoretically optimal assemblies (Theorem 18).
- **Relationship to the open question:** Significant theoretical advance in graph-representation theory. Addresses the information-preservation layer (what information is available), not the likelihood layer (what genome maximizes likelihood given observed read counts). Does not cite the 2016 open question or the Medvedev–Brudno ML formulation. Operates in a different model (chromosome candidate-preserving walks) than the ML objective.
- **Epistemic status:** Source fact. Important adjacent theory but does not bridge the gap to ML optimality.

## What was NOT found

Despite searching:
- exact quoted sentences from the 2016 paper;
- author names (Shomorony, Kim, Courtade, Tse) with ML assembly terms;
- terminology variants (bridged repeat, interleaved repeat, triple repeat, identifiability, unique reconstruction);
- later work by the same authors;
- likelihood-based assembly literature;
- safe-and-complete assembly literature;
- recent theoretical/survey writing on assembly;
- diploid extensions;
- graph-representation theory;

**No paper was found that:**
1. Proves that Shomorony et al. bridging conditions imply that the true genome maximizes the Medvedev–Brudno read-count likelihood;
2. Proves that bridging conditions imply that the true genome is the unique maximum-likelihood genome (up to the intended genome equivalence);
3. Provides a published counterexample where bridging conditions hold but another candidate genome has strictly greater likelihood;
4. Directly cites and resolves the 2016 open question.

## Strongest adjacent theorems (unchanged from existing literature files)

| Theorem | What it establishes | Gap to ML |
|---------|-------------------|-----------|
| Bresler et al. 2013, Thm 1 | Unbridged repeats → equal-likelihood competitor (same length) | Necessity only; does not show bridging → ML sufficiency |
| Shomorony et al. 2016, Thm 1 | Bridging + coverage → unique Eulerian reconstruction | Algorithm-specific; not a global ML comparison |
| Mahajan et al. 2024/2025 | Diploid bridging conditions for reconstruction | Same gap as Shomorony; extends to diploids |
| Bankevich 2026 (Supregraph) | Perfect information-preserving graph representation | Graph layer, not likelihood layer |

## Assessment

The repository's existing conclusion is correct and well-justified: **the problem remains genuinely open as of 2026-09-19.** No new material result was found in this independent verification that would alter the assessment in `literature-status.md`.

The two research lines remain separate in the literature:
- **Information-feasibility / correctness / safety** (Bresler et al., Shomorony et al., omnitigs, SAMA, supregraphs)
- **Maximum-likelihood assembly** (Medvedev–Brudno, GAML, SWALO)

No paper found bridges these two lines by proving that bridging conditions imply ML optimality.
