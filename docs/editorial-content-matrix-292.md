# Editorial Content Matrix — Issue #292

Cross-document editorial acceptance review of README, programmers deck,
biologists deck, and main whitepaper for audit-log-driven exposition dominance.

## Content Matrix

| Topic | README | Programmers deck | Biologists deck | Paper |
|---|---|---|---|---|
| (i) What genome assembly is | Brief: "theoretical genome-assembly open problem" | "Sequencing reads a circular genome in short, overlapping pieces" + assembly problem definition | "A circular genome is copied and read as many short, overlapping fragments" + assembly problem definition | §1.1: genomes, reads, repeat obstacle; §1.3: ML question |
| (ii) Operational graph reconstruction | Not covered | Mentioned in "Three different questions" (graph algorithm) | "Overlaps are the basic signal" + "Repeats create genuine ambiguity" + "Bridging reads resolve repeats" + "The support graph in detail" (de Bruijn graph) | §1.2: bridging; §4.1: window-support graph definition; §4.2: rigidity theorem |
| (iii) Bridging intuition and 2016 guarantee | Not covered | "Right arithmetic, wrong definition" (bridging bug story) | "Bridging reads resolve repeats" + "Shomorony, Kim, Courtade & Tse (2016) formalized when bridging is sufficient" | §1.2: "Shomorony, Kim, Courtade, and Tse made this precise" + bridging conditions; §2.2: formal definition of I_S |
| (iv) ML question and finite positive/negative results | Not covered in detail | "Three different questions" + "The historical boundary" (AAATAT→AAAAAT, ratio 3) + "What was verified" (negative + positive results) | "A finite boundary: when the decoy scores higher" + "Why the reversal happens" + "A positive result: structural rigidity" + "Population uniqueness" | §3: the question mathematically; §4: finite results (rigidity + counterexamples); Table 4.2: finite landscape |
| (v) Population theorem | Not covered | "What was verified" mentions "Population uniqueness: for a truth with mild non-repetition structure (primitive, P2)..." | "Population uniqueness" slide + "Idealized population model" | §5: population ML and uniqueness theorem (Theorem 5.1) |
| (vi) Why Lean matters | "A Lean formalization project" | "What Lean is" + "Why the small kernel is trustworthy" | "This result is verified by a machine-checked proof (Lean)" (in population uniqueness section) | Throughout: "kernel-checked" status tags; Appendix B: epistemic ledger |

## Audit Findings

### Incorrect graph diagrams

- **biologists.md, "The support graph in detail" slide**: The de Bruijn graph diagram
  for genome AAATT (L=3) was incorrect. The edge AAA was shown as connecting
  vertices AA to AT; it should be a self-loop on AA. The edge TTA was shown at
  the bottom without proper direction; it should go from TT to AA.
  **Status: FIXED** — replaced with correct edge list.

### Mislabeled checks or claims

- All exact ratios in the programmers deck (3, 3/2, 15625/11664) match the
  paper's Theorems 4.7, 4.6, and 4.8 respectively.
- All exact ratios in the biologists deck (15625/11664, 3125/3888, 3, 5)
  match the paper's Theorems 4.8 and 4.7.
- The "What is proved, and how strongly" table in the biologists deck correctly
  labels each claim's status.
- The programmers deck's "What was verified" slide correctly labels negative
  and positive results.
- **No mislabeled checks or claims found.**

### Unnecessary process caveats

- The programmers deck's "Right arithmetic, wrong definition" and "A definition
  weaker than the paper's" slides describe internal formalization bugs. While
  process-oriented, they serve the scientific narrative that "definitions are
  part of the claim" and are not debug reports. They do not dominate the
  scientific communication (2 of 10 slides).
- The biologists deck's "What is proved, and how strongly" table includes an
  honest note about machine-checked vs. source-intent. This is scientifically
  appropriate, not a process caveat.
- The paper's epistemic status tags and appendices are appropriate for a
  scientific paper and are clearly separated from the main narrative.
- **No unnecessary process caveats found in audience-facing content.**

### Source-focused fidelity/debug reports in internal docs

- The paper's Appendix B (epistemic ledger) and Appendix D (referents audit)
  are clearly marked as reference material.
- The biologists deck's HTML comments contain verification status notes;
  these are not visible to the audience.
- The programmers deck's HTML comments contain speaker notes; these are
  excluded from the public build.
- **Internal docs correctly contain the fidelity/debug material.**

## Build Validation

| Build | Status |
|---|---|
| CI: check-research-docs.py | PASS |
| CI: verify_historical_coverage_audit.py | PASS |
| CI: verify_247c_historical_witnesses.py | PASS |
| CI: verify_261_binomial_extreme_samples.py | PASS |
| Slides: npm run build | PASS (portal + both decks, validation OK) |
| Paper: sh build.sh (guix + latexmk) | PASS (43-page PDF) |
| Lean: lake build | Pending (Mathlib compilation in progress) |
