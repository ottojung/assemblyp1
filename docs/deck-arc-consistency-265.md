# Deck arc consistency with the two-question whitepaper (#265)

Status: 2026-10-16. Author: agent `68d129da714f`. Repository
`github.com/ottojung/assemblyp1`. Base: `main` @ `a5b6e77`. Branch:
`agent/68d129da714f-issue265-deck-two-question`.

This note records how the two maintained Slidev decks
(`slides/programmers.md`, `slides/biologists.md`) now mirror the
**two-question narrative** that the #268 refocus established in the
whitepaper (commits `e7e3d20`, `b47eb04`; note
`docs/whitepaper-refocus-268.md`), and records the
paper / claims-matrix / bibliography acceptance checks. It is a
deck-centering note: it changes no paper section and no Lean source.

## The two questions

The whitepaper separates the single sentence "the maximum-likelihood
sequence is the true sequence" into two inequivalent questions
(`paper/sections/01-introduction.tex` `sec:intro:two-questions`;
`paper/sections/03-open-question.tex` `sec:two-questions`;
`tab:claims` row 1 vs row 3).

- **Question A (conditional).** Condition on the truth-dependent feasible
  event $E=\{F(S,R)\}$ and restrict candidates to the positive-weight
  feasible fiber $\{g:\pi(g)P_g(R)>0,\ F(g,R)\}$. Under the source model
  assumptions the published 2016 reconstruction theorem makes that fiber a
  single rotation class, so conditional MAP returns the truth. This is
  largely a corollary of the reconstruction premise, not a new likelihood
  result. Evidence: 2016 reconstruction premise (`shomorony2016`) plus the
  kernel-checked conditional/ordinary separation.
- **Question B (unconditional).** Assume only $F(S,R)$ and maximize the
  **original, unrestricted** likelihood over the **original** candidate
  universe. The truth can lose strictly, including under the source's own
  matched-string predicate. This is the substantive finite-sample
  comparison, and ordinary ML never observes the event $E=F(S,R)$.

The key centering point for the decks: **Question A and Question B are
different experiments**, and the reconstruction promise is information that
ordinary ML (Question B) never receives.

## What changed in the decks

- `slides/programmers.md`
  - **"The 2016 question: does the guarantee imply ML?"** now names the two
    questions explicitly: Question A (conditional) is a corollary of the
    reconstruction guarantee; Question B (unconditional) is the substantive
    comparison, answered negatively.
  - **"Why the two methods do not contradict each other"** now maps
    Not-So-Greedy to Question A and ordinary ML to Question B and states that
    the two are different experiments.
  - **"Another extension: what if we are promised reconstruction works?"**
    retitled **"Question A: what if we are promised reconstruction works?"**,
    tying the conditional-posterior result to the hinge slide.
  - **"What the investigation established"** now states that the sentence was
    separated into the two questions, with Question B answered negatively.
  - Speaker notes updated with the paper labels (`sec:intro:two-questions`,
    `sec:two-questions`) and the feasible-fiber / truth-dependent-event
    caveat.
- `slides/biologists.md`
  - **"But the paper left another question"** now labels **Question A
    (conditional)** and **Question B (unconditional)** at the accessible
    level, pointing forward to the decoy example.
  - **"Three take-aways"** annotates the reconstruction guarantee as
    Question A and the finite-sample decoy as Question B.
- `slides/programmers-research-notes.md` (not rendered, but a maintained deck
  artifact): the "Editorial correction: the 2016 negative result and
  conditional Bayes" section now names the paper's **Question B
  (unconditional)** explicitly and distinguishes it from **Question A
  (conditional)**, removing the earlier "conditional implication" wording
  clash.

No slide was added or removed; the approved #254 programmers opening
(lines 1-74) is untouched, and the audiences, the Lean/agent-proof-trust
story, and the existing backup slides are preserved.

## Mapping: programmers' deck → two-question narrative

| Slide | Narrative element |
|---|---|
| The Most Likely Genome | title |
| Our goal: reconstruct the genome | genome → reads setup |
| The mathematical problem we chose to study | model: circular genome, independent uniform-start fixed-`L` reads |
| A first reconstruction: join the overlaps | reconstruction (Question A premise) |
| What if an overlap has several choices? | repeat ambiguity / bridging |
| Sometimes even all short reads are ambiguous | structural non-identifiability |
| Not-So-Greedy: a reconstruction guarantee | Question A premise (published 2016, external) |
| Another approach: how likely are these reads? | likelihood `L(data\|G)` |
| From a read probability to a genome probability | posterior `P(G\|data)` vs sampling |
| More reads: count pairs of possible positions | product likelihood and posterior |
| What that calculation looks like in TypeScript | worked computation |
| What does the "best" assembly algorithm mean? | decision experiment |
| Why no algorithm can beat maximum likelihood in this game | prior-average Bayes optimality (`tab:claims` row 2) |
| The 2016 question: does the guarantee imply ML? | **two-question hinge: A vs B** |
| A counterexample in six reads | Question B witness |
| The longer genome scores higher | Question B strict reversal |
| Why the two methods do not contradict each other | **A vs B separation** |
| A positive result: what if the genome length is known? | restricted positive structural result |
| But can we assume that length is known? | scope limitation |
| Even genomes without repeats can fool finite ML | finite-sample reversal (Question B-adjacent) |
| The clue: the wrong genome fits our six reads exactly | empirical-frequency mechanism |
| Population likelihood: remove sampling noise | population level (strong law) |
| When the exact read distribution is known | identifiability / population uniqueness (`tab:claims` row 4) |
| Do we actually need infinitely many reads? | limiting consistency (`tab:claims` row 5) |
| Question A: what if we are promised reconstruction works? | **Question A detailed endpoint** |
| Choosing the next research question | research arc |
| Why we used multiple AI research agents | agent/Lean story |
| How continuous research was organized | orchestration |
| Why Lean mattered | Lean / kernel trust |
| What the investigation established | conclusion: two questions separated |
| Questions? | end |
| Backup B1-B6 | finite reversal, coverage notions, sample complexity, monotonicity, sources, strong-law limit |

## Mapping: biologists' deck → two-question narrative

| Slide | Narrative element |
|---|---|
| Which genome is most likely? | title |
| A sequencer takes a sample | read model |
| Overlaps help. Repeats confuse. | repeat ambiguity |
| Longer context can resolve a repeat | bridging (Question A premise) |
| The 2016 algorithm connects reads into a graph | Question A premise (published 2016, external) |
| But the paper left another question | **two-question hinge: A vs B** |
| Maximum likelihood is simple | likelihood `P(data\|genome)` |
| Two genomes make different predictions | per-genome read probabilities |
| The likelihood is just multiplication | product likelihood |
| A finite aside: the decoy can win | Question B witness |
| What if we had infinitely many reads? | population maximality (KL) and limit scope |
| When can the truth be identified? | identifiability / population uniqueness (`tab:claims` row 4) |
| A finite positive theorem as well | restricted positive structural result |
| Three take-aways | conclusion: A vs B annotated |
| Thank you | end |
| Backup slides | observation model, same-length witness, sample complexity, monotonicity, limit, sources |

## Paper / claims-matrix / bibliography acceptance

- **Claims matrix (`paper/sections/03-open-question.tex` `tab:claims`).**
  Row 1 is "Conditional reconstruction (Question A)"; row 3 is "Pointwise
  finite-sample failure" (the Question B comparison); rows 2, 4, 5 are
  prior-average Bayes optimality, identifiability, and limiting consistency.
  This is the centered two-question framing, and the deck labels use exactly
  the same Question A / Question B terms. Consistent.
- **References (`paper/references.bib`).** 23 bibliography keys, all 23 cited
  in the paper, with no uncited entries; every `\cite` key resolves and every
  `\ref`/`\eqref` target has a matching `\label`. `paper/build.sh` exits `0`
  with 51 pages and **0 undefined references and 0 undefined citations**.
- **Verification index (`docs/verification.md`).** The Question A row
  (`ConditionalIdentifiability`), the Bayes/MAP rows
  (`FiniteBayesDecision`, `FiniteMapOptimality`), the finite witnesses, and
  the strong-consistency row (`prop:strong-consistency`, external, not
  kernel-checked) are present and consistent with the deck claims.

## Validation

- `node slides/scripts/check-format.mjs` -> OK.
- `node slides/scripts/check-math.mjs` -> OK.
- `cd slides && npm ci && npm run build` -> format, math, both decks,
  portal, `validate-dist` all OK.
- `sh paper/build.sh` -> exit `0` (Guix); 51 pages; 0 undefined references;
  0 undefined citations.
- All CI research-docs steps (`scripts/check-research-docs.py`,
  `verify_historical_coverage_audit.py`, `verify_247c_historical_witnesses.py`,
  `verify_261_binomial_extreme_samples.py`, `verify_261_spelled_flow_adapter.py`,
  `verify_261_spelled_flow_maximality.py`,
  `verify_261_spelled_flow_image_refutation.py`,
  `verify_covered_binomial_weights_259.py`, `verify_281_window_cap.py 3 11 4`,
  `verify_sample_complexity_265.py`, `verify_strong_consistency_265.py`) pass.

## Non-claims

This note does not change the mathematical content of the paper or Lean, does
not settle any open problem, and does not upgrade the published 2016
reconstruction premise or any classical statistics to a kernel-checked
project result. The general non-equal-length ML characterization and the
sharp uniform sample-size question remain open.
