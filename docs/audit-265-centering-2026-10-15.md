# Audit: #265 centering requirements against current `main`

Status: 2026-10-15. Auditor: agent `1da4e6282b15`. Repository
`github.com/ottojung/assemblyp1`. Base: `main` @ `2512e06` (verified with
`git ls-remote origin refs/heads/main`). This note is read-only with respect to
`paper/sections/*.tex` (owned by a live #268 agent); it records present versus
missing for each required item of board #265, with file paths, line references,
and the last commit that touched each artifact. It does not edit the paper and
does not declare any open problem settled.

Labels: **PRESENT** (requirement met on `main`), **PARTIAL** (met in the
whitepaper but not in a maintained presentation, or vice versa), **MISSING**.

## Required mathematical content

| # | Requirement (abbreviated) | Status | Evidence |
|---|---|---|---|
| 1 | Fixed genome `G`, read law `P_G`, reads `R_i`, likelihood `L_n(G)`; starts uniform but read-type probabilities not; `L(data\|G)` vs posterior vs sampling; rotations equivalent | PRESENT | `paper/sections/02-model.tex:14` (`def:spectrum`), `:39` (`rem:cyclic`), `:50` (`def:reads`), `:156` (`def:likelihoods`), `:187` "Uniform start sampling is not uniform read-type probability"; `paper/sections/03-open-question.tex:42` (`sec:two-questions`). Slides: `slides/programmers.md:171` "Another approach: how likely are these reads?", `:194` "From a read probability to a genome probability", `:219` "More reads: count pairs of possible positions"; `slides/biologists.md:34`, `:127` (notes distinguish likelihood vs posterior). |
| 2 | Tiny explicit finite-sample reversal with actual probabilities; finite ML meaningful, not invalid | PRESENT | `paper/sections/03-open-question.tex:314` (`ex:W1W2`); `paper/sections/04-finite-results.tex` (Thms `thm:cex-exact`/`thm:cex-binomial`/`thm:cex-historical-W1/W2`); `paper/sections/01-introduction.tex:20` (`ex:ABAB`). Slides: `slides/programmers.md:392` "A counterexample in six reads", `:428` "The longer genome scores higher" (ratio `15625/11664`), `:530` "Even genomes without repeats can fool finite ML"; `slides/biologists.md:146`, `:186` (ratio `15625/11664`). |
| 3 | Finite candidate set, uniform prior, zero-one loss: MAP=ML maximizes prior-averaged success for every finite `n`; short Bayes proof; limits; tie handling | PRESENT | `paper/sections/03-open-question.tex:87` (`thm:bayes-optimal`), `:102` (proof), `:118` (rotation-class prior), `:132` (prior-average not per-truth; surrogate caveat), `:228` (`ex:worked-bayes`), `:256` (`tab:claims`). Kernel: `AssemblyP1/FiniteBayesDecision.lean:85` `chooseMAP_optimal`, `:91` `chooseMAP_optimal_randomized`. Slides: `slides/programmers.md:278`–`:362` (counting/proof, notes cite `FiniteBayesDecision`). |
| 4 | Prior-averaged `S_{n+1}>=S_n` via ignore-extra-observation; **contrast** with per-truth success which need not be monotone; checked counterexample with model and tie handling | PARTIAL (paper PRESENT; presentations MISSING) | Paper: `paper/sections/03-open-question.tex:139` (ignore-extra-observation), `paper/sections/05-population.tex:558`–`:635` (`sec:nonmonotone`, `prop:nonmonotone`: `S=AAC`, `D=AAAC`, `L=2`, `succ(1)=2/3 > succ(2)=4/9`, tie argument at `:611`). Kernel: `AssemblyP1/FiniteBayesDecision.lean:122` `chooseMAP_success_monotone_under_refinement`; `AssemblyP1/NonmonotonicityWitness281.lean:174` `success_not_monotone`. Notes/script: `docs/issue281-nonmonotonicity-witness.md`, `scripts/verify_nonmonotonicity_witness_281.py`. **Gap:** no deck slide states the prior-average-monotone / per-truth-non-monotone contrast; `slides/programmers.md:832` (B1) is a single realized-sample reversal, not per-truth success probability. Addressed by the new backup slide in this branch. |
| 5 | Infinite-read limit: empirical frequencies converge (SLLN); expected log-likelihood maximized at truth by KL; identifiability modulo rotation gives a.s. correct ML and `P(correct)->1`; limit not infinite product; distinguish population from finite guarantees | PRESENT | `paper/sections/05-population.tex` (`lem:gibbs`, `thm:population`, `rem:consistency-distinction:545`); `paper/sections/03-open-question.tex:144` (`rem:sample-complexity`), `:285` (Table row 5). Kernel: `AssemblyP1/PopulationGibbs` (`popLogLik_le_self'`, `popTie_iff`), `AssemblyP1/Issue94Complete` (`population_unique_ML`). Slides: `slides/programmers.md:598` "Population likelihood: remove sampling noise", `:626` "When the exact read distribution is known", `:650` "Do we actually need infinitely many reads?"; `slides/biologists.md:209`, `:236`. |
| 6 | Connect *proved* AssemblyP1 structural theorems and where they do **not** apply; distinguish population ML, exact finite ML, historical bridging/coverage, MB09 §6.2 flow and §6.1 product-binomial; no upgrade of external stats to "proved in Lean"; no unproved converse as settled | PRESENT | `paper/sections/02-model.tex:89` (`def:Is`), `:103` (`rem:historical-coverage`), `:128` (`rem:2016-vs-rigidity`), `:156` (MB09 §6.1 binomial vs exact multinomial), `:200` (count-dependence surrogate caveat), `:214` (candidate classes incl. §6.2 flows); `paper/sections/03-open-question.tex:12` (`def:historical-match`), `:30` (`thm:notso-greedy`, labelled published), `:202` (`cor:conditional-bridging-error`). Slides: `slides/programmers.md:150` (Not-So-Greedy notes: "external premise, not Lean-proved"), `:873` (B2 coverage notions), `:930` (B4 sources). |
| 7 | Sample complexity as motivating open problem; optionally a scoped union/Chernoff bound for a finite distinguishable family; never claim the limit theorem gives a finite `n` | PRESENT | `paper/sections/03-open-question.tex:144` (`rem:sample-complexity`), `:171` (`cor:explicit-sample-size`, sufficient not necessary, Chernoff comparison), `:194` (conservative-scope caveat). Kernel: `AssemblyP1/FiniteReadRecovery.lean:352` `eventProb_wrong_le_card`, `:424` `il_confidence_99`. Notes/script: `docs/sample-complexity-265.md`, `scripts/verify_sample_complexity_265.py`. Slides: `slides/programmers.md:894` (B3), `slides/biologists.md:342` (backup); both state the unrestricted uniform sample size remains open. |

## Deliverable and framing checks

| Deliverable | Status | Evidence |
|---|---|---|
| Whitepaper arc visible early (genome → reads → likelihood → finite ambiguity → Bayes rule → sample size/consistency → identifiability → structural contributions → open) | PRESENT | `paper/main.tex:19` (abstract); `paper/sections/01-introduction.tex:1`–`:279`, especially `:87` (ML question), `:126` (two questions), `:163` (labelled contributions), `:263` ("How to read this paper"). |
| Slides: arc woven, 1 idea/slide, notes carrying hypotheses/proofs; #254 audience, ~12–14 slides, Lean/agent-trust story preserved | PRESENT | `slides/programmers.md` 14 main slides + backups (frontmatter through `:824`; agents/Lean at `:722`–`:792`); `slides/biologists.md` 15 main + backups. Approved opening (lines 1–74) byte-for-byte from `7aba5d0` (see below). |
| Trace claims to primary references + exact project Lean theorems and paper sources; no unqualified "ML is the best algorithm" | PRESENT | `docs/presentation-arc-265.md` (claim-label table), `docs/verification.md`, `paper/sections/b-epistemic-ledger.tex`, `docs/remaining-open-matrix-255.md`. Slide notes carry kernel endpoints and external-premise caveats. |
| Reviewed, signed source changes; validate paper build, slide rendering, examples, CI; independent review and merge | PRESENT (this audit adds one bounded increment) | See "Landing history" and "Validation" below. |

## Landing history (verified)

- **PR #239** (opening-slide restoration, `slides/programmers.md`):
  merged to `main` as `c8b4b21` (`Merge PR #239: restore user-approved opening
  three slides of the programmers' deck`); PR head `3089f1f`; base `main`.
  Verified by API (`state=closed`, `merged=true`, `merge_commit_sha=c8b4b21`).
  Byte checks on the merged result:
  - `git show 7aba5d0:slides/programmers.md | head -74` == `git show 3089f1f:slides/programmers.md | head -74` (identical).
  - `git show abfbf86:slides/programmers.md | tail -n +75` == `git show 3089f1f:slides/programmers.md | tail -n +75` (identical), where `abfbf86` is the pre-merge `main` (first parent of `c8b4b21`).
  - `git show 2512e06:slides/programmers.md` == `git show 3089f1f:slides/programmers.md` (current `main` carries the merged deck).
  The PR's intermediate commit `704060e` from the handoff is no longer
  reachable (branch deleted/GC); the content is preserved as `3089f1f`.
- **#265 sample-complexity increment** landed earlier as signed merge `069f64e`
  (`docs/sample-complexity-265.md`, `cor:explicit-sample-size`, `slides/*` B3,
  `scripts/verify_sample_complexity_265.py`).
- **#268 refocus** (`f63b37d`) and **#281 rate** (`0b34417`) are the last
  paper-side edits; they are owned by other agents and were not modified here.

## Remaining genuinely open (unchanged by this audit)

- General (non-equal-length) maximum-likelihood characterization.
- A sharp, uniform sample size over the unrestricted genome universe (all
  lengths and models); the finite-family Hellinger/union bound is sufficient,
  not tight.
- Whether the historical predicate admits any *same-length* strict reversal at
  full generality (the two `W1/W2` witnesses are molecule-model, same-length).
- The #268/#255 status matrices own the final reconciliation of claim labels.

## Validation

- `python3 scripts/check-research-docs.py` -> "research documentation integrity
  checks passed".
- Presentation increment (backup slide on prior-average vs per-truth
  monotonicity) validated with the deck toolchain; see the branch's
  `[terminal-handoff]` on board #265 for the exact commands and results.
