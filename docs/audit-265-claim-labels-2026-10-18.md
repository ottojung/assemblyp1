# Audit: #265 required content and proof-to-claim labels at `main` `230eca1`

Status: 2026-10-18. Auditor: agent `06db14c3d056`. Repository
`github.com/ottojung/assemblyp1`. Base: `main` @ `230eca1`. This note records
the present / missing / mislabeled status of the seven required mathematical
items of board #265 against the current whitepaper and both maintained decks,
and the single bounded increment it implements: a claim-label correction in
`paper/sections/03-open-question.tex` `tab:claims` row 1.

Labels: **PRESENT** (met), **PARTIAL** (met in one artifact but not the other),
**MISSING**. Proof classes follow the issue policy: kernel-checked Lean theorem
with source path; proof in paper / not yet Lean; textbook external theorem with
citation; published 2016 external premise; open.

## Seven required items (whitepaper)

| # | Item (abbreviated) | Status | Evidence |
|---|---|---|---|
| 1 | Fixed `G`, read law `P_G`, reads `R_i`, `L_n(G)`; start-uniform ≠ read-type-uniform; `L(data|G)` vs posterior vs sampling; rotations equivalent | PRESENT | `paper/sections/02-model.tex` `def:spectrum` (14), `rem:cyclic` (39), `def:reads` (50), `def:likelihoods` (156), the "Uniform start sampling is not uniform read-type probability" paragraph (187); `paper/sections/03-open-question.tex` `sec:two-questions` (72). |
| 2 | Tiny explicit finite-sample reversal with actual probabilities; finite ML meaningful | PRESENT | `paper/sections/01-introduction.tex` `ex:ABAB` (20); `paper/sections/03-open-question.tex` `ex:W1W2` (525), `ex:worked-bayes` (430); `paper/sections/05-population.tex` `ex:frequencies` (17). |
| 3 | Finite set, uniform prior, 0–1 loss: MAP=ML maximizes prior-average success for every finite `n`, det./randomized; limits; ties | PRESENT | `paper/sections/03-open-question.tex` `thm:bayes-optimal` (117) with proof (132) and kernel endpoints (144); `rem:bayes-certificate` (156) gives the converse, tie witness, and forced strict-maximizer; limits stated (204, 228). |
| 4 | Prior-averaged `S_{n+1}≥S_n` via ignore-extra-observation; per-truth success need not be monotone, with checked counterexample and tie handling | PRESENT | `paper/sections/03-open-question.tex` (235) and statusline (240); `paper/sections/05-population.tex` `prop:nonmonotone` (656) with model, `succ(1)=2/3 > succ(2)=4/9`, and tie discussion. |
| 5 | SLLN, KL nonnegativity, a.s. eventual correct ML and `P(correct)→1` under identifiability modulo rotation; support cases; "infinite reads" is a limit, not an infinite product; population vs finite-sample | PRESENT | `paper/sections/05-population.tex` `sec:strong-consistency` (304), `prop:strong-consistency` (314), `rem:support-convention` (355), `rem:limit-scope` (367), `rem:consistency-distinction` (629). |
| 6 | Proved structural theorems and where they do NOT apply, with verified Lean names, exact candidate domains/read model; distinguish population ML, exact finite-sample ML, historical bridging/coverage, MB09 §6.2 flow vs §6.1 product-binomial; no external-stat upgrade | PRESENT with one corrected label | `paper/sections/02-model.tex` `def:likelihoods` (156), candidate classes (214), `rem:2016-vs-rigidity` (128); `paper/sections/03-open-question.tex` `tab:claims` (452); `paper/sections/06-discussion.tex` `thm:reduced-circuit-occurrences` (97). **Defect:** row 1 attributed "kernel-checked" to the genome-level conditional-reconstruction conclusion and named `ConditionalVsOrdinaryMLSeparation` as its endpoint; corrected below. |
| 7 | Sample complexity framed as open; scoped union/Chernoff bound for a finite distinguishable family; limit supplies no finite `n` | PRESENT | `paper/sections/03-open-question.tex` `rem:sample-complexity` (252), `cor:explicit-sample-size` (279), `prop:chernoff-refinement` (311), `rem:chernoff-sharp` (353), `rem:minimax-sample-size` (381); `rem:limit-scope` (367) states the limit gives no finite `n`. |

## Maintained decks

Both decks cover the seven items; the decks are owned by live #265 work
(#327, #335) and were **not** edited by this audit. Independent check:

- `slides/programmers.md`: items 1–7 all present, including Backup B4
  (prior-average vs per-truth monotonicity) and Backup B6 (strong-law limit,
  marked not kernel-checked). Item 6 names the structural endpoints and domains
  and disclaims the MB09 product-binomial surrogate; the phrase "flow
  likelihood"/"§6.1" is implicit rather than named.
- `slides/biologists.md`: items 2, 4, 5, 7 present; items 1 and 3 are
  note-level rather than slide-level, and the explicit start-vs-read-type
  uniformity distinction and the MB09 §6.1/§6.2 naming are absent. These are
  accessible-level omissions, not overclaims; the issue sanctions an analogous
  rebalance rather than byte-for-byte parity. One unqualified line ("Sample
  complexity … remains open") is looser than the deck's own scoped backup, but
  it is inside a deck under active edit and was left to its owner.

## The one bounded increment

`paper/sections/03-open-question.tex` `tab:claims` row 1 (Conditional
reconstruction, Question A) conflated two support classes:

- the **genome-level** claim that the positive-weight feasible fibre is a single
  rotation class is the external 2016 reconstruction premise applied through
  `prop:strong-guarantee-singleton`, explicitly **not** kernel-checked; and
- the **decision-level** claim that, given that reconstruction interface, the
  conditional posterior is `1` and constrained MAP lands in the decoder's orbit
  is kernel-checked in `AssemblyP1.ConditionalIdentifiability`
  (`ReadModel.conditional_posterior_eq_one`,
  `ReadModel.constrained_MAP_mem_orbit`, `ReadModel.feasible_fibre_unique`),
  which **assumes** the external decoder-correctness premise.

The trailing endpoint list named `ConditionalVsOrdinaryMLSeparation` (the
abstract two-hypothesis #271 witness) as row 1's kernel endpoint, which is the
wrong artifact and implied the genome-level singleton result was kernel-checked.
This audit corrects the row's evidence cell, the trailing endpoint list, and the
`prop:strong-guarantee-singleton` status line so the two support classes are
separated and the correct verified endpoint is named. This is a labeling
correction only: no mathematical statement, hypothesis, or conclusion changes,
and no external result is upgraded to Lean. It is consistent with the existing
claim index `docs/verification.md` (Question A row cites
`ConditionalIdentifiability`).

## Not changed / genuinely open

- The general (non-equal-length) finite-ML characterization remains open.
- A sharp uniform sample size over the unrestricted genome universe remains
  open; the finite-family Hellinger/union, Chernoff, and minimax results are
  scoped to explicit families.
- No deck was edited; `docs/remaining-open-matrix-255.md` and the #255 status
  matrix were not touched.

## Validation

- `python3 scripts/check-research-docs.py` — passes.
- Paper build (`sh paper/build.sh`) — see the branch `[terminal-handoff]` on
  board #265 for the exact command and result.
