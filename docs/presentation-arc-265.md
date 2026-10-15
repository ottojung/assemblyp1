# Presentation arc and reconciliation for #265

Status: 2026-10-14, addendum 2026-10-15. Follow-up correction by agent
`757b22c73e75`, branch `agent/757b22c73e75-issue265-restore-opening`. Base:
`main` @ `b0a6e9f` (deck content unchanged since `22a6233`). The original #265
presentation rebalance was by agent `74a003ebefb4` on base `157ad34`. The
2026-10-15 addendum by agent `1da4e6282b15` records that the opening
restoration (PR #239) is merged to `main` as `c8b4b21`, and adds the
prior-average / per-truth monotonicity contrast (required item 4) as backup
slides in both decks; see the audit `docs/audit-265-centering-2026-10-15.md`.

This note records (i) the revised presentation arc, (ii) the claim labels and
exact project endpoints behind every nontrivial slide claim, (iii) where the
negative finite-sample examples now live, and (iv) the reconciliation of #265
and #268 against the current merged whitepaper. It does not declare any open
problem settled.

## What changed

- **Opening restored (follow-up correction).** The recentered programmers deck
  had altered the user-approved opening. The frontmatter and first three slides
  (`The Most Likely Genome`, `How can we reconstruct a genome?`, `What makes
  assembly difficult?`) are restored byte-for-byte from the approved `#254`
  commit `7aba5d0`. The improved overlap traversal becomes slide 4; the now
  redundant standalone repeat-obstacle slide is removed. No other slide,
  speaker note, claim, or backup is weakened. See "Preserving the approved
  opening" below.
- `slides/programmers.md` — rewritten to a **positive, operational** main arc
  (14 slides) plus four backup slides. The distinct 2016 read-overlap
  Not-So-Greedy graph is restored to the main narrative; the finite reversal is
  a single short aside (slide "A finite aside: even the truth can lose") and
  the full calculation moves to backup B1. Bayes-optimal ML is the entrance,
  not the headline. The founding-agent narrative, orchestration diagram, and
  Lean/kernel-trust story are preserved (two slides plus notes; the coverage
  audit is backup B2).
- `slides/biologists.md` — rebalanced to the same positive arc at an accessible
  level: sequencing model, overlaps and bridging, the 2016 read-overlap graph,
  likelihood, a single "decoy can win" aside, population maximality and
  identifiability, and the restricted finite positive theorem. The two former
  consecutive negative slides are merged into one aside; the extra
  "sample change" and "tie" slides are merged.
- `slides/README.md` — deck descriptions updated to match.

No paper file is changed by this branch. The whitepaper was already recentered
by the merged PR #189 and the #268 revisions (see "Reconciliation" below).

## Revised programmers' main arc (14 slides)

| # | Slide | Idea |
|---|-------|------|
| 1 | The Most Likely Genome | title / framing |
| 2 | How can we reconstruct a genome? | circular genome, independent uniform-start fixed-`L` reads |
| 3 | What makes assembly difficult? | repetition, ambiguous short reads, repeat bridging |
| 4 | Reconstruction from overlaps: a worked traversal | suffix/prefix overlaps; didactic de Bruijn traversal spelling `ACGTA` |
| 5 | The 2016 algorithm uses a different graph | read-overlap graph: vertices are reads, greedy + first disagreeing extension, spurious/transitive pruning, multiplicities, unique Eulerian spelling |
| 6 | The 2016 open question | reconstruction conditions `?=>` truth is a maximum-likelihood genome |
| 7 | Every genome predicts a distribution | `P_G(w) = starts(w)/G`; likelihood vs posterior; uniform starts ≠ uniform read strings |
| 8 | Why ML is worth studying | finite Bayes entrance; prior-averaged zero-one optimality |
| 9 | Positive structural result | same-length rigidity and rotation uniqueness |
| 10 | A finite aside: even the truth can lose | exact same-length finite witness; non-monotone per-truth success |
| 11 | Population level: identifiability | KL maximality, primitive-P2 uniqueness, limiting consistency |
| 12 | Agents were present from day one | founding narrative + orchestration diagram |
| 13 | What Lean is | Curry–Howard, kernel, axiom audit, model-fidelity caveat |
| 14 | Trust the check, not the claim | hierarchy: ML is the entrance; classification is the contribution |

Backups: B1 complete finite reversal; B2 incomparable coverage definitions;
B3 open sample-complexity (Hellinger bound); B4 prior-average monotonicity
versus per-truth non-monotonicity (`succ(1)=2/3 > succ(2)=4/9`); B5 primary
sources. The biologists deck carries the analogous monotonicity backup before
its sources slide.

## Preserving the approved opening

The first three slides of the programmers deck were approved in the `#254`
review and merged at `7aba5d0`. That board review (reviewer
`independent-reviewer@5c6bda33c7ed`, 2026-10-14, about `7aba5d0`) records:
"First three slides byte-for-byte identical to main (empty diff of lines 1-74;
frontmatter title 'The Most Likely Genome' preserved)." The `#265` board finding
(`research-assistant`, 2026-10-14, comments at 05:09 and 05:14) reports that the
`#265` recentering (commits `91e34e4`, `22a6233`) altered them: slide 3 changed
from `What makes assembly difficult?` to `Reconstruction from overlaps: a worked
traversal`, the slide 1 and slide 2 speaker notes were rewritten, and the
frontmatter `info` line changed. This follow-up restores `slides/programmers.md`
lines 1–74 (frontmatter, the three approved slides, and the trailing separator)
byte-for-byte from `7aba5d0`; `diff` of those ranges is empty. Slides 4–14 and
backups B1–B4 are otherwise unchanged from `main`, so the only non-opening body
content removed is the standalone `The repeat obstacle` slide, which is redundant
with the restored slide 3.

`slides/biologists.md` was checked the same way. Its first three headings
(`Which genome is most likely?`, `A sequencer takes a sample`, `Overlaps help.
Repeats confuse.`) are unchanged; only the slide 1 speaker note and one slide 2
body line (adding "oriented … and independent") were refined. The `#254` board
record and the `#265` findings name the programmers deck only; #265 explicitly
sanctioned an analogous biologists rebalance. This correction therefore leaves
the biologists deck as merged rather than asserting a byte-for-byte constraint
that no tracked record states.

## Claim labels and endpoints

Labels: **KERNEL** (checked in Lean at the cited file/theorem), **SOURCE**
(stated by the cited primary source), **EXTERNAL** (standard statistics cited to
a textbook; not proved in Lean here), **COMPUTED** (exact rational certificate),
**OPEN**.

| Slide claim | Label | Endpoint / citation |
|---|---|---|
| Uniform-start fixed-`L` read model | SOURCE | Shomorony et al. 2016, §2 |
| de Bruijn traversal of `ACGTA`, `L=3` | SOURCE / teaching | paper `01-introduction.tex`, §"From reads to a graph algorithm" |
| Distinct 2016 read-overlap graph and unique Eulerian spelling | SOURCE | Shomorony et al. 2016, Thm 1 + supplement (DOI 10.1093/bioinformatics/btw450) |
| `P_G(w)=spec_L(G)(w)/|G|`; starts ≠ strings | SOURCE + EXTERNAL | paper `01-introduction.tex` `ex:ABAB`, `02-model.tex` |
| Likelihood vs posterior vs sampling process | EXTERNAL + project note | standard Bayes; paper `02-model.tex` |
| ML maximizes prior-averaged zero-one success (finite set, uniform prior) | KERNEL | `AssemblyP1/FiniteBayesDecision.lean`: `chooseMAP_optimal`, `chooseMAP_optimal_randomized`, `finite_iid_MAP_optimal` |
| Prior-average success nondecreasing in `n` | KERNEL | `AssemblyP1/FiniteBayesDecision.lean`: `chooseMAP_success_monotone_under_refinement` |
| Per-truth success not monotone in `n` (no per-truth monotonicity claimed) | KERNEL + EXTERNAL | paper `05-population.tex` `prop:nonmonotone`; `AssemblyP1/NonmonotonicityWitness281.lean`: `success_not_monotone`; exact check `scripts/verify_nonmonotonicity_witness_281.py`; backup slide B4 (programmers) / monotonicity backup (biologists) |
| Same-length rigidity + rotation uniqueness | KERNEL | `OrientedRigidity.unique_positive_circulation`; `SameLength62Uniqueness.unique_62_maximizer_up_to_rotation` (unconditional rotation endpoint); `OrientedFinal.oriented_same_length_spectrum_rigidity`; `OrientedFinal.rotation_uniqueness_of_bbt` (conditional on the unproved external BBT premise) |
| Graver-basis rigidity iff | KERNEL | `GraverRigidity.rigid_iff_forall_graver_not_feasible` |
| Same-length finite witness `AAATAT`/`AAAAAT` (exact 3, binomial 5) | KERNEL | `SameLengthSection62Counterexample.samelength_se62_bidirected_flow_counterexample` |
| Historical source-predicate witnesses | KERNEL | `AssemblyP1.HistoricalCoverageSameLength.W1.w1_historical_literal_se62_flow_counterexample`, `w1_historical_maximality_refuted` |
| Population maximality (Gibbs/KL) | KERNEL | `PopulationGibbs.popLogLik_le_self'`; equality `PopulationGibbs.popTie_iff` |
| Population uniqueness up to rotation (primitive, P2, admissible class) | KERNEL | `Issue94Complete.population_unique_ML` |
| Limiting consistency / `P(correct at n) -> 1` | EXTERNAL | standard SLLN + ML consistency (Lehmann & Casella 1998); not kernel-checked here |
| Hellinger/union `99%` bound | EXTERNAL | Tsybakov 2009, Thm 2.4; not kernel-checked here |
| Sample complexity in this model | OPEN | no theorem in paper or Lean |
| Coverage predicates incomparable | KERNEL | `HistoricalCovers.lean`; `HistoricalCoverageSameLengthWitnesses.lean` |
| `AAATT`/`AAAATT` reversal (backup B1) | KERNEL | ratio `15625/11664`: `OrientedVariableLengthSe62.exact_ratio1`; restricted two-candidate illustration, not a source-faithful counterexample |

## Negative-example disposition

- Main decks: exactly one short aside (programmers' slide 10; biologists' "A
  finite aside: the decoy can win").
- Full `AAATT`/`AAAATT` calculation: programmers' backup B1.
- Source-faithful same-length witness: main aside plus the paper's Theorems
  `thm:cex-historical-W1/W2`.
- No deck leads with a negative result or claims ML is invalid.

## Reconciliation of #265 and #268 with the current paper

The current `main` whitepaper already carries the required arc; this branch does
not modify it.

- Abstract: positive-first, ML framed as benchmark/motivation that "does not
  answer the assembly-specific question" (`paper/main.tex`).
- `01-introduction.tex`: genome → reads → de Bruijn teaching graph → the
  **distinct** 2016 read-overlap graph → bridging → the maximum-likelihood
  question with the Bayes entrance → conditional vs unconditional questions →
  contributions labelled motivation/positive/negative/general/population.
- `03-open-question.tex`: Bayes-optimality theorem with explicit limits
  (prior-averaged, not per-truth; not arbitrary loss; binomial is not exact
  Bayes ML), prior-average monotonicity remark, five-notions table, and the
  sample-complexity remark with the scoped Hellinger bound.
- `04-finite-results.tex`, `05-population.tex`, `06-discussion.tex`: the
  positive rigidity, finite counterexamples, population uniqueness, and the
  open problems.

Conclusion: #265's paper-side requirements are satisfied by the merged #189/#268
work; the remaining #265 work was the presentation rebalancing recorded above.
This branch keeps Bayes-optimal ML as the entrance and does not present an
ML-supremacy pitch.

## Validation

- `cd slides && npm ci && npm run build` — format check, math check, both decks
  built, portal assembled, `validate-dist` OK.
- Both decks pass `scripts/check-format.mjs` and `scripts/check-math.mjs`.
- Paper not rebuilt on this branch (unchanged); LaTeX toolchain is provided by
  `paper/build.sh` via Guix.
