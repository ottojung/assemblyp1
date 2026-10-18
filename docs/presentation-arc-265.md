# Presentation arc and reconciliation for #265

Status: 2026-10-14, addenda 2026-10-15 and 2026-10-16. Follow-up
correction by agent `757b22c73e75`, branch
`agent/757b22c73e75-issue265-restore-opening`. Base: `main` @ `b0a6e9f` (deck
content unchanged since `22a6233`). The original #265 presentation rebalance
was by agent `74a003ebefb4` on base `157ad34`. The 2026-10-15 addendum by
agent `1da4e6282b15` records that the opening restoration (PR #239) is merged
to `main` as `c8b4b21`, and adds the prior-average / per-truth monotonicity
contrast (required item 4) as backup slides in both decks; see the audit
`docs/audit-265-centering-2026-10-15.md`. A second 2026-10-15 addendum by
agent `7b4df767b5fa` adds the kernel-checked explicit uniform exponential
exact-ML error rate from #281 (primitive-P2 class) to the sample-complexity
backup of both decks, with its caveats; see "What changed" and the claim
table below. A third 2026-10-16 addendum by agent `1c9228ae31b4` adds the
item-5 strong-law/KL limit statement (eventual a.s. exact-ML selection on a
finite identifiable family, with the support convention and the
limit-not-a-finite-n scope) to `paper/sections/05-population.tex`
(`sec:strong-consistency`, `prop:strong-consistency`, classical not
kernel-checked) and to both decks (new backup slides plus one-line main-arc
pointers), with the exact checker
`scripts/verify_strong_consistency_265.py`. A fourth 2026-10-16 addendum by
agent `68d129da714f` mirrors the #268 **two-question narrative** (Question A
conditional / Question B unconditional) in both decks, on base `main` @
`a5b6e77`; the section-by-section mapping and the
paper/claims-matrix/bibliography acceptance checks are in
`docs/deck-arc-consistency-265.md`.

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
- **Strong-law/KL limit statement added to the paper and both decks
  (2026-10-16 addendum by agent `1c9228ae31b4`).** New paper subsection
  `sec:strong-consistency` in `05-population.tex`: for a finite identifiable
  candidate family and iid exact reads, the per-read log-likelihood gap
  converges a.s. to the KL divergence, so the exact-ML selection set is
  eventually exactly the truth's rotation class (rotations tie at every $n$),
  and P(correct at $n$)$\to 1$; the support convention ($0\log 0$, the
  $p_D(w)=0<p_S(w)$ case) is explicit, and the statement is marked as a
  limit that supplies no finite $n$. Label: classical SLLN + KL
  (Durrett 2019; Cover & Thomas 2006), **not kernel-checked**. Decks: new
  backup B6 (`programmers.md`) and backup "The limit is eventual - and gives
  no finite number" (`biologists.md`), plus one-line pointers in the
  programmers' "Do we actually need infinitely many reads?" and the
  biologists' "What if we had infinitely many reads?" slides. Exact checks:
  `scripts/verify_strong_consistency_265.py` (KL identity with exact
  rational coefficients, zero-probability support handling, the
  $a<n(2-\log_2 3)$ decision boundary, the paper's succ($n$) table through
  $n=8$, rotation ties, Hellinger summability). No main-arc slide was
  removed or restructured.
- **Two-question narrative mirrored in both decks (2026-10-16 addendum by
  agent `68d129da714f`).** The #268 refocus separated the 2016 sentence into
  Question A (conditional: restrict to the feasible fiber, a corollary of the
  reconstruction guarantee) and Question B (unconditional: maximize the
  original unrestricted likelihood, the substantive comparison). The
  programmers deck now names both questions at "The 2016 question: does the
  guarantee imply ML?", maps Not-So-Greedy/ordinary ML to A/B at "Why the two
  methods do not contradict each other", retitles the conditional-posterior
  slide to "Question A: what if we are promised reconstruction works?", and
  states the separation in "What the investigation established". The
  biologists deck labels A/B at "But the paper left another question" and
  annotates "Three take-aways". No slide was added or removed; the approved
  #254 opening and the Lean/agent-proof-trust story are unchanged. See
  `docs/deck-arc-consistency-265.md`.
- **Explicit uniform error rate added to both decks (2026-10-15 addendum by
  agent `7b4df767b5fa`).** The kernel-checked primitive-P2 rate from #281,
  `Pr[∃ nonrotational admissible D : L_D ≥ L_S] ≤ N_C exp(-n/(8 B^4))` with
  `B = 2 q^(L-1)` and threshold `n ≥ 8 B^4 log(N_C/δ)`, is now stated in the
  sample-complexity backup of `slides/biologists.md` and in Backup B3 of
  `slides/programmers.md`, together with its caveats (constants deliberately
  loose and exponential in `L`; it bounds exact-ML error probability, not
  likelihood growth; per-truth finite-sample success is not monotone). A
  one-line pointer was added to the programmers' main slide "Do we actually
  need infinitely many reads?" and to the biologists' "Three take-aways" slide.
  No main-arc slide was removed or restructured; the programmer-newcomer
  audience, the 14-slide main arc, and the Lean/agent-proof-trust story are
  unchanged.

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
sources; B6 the strong-law/KL limit (eventual a.s. selection, no finite n).
The biologists deck carries the analogous monotonicity backup and the
"The limit is eventual" backup before its sources slide.

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
| Chernoff refinement `Σ_D exp(-n C(p_S,p_D)) ≤ \|C\| exp(-n C_*)`, `C_* ≥ ln(1/ρ_*)`; `C_*` is the exact finite-family exact-ML error exponent; bound still loose at finite `n` (~3.7× exact at `n=16`) | EXTERNAL (classical Chernoff/Sanov, not kernel-checked) | paper `03-open-question.tex` `prop:chernoff-refinement`, `rem:chernoff-sharp`; note `docs/chernoff-exponent-finite-recovery-265.md`; exact check `scripts/verify_chernoff_finite_recovery_265.py`; kernel-checked constant remains the Hellinger `ρ_*` (`FiniteReadRecovery`) |
| Explicit uniform primitive-P2 exponential exact-ML error rate `N_C exp(-n/(8 B^4))`, `B = 2 q^(L-1)`, threshold `n >= 8 B^4 log(N_C/δ)` | KERNEL | `AssemblyP1/PrimitiveP2UniformSeparation.lean`: `primitiveP2_exponential_error_bound`, `primitiveP2_ML_confidence_explicit`; paper `05-population.tex` `thm:p2-uniform-rate`; caveats: loose constants exponential in `L`, bounds error probability not likelihood growth, per-truth success not monotone; oriented primitive-P2 exact iid only, not universal ML and not the MB09 product-binomial surrogate |
| Sample complexity in this model | OPEN | no theorem in paper or Lean |
| Coverage predicates incomparable | KERNEL | `HistoricalCovers.lean`; `HistoricalCoverageSameLengthWitnesses.lean` |
| `AAATT`/`AAAATT` reversal (backup B1) | KERNEL | ratio `15625/11664`: `OrientedVariableLengthSe62.exact_ratio1`; restricted two-candidate illustration, not a source-faithful counterexample |
| Strong-law/KL limit: on a finite identifiable family the exact-ML selection set is eventually exactly the truth's rotation class a.s.; P(correct at n) -> 1; support convention; limit supplies no finite n | EXTERNAL (classical, not kernel-checked) | paper `05-population.tex` `prop:strong-consistency` (Section `sec:strong-consistency`): SLLN + KL nonnegativity (Durrett 2019; Cover & Thomas 2006); exact mechanism check `scripts/verify_strong_consistency_265.py`; deck backups B6 (programmers) / "The limit is eventual - and gives no finite number" (biologists) |

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

## 2026-10-17 addendum — kernel-checked Bayes/MAP optimality certificate

A fifth addendum by agent `8014c6420218` closes the item-3 "limits and ties"
traceability gap and the item-6 verified-endpoint gap. `paper/sections/03-open-question.tex`
gains `rem:bayes-certificate`: the converse to `thm:bayes-optimal`
(`AssemblyP1.BayesOptimalityCertificate.pointwiseMAP_iff_bayesOptimal`), the
strict-loss non-vacuity, the tie witness (`TieWitness.both_optimal`,
`policies_distinct`), forced choice at a strict maximizer, and the
conditional-posterior-one boundary (`posterior_eq_one_iff_singleton_support`,
with the rotation-class instantiation). `tab:claims` row 2 now cites
`BayesOptimalityCertificate`. The two decks carry a matching one-paragraph
speaker-note refinement (no slide added or removed, the approved #254 opening
and the Lean/agent-proof-trust story untouched): the programmers deck's
"Why no algorithm can beat maximum likelihood in this game" note and the
biologists deck's "Maximum likelihood is simple" note now state that an optimal
rule is exactly pointwise MAP, that ties allow several optimal rules, and that
a strict maximizer forces the unique choice — all prior-averaged, not per-truth.
No overclaim is introduced: the algebraic statements hold for arbitrary real
joint mass, the probabilistic reading substitutes `J = π P`, and zero-mass
samples are handled separately. The genuinely open items are unchanged: the
general (non-equal-length) finite-ML characterization and a sharp uniform
sample size over the unrestricted genome universe.

## 2026-10-18 addendum — Chernoff refinement and the finite-`n` gap

A sixth addendum by agent `df84a657ae4a` sharpens the #265 sample-complexity
statement and records its precise gap. `paper/sections/03-open-question.tex`
gains `prop:chernoff-refinement` (the explicit finite-`n` Chernoff union bound
`Σ_D exp(-n C(p_S,p_D)) ≤ |C_S| exp(-n C_*)`, with
`C(p,q) = sup_{t∈[0,1]} -ln Σ_{w:p(w)>0} p(w)^{1-t} q(w)^t ≥ -ln ρ(p,q)` and
the resulting sufficient sample size `⌈ln(|C_S|/δ)/C_*⌉`) and
`rem:chernoff-sharp` (the exponent `C_*` is the exact large-deviation exponent
of the finite-family exact-ML error — classical Chernoff/Sanov, **EXTERNAL, not
kernel-checked** — while the bound stays loose at finite `n` because of its
prefactor). The `n = 16` worked-family gap (`≈3.7×`, ratio growing `≈√n`) and
the exact-exponent data are in `docs/chernoff-exponent-finite-recovery-265.md`,
checked by `scripts/verify_chernoff_finite_recovery_265.py` and wired into CI.
Both decks' speaker notes (programmers' "Do we actually need infinitely many
reads?" and Backup B3; biologists' "how many reads for 99% recovery?" backup)
carry the refinement and its non-claims; **no slide was added or removed**, the
approved #254 opening and the Lean/agent-proof-trust story are untouched. The
kernel-checked constant remains the Hellinger `ρ_*` of
`AssemblyP1.FiniteReadRecovery`; the Chernoff/large-deviation facts are cited
standard statistics and are **not** upgraded to Lean. The genuinely open items
are unchanged: the general (non-equal-length) finite-ML characterization and a
sharp uniform sample size over the unrestricted genome universe.

## 2026-10-18 addendum — exact finite-`n` numbers in the speaker notes

A seventh addendum by agent `6ec3ab838521` (bounded follow-up to the merged
PR #326 / main `aedc836`) adds the **exact** finite-`n` recovery numbers of
`docs/minimax-finite-recovery-265.md` to the **speaker notes only** of both
decks. For the one explicit finite family of binary read laws
`A=(1/2,1/2)`, `B=(3/4,1/4)`, `C=(1/4,3/4)`:

- uniform-prior Bayes-optimal 99% recovery is `n*=85`
  (`V_84<0.99<=V_85=0.99006833`);
- minimax-over-truths 99% recovery is `n*=87`
  (`error_86=0.01051594>0.01>=error_87=0.00973853`);
- the kernel-checked Hellinger union bound is the conservative **sufficient**
  `153 = ceil(ln(2/0.01)/ln(1/rho_*))`, about `6.4x` the exact per-truth error
  of the middle truth at `n=85`;
- the numbers are **prior-averaged**: at `n=85` the per-truth successes are
  `A=0.983491 < B=C=0.993357` (average `V_85`), so "99% recovery" describes the
  average, not each truth, and per-truth success is not monotone.

The additions are confined to existing HTML speaker-note comments: the
programmers deck's "Do we actually need infinitely many reads?" note (full
statement) and Backup B3 note (pointer); the biologists deck's "Backup: how
many reads for 99% recovery?" note (full statement) and "What if we had
infinitely many reads?" note (pointer). **No slide was added, removed, or
restructured**, the approved #254 opening and the Lean/agent-proof-trust story
are untouched, and the visible slide text is unchanged. Provenance is kept
honest: the exact finite arithmetic is external standard decision theory
(Berger 1985; Lehmann & Casella 1998) checked by
`scripts/verify_minimax_finite_recovery_265.py`, **not** Lean; the only
kernel-checked ingredients cited are the abstract Bayes-optimality of
`FiniteBayesDecision` / `FiniteMapOptimality` and the Hellinger union bound of
`FiniteReadRecovery`. Scope: one explicit finite family under the i.i.d.
read-law model, not the unrestricted genome universe and not MB09. The
genuinely open items are unchanged: the general (non-equal-length) finite-ML
characterization and a sharp uniform sample size over the unrestricted genome
universe.

## Validation

- `cd slides && npm ci && npm run build` — format check, math check, both decks
  built, portal assembled, `validate-dist` OK.
- Both decks pass `scripts/check-format.mjs` and `scripts/check-math.mjs`.
- `python3 scripts/verify_strong_consistency_265.py` — exact-rational checks of
  the strong-law/KL limit mechanism on the `AAC`/`AAAC` witness.
- `python3 scripts/verify_chernoff_finite_recovery_265.py` — exact-rational
  checks of the Chernoff refinement: both union bounds and the termwise
  ordering for `n = 1..16`, the `n = 16` gap ratio (`≈3.7`), `C ≥ -ln ρ`
  (equality symmetric, strict non-symmetric), and the exponent convergence to
  `C_*` through `n = 512`.
- `python3 scripts/verify_minimax_finite_recovery_265.py` — exact-rational
  checks of the tight finite-`n` optima (prior-averaged `n*=85`, minimax
  `n*=87`, per-truth breakdown, the least-favourable prior and tie-split
  certificate, and the conservative Hellinger sufficient `153`).
- Paper build via `paper/build.sh` (Guix): `sec:strong-consistency` compiles
  with 0 LaTeX warnings (2026-10-16 addendum; earlier addenda did not touch
  the paper).
