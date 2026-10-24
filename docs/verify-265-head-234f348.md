# #265 verification review at `main` 234f348 (2026-10-24)

Reviewer: agent-67yPIgjPAuvZorq4GRQ4LH-minutes. Scope: read-only re-verification
of every Required mathematical content item (1-7) and Deliverables framing at
HEAD `234f348`, which postdates audit `docs/audit-265-centering-2026-10-15.md`
(base `2512e06`). No paper/slide source edited: all items were already present.

## Item-by-item evidence at HEAD

1. Read law / likelihood / posterior distinction: PRESENT.
   `paper/sections/02-model.tex` (`def:spectrum`, `rem:cyclic`, `def:reads`,
   `def:likelihoods`, "Uniform start sampling is not uniform read-type
   probability"); `paper/sections/03-open-question.tex` (`sec:two-questions`).
2. Finite-sample surprise with probabilities: PRESENT.
   `paper/sections/03-open-question.tex` (`ex:W1W2`),
   `paper/sections/04-finite-results.tex`
   (`thm:cex-exact`, `thm:cex-binomial`, `thm:cex-historical-W1/W2`);
   intro `ex:ABAB`.
3. Bayes optimality (finite class, uniform prior, zero-one loss, MAP=ML,
   prior-averaged, ties): PRESENT.
   `paper/sections/03-open-question.tex` (`thm:bayes-optimal`, proof,
   rotation-class prior, prior-average caveat, `ex:worked-bayes`,
   `tab:claims`); kernel `AssemblyP1/FiniteBayesDecision.lean`
   (`chooseMAP_optimal`, `chooseMAP_optimal_randomized`).
4. Prior-averaged monotonicity vs per-truth non-monotonicity: PRESENT in paper
   AND decks (closes the audit's single PARTIAL gap).
   Paper `paper/sections/05-population.tex` (`sec:nonmonotone`,
   `prop:nonmonotone`: S=AAC, D=AAAC, L=2, succ(1)=2/3 > succ(2)=4/9, tie
   argument); kernel `FiniteBayesDecision.lean`
   (`chooseMAP_success_monotone_under_refinement`),
   `NonmonotonicityWitness281.lean` (`success_not_monotone`);
   slides `programmers.md` Backup B4 (line ~1069) states the contrast with
   kernel endpoints in speaker notes.
5. Infinite-read consistency (SLLN, KL, identifiability mod rotation, limit not
   infinite product): PRESENT.
   `paper/sections/05-population.tex` (`lem:gibbs`, `thm:population`,
   `rem:consistency-distinction`, `prop:strong-consistency`);
   slides Backup B6; kernel `PopulationGibbs`, `Issue94Complete`.
6. Proved-structural-theorem connection with boundaries (population vs exact
   finite ML, historical bridging/coverage, MB09 §6.2 flow vs §6.1
   product-binomial; no upgrade of external stats to Lean-proved): PRESENT.
   `paper/sections/02-model.tex` (`def:Is`, `rem:historical-coverage`,
   `rem:2016-vs-rigidity`, candidate classes); `sec:two-questions`;
   `cor:conditional-bridging-error`; epistemic ledger
   `paper/sections/b-epistemic-ledger.tex`.
7. Sample complexity as open problem + scoped union/Chernoff bound, limit gives
   no finite n: PRESENT.
   `paper/sections/03-open-question.tex` (`rem:sample-complexity`,
   `cor:explicit-sample-size`); kernel `FiniteReadRecovery.lean`
   (`eventProb_wrong_le_card`, `il_confidence_99`); slides Backup B3;
   `docs/sample-complexity-265.md`.

## Independent validation run at HEAD (this review)

- `python3 scripts/verify_nonmonotonicity_witness_281.py` -> OK
  (succ(1)=2/3 > succ(2)=4/9, no positive-probability ties for 1<=n<40).
- `python3 scripts/verify_strong_consistency_265.py` -> OK
  (rho=0.985599<1, Borel--Cantelli cross-check, rotation ties).
- `python3 scripts/verify_sample_complexity_265.py` -> PASS (n=33 worked
  example, union bound n=1..14, `il_confidence_99` n=55).
- `python3 scripts/verify_chernoff_finite_recovery_265.py` -> PASS
  (exact-vs-bound ratio ~3.7 at n=16 as recorded).
- `python3 scripts/check-research-docs.py` -> passed.
- `node slides/scripts/check-math.mjs` -> OK; `check-format.mjs` -> OK.
- `sh paper/build.sh` -> `main.pdf` up-to-date (no rebuild needed, no error).

## Remaining open (not changed by this review)

- Main-deck length vs #254 target: `slides/programmers.md` carries ~31 `#`
  section headers / 34 `---` separators before the backup section (line 887),
  against the agreed ~12-14-slide programmer-newcomer target. The earlier audit
  states "14 main slides + backups", which does not match the current file;
  reconciling length without discarding the approved arc is an owner scope
  decision for #254, not a unilateral cut. Left untouched.
- Genuinely open mathematics per the audit: general non-equal-length ML
  characterization; sharp uniform sample size over the unrestricted universe;
  same-length strict reversal under the historical predicate at full
  generality; final #268/#255 claim-label reconciliation.
- Issue stays open; no unproved rate claimed; no external statistic presented
  as Lean-proved.
