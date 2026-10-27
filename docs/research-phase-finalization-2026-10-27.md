# AssemblyP1 research-phase closure ledger — 2026-10-27

This records the **disposition of existing research work**, not the completion of
every originally proposed mathematical proof. On final publication, unfinished
proof attempts become the explicit open questions in
`paper/sections/06-discussion.tex` (§ *Open questions after the proved results*).
A board issue can be closed as **research phase finalized**, without asserting
its original universal conjecture was proved. For primary theorem hypotheses and
proof-level provenance, see `docs/verification.md` and the white paper's
epistemic ledger.

## What is established

- **Finite decision theory:** finite-sample MAP maximizes prior-average
  zero-one reconstruction success; uniform-prior rotation-class MAP agrees
  with ML. Bayes-value monotonicity is an *averaged* statement, not per-truth
  monotonicity. See `FiniteBayesDecision.lean`,
  `BayesOptimalityCertificate.lean`, and `IidMapMonotonicity.lean`.
- **Finite counterexamples:** exact ML can favor an incorrect genome; the
  oriented length-5/length-6 and reverse-complement examples have different
  read-type models and must not be conflated. The historical matched-string
  bridges admit kernel-checked strict counterexamples in their stated model.
  The newly integrated AAC versus AAAC two-candidate computation illustrates
  sampling reversal and a drop in *per-truth* success from 2/3 to 4/9;
  it is a rational verifier, not an additional Lean theorem.
- **Positive restricted results:** oriented complete-spectrum rigidity on
  the specified same-length admissible class; primitive-P2 oriented
  population uniqueness up to rotation; exponential finite-sample recovery
  in finite identifiable families and the full bounded primitive-P2
  oriented class, with conservative explicit rate.
  See `OrientedFinalRigidity.lean`, `Issue94Complete.lean`,
  `PrimitiveP2FiniteClass.lean` and `PrimitiveP2UniformSeparation.lean`.
- **Optimization and graph lemmas:** precise Graver/circulation
  certificates, fixed-$N$ effective-weight criteria, spelling identities
  for specified overlap reductions, signed/physical count-vector
  transport under stated hypotheses, and the kernel-checked KKT derivative
  refutation from merged PR #407. None is a blanket equivalence for the
  historical reverse-complement Section 6.2 graph.
- **Proof levels are not interchangeable:** all claims in the main text
  and verification index must distinguish checked Lean endpoints, paper
  proofs, finite exact computations, classical external theorems, and
  the published Not-So-Greedy reconstruction theorem taken as a premise.

## Disposition of the Antonina research issues

The table gives the final research-phase status to be reported **when the
white paper is merged and published**, not a claim that issue closure has
already happened.

| Board issue | Established material to retain | Unfinished direction in paper |
|---|---|---|
| #255 — general finite likelihood | Fixed-sample witnesses; restricted iffs and objective-order transformations | **Q1**: general exact finite-sample classification |
| #257 — rigidity beyond repeat bounds | Concrete rigidity and Graver certificates, scoped structural results | **Q2, Q3**: source-faithful model and sufficient realizability hypotheses |
| #259 — MB09 binomial likelihood | Effective-weight criteria, scoped dominance and exact witnesses | **Q1**: broader source-faithful all-observations classification |
| #261 — bidirected flow maximality | Flow/spelling and physical-objective statements under their hypotheses | **Q2–Q4**: source correspondence, realizability and optimizer transport |
| #263 — separable convex Graver | Discrete convex/Graver certificates; merged #407 KKT boundary | **Q4**: full historical admissible-flow/ML equivalence |
| #265 — paper/decks finite inference | Finite counterexamples, proof status, sample-reversal illustration | Editorial deliverable; open math cross-referenced to **Q1, Q5–Q7** |
| #268 — Bayesian/ML framing | Bayes/MAP optimality under specified prior, loss and model | Editorial deliverable; distinguish **Q7** conditional posterior |
| #269 — finite MAP optimality | Finite MAP/certificate, orbit quotient under stated invariance | Completed scoped theorems; **Q7** is a different minimal-certificate question |
| #271 — conditional vs ordinary ML | Conditional posterior statements plus separation witnesses | **Q7**: exact conditions for ordinary ML to inherit guarantees |
| #272 — minimal side information | Abstract posterior-support and concrete adapter/witness results | **Q7**: minimal historical read-string decoder certificate |
| #281 — exponential finite recovery | Hellinger/finite-family bounds and primitive-P2 bound | **Q5**: sharp primitive-P2 asymptotic exponent |
| #284 — transitive reduction/spelling | Checked spelling counts for specified graph reductions | **Q2–Q4**: physical-source equivalence and realizability |
| #300 — small finite counterexamples | Kernel-checked short finite ML examples; exact verifiers | No additional theorem assumed necessary for this phase |

## Closure procedure

1. Stop dispatching *new proof tasks* for these issues. Do not discard signed
   partial work or upgrade it to a theorem.
2. Merge a GPG-signed final publication PR only after required checks pass:
   full Lean build, kernel replay and axiom audit, documents/PDFs, slides,
   source/document validators.
3. On every listed Antonina issue, append a short terminal note linking the
   merged publication and referencing the applicable open question(s);
   close each issue as **finalized, not mathematically solved**.
4. Close the dedicated Antonina finalization issue
   `#TkyTXmJpMW5j5T750JoWVt-coli` **last**.
5. Confirm the PDF release points to the final merged `main` commit and
   verify board and GitHub open-issue/PR counts. Other projects are out of scope.

GitHub tracking issue: #408. This ledger is a snapshot for the
finalization process; if later source review finds a narrower or stronger
precise theorem, update the paper and the relevant cell, not the proof status
by inference from old board comments.
