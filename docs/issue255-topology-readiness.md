# Issue #255 topology readiness — 2026-10-27

## Repository and board state checked

The verified repository is `https://github.com/ottojung/assemblyp1`; the
checkout used for this review is the isolated
`/workspace/assemblyp1-agent-5JYzakCUmDnWBh5Ciahq8h-issue255` clone. Its
`origin/main` at review time is `3decc39b4f8b5e187dc3df1b8c56720b4615045a`
(merge PR #405). The newest local board comment available was
`board-comment-255-491a5de6e543.md`; it records the preceding handoff as
awaiting human review, but is dated before the merged #405 changes. GitHub
remote refs and current `origin/main` were independently fetched and inspected.

## Topological readiness

The #255 work graph is **partially ready, not closure-ready**:

* Current `main` already includes the signed exact-cell branch through PR #405.
  `docs/issue255-fixedx-loss-ratio.md` on `main` records the exact fixed-sample
  ratio `243/64` for `AAABBB` versus `AABBBB`; the matrix records the bounded
  64-genome enumeration and scopes it as evidence, not a general theorem.
* The robust branch
  `agent/z51GSYwbsBHMMG19AocOLT-robust-issue255` at
  `74b557f6de7e1d4875eaddc1490c859fdcaef350` contains the same witness and
  census, but claims ratio `16` and uses candidate `BB=4`. Inspection of
  circular `AABBBB` gives spectrum `(AA,AB,BA,BB)=(1,1,1,3)`, so its actual
  ratio is `3^5/2^6=243/64`, not `16`. The current main note is correct; the
  robust branch is stale and should not be integrated.
* The separate matrix branch
  `agent/67ddc161868f/issue255-integrate-matrix` changes only the matrix and
  does not carry the fixed-x witness. Its matrix snapshot predates current
  main and retains superseded statements (for example, it describes the iid
  all-full-start-covered classification as open while current main records
  the later kernel-checked result). Cherry-picking it wholesale would regress
  the record; reconcile against current main first.
* Consequently, no new branch or PR is needed for this bounded issue: the
  substantive fixed-x witness and its corrected exact ratio are already
  integrated. #255 and general fixed-x classification remain open. The frozen
  distinctions (orientation/RC, exact multinomial/fixed-N binomial, lengths,
  spelled genomes/§6.2 flows and overlap floor, truth candidacy, and the two
  `I_s` readings) remain essential to any next child-front work.

## Verification performed

* Confirmed `origin/main` and both unmerged remote branch refs by fetch and
  remote-ref inspection.
* Read the merged fixed-x note and compared its spectrum and ratio directly
  with the candidate `AABBBB` cyclic word.
* Confirmed the candidate matrix branch does not contain the witness text and
  is based on a stale matrix snapshot.

This is a topology/reconciliation diagnostic, not a proof of the umbrella
classification and not grounds to close #255.
