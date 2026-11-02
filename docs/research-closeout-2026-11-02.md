# AssemblyP1 research closeout — 2026-11-02

## Decision

The v1.6.6 white paper is a finished first research publication.
**Do not reopen active mathematical research or spawn AssemblyP1 agents to
clear a backlog.** The open questions in
[the paper, §6](../paper/sections/06-discussion.tex) are future-work proposals,
not prerequisites to the published conclusions. Formalization of an already
proved paper-level theorem is a distinct verification project, not evidence
that the theorem is currently an unsupported assumption.

## Disposition of the five remaining GitHub issues

| Issue | Disposition | Paper referent |
| --- | --- | --- |
| [#420](https://github.com/ottojung/assemblyp1/issues/420): Lean-check rational-potential ML certificates | **Defer** end-to-end Lean formalization; exact arithmetic checks and the paper proof are already integrated | Further formal verification after Q1–Q9 |
| [#421](https://github.com/ottojung/assemblyp1/issues/421): balanced-flow spelling | **Defer** source-faithful physical/bidirected realization; distinguish the settled paper-level connected integral oriented criterion | Q3–Q4 |
| [#422](https://github.com/ottojung/assemblyp1/issues/422): physical reverse-complement correspondence | **Defer** model/source mapping; the integrated strand-collapsed primitive-P2 counterexample does not prove the historical MB09 correspondence | Q2, Q4, Q6 |
| [#423](https://github.com/ottojung/assemblyp1/issues/423): primitive-P2 recovery exponent | **Complete** sharp order Θ(1/B) at paper level; defer best constant, extremizer classification and Lean formalization | Q5; Further formal verification |
| [#424](https://github.com/ottojung/assemblyp1/issues/424): bridging threshold vs ML/MAP threshold | **Defer** joint high-probability reconstruction/statistical reliability theorem | Q8 |

## Non-issue work audited

- **Manuscript/publication:** The signed `paper-v1.6.6` release contains a
  downloadable PDF. The paper has a reproducibility appendix containing
  the dynamic source-commit URL, not a title-page link. No new mathematical
  proof is needed to validate the publication.
- **Other paper questions:** Q1 (general classification), Q7 (minimal
  sufficient certificate), and Q9 (sharp unrestricted branching rates)
  remain mathematical future work; none is an actionable release blocker.
  Q5 concerns sharp constants, **not** the already proved Θ(1/B) order.
- **Formalization and proof-status ledger:** Preserve explicit distinctions
  between Lean-kernel-checked results, mathematical paper proofs, external
  theorems, scripts, and genuinely open model correspondence. The verification
  index already records the relevant limitations, including external weighted
  BEST arithmetic in the full fibre count.
- **Slides and documentation:** Presentation and PDF build pipelines are
  present; no new publication-critical content change was identified in
  this closeout. These are not a mandate to restart agent work.
- **Branches:** A snapshot showed 1,095 remote branches, largely historical
  agent/research branches, with no open PRs. Branch garbage collection is
  optional repository maintenance, *not* mathematical unfinished work.
  Do not cherry-pick old exploratory branches merely to reduce their count.
- **Agent and board state:** The local `antonina agent list --running`
  snapshot on `marceline-dev` reported no running agents. The repository
  reports that AssemblyP1 board issues were closed, but a fresh board-list
  query returned a board-pointer/credential mismatch; this audit therefore
  does **not** independently certify their live board state. That access
  problem is not a reason to reopen AssemblyP1 research.

## Future priority, if research is explicitly reopened

1. **Highest scientific value:** establish source-faithful physical
   reverse-complement/flow/spelling semantics (Q2–Q4, Q6).
2. **Next:** relate bridging sample thresholds to a well-defined
   length-restricted ML or length-prior MAP estimator (Q8).
3. **Optional refinements:** Q1, Q5, Q7, Q9, and the separate Lean
   formalization backlog.

This document records disposition, not a schedule to start these tasks.
