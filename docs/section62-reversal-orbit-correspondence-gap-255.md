# Reversal-orbit source-model correspondence: precise remaining gap (#255/#261 front)

_Status: gap-pinning note at `origin/main` `f338cdfe34442d6bc1767e59c577b284d60d66a3`
(2026-10-17). The #295 source-fidelity blocker is **OPEN**. This note records exactly
which lemmas merged work delivers and which correspondence lemma remains unproved.
It changes no merged claim and edits no classification._

## The question

PR #295 (head `dc6419d1481475aee04ad9db45195ce12b61851d`, OPEN, blocked) claims a
"corrected MB09 §6.2 source model" via explicit orientation tags
(`OStrand W = W × Bool`, `AssemblyP1/Section62OrientedStrandFlow.lean`). Reviewer
objections (PR #295 comments `6226733092`, `626803094`, `627270544`, all
2026-10-16/17): MB09 §1.1/Fig. 1 identify **three** bidirected endpoint-orientation
edge types up to symmetry, while the tagged model enumerates **four** ordered
orientation pairs as distinct `BdEdge` values; and the inherited departure-based
`throughput` is not invariant under reverse-complement edge reversal.

## What merged work delivers (the two lemmas)

1. **The 4-versus-3 count divergence is kernel-checked.** On the ATAT self-palindrome,
   the four ordered tagged edges fall into exactly three bidirected reversal orbits:
   `AssemblyP1/Section62PalindromeEdgeMultiplicityAudit.lean:277`
   (`tagged_three_reversal_orbits`), with the involution at `:224`
   (`reverseTaggedEdge`), the swap/fix pattern at `:229`/`:237`, and orbit
   canonicity at `:266`. Merged via PR #282 (merge `aa24b18`, branch
   `research/284-palindrome-edge-multiplicity-20261016`), integrated by PR #296
   (`c56166b`), root-imported at `AssemblyP1.lean:70`. This is a finite comparison
   model only: the module docstring (`:216-222`) states it "is not a theorem that
   the complete historical algorithm uses this particular quotient".

2. **Half-incidence invariance and departure non-invariance are kernel-checked.**
   `AssemblyP1/Section62PhysicalHalfIncidence.lean:55` (`posHalf_reverse`) and
   `:60` (`negHalf_reverse`) prove per-class positive/negative signed half-edge
   incidences are separately invariant under `reverseEdge` (`:44`); `:80`
   (`sample_departure_failure`) witnesses that the legacy departure count is NOT
   invariant. Merged via PR #300 (merge `f338cdf`). This module is not
   root-imported (absent from `AssemblyP1.lean`).

## The precise remaining lemma (OPEN)

The blocker is not the two lemmas above; it is the correspondence and transport
layer, none of which exists on `main`:

- **L1 (correspondence).** An orientation-preserving correspondence between the
  reversal-quotient of the tagged overlap edges and MB09's physical bidirected
  edge set (§6.2, Fig. 1), preserving edge multiplicity and signed self-loop
  incidence. Explicitly disclaimed at
  `AssemblyP1/Section62PalindromeEdgeMultiplicityAudit.lean:221`,
  `docs/section62-palindrome-edge-multiplicity-audit-284.md` ("does not prove that
  every edge quotient in their full algorithm follows this exact construction";
  "A future source-faithful result must specify the intended multiplicity
  convention (including palindrome incidences) and prove the appropriate mapping
  from one flow domain to the other"), and
  `AssemblyP1/Section62PhysicalHalfIncidence.lean:8-11`.
- **L2 (flow transport).** A flow discipline on quotient orbits: either a
  requirement `f e = f (rev e)` on tagged edge values, or flow defined directly on
  quotient edge orbits, with a proof that the physical feasible set is unchanged.
  On `main`, `BdFlow : BdEdge → ℕ` (`AssemblyP1/Section62BidirectedFlow.lean`)
  still assigns independent multiplicities to reversal-equivalent edge values; no
  such requirement or quotient-flow definition exists.
- **L3 (throughput invariance).** The exact reversal-invariance/visit-count
  correspondence on edge orbits: the total positive half-edge incidence at a
  vertex (`posHalf`, `AssemblyP1/Section62PhysicalHalfIncidence.lean:33`) equals
  the legacy departure throughput on the quotient, with `Feasible62` revisited
  under this definition. On `main`, `throughput`
  (`AssemblyP1/Section62BidirectedFlow.lean:293`) remains departure-based;
  `Feasible62` (`:404`) and the count-vector adapter
  (`AssemblyP1/Section62FlowCountVectorAdapter.lean:74`, `throughputVec`) inherit
  the non-invariant definition; `posHalf`/`negHalf` are not wired into either.

## Verdict

**OPEN.** Merged work (#282/#284 audit, #300 half-incidence) resolves the count
question and the invariance lemma, but the #295 source-fidelity blocker — the
orientation-preserving correspondence to MB09's physical graph together with the
quotient-flow discipline and the `Feasible62`/throughput revisit — is not resolved
at `origin/main` `f338cdf`. PR #295 (`dc6419d`) remains blocked; per reviewer
comment `627270544` it should be read as a bounded tagged-model experiment until
L1-L3 are proved or the model is retitled a tagged representation candidate.
