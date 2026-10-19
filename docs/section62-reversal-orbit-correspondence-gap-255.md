# Reversal-orbit source-model correspondence: precise remaining gap (#255/#261 front)


## Update — 2026-10-18: the first L2 disjunct is REFUTED (kernel-checked)

The L2 flow-transport discipline below offered two alternatives: (a) require
`f e = f (reverseEdge e)` on tagged edge values, or (b) define the flow directly
on quotient edge orbits, "with a proof that the physical feasible set is
unchanged". Alternative **(a) is refuted** by
`AssemblyP1.Section62ReversalOrbitTransport` (kernel-checked, no
`sorry`/`admit`/`axiom`/`native_decide`, axioms `⊆ {propext, Quot.sound}`):

* `throughput_pair_selfloop` — for a self-loop `e` and any flow `f`,
  `throughput cls f [e, reverseEdge e] v = f e + f (reverseEdge e)`;
* `throughput_pair_selfloop_symm` — for a reversal-symmetric flow the inherited
  departure throughput is `2 * f e`, hence **even**;
* `no_revsymm_flow_realizes_unit_loop` — no reversal-symmetric oriented flow
  realizes the physical visit count **one** of the unit mixed-sign loop orbit;
* `mixed_physical_visit_one` — the quotient model (`physPos` on `PhysEdge`)
  *does* realize it, by representation invariance of `posHalf`/`negHalf`.

The **smallest witness** is the length-`1` mixed-sign self-loop `mixedLoop` on
`Tagged Bool` (`AssemblyP1.Section62PhysicalHalfIncidence`), not the length-`4`
`ATAT` palindrome. So the `f e = f (rev e)` symmetrization does not leave the
physical feasible set unchanged; the correct route is alternative (b), the
quotient-orbit flow already merged in `Section62PhysicalEdgeOrbit`.

**Still OPEN (L1).** The quotient model is *not* yet identified with MB09's
physical RC overlap multigraph (edge multiplicity, transitive-reduction
contract). Reversal-orbit transport of *incidences* is settled; the source-graph
correspondence is not.

Independent exact-integer verifier:
`scripts/verify_261_reversal_orbit_transport.py` (86 assertions, exit 0).

## Update — 2026-10-19: the L3 objective transport is landed (kernel-checked)

The **L3 remainder** ("the exact ML objective is not yet transported to physical
orbit totals") is now settled at the level of the objective argument and the
maximality reduction. `AssemblyP1.Section62PhysicalOrbitObjective` (with
`AssemblyP1.Section62PhysicalOrbitObjectiveAudit`) defines the physical
visit-count / read-copy vector `physVisitVec` on physical orbit totals, proves it
is representative-invariant (`physVisitVec_reverse`), additive over orbit-flow
decomposition (`physVisitVec_add`), transports the §6.2 vertex lower bound
(`PhysVertexBound`, `physVertexBound_reverse`), and transports the
flow-to-count-vector reduction `physMaximal_image_iff` (plus
`physMaximal_reverse_iff`). On the length-`1` mixed-sign self-loop witness the
physical visit count is `1` while the induced oriented departure throughput is
`2` (`Witness.mixed_physical_ne_departure`), so the transport is not vacuous.
Axioms `⊆ {propext, Quot.sound}`; no `sorry`/`admit`/`axiom`/`native_decide`.
Scoped note: `docs/issue261-physical-orbit-objective.md`.

**Still OPEN: L1 only.** The quotient edge set is not yet identified with MB09's
physical RC overlap multigraph (edge multiplicity, transitive-reduction
contract), and no physical orbit flow is identified with a single circular
spelled genome.


## Updated status — 2026-10-17 (supersedes the historical snapshot below)

At current `main` after PR #307, the **abstract orbit flow discipline and
representation-invariant incidence algebra ARE formally implemented**:
`AssemblyP1.Section62PhysicalEdgeOrbit` defines a reversal Setoid quotient
of tagged signed edges, physical positive/negative half-incidence functions,
and edge-orbit-indexed visit/flow totals. The `ATAT` witness kernel-checks
three orbits and a mixed-sign loop with one physical visit; blindly copying
the orbit flow onto both oriented representatives yields inherited departure
throughput TWO rather than one. Different overlap lengths remain distinct.

Consequently the old statement below, "no quotient-flow definition exists on
main", is a **historical fact at f338cdf, not a current open lemma**.
Likewise, MB09 Observation 7 for genuine closed signed circuits of the
repository's *implemented* spelling-preserving reduction has already been
kernel-proved in merged PR #265, via
`AssemblyP1.Section62GlobalSkippedBridge.observation7_reduced_signed_circuit_range_count`.
The idealized same-spelling two-hop reduction equivalence is also merged in
`Section62MyersIdealTransitivity`.

**Actual remaining gaps:** (i) identify the constructed quotient edge IDs,
including genuinely parallel edges, with MB09's **physical** RC overlap
multigraph and its transitive-reduction contract; (ii) transport source
vertex-splitting bounds, read-copy counts, and the exact ML objective to
those physical edge-orbit flow totals; (iii) transport repo Observation 7
across the source model and justify any contig/single-genome Eulerian
realizability hypotheses. Reversal quotient alone does not give these.

PR #304 (merged as content through signed PR #313, merge `23881843a`)
is an intentionally *experimental tagged-overlap* theorem about RC reversal
and three palindrome edge orbits; its older departure-based feasible-flow
domain is explicitly **not** a faithful physical MB09 model.
Do not conflate the already-merged #307 physical edge-orbit abstraction with
a complete source-graph/optimizer equivalence theorem.

---

### Historical snapshot below (as of `f338cdf`)


_Status: gap-pinning note at `origin/main` `f338cdfe34442d6bc1767e59c577b284d60d66a3`
(2026-10-17). The #295 source-fidelity blocker is **OPEN**. This note records exactly
which lemmas merged work delivers and which correspondence lemma remains unproved.
It changes no merged claim and edits no classification._

## The question

PR #295 (head `dc6419d1481475aee04ad9db45195ce12b61851d`, OPEN, blocked) claims a
"corrected MB09 §6.2 source model" via explicit orientation tags
(`OStrand W = W × Bool`, `AssemblyP1/Section62OrientedStrandFlow.lean`). Reviewer
objections (PR #295 comments `6226733092`, `6226803094`, `627270544`, all
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
   canonicity at `:266`. Integrated by PR #296 (`c56166b`), the #284
   workstream's palindrome-audit piece (the same workstream's PR #282, merge
   `aa24b18`, branch `research/284-generic-anchors-rc-law-20261016`, delivered
   its generic anchored-window spelling identity and word-level RC law),
   root-imported at `AssemblyP1.lean:70`. This is a finite comparison
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

**OPEN.** Merged work (#284 audit via #296, #300 half-incidence) resolves the count
question and the invariance lemma, but the #295 source-fidelity blocker — the
orientation-preserving correspondence to MB09's physical graph together with the
quotient-flow discipline and the `Feasible62`/throughput revisit — is not resolved
at `origin/main` `f338cdf`. PR #295 (`dc6419d`) remains blocked; per reviewer
comment `627270544` it should be read as a bounded tagged-model experiment until
L1-L3 are proved or the model is retitled a tagged representation candidate.
