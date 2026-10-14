# Issue #261 axis matrix — independent audit (2026-10-14)

This note is the independent open/closed matrix requested by the #261 delegated
task.  It audits `origin/main` at `e024af24227bccbb88c26d22e1239d84f02e2684`
(merge of PR #206, the #284 global-circular branch) against the declared axes of
#261, #259, #262 and #284, and records for each axis the *exact* kernel-checked
artifact, its scope, and the remaining obligation.  It **does not** reopen the
settled count-vector results of PR #201 (merged as `72dca8a`).

Method: read the merged Lean modules and docs on `origin/main`, and check each
claimed result's hypotheses against the source model (MB09 §6.1–§6.2, Myers
2005).  Nothing below is promoted beyond its artifact's actual scope.

## 1. The declared axes and their status

| Axis (declared in #261) | Status | Artifact on `origin/main` | Scope / caveat |
|---|---|---|---|
| §6.1 exact **variable-length multinomial** criterion | **RESOLVED** (project objective) | `GeneralBidirectedFlowML.varLengthCriterion` | §6.1 first display; not the §6.2 solver objective |
| Fixed-external-`N` **multinomial product** criterion | **RESOLVED** | `GeneralBidirectedFlowML.flow_dominance_criterion` | coordinatewise dominance; *not* the §6.1 separable binomial |
| Genuine §6.1 **separable-binomial count-vector** criterion | **RESOLVED at the count-vector layer** | `Section62BinomialCriterion.binomCoreNat_eq_prod_qFac`, `.binomCoreNat_concentrated`, `.binomial_uniform_criterion` | fixed external `N`, interior truth, all `n≥m`; q-factorization `K(d;x)=∏ᵢqᵢ(d)^{xᵢ}` |
| Fixed-`n` (non-uniform) **extreme-sample iff** | **OPEN** (numerically audited) | `scripts/verify_261_binomial_extreme_samples.py` | Lean formalization absent |
| §6.1 binomial over the **§6.2 feasible-flow set** | **OPEN** | adapter half: `Section62FlowCountVectorAdapter` (this branch) | see §2 |
| **Half-integral relaxation gap** | **RESOLVED** (flow level) | `Section62NonSpelledFlow.half_integral_strictly_better`; arithmetic `GeneralBidirectedFlowML.half_integral_gap` | the finite `AAATT` instance; not a general theorem |
| **Non-spelled-flow** maximality criterion | **OPEN** (finite obstruction kernel-checked) | `Section62NonSpelledFlow.no_sequence_has_star_spectrum`, `.star_argmax`, `.nonspelled_se62_flow_domain_countermodel` | no general necessary-and-sufficient condition known |
| **Transitive reduction** interaction with ML | **PARTIAL** | `Section62SpellingReductionCandidate.spellPath_eq_spellDirect`, `.fullOverlap_survives`; `Section62ReductionDependencyAudit` | correct predicate defined and audited; ML-invariance under reduction still OPEN |
| **Orientation / RC class** interaction | **OPEN** (indexing decision recorded) | `docs/section62-full-spectrum-adapter-284.md` §1; `Section62GlobalCircularCorrespondence` | adapter is a modeling decision; general ML statement absent |
| **Sample realizability at arbitrary overlap** | **OPEN** | — | — |
| **Canonical circular genome from a signed walk** (seam coherence) | **OPEN** | `Section62CircularWindowAdapter` (interface only) | construction + `CircularSpelling` hypotheses unproved |
| **Rescaling ties** at variable length | **RESOLVED** | `GeneralBidirectedFlowML.rescaling_tie` | uniqueness impossible at variable length |

## 2. Axis (a): the §6.2 feasible-flow → count-vector adapter

The count-vector criterion `binomial_uniform_criterion` is stated for an abstract
candidate set of throughput vectors.  Nothing on `main` connects a *flow* to its
*throughput vector*.  This branch adds the two available halves in
`AssemblyP1/Section62FlowCountVectorAdapter.lean`:

* `maximal_of_subset` / `not_maximal_of_subset` — the transfer principle the issue
  statement requires: positive maximality statements restrict to sub-classes,
  while negative witnesses transfer from a sub-class to any super-class once
  inclusion is proved.  This is the formal backbone of the #262 full-overlap
  negative-witness lift (which supplies the inclusion `overlapEdges_mono`).
* `throughputVec_congr` and `maximal_image_iff` — the likelihood factors through
  the throughput map `Θ(f) = throughput(f)`, so ML maximality over a feasible flow
  set `F` is equivalent to ML maximality over the **throughput image** `Θ(F)`.

What this does **not** prove, and what stays OPEN:

1. **Characterization of the throughput image** of the §6.2 feasible set.  This is
   the incidence/Graver problem.  It is not the vertex-bound + balance set: the
   `AAATT` obstruction (`no_sequence_has_star_spectrum`) is a balanced, connected,
   vertex-`lb`-`1` feasible flow whose throughput is not any genome's spectrum.
   So no spelling-based or support-based characterization is complete.
2. **Spelled circuit → feasible flow with `d = Spelling.visits`.**  The
   instance-specific equalities exist (`Section62BridgingCounterexample.truth_visits_eq_spectrum`,
   `Primitive62Uniqueness.walkFlow_eq_flow`), but the general theorem
   (`Spelling.flow` is `Feasible62` and its throughput is `Spelling.visits`) is not
   on `main`.  It requires the edge-indexed `balCore`/`throughput` folds to be
   rewritten as position sums over the walk and the incidence cancellation
   `OppositeAtInterior`; a complete proof sketch is in §4.

## 3. Axis (b): the general non-spelled-flow maximality criterion

The finite obstruction is complete and kernel-checked in
`AssemblyP1/Section62NonSpelledFlow.lean`: the `AAATT` instance at `o_min=1` has
`star_argmax` (the truth beats every feasible flow with throughputs `≤5`), yet the
optimizer set `{(2,1,1),(3,1,1)}` is non-spelled (`no_sequence_has_star_spectrum`),
and the half-integral relaxation is strictly better (`half_integral_strictly_better`).
A *genuinely spelled* same-length challenger (`spelledCandidate261`, word `AAATA`)
also beats the truth under the fixed-`N=5` product-binomial
(`spelledCandidate261_binomial_better`, ratio `65536/50625`), while tying under the
exact iid score (`spelledCandidate261_iid_tie`).

**No tractable necessary-and-sufficient structural criterion is known.**  The
honest partial implications are:

* **(Necessary, transfer)** If the truth is sample-uniformly maximal over the
  whole §6.2 feasible flow set, then it is maximal over every sub-class of
  feasible flows (spelled circuits, zero-terminal circuits, etc.).  Contrapositive:
  any sub-class witness of defeat refutes whole-domain maximality.  This is
  `maximal_of_subset` / `not_maximal_of_subset`.
* **(Necessary, throughput)** Whole-domain maximality requires maximality over the
  throughput image `Θ(F)`; the count-vector criterion then applies to each element
  of `Θ(F)`.  But since `Θ(F)` contains non-spelled vectors (the `AAATT` witness),
  the image is strictly larger than the spelled throughputs and the criterion is
  *not* reducible to spelled candidates.
* **(Sufficient, restricted)** The scoped count-vector corollary of #259: if every
  candidate's throughput equals the truth's spectrum `A`, then the truth is a
  maximizer (all scores equal).  This is the `F ⊆ Θ⁻¹(A)` case.

**Explicit OPEN sub-claim (b1).**  There is no known finite, structurally checkable
predicate `P` on the §6.2 feasible flow set such that truth is sample-uniformly
maximal iff `P` holds.  A tractable target would be a conformal Graver-augmentation
certificate for each fixed extreme sample (#263); this is not yet a theorem.

## 4. Proof sketch for the unproved general adapter (b2)

To prove `Spelling.flow` is `Feasible62` with `d = Spelling.visits` for a circular
spelling `sp` whose steps lie in a `Nodup` graph `edges` and which satisfies
`BidirectedCircuit`:

1. **Throughput.**  `Spelling.flow sp e = steps.countP (· = e)` where
   `steps = (finRange n).map sp.step`.  The weighted de-duplication identity
   `Σ_{e∈edges} (steps.countP (·=e)) · g(e) = Σ_i g(step i)` (needs `edges.Nodup`
   and `steps ⊆ edges`) turns `throughput` into the position sum
   `Σ_i [rep (step i).sx = v]`, which is `Spelling.visits rep v`.
2. **Balance.**  With the same identity, `balCore` at `v` becomes
   `Σ_{i : rep (strand i) = v} (sgnX(step i) + sgnY(step (i-1)))`, which is `0`
   termwise by `BidirectedCircuit` (`OppositeAtInterior`).
3. **Vertex lower bound.**  Requires `∀ v ∈ verts, 1 ≤ visits v`, i.e. the walk
   visits every observed vertex at least once — a genuine extra hypothesis.
4. **Terminals / edge bounds** are immediate with `noTerminals` and edge `lb 0`.

This is a finite list-rewriting proof, not a conceptual obstacle; it was not
completed in this run because the host cgroup was memory-saturated
(`memory.events oom_kill > 300`) and local Lean elaboration of `import Mathlib`
was OOM-killed.  It is recorded here so a follow-up can finish it.

## 5. Coordination with siblings

* **#259** (binomial surrogate): `CoveredBinomialWeightsIff` delivers the
  fixed-`N` same-support samplewise iff for a fixed candidate; it does **not** lift
  to the §6.2 flow domain, which needs the adapter of §2.  No overlap with this
  branch's transfer lemmas.
* **#262** (full-overlap lift): delivers the negative-witness lift with the
  inclusion `overlapEdges_mono`.  Its transfer is the concrete instance of
  `not_maximal_of_subset`.  It does **not** cover the non-spelled optimum, and
  positive statements do not lift.
* **#284** (spelling-preserving reduction): supplies the correct reduction
  (`isReducibleSpellingB`) and the Observation 7 window identity; its declared
  next obligation (canonical circular genome + seam coherence) is still OPEN and is
  the prerequisite for the general adapter's spelled half.

## 6. Source-fidelity boundary

All §6.2 statements are about the *project* feasibility object `Feasible62`
(zero-terminal circuits, observed-vertex graph).  MB09 §6.2 permits non-contiguous
walk collections and penalized terminals; the pure binomial ML objective and the
penalized solver objective are different.  No row above claims Myers/MB09
algorithm equivalence.
