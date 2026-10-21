# Issue #261: integer flows vs half-integral relaxation for the **exact** §6.2 likelihood

Child of #255.  A bounded, source-connected increment on the `#261` axis
"integer flows vs half-integral relaxation", stated against the **literal**
MB09 §6.2 flow object of `AssemblyP1/Section62BidirectedFlow.lean`
(`BdEdge`, `throughput`, `balCore`, `Admissible`, `Feasible62`).

## The question

*Can the half-integral relaxation of the MB09 §6.2 bidirected-overlap flow
polytope ever yield a strictly higher **exact** read likelihood than the best
integer flow?*

Answer for this family: **No** (kernel-checked).  The relaxation is nevertheless
a **strict** enlargement of the candidate point set, so this is a real statement
about a strictly larger feasible set.

## The class made precise

* **Candidate set.**  Rational flows `f : BdEdge A W → ℚ` satisfying the §6.2
  clauses:
  1. edge lower bound `0`,
  2. vertex lower bound `1`,
  3. zero-terminal signed-incidence balance `0`,
  4. throughput vector `d`.
  This is `Feasible62Rat`, the `ℚ`-analogue of the literal `Feasible62`, with
  `qThroughput`/`qBalance` defined by the *same* edge-occurrence folds as the
  source `throughput`/`balCore` (bridged by `qThroughput_cast`/`qBalance_cast`).
  Candidates are **flows**, not spelled circuits and not circular genomes.
  *Integer* flows are the literal `Feasible62` `ℕ`-flows; *half-integral* flows
  are those with `IsHalfIntegral` (`∀ e, ∃ n : ℤ, f e = n / 2`).
* **Truth.**  Admitted (any feasible rational flow).
* **Likelihood.**  The exact multinomial likelihood `qExactLik` of the
  candidate's normalized throughput, with the candidate's own length
  `N = ∑ᵥ dᵥ` — the §6.1 first display.  Concretely
  `qExactLik d x verts = ∏ᵥ (dᵥ / ∑ᵤ dᵤ) ^ (xᵥ)`.
* **Length universe.**  Variable (`N = ∑ d`), not a fixed external `N`.

## The result

1. **`qExactLik_smul` (scale invariance).**  The exact likelihood is homogeneous
   of degree `0`: `qExactLik (k · d) x verts = qExactLik d x verts` for `k > 0`.
   No positivity of the total is needed.
2. **`feasible62Rat_smul` (homogeneity of the clauses).**  The §6.2 clauses are
   linear, so scaling a feasible rational flow by `k ≥ 1` preserves feasibility.
3. **`halfIntegral_double_feasible62` (source-connected doubling).**  Doubling a
   half-integral `Feasible62Rat` flow yields a **literal integer `Feasible62`
   flow** (`halfDoubleNat`), with doubled throughput.
4. **`no_half_integral_gap_exact`.**  That integer double has exactly the same
   exact likelihood as the half-integral flow, on every observed sample.
5. **`truth_half_maximal_iff_int_maximal`.**  Consequently the truth is maximal
   against every half-integral candidate **iff** it is maximal against every
   integer candidate; the relaxation gap cannot change ML maximality of the
   truth flow for this objective.
6. **`integral_strict_subset_half_integral`.**  On the four-edge witness graph
   the half-integral circulation `(1/2,1/2,1/2,1/2)` is feasible (throughput
   `(1,1)`) and has **no** integral representative, so the equivalence of optima
   is over a strictly larger set.

## Why this is *not* the already-merged binomial answer

`docs/issue261-general-bidirected-flow-ml.md` (Class 3) records the MB09 §6.1
**separable binomial** half-integral gap, kernel-checked in
`AssemblyP1.GeneralBidirectedFlowML.half_integral_gap`: for the binomial with a
**fixed external** `N`, the `AAA` marginal `d²(N−d)²` is strictly larger at the
half-integral `d = 5/2` than at the integral maximizers `d = 2, 3`
(`625/576 > 1`).  That objective is **not homogeneous**: the `(N − d)` factor
keeps the external `N` fixed while `d` changes, so doubling a half-integral flow
changes its value.  The exact multinomial is different — its length is the
candidate's own `N = ∑ d`, so the normalized spectrum is invariant.  The two
answers therefore differ, and both are correct *for their stated objective and
length universe*.  The verifier checks the binomial contrast too (W5).

## Scope and non-claims

* This is **one concrete, fully specified family**: rational §6.2 flows under the
  exact variable-length multinomial.  It is **not** a general criterion, and no
  general criterion is claimed from this single family.
* No claim about spelled circuits, circular genomes, the **real**
  (non-half-integral) LP relaxation, transitive reduction, or arbitrary-`o_min`
  sample realizability.  The real relaxation remains OPEN: a real optimal vertex
  need not be half-integral, so the doubling argument does not apply.
* No claim about the fixed-external-`N` binomial (that is the merged Class 3
  answer, with the *opposite* conclusion).
* No `sorry`, `admit`, `axiom`, or `native_decide`.

## Artifacts

* `AssemblyP1/Section62HalfIntegralSourceML.lean` — kernel-checked
  (`Feasible62Rat`, `qThroughput`/`qBalance` + bridges, `feasible62Rat_smul`,
  `IsHalfIntegral`, `halfDoubleNat`, `halfIntegral_double_feasible62`,
  `qExactLik`, `qExactLik_smul`, `no_half_integral_gap_exact`,
  `truth_half_maximal_iff_int_maximal`, `integral_strict_subset_half_integral`).
  Axioms `⊆ {propext, Classical.choice, Quot.sound}`.
* `AssemblyP1/Section62HalfIntegralSourceMLAudit.lean` — axiom audit.
* `scripts/verify_261_half_integral_source_ml.py` — independent exact-rational
  verifier (W1 scale invariance, W2 witness doubling, W3 strict superset, W4
  brute-force optimum equivalence, W5 fixed-`N` binomial contrast, W6 red
  mutations), exit 0.
* `AssemblyP1.lean` — root imports and `#print axioms` audit.

## Relation to the unmerged abstract branch

An earlier, unreported branch `research/261-halfintegral-relaxation` proved the
same no-gap statement for a self-contained rational proxy `QFeasible62` that was
**not** connected to the literal `Feasible62`/`throughput`/`balCore`.  This
increment reproduces the conclusion *against the source definitions* (the
bridges `qThroughput_cast`/`qBalance_cast` and the literal `Feasible62` doubling
`halfIntegral_double_feasible62`), which is what #261's "independently audited
source definitions" requirement asks for.
