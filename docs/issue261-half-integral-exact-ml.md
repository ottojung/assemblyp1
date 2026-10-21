# Issue #261: integer vs half-integral relaxation for the **exact** §6.2 read likelihood

Child of #255.  One bounded increment on the `#261` free link "integer flows vs
half-integral relaxation".

## The question

*Can the **half-integral relaxation** of the MB09 §6.2 bidirected overlap flow
polytope ever yield a strictly higher **exact** read likelihood than the best
**integer** flow, for some finite read sample?*

Answer: **No.**  Status: **PROVED** (kernel-checked).

## The class made precise

* **Candidate set.**  Rational flows `f : BdEdge A W → ℚ` on the §6.2
  bidirected overlap graph `edges` over the vertex list `verts`, satisfying the
  §6.2 clauses:
  1. edge lower bound `0`,
  2. vertex lower bound `1`,
  3. zero-terminal signed-incidence balance `0`,
  4. throughput vector `d`.
  *Integer* flows are those with `∀ e, ∃ n : ℤ, f e = n`; *half-integral*
  flows are those with `∀ e, ∃ n : ℤ, f e = n / 2`
  (`AssemblyP1.Section62HalfIntegralExactML.IsHalfIntegral`).  The candidate set
  is **flows**, not spelled circuits and not circular genomes.
* **Truth.**  Admitted (any feasible flow).
* **Likelihood.**  The exact multinomial likelihood of the candidate's
  normalized throughput, with candidate length `N = ∑ᵥ d v` — the variable-length
  §6.1 first display.  Concretely
  `exactLik d x verts = ∏ᵥ (d v / ∑ᵤ d u) ^ (x v)`.
* **Length universe.**  Variable (`N = ∑ d`), not a fixed external `N`.

## The proof

Two facts:

1. **`exactLik_smul` (scale invariance).**  The exact likelihood is homogeneous
   of degree `0` in the throughput:
   `exactLik (k · d) x verts = exactLik d x verts` for `k > 0`.
2. **`half_integral_doubling` (homogeneity of the §6.2 clauses).**  The §6.2
   feasibility clauses are linear, so doubling a half-integral feasible flow
   `f` gives the integer flow `2f = halfIntegralDouble f h` with throughput
   `2d`, and `2f` is again §6.2 feasible.  The two facts combine to
   `exactLik (2d) = exactLik d`.

Consequently every half-integral candidate's exact likelihood is matched by an
integer candidate (its double), so the half-integral optimum equals the integer
optimum for the exact multinomial objective.  The kernel-checked statements are
`AssemblyP1.Section62HalfIntegralExactML.exactLik_smul` and
`AssemblyP1.Section62HalfIntegralExactML.half_integral_doubling`.

The supporting lemmas are the homogeneity of the rational throughput and balance
(`qThroughput_smul`, `qBalance_smul`) and of feasibility (`qFeasible62_smul`).

## Why this is *not* the already-merged binomial answer

`docs/issue261-general-bidirected-flow-ml.md` (Class 3) records the MB09 §6.1
**separable binomial** half-integral gap, kernel-checked in
`AssemblyP1.Section62NonSpelledFlow.half_integral_strictly_better` and
`AssemblyP1.GeneralBidirectedFlowML.half_integral_gap`: for the binomial with a
**fixed external** `N`, the AAA marginal `d²(N−d)²` is strictly larger at the
half-integral `d = 5/2` than at the integral maximizers `d = 2, 3`.

That binomial objective is **not homogeneous**: the `(N − d)` factor keeps the
external `N` fixed while `d` changes, so doubling a half-integral flow changes
its value.  The exact multinomial is different: its length is the candidate's
own `N = ∑ d`, which scales with `d`, so the normalized spectrum — and hence the
exact likelihood — is invariant.  Therefore **the binomial gap does not transfer
to the exact objective**, and the two answers must be kept distinct.  The
independent verifier checks both facts (W3).

## Scope and non-claims

* No claim about **spelled circuits** or **circular genomes**; the candidate set
  is flows.
* No claim about the fixed-external-`N` binomial (that is the merged Class 3
  answer, with the *opposite* conclusion).
* No claim about the **real** (non-half-integral) LP relaxation: a real optimal
  vertex need not be half-integral, so the doubling argument does not apply.
  This remains OPEN.
* No claim about the throughput-image characterization, transitive reduction, or
  arbitrary-`o_min` sample realizability.

## Artifacts

* `AssemblyP1/Section62HalfIntegralExactML.lean` — kernel-checked
  (`exactLik`, `exactLik_smul`, `IsHalfIntegral`, `halfIntegralDouble`,
  `half_integral_doubling`, plus the homogeneity lemmas).  Axioms
  `⊆ {propext, Classical.choice, Quot.sound}`; no
  `sorry`/`admit`/`axiom`/`native_decide`.
* `scripts/verify_261_half_integral_exact_ml.py` — independent exact-rational
  verifier (W1 scale invariance, W2 AAATT half vs double, W3 binomial contrast,
  W4 tiny §6.2 circulation doubling), exit 0, with red mutations.
* `AssemblyP1.lean` — root import and `#print axioms` audit.
