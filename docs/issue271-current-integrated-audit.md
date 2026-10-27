# Issue #271 integrated-state audit

This is a bounded verification handoff, not a new classification or a competing
manuscript edit. The main comparison note is
[`conditional-vs-ordinary-ml-separation-271.md`](conditional-vs-ordinary-ml-separation-271.md).

## Verified repository state

* Remote: `https://github.com/ottojung/assemblyp1.git`.
* Starting `main`: `3decc39b4f8b5e187dc3df1b8c56720b4615045a` (PR #405 merge).
* PR #398's comparison-note follow-up is integrated at
  `62c0e789d33a79d5daefe4fafe8d1cc2b78c42dc`, an ancestor of this `main`.
* The current docs include the comparison axes, both abstract separations,
  W1/W2 compatibility boundary, fixed-sample distinction, L3 literal
  source-faithful separation, and manuscript-safe wording. No artifact from the
  prior checkpoint needed re-integration.

## Exact bounded claim and evidence

For a fixed finite hypothesis set and an observation `r`, conditional certainty
under a truth-dependent promise can coexist with the R-only likelihood
strictly preferring a wrong candidate; conversely, unique R-only ML selection
does not force an uncertain-free posterior under the prior. These are abstract
finite-model facts. Separately, the integrated oriented L3 adapter supplies a
concrete genome-level `A ∧ ¬B` witness with the literal historical information
feasibility predicate: at read `000`, orbit 1 is the sole `E`-feasible orbit,
while orbit 0 has greater ordinary likelihood. It is explicitly not a W1/W2
conditional-posterior adapter. W1/W2 instantiate ordinary-likelihood failure
under their RC-collapsed count-vector model, but do not define the normalized
prior-and-promise experiment required for (A).

The comparison remains separate from #255/#258/#259/#261 classifications;
conditional recovery, ordinary ML, MAP, the §6.1 product-binomial score, and
§6.2 flow feasibility are not interchangeable objectives.

## Validation performed on current `main`

* `lake build AssemblyP1.ConditionalVsOrdinaryMLBoundary271 AssemblyP1.ConditionalBayesEImpliesB271 AssemblyP1.ConditionalVsMLLiteralL3Adapter271` — **passed**, 8,934 jobs, all three requested modules built; reported theorem axioms were only `propext`, `Classical.choice`, and `Quot.sound`.
* `python3 scripts/check-research-docs.py` — **passed**.
* `python3 scripts/verify_271_literal_l3.py` — **passed**; `E(orbit,000)` selects orbit 1, likelihood multiplicities `[4,1,0,0,0,0]`, and the witness placement `{0,1,3}` is non-saturated.
* `git diff --check` — **passed**; the worktree was clean before adding this audit note.

Remaining research questions (including the #272 proper-promise boundary and
any exact W1/W2 conditional adapter) remain open unless established elsewhere;
this audit makes no new theorem claim about them.
