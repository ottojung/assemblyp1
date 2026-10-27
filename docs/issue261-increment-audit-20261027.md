# #261 increment audit: corrected reduction and a bounded flow result

**Scope.** This is an audit of the verified ACA/CAC finite-cell result already
present on `main`, not a new general reduction theorem. Candidates are integer
zero-terminal balanced bidirected flows with vertex lower bound 1, throughput
coordinates bounded by external `N=3`; the observed non-palindromic RC classes
are ACA and CAC at read length 3 and overlap floor 1. Scores use the fixed-`N`
§6.1 product-binomial core at sample `(2,1)`. Unobserved coordinates are fixed
to zero in this within-flow comparison. The truth flow `(1,1)` is admitted.

The prior terminal claim refers to commit `cfe544c` on a branch not present in
the fresh clone. Its two files are absent from current `main` (the cited script
cannot be run here), so the old shortest-overlap enumeration is **not** treated
as independently reproduced. The tracked `verify_261_flow_cell_acac.py` does
reproduce the main-cell witness: truth score 8, feasible non-spelled flow score
16. The separately tracked `verify_261_spelled_flow_image_refutation.py` also
passes, but concerns a different small graph.

The corrected #284 theorem documented in
`docs/section62-simultaneous-reduction-284.md` establishes preservation of
spelled edge words under simultaneous spelling-preserving reduction. It
explicitly does not preserve vertex visits, flow lower bounds, or vertex-derived
likelihood. Therefore neither candidate-set inclusion between reduced and
unreduced flow domains nor an ML transfer follows. The finite ACA/CAC result is
reduction-vacuous only for the audited legacy predicate; no assertion is made
about a source-faithful nontrivial reduction.

**Useful surviving implication:** the flow-count-vector adapter's
`not_maximal_of_subset` (and spelled-flow maximality's
`flow_not_maximal_of_spelled_witness`) transfers a concrete spelled defeater to
the larger flow class when actual candidate-set inclusion is proved. Conversely
`spelled_maximal_of_flow_maximal` transfers positive maximality only from flows
to their subset; the reverse implication is invalid in general, as the verified
ACA/CAC witness demonstrates. This is an unaffected conditional statement,
not a solution for corrected-reduction domains.

**Validation:** `python3 scripts/verify_261_flow_cell_acac.py` passed;
`python3 scripts/verify_261_spelled_flow_image_refutation.py` passed. The prior
shortest-edge script is absent from main. `lake build
AssemblyP1.Section62SimultaneousReduction` attempted to fetch Mathlib but timed
out before producing a build result. No Lean source was changed.

**Next:** independently reproduce and land the shortest-edge boundary verifier
or supersede it with a fresh exact enumeration; then establish candidate-set
inclusion (if any) under the corrected reduction plus orientation/RC transport.
Keep #261 and #255 open.
