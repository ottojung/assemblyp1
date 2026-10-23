# Independent audit of the bounded spelled/flow sweep (#261)

This note audits commit `d450ed4` (`search_261_spelled_vs_flow_ml.py`) against
the source-model boundary recorded in `issue261-general-bidirected-flow-ml.md`
and `section62-mb09-bidirected-graph-audit.md`. The script was rerun unchanged:
it reports 508 truth instances at read length 2 and 504 at read length 3, with
no separating count vector. This is a correct bounded result for its stated
surrogate.

## Precisely enumerated statement

For binary `A/T` circular truths of lengths from the read length through 8,
the script takes the truth's complete reverse-complement molecule spectrum as
the sample. It first tests spelled circular genomes of lengths through 8 under
the candidate-intrinsic exact score

`prod_c (d_c / N) ^ x_c`,

where `N` is the candidate count-vector total. For truths maximal in that
bounded spelled universe, it checks all weak compositions of every total
`1 <= N <= 8` over the full binary molecule-class universe. The score
comparisons use exact rational arithmetic. It does not inspect an overlap
graph or construct a flow.

## Why this does not answer the §6.2 flow converse

There are three independent mismatches; each is material to a transfer.

1. **Objective.** The sweep scores variable-length exact multinomial
   likelihood. MB09 §6.1's first display is that exact count likelihood,
   constrained by `sum_i d_i = N(D)`. The §6.2 convex-flow algorithm instead
   optimizes the §6.1 product-of-binomial approximation at externally fixed
   genome size `N`. The latter retains factors `(1 - d_i/N)^(n-x_i)` and is
   not the score enumerated here. Thus even a count vector that happens to be
   flow-feasible would be compared under the wrong objective for the literal
   §6.2 algorithm question.

2. **Candidate domain.** A weak composition is not certified as a feasible
   flow. It need not arise from edges of length at least `o_min`, satisfy
   signed-incidence balance (or the source/sink completion), obey the
   vertex lower bound on every observed graph vertex, or use the
   transitively reduced edge set. Conversely, the script only explores totals
   through 8 and a binary class universe; it does not establish coverage of
   every source graph, every read alphabet, or unbounded feasible throughput.
   No graph-specific map from all §6.2 feasible flows into the enumerated
   weak compositions with the same objective and length parameter is proved.

3. **Truth and spelled class.** Spelled maximality is checked only among
   binary circular genomes with lengths in the finite enumerated interval,
   using the truth's complete spectrum. This is not a proof of maximality
   among all circular genomes, and is distinct from maximality among
   flow-throughput vectors. The source adapter on `main` proves the inclusion
   of a restricted spelled-circuit visit-vector class into the feasible-flow
   throughput image; it does not identify that image with all count vectors
   or all genome spectra. The known strict-image examples show why equality
   cannot be presumed.

## Transfer conclusion

If a candidate-set inclusion is established and both sides use the *same*
likelihood, length parameter, molecule universe, and truth, then an actual
strict defeating candidate in a subclass transfers to a superclass. This
sweep found no such candidate and supplies no such inclusion. Absence of a
defeater in an unconstrained superset could imply absence in a subset only
inside the identical objective and bounded universe; the source §6.2
objective and unbounded graph-dependent flow domain are not that universe.
Consequently the run establishes only the finite exact-multinomial
non-separation stated above. It neither proves nor refutes the converse
“spelled-maximal truth implies flow-maximal truth” for literal §6.2 flows.

## Reproduction

At `d450ed4`:

```text
python3 scripts/search_261_spelled_vs_flow_ml.py
PASS: 1012 spelled-maximal truth instances; no surrogate witness
python3 scripts/verify_261_spelled_flow_maximality.py
ALL CHECKS PASSED
```

The remaining productive route is an exact graph-specific enumeration under
one declared §6.2 interpretation (reduced edges, RC orientation classes,
vertex lower bound 1, integer flow, and chosen terminal convention), followed
by scoring with the explicitly declared objective. The existing
`AAATT`/`o_min=1` certificates concern non-spelled flow optima and do not by
themselves supply the missing spelled-maximal-but-flow-nonmaximal witness.
