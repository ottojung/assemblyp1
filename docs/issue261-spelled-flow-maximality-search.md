# #261 spelled-maximal versus flow-maximal: bounded exact search

## Question and scope

This diagnostic searches for a truth that is maximal among circular spelled
genomes but is not maximal among a larger count-vector universe, under the
variable-length exact multinomial likelihood. Such a witness would refute the
converse of the existing transfer
`spelled_maximal_of_flow_maximal` for that larger universe. It would not, by
itself, refute any claim about the literal §6.2 feasible-flow domain: the
surrogate count vectors are not required to satisfy overlap-graph incidence,
vertex lower bounds, transitive reduction, or the §6.2 overlap floor.

## Exact bounded sweep

`scripts/search_261_spelled_vs_flow_ml.py` enumerates circular `A/T` words of
length `L..8` for `L ∈ {2,3}`. Molecule classes identify reverse complements;
the truth sample is the truth's complete spectrum. Candidate likelihood is
computed exactly as `∏_c (d_c/N)^(x_c)` using rational arithmetic. For each
spelled-maximal truth, it tests all weak compositions of every length
`N ∈ {1,..,8}` over the complete `A/T` molecule-class universe. The latter is
an unconstrained count-vector superset, not the general bidirected feasible-flow
set.

Result: no separation in 1,012 spelled-maximal truth instances: 508 at `L=2`
and 504 at `L=3`. The search is finite evidence only. Because the comparison
universe here is larger than the actual flow image, this no-witness result does
not imply that a spelled-maximal truth is flow-maximal; and because it is a
binary alphabet, bounded lengths, and the exact likelihood, it does not address
four-letter genomes, longer lengths, fixed-external-`N` binomial likelihood, or
the source-faithful §6.2 flow class.

## Status

This does not settle either direction of the general converse. Existing results
do establish (i) spelled candidates lie in the corrected flow throughput image,
so a spelled strict dominator disproves flow maximality, and (ii) strict
containment of the image in general. Whether a spelled-maximal truth can fail
flow maximality for the literal feasible-flow likelihood remains OPEN. The
bounded surrogate search is retained as a reproducible diagnostic, not a
positive structural claim.
