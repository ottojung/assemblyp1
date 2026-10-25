# Independent review: #261 transitive-reduction scope cell

## Scope

This review concerns the finite cell in `issue261-transitive-reduction-scope-20261025.md` at commit `58b5f21109da14d7d867a820b636e7cf2798fc96`: candidates are the admitted integer edge-multiplicity flow spectra (edge values 0..2), with throughput at least one on the two selected physical vertices, zero signed balance, and no terminal arcs. It compares the complete ten-edge `o_min=1` graph with the four-edge maximal-overlap graph. The objective comparisons use sample `x=(1,2)`, the fixed external binomial denominator `N=4` on its 4-class box universe, and the variable-length exact multinomial. Truth `(2,2)` is admitted. This is a finite flow-image census, not a general criterion, and does not identify these flows with circular genomes.

## Review evidence

The verifier was re-run on the exact checkpoint commit, not reconstructed from the prose. Its independent integer/Fraction enumeration passes: complete graph has 78 images, with fixed-N winner `(1,3)` and exact winners `(1,2),(2,4)`; reduced graph has four images and both objectives select `(1,3)`. The truth is feasible and loses under both objectives. Both embedded mutants fail as expected (reduced census omission; swapped exact sample). The parent `check-research-docs.py` check passes on the checkpoint docs.

The local source audit supports the *programmed* reduction on this particular graph: each dropped edge has a two-step path in the complete graph, and the four retained edges are the maximal-overlap cycle. This is a concrete finite graph criterion; it does not establish equivalence to every detail of MB09's transitive-reduction definition (notably spelling preservation and signed endpoint compatibility). Accordingly the title's “MB09-style” is appropriately less than a universal source-faithfulness claim, but the documentation should continue to label the reduction model as this finite cell's explicitly defined construction.

## Result and limits

The exact-likelihood maximizing image changes under this graph restriction, while the fixed-N maximizing image does not. Thus no general transfer of positive maximality claims between these two candidate sets follows. The negative witness for the truth is verified in both sets, so that failure transfers here by direct admission checks, not by an assumed inclusion theorem. This is a useful scope counterexample and not a necessary-and-sufficient characterization.

Reproduction: `python3 scripts/verify_261_transitive_reduction_scope.py`; `python3 scripts/check-research-docs.py`.
