# Myers §2–§3 source-fidelity matrix for §6.2 reduction (#284)

**Purpose.** This is an inspectable source comparison for the remaining Myers
algorithm-fidelity question. It distinguishes the ideal equal-length,
error-free two-hop relation proved in Lean from Myers's practical string-graph
algorithm; the former must not be presented as formal equivalence to the latter.

**Primary source:** Eugene W. Myers, “The fragment assembly string graph,”
*Bioinformatics* 21 Suppl. 2 (2005), ii79–ii85, §2 (p. ii81), §3 and Fig. 4
(pp. ii81–ii82), <https://www.cs.utoronto.ca/~brudno/csc2427/myers.pdf>.

| Myers source behavior | Exact Lean / repo correspondence | Status and consequence |
|---|---|---|
| §2: an edge `f → h` is transitive when a two-hop path `f → g → h` spells the same sequence | `Section62MyersIdealTransitivity.TwoHopSameSpelling` and `reducible_iff_ideal_two_hop`; `Section62SpellingReductionCandidate.isReducibleSpellingB` | **Kernel-checked under stated idealized hypotheses:** equal-length reads, proper direct overlap, observed intermediate strand, legal suffix-prefix overlaps, exact spelled-word equality. This establishes the ideal two-hop relation, not the complete assembler. |
| §2 string-graph reduction removes transitive edges while retaining irreducible overlaps | `transitivelyReducedSpelling`, plus `Section62SimultaneousReduction.reduction_preserves_language` | **Kernel-checked for this model:** one-edge replacement preserves the spelled word; well-founded simultaneous elimination preserves language. This does not verify the practical implementation's complete graph-building pipeline. |
| §3 / Fig. 4: approximate overlaps are admitted with `FUZZ=10` to accommodate sequencing errors | No Lean predicate represents approximate/edit-distance overlaps or the `FUZZ=10` policy | **Not modeled / not proved.** A correspondence would require defining its error and overlap semantics and auditing whether exact spelling-preservation still applies. The current exact relation cannot certify noisy-input transitivity. |
| §3 / Fig. 4: contained reads and their removal/handling are part of graph construction | No contained-read filtering stage is represented by `overlapEdges` / `isReducibleSpellingB` | **Not modeled / not proved.** The equal-length deduplicated read setting simplifies containment, but this is not a theorem about arbitrary practical input or containment filtering. |
| §3 / Fig. 4: practical algorithm uses orientation, overlap processing, and graph cleanup beyond the abstract two-hop predicate | Lean models observed strands and reverse-complement orientation for the corrected witness relation; it does not implement every practical processing and cleanup step | **Partial correspondence only.** The orientation component is modeled in the ideal relation; full algorithm equivalence remains open. |
| Myers's practical construction operates on the input fragment set and produces a graph consumed downstream | `Observed`/`overlapEdges` provide an abstract finite graph input; no execution trace or end-to-end implementation correspondence is proved | **Not modeled / not proved.** A proof of a local reduction predicate is not an end-to-end validation of graph construction or assembly output. |

## Safe claim boundary

The checked theorem is an exact equivalence between the repository predicate and
an explicitly defined, error-free, equal-length **ideal** two-hop same-spelling
relation. It justifies using that relation as a corrected graph model for the
downstream #261/#262 mathematical handoff, subject to their separate model
assumptions. It does not establish equivalence with all of Myers's practical
algorithm, particularly its `FUZZ=10` approximate-overlap behavior and
contained-read handling. These gaps remain explicit rather than being inferred
away from the ideal theorem.

## References to the formal artifacts

* [`section62-myers-ideal-transitivity-284.md`](section62-myers-ideal-transitivity-284.md)
  states the exact theorem and its hypotheses.
* [`section62-reduction-survival-matrix-284.md`](section62-reduction-survival-matrix-284.md)
  audits old-predicate dependents and the finite nontrivial regression.
* [`section62-spellchain-window-transport-284.md`](section62-spellchain-window-transport-284.md)
  states the remaining likelihood/physical-visit transport boundary.
