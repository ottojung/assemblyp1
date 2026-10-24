# Issue #261 non-vacuous reduction cell: spelled witness transfers across a strict transitive reduction

Child of #255. Instantiates the Lean transfer theorem
`spelled_witness_transfers_across_reduction` (PR #394, commit `4d1377f`) on an
instance where transitive reduction is **strictly non-vacuous**.
Independent exact-integer witness; verifier:
[`scripts/verify_261_flow_cell_nonvacuous.py`](../scripts/verify_261_flow_cell_nonvacuous.py).

## Fixed instance (source-faithful MB09 Sec. 6.2)

Same observed support as the vacuous cell (`docs/issue261-flow-cell-acac-20261023.md`):
alphabet `A=0,C=1,G=2,T=3`; strands `ACA=(0,1,0)`, `CAC=(1,0,1)`,
`TGT=rc(ACA)`, `GTG=rc(CAC)`; RC verified against Watson-Crick complement.
Observed molecule support `verts={ACA,CAC}` (two RC classes, no palindromes);
`readLen L=3`, `o_min=1`. Complete `overlapEdges` graph: 8 edges (4 len-1 + 4 len-2).

Reduction used here is the **spelling-based** predicate
`isReducibleSpellingB` (`AssemblyP1/Section62SpellingReductionCandidate.lean`:
`l1 + l2 == readLen + e.len`, i.e. the direct edge's spelled word equals a
two-step spelling), **not** the literal length-based `isReducibleB`
(`l1,l2 < ln`), which is vacuous on every `L=3` instance (it requires
`ln >= L+2`, impossible for `ln <= L-1`). The predicate choice is part of the
cell specification.

## Proven statements (exact, finite)

1. **Strict non-vacuity.** Spelling-based reduction removes exactly the 4 len-1
   self-loop edges (each spelled by a len-2 pair, e.g. `ACA->ACA(len1)` by
   `ACA->CAC->ACA(len2,len2)` since `2+2 = 3+1`): 8 -> 4 edges. The reduced
   graph is a strict edge-subset of the complete graph.
2. **Maximal-edge survival (general arithmetic lemma).** Maximal edges
   (`ln = L-1`) are never spelling-reducible: `l1 + l2 <= 2(L-1) < L + (L-1)`.
   Hence every maximal-edge spelled circuit on the complete graph survives
   reduction; the spelled class can only shrink through non-maximal steps.
3. **Inclusion (computational shadow of Lean `spelledVisitSet_mono_edges`).**
   `spelled(reduced) = {(1,1),(2,2)} ⊆ spelled(complete)` at `n <= 4`, both
   vertices visited. `(2,1)` is in neither.
4. **Transfer with strict witness.** Candidate class: spelled circuits on the
   REDUCED graph. Truth: the spelled 2-circuit walk flow with throughput
   `d*=(1,1)`, feasible on the COMPLETE graph. Likelihood: fixed-`N`
   product-binomial core with `N=4`, sample `x=(3,1)` (`n=4`). Length universe:
   the spelling length `n=4` of the witness circuit. The reduced-graph spelled
   witness `(2,2)` (4-circuit using only kept len-2 edges) scores `K=256 > 81`,
   so the truth is NOT maximal over the complete-graph feasible-flow set. The
   transfer is licensed by the proved inclusion (3), i.e. this cell is a
   concrete instance of `spelled_witness_transfers_across_reduction`.

## Scope and what stays OPEN

This cell resolves the "non-vacuous-reduction" row for one RC support: a strict
reduction whose spelled failure transfers upward under proved inclusion.
It is not a general maximality criterion: other RC supports, the throughput-image
characterization, the real LP relaxation, sample realizability at arbitrary
overlap, and the unobserved-coordinate convention all stay OPEN.
#261 and #255 stay open.
