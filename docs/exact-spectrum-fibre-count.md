# Exact same-length complete-spectrum fibre count

This note records the mathematical counting result developed and independently audited in issue #83. It concerns only the same-length complete-spectrum fibre.

## Setup and weighted count

Let c(e) be a nonzero capacity vector on directed edge types. Assume the capacitated support is balanced and strongly connected. Copies of one edge type are indistinguishable, and spellings are identified by cyclic rotation. Let d_u be the capacitated outdegree.

Fix a support vertex r. Let t_r(c) be the number of directed spanning in-arborescences toward r in the labelled-edge-instance multigraph. Equivalently it is the weighted directed Matrix-Tree cofactor on the edge-type support graph with edge weight c(e). Self-loops contribute to d_u, but not to the arborescence cofactor.

For a cyclic spelling orbit W let s(W) be its rotational stabilizer size. Then

    B(c) := sum_W 1/s(W)
          = t_r(c) * product_u (d_u-1)! / product_e c(e)!.

Proof: temporarily distinguish repeated edge occurrences and let T_r be labelled linear Euler circuits starting at boundary vertex r. Directed BEST with arbitrary first labelled outgoing edge at r gives

    |T_r| = d_r * t_r(c) * product_u (d_u-1)!.

An edge-type cyclic orbit W has d_r/s(W) distinct type-linearizations starting at r, and each has product_e c(e)! labellings. Summing over W and cancelling d_r gives the formula. No extra total-length, root-outdegree, or stabilizer factor occurs.

## Gcd-one specialization

If gcd_e c(e)=1, every spelling has trivial rotational stabilizer, since a repetition exponent greater than one would divide every edge multiplicity. Therefore B(c) is the actual number of cyclic spelling orbits. The fibre is a singleton modulo rotation exactly when

    t_r(c) * product_u (d_u-1)! = product_e c(e)!.

## Arbitrary gcd

Write c = g*c0 with gcd_e c0(e)=1. For each positive h let B_h=B(h*c0), and let P_h count primitive cyclic spelling orbits with capacity h*c0.

Every orbit at level h has a unique primitive root at some level j dividing h. Repeating that root h/j times gives stabilizer h/j. Hence

    h*B_h = sum_{j|h} j*P_j.

Mobius inversion yields

    P_h = (1/h) * sum_{j|h} mu(h/j)*j*B_j
        = sum_{d|h} mu(d)/d * B_{h/d}.

Every orbit at target level g is the repetition of a unique primitive orbit at exactly one divisor level. Thus the actual unweighted count is

    N(c) = sum_{h|g} P_h.

Together with the BEST formula at every divisor level this is an exact finite counting procedure for arbitrary capacities. The same-length complete-spectrum fibre is a singleton modulo rotation exactly when N(c)=1.

## Verification and scope

Issue #83 records an independent exhaustive exact evaluator over every binary circular word of lengths 1 through 9 for L in {2,3}. For every realized capacity vector, direct rotation-orbit enumeration agreed with independently computed Matrix-Tree/BEST values plus the Mobius inversion. This is computational evidence, not part of the proof.

The identities and singleton criterion above have epistemic status mathematical proof under the explicit graph/spelling assumptions in this note; they are not yet kernel-checked.

This result does not settle the historical Medvedev-Brudno candidate-genome universe, oriented versus reverse-complement-collapsed read types, variable candidate length, finite-sample likelihood, or bridging sufficiency. Those source/model boundaries remain governed by docs/open-problem.md and its source notes.
