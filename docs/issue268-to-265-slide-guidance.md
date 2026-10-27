# Reusable narrative guidance for issue #265

This note is for the #265 paper-and-presentations integration owner. It is
companion guidance for the foreground ML narrative, not a request to duplicate
whitepaper edits in a deck.

## Narrative sequence

1. **Set the experiment first.** A candidate circular genome of length `G`
   yields an error-free length-`L` read by choosing one of its `G` start
   positions uniformly and independently. The probability of a read *type* `w`
   is its number of occurrences divided by `G`; uniform starts do not mean
   uniform read types. Observed counts have the exact joint multinomial law.
2. **Explain the benchmark.** On a finite universe of target equivalence
   classes, under a correct common observation model and zero-one exact-class
   loss, MAP maximizes prior-averaged probability of correct classification.
   Under the explicitly chosen uniform prior on rotation classes this is ML,
   for every finite read count `n`. Say “prior-averaged”: this does not promise
   success for every fixed genome or every sample, and it does not cover an
   arbitrary prior/loss or MB09's product-binomial pseudo-likelihood.
3. **Introduce Not-So-Greedy as structural reconstruction.** Its source
   coverage/bridging predicate is about observed strings, and the published
   theorem guarantees a unique Eulerian spelling for observations satisfying
   it under the full source assumptions. Multiple genomes can generate the
   same reads; at most one rotation class can satisfy that strong sufficient
   guarantee for the same observations.
4. **Show the two questions immediately.** (A) If the candidate set is
   restricted to positive-likelihood feasible candidates and the truth
   satisfies the predicate, the conditional posterior is a singleton; this is
   reconstruction plus conditioning. (B) If we only assume the truth is
   feasible but maximize the original likelihood over its original universe,
   ML need not return the truth. This is the nontrivial finite comparison.
   Feasibility of the hidden truth is not generally knowable from reads alone.
5. **Place results on separate axes.** Distinguish conditional recovery,
   prior-average optimality, finite-sample error, identifiability, and limiting
   consistency. Use `AABB/ABAB` for a same-length oriented read-law collision;
   `W1/W2` only for their certified source-faithful RC-molecule model; and
   variable-length `P1` witnesses and the MB09 §6.1 binomial objective only
   with their respective candidate and objective scopes. Do not present them
   as comparisons under one common model.
6. **Close with positive results.** Same-length oriented rigidity and
   population primitive-P2 uniqueness remain prominent. Population KL/Gibbs
   maximality holds for any included truth; special P2 identifiability gives
   uniqueness. Neither is finite-sample pointwise optimality or a consequence
   of feasibility conditioning. State a 99% bound only with its explicit
   candidate count and separation constant.

## Proof labels for slides

Keep the paper's five labels visible wherever a headline is used: (i)
kernel-checked exact Lean theorem with path; (ii) proof in the paper, not yet
Lean; (iii) textbook/external theorem with citation; (iv) published 2016
reconstruction premise; (v) open. In particular, Question A's posterior/MAP
lemma is kernel-checked under a decoder-correctness premise, but the Lean module
does not formally instantiate the historical Not-So-Greedy algorithm. Do not
label the composition “Lean-proved” without retaining that dependency.

## Current manuscript source of truth

The issue #268 manuscript organization in `paper/sections/01-introduction.tex`
and `paper/sections/03-open-question.tex` already gives this order. The
conditional proof-boundary wording is clarified in the #268 branch commits; the
claim-to-evidence table is in the five-notion matrix and Appendix B ledger.
