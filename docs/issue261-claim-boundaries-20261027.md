# #261 claim boundaries and next obligations (2026-10-27)

This checkpoint reconciles the current branch's flow/count-vector results with
the latest physical-orbit audit. Repository identity was verified as
`https://github.com/ottojung/assemblyp1`; the audited branch starts at
`cc918b65` (`docs(#261): record physical orbit occurrence gap`).

## Candidate-domain implications

Write `F` for a feasible-flow set and `Theta(F)` for its throughput image. A
likelihood that depends on a flow only through throughput induces exactly the
same maximizers as the likelihood on `Theta(F)`. Consequently, an exact
necessary-and-sufficient condition is always available *extensionally*: truth
throughput `a` is maximal iff every `d` in `Theta(F)` has score at most the
score of `a`. This is the image maximality equivalence, not a structural
description of which vectors are in the image. It does not reduce the problem
to spelled circuits: the recorded `AAATT` feasible flow has a non-spelled
throughput, so the spelled subset is proper.

For a proved inclusion `S ⊆ F`, maximality over `F` implies maximality over
`S`; conversely a strict-score witness in `S` disproves maximality over `F`.
Neither implication licenses positive transfer from `S` to `F`. In particular,
full-overlap counterexamples only transfer to a general-overlap domain when the
candidate inclusion and likelihood agreement are established. The present
physical-orbit audit finds no source-defined window-occurrence-to-edge map, so
it supplies no such inclusion for arbitrary circular genomes.

## Likelihood and universe boundary

The documented count-vector criterion concerns the fixed-external-`N`
separable-binomial surrogate, with the stated interior-truth and candidate
length hypotheses. Its score is not interchangeable with exact iid likelihood:
the recorded same-length `AAATA` comparison beats truth by `65536/50625` under
that binomial score but ties under exact iid score. Likewise, a length statement
proved for circular spellings (total visit count equals number of positions)
does not identify the length universe for arbitrary feasible flows or flow
relaxations. Those domains must be stated independently in any maximality claim.

## Reduction and orientation boundary

Reduction invariance requires a correspondence between candidate sets before
and after reduction that preserves both the declared likelihood and truth
membership. A spelling-preserving path lemma alone proves neither surjectivity
onto reduced candidates nor the survival of every source window edge. The
physical-orbit audit specifically separates edge-orbit representative
independence from the missing occurrence adapter; hence no general reduction
invariance follows from it.

Similarly, an orientation/RC quotient requires the objective and feasibility
predicate to be invariant under the quotient action, and truth/candidates to be
mapped compatibly. The existing orbit/half-incidence lemmas verify local
representative independence for already-given physical edges; they do not
establish the global action on arbitrary flow candidates or genomes.

## Status and next concrete obligations

No unrestricted structural necessary-and-sufficient maximality criterion is
established here. The image criterion is exact but may be computationally
intractable; the non-spelled feasible witness precludes replacing its domain by
spelled candidates without an additional theorem. Keep the general structural
criterion, arbitrary-overlap source adapter, reduction invariance, and global
orientation/RC transport explicitly open.

The next proof-producing step is to define a source-faithful circular window
occurrence adapter, state its overlap/sign/edge-availability premises, then
prove its physical-orbit mapping. Only after that can candidate inclusion be
used to transfer a witness or analyze reduction survival. Exact and fixed-`N`
objectives, and flow versus spelled-genome candidate sets, remain separately
quantified throughout.
