# Issue #261: observed-window admission boundary (2026-10-26)

## Exact finite-sample obstruction

In the §6.2 construction audited in `docs/issue261-general-bidirected-flow-ml.md`,
vertices are observed read-molecule classes. Consequently a circular genome does
not automatically define a candidate in a graph whose candidate/spelling class
requires every length-`L` circular window to be a vertex. This is an admission
obstruction, before any question about overlap edges, transitive reduction, or
likelihood maximality.

Take alphabet `{A,C}`, circular truth `AAC`, read length `L=2`, and one sampled
read `AC`. The circular windows, listed by their start positions, are exactly
`AA`, `AC`, and `CA`; the observed vertex set is exactly `{AC}`. This is a
positive-probability sample under uniform sampling of truth starts: the start
whose window is `AC` is sampled. Yet the truth is not a circular spelling whose
every window belongs to the observed vertex set (`AA` and `CA` are missing).
The witness is exact and does not depend on an orientation convention: no
reverse-complement representative of `AA` or `CA` equals the observed word `AC`.

Thus the implication

> a true circular genome is admitted by the candidate class “genomes all of
> whose length-`L` windows are observed vertices”

is false for finite samples. In particular, that candidate class cannot be used
without qualification when a maximality statement presupposes that truth is a
candidate. This does **not** refute truth admission for flow candidates under a
different convention (e.g. vertex lower bounds plus a partial observed-window
mapping), and does not establish an ML comparison.

## Consequences for the window-to-edge bridge

The conditional bridge in `docs/issue261-window-step-bridge-audit-20261026.md`
needs both (a) content agreement for an overlap and (b) membership of both
strands among the graph's observed representatives (or their reverse
complements). The current exact example shows why (b) cannot be silently
derived from “this is the truth”: finite sampling may leave truth windows
unobserved. An unconditional circular-genome-to-edge inclusion therefore
requires either a truth-coverage hypothesis or a different candidate definition
that does not require every genome window to be a graph vertex.

Even under complete window coverage, the audit's third requirement—an edge
survives the *particular* transitive reduction—remains separate. This note makes
no reduction-survival, flow-image, or ML-maximality claim.

## Candidate and likelihood bookkeeping

This example concerns only **admission**. It does not identify flows, spelled
circuits and circular genomes. In the distinction used by MB09, §6.1's exact
global multinomial and fixed-external-`N` product-binomial approximation are
different objectives; neither assigns a likelihood comparison to the empty
candidate class containing no truth. For any subsequent truth-maximality claim,
state the candidate class first and separately specify truth admission, exact
versus approximate likelihood, and fixed versus variable length. No such choice
is resolved by this witness.

## Reproducibility / status

The window list is computed directly from the cyclic word: `AA` (start 0), `AC`
(start 1), `CA` (start 2). The single-read sample `AC` has positive probability
under the standard independent-uniform-start sampling model because one of the
three starts yields it. This is a finite exact witness, not a claim that
incomplete coverage is likely or that all flow candidates exclude truth.

The general genome-to-edge inclusion, its survival under transitive reduction,
and necessary-and-sufficient maximality for the resulting source-faithful
candidate classes remain OPEN.
