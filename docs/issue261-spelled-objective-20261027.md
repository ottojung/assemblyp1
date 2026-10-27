# Issue #261: spelled-circuit objective transfer for one well-defined class (2026-10-27)

**Status:** kernel-checked increment for ONE class; all other axes stay OPEN.
Keep #261 and parent #255 open.

## Predecessor state (verified, not duplicated)

* `db88052` (`docs/issue261-reduction-correspondence-20261027.md`) reconciled
  MB09 §3.2/§3.3/§6.2 walk/cycle/Observation 7 with `Chain`, `spellChain`,
  `BidirectedCircuit`, `Spelling.visits`, `Spelling.flow`, `Feasible62`,
  `SpelledFeasible62`, and showed linear-word equality does not imply cyclic
  walk or flow/genome representability.
* `AssemblyP1/Section62SpelledFlowAdapter.lean` (already in tree) proves
  `throughput_eq_visits` and `spelling_flow_feasible` for spelled circuits.
* `AssemblyP1/Section62VisitTransport.lean` proves the negative side: the
  `L = 5` witness shows spelling preservation does not transport vertex
  visits across graphs, and no function of the invariant window multiset
  recovers physical class counts.

## This increment: `AssemblyP1/Section62SpelledObjective261.lean`

New kernel-checked module (`lake build` clean, no `sorry`/`admit`; axioms only
`propext`, `Classical.choice`, `Quot.sound` from Mathlib/Finset machinery):

* **Lemma (occurrence/throughput identity, cyclic only):** reuses the
  source-faithful `throughput_eq_visits` — throughput of `Spelling.flow` over a
  `Nodup` graph containing all cyclic steps equals `Spelling.visits`.
  The sum is over the **cyclic** walk including the wraparound departure from
  position `n-1` to `0`. A linear `spellChain` word equality has no closing
  step and proves nothing here; the `Section62VisitTransport` `L = 5` witness
  is the explicit counterexample to the linear reading.
* **Candidate-set inclusion (one class):** `spelled_mem_feasible` — the walk
  flow of a spelled circuit (integral domain, `BidirectedCircuit`,
  step-inclusion, vertex lower bound `1`) is a zero-terminal feasible flow
  with spectrum `Spelling.visits`.
* **Objective transfer (one class):** `spelled_objective_eq_flow_objective` —
  for **any** spectrum-factoring score `(W → ℕ) → ℚ`, the spelled candidate's
  objective equals its walk flow's throughput objective. This covers the exact
  iid score and the fixed-`N` product-binomial surrogate of
  `Section62BinomialCriterion` (both evaluate a count vector `d`) **without**
  identifying the two likelihoods with each other.
* **Maximality reading (one direction):** `spelled_maximal_transfer` —
  maximality of a spelled spectrum over the feasible throughput image gives
  maximality of its walk flow over the feasible flow set for the pulled-back
  score.

## Exactly-one-class declaration (no conflation)

* Integral flows only (`BdFlow = BdEdge → ℕ`); half-integral/`ℚ` relaxation
  excluded (OPEN).
* Spelled circuits only; arbitrary feasible flows, unspelled flows, and
  circular genomes not spelling one walk excluded — converse is false by the
  `AAATT` obstruction (`Section62NonSpelledFlow.no_sequence_has_star_spectrum`).
* Exact vs fixed-`N` likelihoods: both admitted as instances of
  spectrum-factoring scores; their identification with each other is NOT
  proved (OPEN).
* Length universe: all `n ≥ 1`, arbitrary `readLen`, arbitrary `verts`.
* Truth admitted; statements are likelihood-independent identities.
* RC quotient fixed by caller-supplied `rep`; visits and throughputs count
  classes via the same `rep`.

## Remaining OPEN transfers

Half-integral relaxation, unspelled-flow maximality, transitive-reduction
interaction with ML maximality (`edges` here is an abstract `Nodup` graph),
exact-vs-fixed-`N` identification, and genome-level (dihedral-orbit) maximality.
Full-overlap failures transfer only via proved inclusion
(`not_maximal_of_subset`); positive statements do not transfer outward.

## Evidence

* `lake build AssemblyP1.Section62SpelledObjective261` — success (8927 jobs).
* `python3 scripts/check-research-docs.py` and `git diff --check` — see
  commit validation.
* Sources: MB09 §3.2 (walk/cycle), §3.3 (overlap edges), §3.4 (balance),
  §5.2 (vertex split/throughput), §6.1 (binomial surrogate), §6.2
  (reduction, vertex bound 1, Observation 7); Myers (2005) §2 (idealized
  transitive edge).
