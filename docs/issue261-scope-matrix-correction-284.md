# #261 scope-matrix correction under the #284 reduction semantics

Bounded verifier report. Does not duplicate #284 implementation; no new Lean
theorem is claimed here.

## Verdict

The pushed matrix
`research/261-scope-matrix-RQZTG1WbAejzEkEnSWm7Wr-chemical@5d61318`
(`docs/issue261-sweep-scope-matrix-20261023.md`) remains **valid in its central
non-transfer conclusion**: the bounded binary-string / weak-composition sweep
builds no graph, shares no fixed-external-`N` binomial score, and proves no
candidate-set inclusion, so it yields neither a positive nor a negative §6.2
maximality result. Its reduction row ("sweep says nothing about reduction
invariance") is also still correct.

One source-fidelity caveat must be tightened. The matrix asks for a
"source-faithful reduced signed graph" whose reduction "must preserve spelling
and signed endpoints". Under #284 the two halves of that phrase now have
different statuses:

- **Word-spelling preservation: resolved in the idealized model.** For
  equal-length error-free reads,
  `AssemblyP1/Section62MyersIdealTransitivity.reducible_iff_ideal_two_hop`
  proves the implemented test `isReducibleSpellingB`
  (`l1+l2 = L+l`, genuine overlaps, `oMin` legs) is equivalent to the semantic
  two-hop same-spelling relation `TwoHopSameSpelling`, and
  `reduced_mem_iff_no_ideal_detour` lifts it to the edge filter. Scope is the
  idealized relation only: the module docstring explicitly excludes Myers 2005
  `FUZZ=10`, noisy overlaps, containment, orientation/parallel-edge handling.
- **Signed-endpoint / throughput transport: still OPEN.** #284 proves the
  reduction preserves spelled words and hence complete length-`L` window
  multisets (`Section62VisitTransport.windows_detour_eq`), but its companion
  diagnostic proves word equality does **not** determine physical visit counts:
  `no_transport_function` / `transport_required_false` exhibit three walks
  spelling `012341200` with visit-list lengths 2, 3, 4. The linear-walk upper
  bound `genuineWalk_dominates` (`throughputOf <= windowCount`) is not a
  cyclic throughput adapter (its own note marks the cyclic correspondence as
  prose, not a formalized theorem).

So "preserve spelling" is now a checked idealized property of the corrected
predicate, while "preserve signed endpoints / vertex throughputs / ML score"
remains an explicit open adapter. The matrix's single phrase should be read
split this way; it must not be cited as claiming the corrected reduction is
the full practical Myers algorithm or that window invariance transports an ML
objective.

## Why the old predicates are not the corrected relation

`AssemblyP1/Section62BidirectedFlow.isReducibleB` (lines 182-193) requires
legs `len1,len2 < e.len` together with `len1+len2-readLen = e.len`, i.e.
`len1+len2 = readLen+e.len`. For a proper edge `e.len < readLen` this demands
`len1+len2 > 2*e.len` with each leg below `e.len`: arithmetically impossible,
so it deletes no proper overlap. `isReducibleLongerB` checks only that both
legs are longer than the direct edge; it does not require genuine spelled-word
equality. Neither is equivalent to the #284 idealized relation above. This
confirms (rather than weakens) the matrix's warning not to treat either
surrogate as the source rule.

## Claim-by-claim status under corrected semantics

| Matrix axis | Status after #284 |
|---|---|
| Graph/overlap range (no graph built) | Unchanged, valid. Sweep has no `overlapEdges` construction. |
| Reduction | Valid caution; caveat tightened as above (idealized word-spelling yes, signed/throughput transport and practical-Myers equivalence no). |
| Vertex lower bound 1, signed balance, orientation/RC quotient | Unchanged, still required and unproved for the sweep. |
| Candidate object (flows vs spelled circuits vs genomes) | Unchanged; #284 window/iid results add no flow↔genome adapter. |
| Integer vs half-integral | Unchanged; untouched by #284. |
| Objective/length (exact variable-length multinomial vs fixed-external-`N` binomial) | Unchanged; #284's iid lemma equates exact uniform-start ordered-sample likelihoods under *complete oriented* window-count equality for circular genomes — a different candidate class, sampling law, and score from the RC-throughput fixed-`N` binomial. It is not an ML-maximality theorem and its own note excludes the RC-throughput objective. |
| Sample/truth (truth feasibility for a fixed support) | Unchanged; nothing in #284 proves truth feasibility in a support-fixed graph. |

## Exact evidence

- Old-predicate vacuity: `isReducibleB` conjuncts `len1 < e.len`,
  `len2 < e.len`, `len1+len2-readLen = e.len` (`Section62BidirectedFlow.lean`
  lines 189-193). Arithmetic note above; no proper edge satisfies all three.
- Corrected idealized equivalence: `reducible_iff_ideal_two_hop`,
  `reduced_mem_iff_no_ideal_detour`
  (`AssemblyP1/Section62MyersIdealTransitivity.lean` lines 37-108); module
  header lines 12-14 exclude noisy/practical Myers behavior.
- Spelling preserves words/windows: `spellPath_eq_spellDirect`
  (`Section62SpellingReductionCandidate.lean`); `windows_detour_eq`
  (`Section62VisitTransport.lean`); `section62-visit-transport-284.md` §What
  the reduction preserves.
- No visit transport: `no_transport_function`, `transport_required_false`
  with the `012341200` 2/3/4-visit witness
  (`section62-visit-transport-284.md` §§ What it does NOT preserve,
  obstruction); upper-bound-only scope
  (`section62-visit-window-bridge-284.md` §§ Why useful, Scope).
- Likelihood boundary: `section62-iid-likelihood-transport-284.md` states
  oriented uniform-start iid equality and explicitly excludes the §6.2
  RC-throughput objective and physical visited reads.

## Implication for the sweep

No finite-sweep claim changes. The sweep stays a bounded surrogate census under
its stated exact variable-length score; #284 neither invalidates nor promotes
it. Any future promotion to a source-flow claim still needs the matrix's
minimal adapter: one fixed observed RC support, `L`/`oMin`, corrected
reduced signed graph, terminal convention, external `N`, truth feasibility
proof, enumerated integer feasible-flow throughputs, and a common fixed-`N`
binomial comparison — with the unobserved-coordinate convention stated
separately.
