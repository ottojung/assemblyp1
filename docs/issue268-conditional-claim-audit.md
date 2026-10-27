# Issue #268 bounded conditional-claim audit

This is a source-to-claim review artifact for the active #265 integration. It
does not edit manuscript or slide sections.

## Finding: distinguish the real-source adapter from its abstract theorem

The conditional claims in `paper/sections/03-open-question.tex`, especially
Question A (lines 94--107) and the status line following the NSG singleton
claim (lines 66--76), are appropriately cautious about the published 2016
reconstruction theorem being an external premise. The proof ledger likewise
labels the conditional result `(i) conditional on (iv)` at
`paper/sections/b-epistemic-ledger.tex` lines 74--78. The main remaining
precision issue is the phrase “source-specific event/marginalization
correspondence”: it should not be read as an instantiated historical algorithm
theorem proved in Lean.

`AssemblyP1/ConditionalIdentifiability.lean` makes this boundary explicit:

* `ReadModel.conditional_posterior_eq_one` and
  `ReadModel.constrained_MAP_mem_orbit` (module lines 138--187) are kernel-
  checked consequences of `ReadModel.decode_correct`, an assumed abstract
  deterministic-decoder premise.
* `PlacementModel.placementJoint`, `placement_support_subset_orbit`, and
  `placement_posterior_certain` (lines 241--282) formalize weighted
  marginalization over candidate-specific compatible placements satisfying the
  event. They do not identify this weighted event with the manuscript's exact
  likelihood experiment.
* The historically scoped `historical_feasible_fibre_unique` (lines 284--335)
  uses the repository's literal `HistoricalInformationFeasibleLiteral` and
  observed-string adapter, but still takes `hNSG`—the external decoder
  correctness premise—as a hypothesis. The module explicitly says it does not
  formally instantiate the source algorithm.

Consequently, the exact safe attribution is: **(i)** the abstract conditional
posterior/MAP implications and source-shaped adapter lemmas are kernel-checked
in `AssemblyP1/ConditionalIdentifiability.lean`; **(iv)** the historical
Not-So-Greedy decoder correctness is the published 2016 external premise; the
composition is conditional on that premise, not a kernel-checked proof of the
historical algorithm guarantee. Existing text mostly says this already; retain
that qualification in summaries, tables, and slides.

Suggested replacement if the current broad status sentence is shortened:

> Given an explicit decoder-correctness premise for the literal historical
> predicate and observed read strings, the conditional posterior-one and
> constrained-MAP implications are kernel-checked in
> `AssemblyP1/ConditionalIdentifiability.lean`; the premise is the published
> 2016 reconstruction result, not a Lean formalization of Not-So-Greedy.

## Cross-checks

`docs/verification.md` lines 46 and 59 independently state the same boundary:
the Question-A endpoints assume the external reconstruction interface, and the
historical witness endpoints use the distinct matched-string predicate.
`paper/sections/02-model.tex` lines 103--121 explicitly distinguishes
historical observed-string matching from placement-based feasibility. This is
consistent with the conditional module's source-fidelity notes (lines 39--66).

The manuscript's two-question distinction is statistically sound: Question A
restricts weights by the truth-dependent event and the model support, whereas
Question B maximizes the unrestricted likelihood. The event-weighted
placement sum must not be replaced by likelihood times an existential
feasibility indicator; the module's `placementJoint` definition uses the sum
over compatible feasible placements, exactly as its comments explain.

## Access and scope

The project remote was confirmed as `https://github.com/ottojung/assemblyp1.git`;
review was against `origin/main` at `3decc39` in an isolated clone. `gh` is not
installed in this runtime, so live #268/#265 issue comments and PR #406 status
could not be retrieved here. The audit is limited to the checked-out manuscript
and Lean source and makes no claim about later unmerged integration changes.
