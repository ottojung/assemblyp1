# Simultaneous spelling-preserving transitive reduction (#284)

**Status:** Lean-kernel-checked increment on the open #284 blocker. It adds the
*global* (simultaneous) language-preservation property that the one-step
`Section62SpellingReductionCandidate.isReducibleSpellingB` predicate and its
`Section62MyersIdealTransitivity` equivalence leave open. It does **not** reprove
the already-merged Observation 7 theorem
(`Section62GlobalSkippedBridge.observation7_reduced_signed_circuit_range_count`)
or the idealized two-hop equivalence
(`Section62MyersIdealTransitivity.reducible_iff_ideal_two_hop`), and it does not
redefine the audited legacy `Section62Flow.isReducibleB` /
`Section62Flow.transitivelyReduced` symbols.

## The gap this closes

`isReducibleSpellingB` removes an overlap edge when a *single* two-hop detour
through an observed molecule spells the same word. That is a **local** statement:
it says nothing about whether the detour legs survive when *all* reducible edges
are removed at once. A detour leg can itself be reducible, so a one-step
replacement need not be present in the fully reduced graph.

## The well-founded measure

MB09 §6.2 attributes transitive reduction to Myers (2005), whose transitive edge
is one whose spelled sequence is recovered by a two-hop path. For equal-length,
error-free reads the repository's spelling identity is the overlap law
`l₁ + l₂ = L + e.len`. `Section62SpellingReductionCandidate.
replacement_overlaps_longer` proves that whenever this law holds with proper
overlaps `l₁, l₂ < L`, both detour overlaps are **strictly longer** than the
direct overlap: `e.len < l₁` and `e.len < l₂`.

Equivalently the *extension length* `Ext L e = L - e.len` — the number of bases
an edge appends beyond its departure read — strictly decreases on both legs. Since
extension lengths are natural numbers, repeatedly expanding reducible legs
terminates.

## Kernel-checked results (`AssemblyP1/Section62SimultaneousReduction.lean`)

* `spellChain` and `Chain` formalize the word spelled by a chain of overlap edges
  and the bidirected-walk validity of that chain; `spellChain_append` shows a
  spelled chain composes by appending the part of the second chain's word beyond
  the shared `L`-symbol read.
* `exists_detour_of_reducible` extracts the observed intermediate strand and the
  two proper overlap lengths from the reduction predicate.
* `exists_irreducible_expansion` is the well-founded recursion on `Ext L e`: every
  proper edge of the complete `overlapEdges` graph admits a finite chain of
  **irreducible** graph edges that starts at the edge's departure strand, ends at
  its arrival strand, and spells exactly the edge's word.
* `reduction_preserves_language` packages the same statement in terms of the
  actual reduced graph `transitivelyReducedSpelling`: every edge of the complete
  graph expands into a chain whose edges all lie in the reduced graph and whose
  spelled word is unchanged.

## Finite positive regression (a genuine two-level cascade)

The `Section62SpellingReductionCandidate` regression removes a `1`-overlap
through two maximal `2`-overlaps, which are already irreducible, so it does not
exercise simultaneity. `Section62SimultaneousReduction` adds four length-`5`
reads `sx = 01234`, `m₁ = 23412`, `m₂ = 12341`, `sy = 41200` over which:

* `sx → sy` (overlap `1`) is reducible through `m₁` (`3 + 3 = 5 + 1`);
* its first leg `sx → m₁` (overlap `3`) is **itself reducible** through `m₂`
  (`4 + 4 = 5 + 3`), so the naive one-step detour legs do not survive;
* the fully expanded chain `sx → m₂ → m₁ → sy` consists of the two maximal
  `4`-overlaps and the surviving `3`-overlap `m₁ → sy`, all irreducible, and
  spells exactly the direct `1`-overlap's word.

These facts are `decide`-checked (`cascade_direct_reducible`,
`cascade_leg_reducible`, `cascade_f1_irreducible`, `cascade_f2_irreducible`,
`cascade_leg2_irreducible`, `cascade_chain`, `cascade_spell`).

## Axiom hygiene

`lake build --wfail` succeeds; `leanchecker` replays the module; every endpoint
depends only on a subset of `{propext, Classical.choice, Quot.sound}`
(`cascade_spell` on `propext` alone), with no `sorryAx`.

## Still outside this theorem

This is the idealized equal-length, error-free, deduplicated model. It does not
claim equivalence to the practical Myers 2005 algorithm (`FUZZ = 10`, noisy
approximate overlaps, contained reads) or to the full unobserved `4^k`/RC-class
universe; those remain separate #284 fronts.

**References:** Medvedev–Brudno, *Maximum Likelihood Genome Assembly*, J. Comput.
Biol. 16(8) (2009), §3.3, §6.2, <https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/>;
Myers, *The fragment assembly string graph*, Bioinformatics 21 Suppl. 2 (2005),
ii79–ii85, §2–§3.
