# §6.2/§6.1 global audit for #284: corrected-reduction dependency re-audit, circular spelling, and the §6.1 unseen-factor identity

**Status (2026-10-14):** kernel-checked additions plus a precise statement of the
one remaining formal obligation. This note does **not** claim Myers/MB09
algorithm equivalence, and does **not** settle full genome ML maximality.

Primary sources:

- Medvedev–Brudno, *Maximum Likelihood Genome Assembly*, J. Comput. Biol. 16(8)
  (2009) 1101–1116, §3.1–3.4, §5.2, §6.1–6.2,
  <https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/>.
- Myers, *The fragment assembly string graph*, Bioinformatics 21 Suppl. 2 (2005)
  ii79–ii85, <https://www.cs.utoronto.ca/~brudno/csc2427/myers.pdf>.

## 0. The three predicates (unchanged, audited)

The corrected model does **not** redefine any proven symbol. The three predicates
coexist:

1. `Section62Flow.isReducibleB` / `transitivelyReduced` — the literal "two
   strictly shorter shared overlaps" reading. Kernel-proved **vacuous** on every
   proper-overlap edge, hence the identity filter:
   `Section62ReductionVacuityAudit.transitivelyReduced_eq_self_of_proper`.
2. `Section62Flow.isReducibleLongerB` / `transitivelyReducedLonger` — the
   longer-shared-overlap-only filter. **Not** the spelling-preserving reduction:
   `Section62ReductionMismatch.longer_is_not_spelling_preserving` is a
   kernel-checked finite witness where it deletes an edge whose detour spells a
   *different* word.
3. `Section62SpellingReductionCandidate.isReducibleSpellingB` /
   `transitivelyReducedSpelling` — the true two-edge **spelling-preserving**
   reduction: a genuine observed intermediate strand `m` and proper overlaps
   `l₁, l₂ < readLen` with `l₁ + l₂ = readLen + e.len`, whose path spells exactly
   the direct word (`spellPath_eq_spellDirect`). Forced `l₁, l₂ > e.len`
   (`replacement_overlaps_longer`), and full-overlap edges are never removed
   (`fullOverlap_not_reducible`/`fullOverlap_survives`).

Requirement (1) — "preserve the old predicate explicitly as a model being
audited" — is satisfied by keeping (1) and (2) in place with their audit notes,
and by adding (3) rather than mutating (1).

## 1. Re-audit of every §6.2 result that depended on the old `transitivelyReduced` (requirement 6)

The old predicate is the identity on proper-overlap edge lists
(`transitivelyReduced_eq_self_of_proper`). Therefore every formal statement of
the form "these walk steps survive the reduction" was **vacuous**; its real
content was membership in the unreduced `overlapEdges` graph. The dependent
modules and their verdicts under the corrected `transitivelyReducedSpelling`:

| Module | Old-reduction use | Corrected-reduction verdict | Kernel evidence |
|---|---|---|---|
| `Section62BridgingCounterexample.lean` | `truth/competitor_steps_survive_reduction` via `transitivelyReduced` | **survives**: all steps are maximal `L−1 = 2` overlaps; no full-overlap edge is reducible | `fullOverlap_survives`; general `transitivelyReducedSpelling_eq_self_of_full` |
| `SameLengthSection62Counterexample.lean` | same | **survives**: maximal-overlap walk | `fullOverlap_survives` |
| `PerOccurrenceSameLengthCounterexample.lean` | same | **survives**: `oMin = readLen − 1 = 2`, only maximal overlaps | `fullOverlap_survives` |
| `Section62NonSpelledFlow.lean` | `graph_reduction_vacuous_literal`; flows checked on `reducedList` | **survives**: spelling reduction of `graph1` equals `reducedList`; the used length-`1` edge `AAT→TAA` survives because its only spelling detour goes through the **unobserved** `ATA` | `nonspelled_reduction_spelling_eq` (`decide`), `star21_feasible62_spelling_reduced` |
| `Section62ReductionVacuityAudit.lean` | diagnostic of (1) | **unchanged**: it is the audit, not a consumer | `transitivelyReduced_eq_self_of_proper` |

Kernel-checked bridge theorems live in
`AssemblyP1/Section62ReductionDependencyAudit.lean`:

- `transitivelyReducedSpelling_eq_self_of_full` — any edge list all of whose
  edges have the maximal proper overlap length `readLen − 1` is fixed by the
  spelling-preserving reduction. This covers every `oMin = readLen − 1` witness.
- `stepsSurviveReductionSpelling_of_maximal` — the corrected replacement for the
  vacuous `StepsSurviveReduction`: the steps of any spelling walk lie on the
  spelling-reduced graph.
- `nonspelled_reduction_spelling_eq` — at `oMin = 1`, the spelling reduction of
  the `AAATT` graph equals `reducedList` exactly (order included).
- `star21_feasible62_spelling_reduced`, `truth_feasible62_spelling_reduced`,
  `star31_feasible62_spelling_reduced` — the `Section62NonSpelledFlow` flows are
  §6.2-admissible on the **spelling-reduced** graph, not merely on the
  longer-overlap reduction.

**Conclusions that survive verbatim:** the bridging, same-length and
per-occurrence strict-ML/bridging counterexamples; the non-spellable-flow
countermodel (`no_sequence_has_star_spectrum`, `star_argmax`) and its strict
likelihood ratios.

**Conclusions that must be re-stated (mathematically unchanged, wrapper
changed):** any theorem whose *statement* mentions `SpelledFeasible62` or
`StepsSurviveReduction` (the old vacuous conjunct). The mathematical content
(the flow is feasible on the reduced graph) survives; the formal predicate should
be read with `transitivelyReducedSpelling`. `spelled_subset_general` and the
non-spellable-flow countermodel are already stated over the general `Feasible62`
predicate and are unaffected.

**Not dependent on the old predicate (survive unchanged, but their feasibility is
on the full `overlapEdges` graph and must be placed in the reduced model by the
same support-survival argument):** `SameLengthSection62Parametric`,
`Section62FullOverlapDisconnected`, `Section62VariableOverlap247e`,
`Section62VarlenPerOccurrence`, `OrientedVariableLengthSe62`, and the
`SameLength*` ML modules. None of their stated theorems reference the old
reduction; adopting the corrected graph requires only the (mostly maximal-overlap)
support check, not a re-proof of their inequalities.

## 2. Global circular spelling and the seam criterion (requirement 5)

The graph-side half is kernel-checked in
`AssemblyP1/Section62GlobalCircularAudit.lean`:

- `global_walk_reduced_skips_no_observed_window` — for **any** signed walk of
  `overlapEdges` edges, its surviving expansion is a signed walk of
  spelling-reduced edges with the same endpoints, the same spelled tail
  (`toList start ++ pathTail`), and **no** observed internal length-`readLen`
  window on any edge. The intermediate strand is quantified over
  `strandsOf rc verts`, so both strands of every observed molecule class are
  covered (the RC/class lift is automatic at this level).
- `global_closed_walk_reduced_skips_no_observed_window` — the closed (circular)
  specialization.

The remaining obligation is the **cyclic-start partition identity** for the
spelled circular genome `D` of a closed walk with visits `u₀,…,u_{m−1}`, proper
overlaps `ell_j < L`, extensions `e_j = L − ell_j ≥ 1`, partial sums
`s₀ = 0`, `s_j = Σ_{a<j} e_a`, and circular length `G = Σ_j e_j`:

    C_D(c) = V(c) + Σ_{j=0}^{m−1} Σ_{u=1}^{e_j−1} [ class(window(D, s_j + u)) = c ],

where `C_D(c)` counts **all `G` circular length-`L` windows** of class `c` and
`V(c)` counts the visited reads of class `c`. Because the intervals
`[s_j, s_j + e_j)` partition the `G` circular start positions and the `u ≥ 1`
terms are nonnegative, for any observed class set `S`:

    (∀ c ∈ S, C_D(c) = V(c))  ⇔  no skipped internal window has class in S.

This identity is now **kernel-checked in two layers**:

- the abstract cyclic-start partition and its iff criterion are proved for any
  class-valued function of genomic starts in
  `AssemblyP1/Section62CircularStarts.lean`
  (`covered_class_count`, `covered_count_eq_anchors_iff_no_internal`);
- the **circular spelling adapter** `AssemblyP1/Section62CircularWindowAdapter.lean`
  instantiates that partition at the concrete circular window
  `window D readLen s = (D.drop s ++ D.take s).take readLen` of the spelled
  genome, via the `CircularSpelling` spelling hypotheses (genome length =
  extension sum, anchored windows = visited reads in order, no observed internal
  window).  Its `window_count_decomposition` is exactly (1), its
  `window_count_eq_anchors_iff` is exactly (2), and `observation7_window_count`
  is Observation 7 at the word level: for every observed strand `m`, the number
  of circular `readLen`-windows of `D` spelling `toList m` equals the number of
  walk vertices spelling `toList m`.  The bridge
  `interior_count_zero_of_pointwise` turns the pointwise surviving-edge no-skip
  theorem into the count-zero hypothesis the partition consumes.

  **Window-scope caveat.**  `window D readLen s` is the true length-`readLen`
  circular window only when `readLen ≤ D.length`; when the spelled genome is
  shorter than one read (`G = D.length < readLen`) the rotation
  `D.drop s ++ D.take s` has length `G`, so `.take readLen` returns the whole
  rotation rather than a genuine wrap-around length-`readLen` window.  The
  adapter's `observation7_*` theorems are stated for the concrete `window`
  function and therefore cover the `readLen ≤ G` regime; the `G < readLen`
  wrap-around window is part of the bounded remaining work recorded below.

The **only remaining sub-obligation** is the canonical construction of the
circular genome `D` from a signed walk and the proof that it satisfies the
`CircularSpelling` hypotheses (the coherence of the signed overlap data across
the seam); the adapter is the composition interface that the source note
`docs/section62-observation7-skipped-windows.md` calls for.

### The circular seam itself (new module)

`AssemblyP1/Section62GlobalCircularCorrespondence.lean` supplies the *circular*
half of the global spelling correspondence, which the open-walk expansion above
does not by itself provide. A `Circuit v walk` is a `SignedPath v v walk` whose
last edge arrives at `v` with the incidence opposite to the first edge's
departure (`Circuit`'s seam conjunct, the MB09 §3.2 signed-walk condition at the
closing vertex). The module proves:

- `surviving_seam_opposite` — every surviving expansion of a closed walk closes
  with opposite incidences at the seam, because both boundary edges are graph
  edges (`edge_signs_of_mem`) and `sgnRep`/`sgnTgt` are negatives
  (`sgnRep_neg_sgnTgt`);
- `global_circuit_signed_expansion` / `global_circuit_circular_word` — a circuit
  of `overlapEdges` edges expands into a circuit of `transitivelyReducedSpelling`
  edges spelling the same circular word `pathTail`;
- `pathTail_length` / `circularWord_length` — the total spelled length is
  `G = Σ_e (readLen − e.len)`, with **no** hypothesis `readLen ≤ G`, so the
  `G < readLen` regime (genomes shorter than one read, with wrap-around windows)
  is covered by the same statement;
- `mem_strandsOf_self` / `mem_strandsOf_rc` — the intermediate strand of the
  reduction ranges over `strandsOf rc verts`, which contains both `m` and `rc m`
  for every observed molecule class, so reverse-complement intermediates are
  available.

The corrected predicate itself is **not** redefined in the base §6.2 model
module; it remains exactly `Section62SpellingReductionCandidate.transitivelyReducedSpelling`,
which is what #261/#262 consume. Requirement (1) is satisfied by keeping the old
`Section62Flow.isReducibleB`/`transitivelyReduced` and the coarse
`isReducibleLongerB`/`transitivelyReducedLonger` in place (with their audit
notes) and adding the corrected predicate alongside, not by mutating either.

### Scope caveat (source fidelity)

This proves Observation 7 for the *implemented spelling-preserving candidate*, not
for the literal MB09 "two shorter nucleotide overlaps" predicate (which is
vacuous, §0) and not for Myers's full algorithm (contained reads, parallel
overlaps, minimum-overlap policies, RC details unchecked). It also does not by
itself establish full genome ML; see §3.

## 3. The §6.1 full-spectrum unseen-factor identity (requirements 4–5, source fidelity)

MB09 §6.1 defines the global read-count likelihood over **all `4^k` k-molecule
outcomes** and approximates it by the product of per-molecule binomials over
**all** classes:

    L ≈ ∏_i C(n, x_i) (d_i/N)^{x_i} (1 − d_i/N)^{n − x_i}.

A class with `x_i = 0` and `0 < d_i < N` contributes the **strict penalty**
`(1 − d_i/N)^n < 1`. The §6.2 graph vertices are only *observed reads*, so the
observed-vertex flow surrogate omits these penalties.

Kernel-checked in `AssemblyP1/Section62FullSpectrumUnseenFactor.lean`. For the
`#214` non-spellable circuit `AAA → AAA → AAT → TAA → AAA` spelling
`D = AAATA` (length `N = 5`), with `n = 4` reads and sample
`x = (AAA:2, AAT:1, ATA:0, TAA:1)`:

- truth `S = AAATT`: spectrum `dS = (AAA:1, AAT:2, ATA:0, TAA:2)`;
- candidate `D = AAATA`: spectrum `dD = (AAA:2, AAT:1, ATA:1, TAA:1)`;
- observed-vertex ratio `L_obs(D)/L_obs(S) = 256/81 > 1`;
- unobserved-`ATA` factor ratio `(1 − 1/5)^4 = 256/625 < 1`;
- **full** §6.1 ratio `L(D)/L(S) = (256/81)·(256/625) = 65536/50625 > 1`
  (`full_ratio`, `full_ratio_gt_one`), strictly below the observed-only ratio
  (`full_ratio_lt_observed_ratio`).

Theorems: `observed_ratio`, `unseen_factor_ratio`, `unseen_factor_lt_one`,
`full_eq_observed_mul_unseen`, `full_ratio`, `full_ratio_gt_one`,
`full_ratio_lt_observed_ratio`, and the general contraction lemma
`unseen_factor_contract`.

**Consequence:** the non-spellable candidate still beats the truth under the
*full-spectrum* §6.1 objective, but the observed-vertex surrogate **overstates**
it by exactly `256/625`. The observed-flow surrogate and the complete-spectrum
likelihood are therefore genuinely different objectives and must not be conflated.

### The indexing decision (recorded as an explicit modeling choice; kernel-checked for the instance)

§6.1 indexes `X_i` over `4^k` outcomes while calling them *k-molecules*.  MB09
§3.1 models a DNA molecule as an unordered reverse-complement strand pair, so the
repository **chooses** to index by **reverse-complement classes**, not oriented
k-mers: a non-palindromic oriented k-mer `w` and `rc w` are the same molecule,
counted once with class frequency `c_S(w) + c_S(rc w)`.  For length `k` there are
`(4^k + f_k)/2` RC classes (`f_k = 0` for odd `k`, `f_k = 4^{k/2}` for even `k`
by Burnside on the involution `rc`).

This choice is a **modeling decision, not a source fact**, and the two readings
have different cardinalities and different likelihood objectives.  MB09 §6.1
states literally that "There are `4^k` such variables"; that count is the number
of *oriented* k-mers, whereas the unordered RC molecule classes of §3.1 number
`(4^k + f_k)/2` — roughly half.  The `4^k` wording therefore cannot itself be the
RC-class count, and treating the §6.1 index as RC molecule classes refines the
literal text rather than following from it.  The repository adopts the RC-class
reading because §3.1 defines a molecule as an unordered strand pair and §6.2
builds molecule vertices; the choice is recorded here so it is not mistaken for
an established reading of the source.  This decision is kernel-checked for the
binary length-3 instance in
`AssemblyP1/Section62FullSpectrumIndexing.lean`: `rc3_orbit_count` proves the
reverse-complement involution `rc3` on `Fin 3 → Bool` has exactly `4` orbits,
each of size `2` (`rc3_orbit_card_two`), matching `(2^3 + 0)/2` and
`Mol = Fin 4`.  The same module proves the general full-spectrum identity
`fullProduct = observedProduct * unseenProduct`, that unseen count-zero factors
are exactly `1`, and that an unseen class with `0 < d < N` contributes the strict
penalty `(1 − d/N)^n < 1` (`factor_zero_lt_one`).  The fully general Burnside
orbit count for arbitrary `k`, and the `G < k`/seam edge cases, remain to be
formalized before promoting any complete-spectrum likelihood statement.

## 4. Summary

- Requirement (1): old predicates preserved and audited; corrected predicate
  added, not substituted.
- Requirements (2)–(3): already kernel-checked on `main`
  (`Section62SpellingReductionCandidate`): genuine proper overlaps,
  composition law, forced `l₁,l₂ > e.len`, reverse-complement-aware intermediates,
  automatic signed-incidence consistency.
- Requirement (4): finite positive regression with a genuinely removed edge and
  the longer-only vs spelling-preserving mismatch witness
  (`Section62ReductionMismatch`).
- Requirement (5): global walk expansion + no-observed-skip theorem, the exact
  circular seam partition and iff criterion (`Section62CircularStarts`), the
  circular spelling adapter and Observation-7 word-count identity
  (`Section62CircularWindowAdapter`), and the §6.1 full-spectrum identity and
  indexing decision (`Section62FullSpectrumIndexing`) — all kernel-checked.
  The canonical construction of the circular genome from a signed walk and the
  seam-coherence proof of the `CircularSpelling` hypotheses remain open.
- Requirement (6): dependency re-audit above; all dependent conclusions survive,
  with the precise "wrapper must be re-stated" caveat.
- Requirement (7): signed branch/PR, kernel replay and axiom audit on the exact
  head; this note and its modules are the artifact.
