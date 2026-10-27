# Issue #261: Myers signed-edge reduction reconstruction and correspondence result (2026-10-27)

**Agent:** agent-bNlFBN92 (isolated clone `/workspace/agent-bNlFBN92-issue261`,
branch `agent-bNlFBN92-issue261-myers-reduction`, base `main@3decc39`).
**Status:** checkable increment; does NOT close #261 or #255.

## 1. Independent reconstruction (Myers 2005 §2 → repository predicates)

Myers 2005 §2 (ii81): an edge `f→h` is transitive iff a two-hop path `f→g→h`
spells the same sequence. Repository formalization reviewed in this checkout:

- Semantic relation: `Section62MyersIdealTransitivity.TwoHopSameSpelling` —
  observed intermediate strand `m`, proper overlaps `l1,l2 < L` with
  `oMin ≤ l1,l2`, genuine suffix/prefix matches, and word equality
  `spellPath = spellDirect`.
- Implemented test: `Section62SpellingReductionCandidate.isReducibleSpellingB`
  — same data plus the Diophantine law `l1 + l2 = L + e.len`.
- Kernel-checked iff (`reducible_iff_ideal_two_hop`, both directions; converse
  via spelled-length comparison `3L-l1-l2 = 2L-l`): the test is exactly the
  idealized same-spelling two-hop relation for proper equal-length error-free
  reads. `reduced_mem_iff_no_ideal_detour` lifts it to the edge filter.
- Signed/bidirected incidence: detour legs `bdEdge rep e.sx m l1`,
  `bdEdge rep m e.sy l2` satisfy complementary signs
  (`detour_signs_match`), so the two-hop replacement is a signed bidirected
  path, not merely a word equality.
- Scope boundary (unchanged): equal-length, error-free, deduplicated model
  only. No claim about Myers §3/Fig.4 `FUZZ=10` noisy overlaps, contained
  reads, or parallel-edge collapsing. Verified by reading
  `docs/section62-myers-ideal-transitivity-284.md` against the Lean sources
  in this checkout (not by a fresh `lake build`; full build exceeded 600s
  timeout in this environment — recorded as not-run).

## 2. Graph-language correspondence: HOLDS (idealized model)

`Section62SimultaneousReduction.reduction_preserves_language`
(kernel-checked per `docs/section62-simultaneous-reduction-284.md`):
every edge of the complete `overlapEdges` graph expands into a chain of
**irreducible** edges of `transitivelyReducedSpelling` spelling the same word.
Well-founded measure `Ext L e = L - e.len` strictly decreases on both detour
legs (`replacement_overlaps_longer`). The two-level cascade
`sx=01234, m1=23412, m2=12341, sy=41200` exercises simultaneity (first detour
leg itself reducible); all six `decide` facts re-verified numerically in this
run (see §4): direct `1`-overlap and one-step `3+3` path both spell
`012341200`; expanded chain `sx→m2→m1→sy` spells the identical word.

## 3. Observation-7 occurrence correspondence: HOLDS for reduced signed circuits, FAILS for arbitrary edge expansion (exact counterexample)

- **Positive (reduced signed circuits):**
  `Section62GlobalSkippedBridge.observation7_reduced_signed_circuit_range_count`
  proves that for a signed circuit `walk` whose every edge survives in
  `transitivelyReducedSpelling`, every observed oriented read word occurs in
  the spelled circular genome exactly as many times as it is visited as an
  edge departure strand (all `G` circular starts, wraps `G<L` included).
  `Section62Observation7Regression` kernel-checks two instances (`G=4,L=3`
  and `G=3,L=5`). This is the source-faithful Observation 7 for the
  implemented reduction; hypotheses are explicit (signed path, survival,
  equal read length).
- **Negative (arbitrary edge↔expansion substitution):** the same cascade is an
  exact counterexample to the stronger claim sometimes needed for ML transfer.
  Both the direct edge `sx→sy` and the expansion `sx→m2→m1→sy` spell
  `012341200`; the full length-5 window multiset
  `{01234,12341,23412,34120,41200}` is identical. But the direct walk visits
  `[sx,sy]` while the expansion visits `[sx,m2,m1,sy]`, and window `34120` is
  a physical window of the spelled word with **no observed read vertex**.
  Hence neither spelled-string equality nor its physical-window multiset
  implies equality of graph-vertex visits with physical occurrence counts.
  Re-verified by exact integer computation in this run (all windows listed,
  membership tested). This blocks inferring a vertex-throughput ML objective
  from language preservation alone.

## 4. Exact small-instance evidence (this run, no Lean build)

```
direct  sx→sy (ov 1): [0,1,2,3,4,1,2,0,0]
one-step via m1 (3+3=5+1): identical
chain sx→m2→m1→sy: identical
windows (L=5): 01234, 12341, 23412, 34120, 41200
34120 ∈ windows: True; 34120 ∈ {sx,m1,m2,sy}: False
```

## 5. Arbitrary-`o_min` candidate/likelihood audit (resume)

| Axis | Candidate universe | Truth admitted? | Likelihood / length universe | Result |
|---|---|---|---|---|
| Variable-length exact multinomial | count vectors, variable `N` (flows, not circuits) | yes | exact `∏(d_i/N)^x_i`, variable `N` | RESOLVED (count-vector layer; not the §6.2 algorithm objective) |
| Fixed-external-`N` product | throughput vectors, `N=G` fixed | yes | exact multinomial w/ common `N`, fixed | RESOLVED, correctly labelled (not binomial) |
| Genuine §6.1 product-binomial | full-universe count vectors `d:T→ℕ` | yes (interior `q_i(A)>0`) | separable binomial, fixed external `N=G` | RESOLVED at count-vector layer (uniform + fixed-`n` extreme iff); flow-level OPEN (image, unobserved-coordinate convention, probability bounds `0≤d≤N` vs infinite capacities) |
| Integer vs half-integral | integer `Feasible62` vs `ℚ` relaxation; **flows** | yes | exact multinomial, variable `N=∑d` | RESOLVED for half-integral (`no_half_integral_gap_exact`); real LP OPEN |
| Non-spelled flows | §6.2 feasible flows incl. non-spelled | yes | separable binomial, fixed `N=G` | OPEN as general criterion; `AAATT o_min=1` 256/81 obstruction kernel-checked |
| Orientation/RC | tagged `OStrand` corrected domain | yes | throughput-factoring scores | PARTIAL (representation fixed; reduction interaction + RC quotient OPEN) |
| Transitive reduction × ML | spelled circuits on reduced graph | yes | binomial / exact | OPEN: language preservation + Observation 7 proved, but no ML maximality criterion; full-overlap failures transfer only via proved candidate-set inclusion (`maximal_of_subset` direction) |

Transfer rule respected: negative ML results move to §6.2 only with proved
candidate-set inclusion; positive statements do not transfer (`Section62FlowCountVectorAdapter`).

## 6. Validation

- `python3 scripts/check-research-docs.py`: PASS.
- Cascade numeric re-verification (python3 one-liner): PASS (see §4).
- `lake build` of the three reduction modules: NOT RUN to completion
  (timeout >600s building Mathlib deps in this environment); Lean claims
  above cite the kernel-checked modules/docs already in `main`, independently
  re-read here, not re-proved here.
- `git diff --check`: PASS (after write). No Lean changes in this increment.

## 7. Next

- Kernel-replay the three modules where a warm `.lake` build exists, or
  `leanchecker` a single module; then re-run `scripts/verify_261_*` + 284
  spelling verifiers on the exact reduced graph.
- Flow-level binomial adapter: throughput-image characterization, `0≤d≤N`
  convention, terminal-penalty separation, fixed-support Graver program.
- Keep #261 and #255 OPEN.

**Sources:** MB09 §6.2 (PMC3154397); Myers 2005 §2–§3; repo modules
`Section62SpellingReductionCandidate`, `Section62MyersIdealTransitivity`,
`Section62SimultaneousReduction`, `Section62GlobalSkippedBridge`,
`Section62Observation7Regression`; docs `section62-myers-ideal-transitivity-284.md`,
`section62-simultaneous-reduction-284.md`.
