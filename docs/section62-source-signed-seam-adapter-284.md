# §6.2 signed-circuit to aligned-circular-genome adapter (#284)

_Status: kernel-checked adapter plus a concrete non-vacuity regression,
2026-10-15. This note records the source-specific adapter that turns a genuine
closed signed overlap walk in the §6.2 complete bidirected graph into the exact
cyclic seam and the aligned circular word consumed by the periodic-seam lemmas.
It does **not** claim Myers/MB09 algorithm equivalence and does **not** settle
full genome ML maximality; those stay with #261/#262._

Primary sources:

- Medvedev–Brudno, *Maximum Likelihood Genome Assembly*, J. Comput. Biol. 16(8)
  (2009) 1101–1116, §3.1–3.4, §5.2, §6.1–6.2,
  <https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/>.
- Myers, *The fragment assembly string graph*, Bioinformatics 21 Suppl. 2 (2005)
  ii79–ii85, <https://www.cs.utoronto.ca/~brudno/csc2427/myers.pdf>.

## 1. The audited model is unchanged

The corrected model does **not** redefine any proven symbol. In particular
`Section62BidirectedFlow.isReducibleB` and `Section62Flow.transitivelyReduced`
(the literal "two strictly shorter shared overlaps" reading) remain in place as
the model being audited; the spelling-preserving predicate
`Section62SpellingReductionCandidate.transitivelyReducedSpelling` is a separate
symbol. This note adds no change to either. The dependency re-audit is in
`section62-global-circular-and-unseen-factor-284.md` §0 and §2.

## 2. The word-level overlap-walk lemmas (`Section62OverlapSuffix`)

These are graph-independent `List` identities. They make no claim about
arbitrary feasible flows; the graph must still supply legal overlap edges, a
closed signed walk, and its visited anchors.

| Theorem | Statement (informal) |
|---|---|
| `direct_spelling_ends_in_target` | For `u.length = L`, `ell ≤ L` and suffix/prefix overlap `u.drop (L-ell) = v.take ell`, the spelled word `u ++ v.drop ell` has final length-`L` window exactly `v`. |
| `appended_extension_ends_in_target` | If `X`'s last `L` symbols are `u` and a legal overlap `u → v` is appended, `X ++ v.drop ell`'s last `L` symbols are `v`. |
| `pathExt_ends_in_target` | By induction on `ValidPath L u steps`: the walk's spelled word ends in its final visited read `pathTarget u steps`. |
| `pathExt_eq_append_tails` | The spelled word factors as `X ++ steps.flatMap (fun p => p.2.drop p.1)`. |
| `closed_path_seam` | If the walk is closed (`pathTarget start steps = start`), then with `X := start ++ tails` and `tails.length = G`, `X.take L = X.drop G`. |

## 3. The graph-level adapter (`Section62SourceSignedSeamAdapter`)

`SignedPath start sy edges` (from
`Section62GlobalSpellingPreservation`) records signed walk adjacency;
`overlapEdges A W toList rep rc readLen oMin verts` is the complete bidirected
overlap edge set of the observed vertex classes.

| Theorem | Statement (informal) |
|---|---|
| `valid_graph_steps` | If every step edge lies in `overlapEdges` and the edges form a `Step`-chain, then `graphSteps toList edges` is a `ValidPath readLen (toList start)`. |
| `target_graphSteps_of_last` | Purely structural: the projected walk's final target read is the last source edge's arrival strand `toList sy`. |
| `signedPath_valid_graph_steps` | **The projection.** A genuine `SignedPath start sy edges` whose edges lie in `overlapEdges` projects to `ValidPath readLen (toList start) (graphSteps toList edges)` **and** `pathTarget … = toList sy`. Source endpoints are preserved. |
| `graphSteps_tails_eq_pathTail` | The projected steps append exactly the source spelling's `pathTail toList edges`. |
| `signed_circuit_seam` | A **closed** genuine signed walk (`SignedPath start start edges`) satisfies `(toList start ++ pathTail).take readLen = (toList start ++ pathTail).drop (pathTail).length` — the exact seam hypothesis of the merged periodic-seam lemmas. |
| `signed_circuit_tail_pos` | A closed circuit has `0 < (pathTail …).length` (graph overlaps are proper), so the period `G` is nonzero. |
| `signed_circuit_aligned_periodicity` | Composing the seam with `Section62PeriodicSeam.seam_periodic_prefix`: for every in-bounds `i`, `X.getD i default = (X.take G).getD (i % G) default`, where `X = toList start ++ pathTail` and `G = (pathTail …).length`. Handles `G < readLen`. |

Here `D := (toList initialVertex ++ pathTail).take G` is the aligned circular
word (the **first** `G` letters of the linearization, not the appended tail), and
the initial read is anchored at index `0` by
`Section62PeriodicSeam.seam_tail_rotation` (the tail is a rotation of `D` by
`readLen`).

## 4. Non-vacuity regression (`Section62SignedAdapterRegression`)

The adapter hypotheses are instantiated on two concrete legal signed overlap
circuits, so they are true by `decide`/`rfl` rather than assumed, and the
conclusions are checked against exact expected words:

- **Instance 1** (`readLen = 3`, `G = 4`): the cycle `ABC → BCD → CDA → DAB →
  ABC` with proper 2-letter overlaps. `X = ABCDABC`, aligned genome `D = ABCD`,
  `pathTail = DABC` (rotation by `readLen % G = 3`).
- **Instance 2** (`readLen = 5 > G = 3`): the cycle `ABCAB → BCABC → CABCA →
  ABCAB` with proper 4-letter overlaps. The length-5 reads wrap the length-3
  genome twice; `window` from the merged circular-window adapter still yields a
  genuine length-5 read.

Each instance records two **revert witnesses**: replacing the aligned genome by
the raw `pathTail` makes the start-0 anchor the wrong read (`DAB ≠ ABC`), and
reverting to the pre-#219 rotation-only window makes the `G < readLen` window
too short to be a read (`[0,1,2] ≠ ABCAB`, length 3 ≠ 5). The module checks the
adapter's seam/periodicity conclusions and the anchored half of
`CircularSpelling.hAnchors` only; it claims no full `CircularSpelling`, no
`hInteriorSkipped`, no Observation 7, and no Myers/MB09 equivalence.

## 5. What is and is not established

| Claim | Status |
|---|---|
| A legal signed `overlapEdges` walk projects to a word-level `ValidPath` | **kernel-checked** (`signedPath_valid_graph_steps`) |
| A closed genuine signed walk forces the exact length-`L` cyclic seam | **kernel-checked** (`signed_circuit_seam`) |
| The aligned word `D = (toList start ++ pathTail).take G` is periodic and anchors the first read at index 0, including `G < readLen` | **kernel-checked** (`signed_circuit_aligned_periodicity` + `Section62PeriodicSeam`) |
| Non-vacuity on concrete legal circuits | **kernel-checked** (`Section62SignedAdapterRegression`) |
| Canonical construction of `D` from a *general* signed walk (not a single closed circuit) and the seam-coherence proof of `CircularSpelling` | **open** |
| Fully general Burnside orbit count for arbitrary `k`, and `G < readLen` wrap-around windows in full generality | **open** |
| Exact Myers/MB09 algorithm equivalence (contained reads, parallel overlaps, minimum-overlap policy) | **open** |
| Full genome ML maximality lift for #261/#262 | **open** (not this note) |

## 6. References

- `docs/section62-global-circular-and-unseen-factor-284.md` (dependency re-audit,
  corrected reduction predicate, §6.1 unseen-factor identity).
- `docs/section62-full-spectrum-adapter-284.md` (§6.2 observed-vertex objective
  vs. §6.1 full-spectrum product).
- `docs/ml-formalization-contract.md` (flow feasible set vs. candidate universe).

## Window alignment bridge (new, Lean-verified)

`Section62AnchoredWindowBridge.periodic_window_eq_drop_take` proves that
for a closed spelling `X` of length `L+G` with `G>0` and
`X.take L=X.drop G`, its derived circular genome `D=X.take G` obeys

`window D L s = (X.drop s).take L` for each `s<G`.

The source-specific corollary `signed_circuit_window_eq_linear` obtains
this equality directly from a genuine `SignedPath` of `overlapEdges`,
including `G<L` (multiple wrapping). This proves geometric alignment
of actual genomic windows with the linearized spelling but does **not** yet
identify the *j*-th linear read at its accumulated extension anchor or
transport the reduced-edge no-skipped-observed-window property. Those
remain necessary for unconditional Observation 7 occurrence equality.

## Source-read anchor equality (new, kernel-checked)

`Section62AnchorSourceWords.aligned_source_words` is a generic induction over
honest suffix/prefix overlaps: at every cumulative edge-extension anchor, the
linearized spelling's length-`L` window is exactly the source read for that
edge. The source-specific corollaries
`signed_circuit_anchors_linear` and
`signed_circuit_anchors_are_read_words` discharge the
`CircularSpelling.hAnchors` field **for any actual closed SignedPath of the
complete overlap graph**, including repeated wraps when `G<L`.
They derive both the exact tail-length equation and positivity of extensions
from graph membership; anchor-bounds are proved, not assumed.

The remaining independent `CircularSpelling` obligation is
`hInteriorSkipped`: translate the implemented spelling-reduced graph's
local no-observed-intermediate-window certificate into the periodic circular
genome's internal windows. That source-specific translation is required
before claiming unconditional Observation 7.

## Full reduced-circuit Observation 7 (new, Lean-verified)

`Section62GlobalSkippedBridge` now **discharges** the remaining
`CircularSpelling.hInteriorSkipped` clause rather than assuming it.
Its `aligned_interiors_no_observed` proves by induction that every internal
window of a legal multi-edge linearized spelling is contained in its edge's
direct spelling, or in the corresponding suffix subwalk.
`reduced_graph_no_observed_steps` obtains the local premise directly from
the *implemented* `transitivelyReducedSpelling` edge predicate and
`surviving_edge_skips_no_observed_strand`.
`reduced_signed_circuit_no_skipped_windows` then transports that fact to
the genuinely **periodic circular** genome, including all seam crossings.

The target theorem
`observation7_reduced_signed_circuit_range_count` states directly in Lean
that **for every observed strand word** the count among all circular read
windows equals the number of visits to that strand as a signed circuit's
departure read. Its `CircularSpelling` witness is *constructed* from the
actual reduced signed path, not supplied as a hypothesis.

`Section62Observation7Regression` instantiates this theorem on concrete
nonempty reduced circuits for both `G=4,L=3` and `G=3,L=5` (multiple wraps),
with all graph-membership, reduction and signed-circuit premises kernel-checked.
Both examples have extension length one. An additional **independent
computational** check, `python3 scripts/verify_284_nontrivial_skipped_windows.py`,
exercises two reduced edges of extension length two on the circle `ABCD`:
visited reads `ABC,CDA`, skipped windows `BCD,DAB`, neither observed.
This check is not presented as an extra Lean theorem; the general Lean
proof already covers all positive extension lengths.

**Scope:** This proves the full oriented-strand word-count statement for the
repository's spelling-preserving reduction. It does **not** prove that the
implemented reduction is identical to Myers 2005 / the exact MB09 graph
construction, nor that every feasible balanced integer flow is a single
closed signed walk, nor the quotient treatment of reverse-complement molecule
classes (especially palindromic reads). Those remain independent obligations.
