# §6.2 spelling preservation does not transport vertex visits (#284)

This note records the precise status of the **physical visit-count transport**
question for the corrected §6.2 spelling-preserving transitive reduction. It is
the diagnostic requested on the board after the research-assistant caution that
word-spelling preservation does **not** imply graph-vertex visit-count or ML-flow
equivalence.

## What the reduction preserves

`AssemblyP1.Section62SpellingReductionCandidate` replaces a direct overlap edge
`sx → sy` of length `l` by a two-edge path `sx → m → sy` with proper overlaps
`l₁, l₂` satisfying the composition law `l₁ + l₂ = L + l`, under which both paths
spell the same word (`spellPath_eq_spellDirect`). A simultaneous reduction
therefore preserves the **spelled word** of every walk.

Because the full length-`L` window multiset of a word is a function of the word
alone, the reduction also preserves that window multiset. This is the positive
invariant, kernel-checked in
`AssemblyP1/Section62VisitTransport.lean`:

- `windows_congr` — equal words have equal window multisets;
- `windows_detour_eq` — a detour replacement preserves the window multiset
  (hypothesis: the detour spells the same word, which is exactly what the
  composition law gives).

## What the reduction does NOT preserve

The reduction does not preserve the physical class count. The
**physical class count** — the multiset of vertices (observed read molecules)
visited by a walk — is *not* determined by the spelled word. The `L = 5` witness
(`sx = 012341…`, i.e. `sx = 01234`, `m₁ = 23412`, `m₂ = 12341`, `sy = 41200`):

| walk | overlaps | spelled word | vertex visit list |
|------|----------|--------------|-------------------|
| direct `sx → sy` | `1` | `012341200` | `[sx, sy]` |
| one-step `sx → m₁ → sy` | `3, 3` | `012341200` | `[sx, m₁, sy]` |
| two-step `sx → m₂ → m₁ → sy` | `4, 4, 3` | `012341200` | `[sx, m₂, m₁, sy]` |

All three spell the same word, so all three have the same full window multiset
`{01234, 12341, 23412, 34120, 41200}`. But the vertex visit lists differ (lengths
2, 3, 4). The window `34120` is a **seam window**: it is a length-`5` window of
the spelled word but is not a vertex of *any* of the walks.

Consequently the invariant window multiset decomposes differently for different
walks:

- direct: `{sx, sy}` (2 observed) `+ {m₂, m₁, 34120}` (3 unobserved);
- two-step: `{sx, m₂, m₁, sy}` (4 observed) `+ {34120}` (1 unobserved).

The observed part grows while the unobserved part shrinks; only the total is
invariant.

## The precise obstruction

`no_transport_function` (kernel-checked): **no function of the invariant window
multiset can transport physical class counts.** Any such function would have to
send the same window multiset to two different vertex multisets. Equivalently,
`transport_required` — "walks with the same spelled word have the same vertex
multiset" — is refuted at `L = 5` (`transport_required_false`).

This is the exact missing invariant. To carry a §6.2 vertex-throughput or ML
objective through the reduction one would need an extra hypothesis identifying
which windows of the spelled word are physically observed reads (an explicit
source-model convention accounting for seam windows). Spelling preservation alone
does not provide it.

## Scope

- The positive invariant (`windows_detour_eq`) is a genuine, kernel-checked
  consequence of the merged spelling reduction.
- The obstruction is a genuine, kernel-checked refutation of the naive transport.
- This module does **not** redefine `isReducibleB`, `transitivelyReduced`,
  `SpelledFeasible62`, or `StepsSurviveReduction`, and does not reprove any merged
  §6.2 theorem. It is self-contained (Lean core only) so the diagnostic stands
  independently of the heavy §6.2 chain.
- The physical visit-count transport to §6.2 feasible flows / ML likelihood
  remains **OPEN**; see the board for the assigned follow-up.

## Verification

- `lean` compile of the module: exit 0.
- `leanchecker AssemblyP1.Section62VisitTransport`: exit 0.
- Every `#print axioms` endpoint depends only on `{}` or
  `{propext, Classical.choice, Quot.sound}`; no `sorryAx`.
- `scripts/verify_284_visit_transport.py`: exit 0.
