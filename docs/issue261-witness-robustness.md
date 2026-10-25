# Robustness axes of the #261 real-flow midpoint witness (#261)

Bounded increment on top of `docs/issue261-real-flow-candidacy.md` (which
places the midpoint `(3/2,1,1,1)` in (F) but in none of (I)/(C)/(G) with
fixed-`N` binomial ratio `625/576`). This note records three exact,
small-instance robustness facts about that same `AAATT` witness (`L=3`,
`o_min=1`, full overlap `graph1`, zero terminals, external `N=5`, read
counts `x=(2,1,1)`). Checked by
`scripts/verify_261_witness_robustness.py` with exact rationals. It states
no general maximality criterion.

## (O) Overlap-threshold sensitivity: the witness is `o_min=1`-specific

The four `graph1` edges have proper-overlap lengths `(3, 2, 1, 2)` in
coordinates `(AAA loop, AAA→AAT, AAT→TAA, TAA→AAA)`: the loop is the
full-length self overlap, `AAA→AAT` and `TAA→AAA` share `"AA"`, and
`AAT→TAA` shares only `"T"`. Every witness flow (both integer endpoints
and the midpoint) carries flow `1` on the overlap-1 edge, which is absent
at `o_min=2`. Hence the witness is infeasible outside `o_min=1`: it does
**not** transfer upward to stricter thresholds, and a fortiori no claim is
made about transitively reduced graphs. A general `o_min`-uniform
maximality statement remains OPEN and needs a new witness family.

## (V) Vertex-bound tightness: lower bound 1 binds at two vertices

Throughputs are `(2,1,1)`, `(3,1,1)`, `(5/2,1,1)` for endpoint A, endpoint
B, and the midpoint. In all three, the `AAT` and `TAA` throughputs equal
exactly `1` (bound tight, slack `0`) while `AAA` is slack (`1`, `2`,
`3/2` of slack respectively). So the vertex lower bound is load-bearing
for feasibility of the witness class on this instance: dropping it to `0`
would strictly enlarge (F), and tightening it above `1` would kill the
witness. The bound-`1` axis is therefore resolved for this instance and
open in general.

## (L) Likelihood-choice sensitivity: tie vs strict ranking

- **Fixed external-`N` product-binomial** (`N=5`, §6.1 second display, the
  objective §6.2 optimizes): the two integer endpoints tie exactly (this
  matches Lean `star_argmax`); the real midpoint beats them by `625/576`.
- **Exact candidate-intrinsic-`N` multinomial** (`N(D) = Σd`, §6.1 first
  display, up to the common `n!/x!` coefficient): endpoint A
  (`(2,1,1)`, `N=4`) scores `1/64`, endpoint B (`(3,1,1)`, `N=5`) scores
  `9/625`, so A strictly beats B by exactly `625/576` — the same rational
  number as the relaxation gap. The real midpoint is inadmissible here
  (fractional counts, fractional intrinsic length `9/2`).

Partial implication: likelihood choice flips the integer ranking (tie vs
strict) on the same support, so any maximality claim must name its
likelihood and length universe; a general necessary-and-sufficient
criterion for either class stays OPEN, as do transitive reduction,
orientation/RC classes, and the half-integral-vs-full-real comparison.
This note uses only the full `graph1` and invokes no reduction
convention, so it is unaffected by the issue #284 graph-model blocker.
Keep #261 and #255 open.
