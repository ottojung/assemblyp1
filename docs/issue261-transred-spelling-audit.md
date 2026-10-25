# Transitive-reduction audit on the AAATT witness cell (#261)

Bounded increment on the AAATT witness cell (`L=3`, `o_min=1`, full overlap
`graph1`, zero terminals, external `N=5`, read counts `x=(2,1,1)`) shared with
the real-flow candidacy note (`research/261-candidacy-SwsBhXqC-insects`) and
the strict-threshold cell note (`research/261-candidacy-wSg3ws-happiest`).
Exact-string verification in
`scripts/verify_261_transred_spelling_audit.py`. It states no general
maximality criterion. Keep #261 and #255 open.

## Cell declaration

- **Candidates**: (F) nonnegative real edge flows satisfying the same
  signed-incidence balance equalities and vertex throughput lower bound `1`
  as `Feasible62`, on the full `graph1` edge set and on each reduced edge
  set below; and (I) the integer (`ℕ`-valued) sub-class. (C)/(G) embed in
  (I) as before.
- **Truth**: admitted on the full graph and on the standard-reduced graph
  (identical edge sets); not in question on the lax-reduced graph, where
  even the witness is infeasible.
- **Likelihood**: fixed external-`N` product-binomial (`N=5`, §6.1 second
  display, the objective §6.2 optimizes) — same as the witness notes, so the
  ranking comparison is apples-to-apples.
- **Length universe**: fixed `N=5`.

## Exact result

Direct edge spellings (`u + v[k:]`): loop `AAA`, `AAA→AAT` = `AAAT`
(overlap 2, `"AA"`), `AAT→TAA` = `AATAA` (overlap 1, `"T"`), `TAA→AAA` =
`TAAA` (overlap 2, `"AA"`).

1. **Standard spelling-preserving reduction** (edge `u→v` reducible only via
   a 2-step `u→w→v` path with `w` distinct from `u` and `v` spelling the
   identical string, Myers 2005): **no edge is reducible** — the only
   outgoing step from `AAT` besides the direct edge leaves the target, and
   likewise around the triangle. The reduced graph equals the full graph.
2. **Lax convention** (loop-mediated 2-paths admitted, intermediate equal to
   an endpoint): `AAA→AAT` is reproduced by `AAA→AAA→AAT` (`AAAT`) and
   `TAA→AAA` by `TAA→AAA→AAA` (`TAAA`); `AAT→TAA` is reproducible under
   neither convention. Reduction invariance on this cell is therefore
   **convention-relative**, not absolute.
3. **ML transfer**: under the standard convention the witness flows (integer
   endpoints, real midpoint) survive untouched; endpoints still tie and the
   midpoint still wins by exactly `625/576`, so the full-overlap failure
   **transfers intact** to the reduced graph (the issue's inclusion
   precondition holds with equality of candidate sets). Under the lax
   convention the witness is killed (every witness flow needs flow `1` on
   the deleted `AAA→AAT`), so the failure does **not** transfer there.

## Relation to the Lean predicates (audit, not reliance)

No verdict here uses `isReducibleB` or `isReducibleLongerB` (cf. the issue
#284 graph-model blocker). Consistency remark: the audited vacuity finding
(`isReducibleB` deletes no proper overlap anywhere) agrees with outcome 1 on
this cell but for the wrong reason — it would also keep edges under genuinely
reducible configurations. Outcome 2 additionally shows `isReducibleLongerB`
leg-length-only logic cannot reproduce the spelling-equality distinction
between the two conventions. A general reduction-invariance criterion stays
OPEN, as do orientation/RC classes, half-integral-vs-full-real comparison,
and all other overlap thresholds and supports. This note uses only the
unreduced `graph1` plus explicit string computation, so it is unaffected by
#284.
