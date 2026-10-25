# Degenerate-threshold cell at `o_min=3`: feasible set empty, no witness transfer (#261)

Bounded increment complementing the `o_min=2` strict-threshold cell in
`docs/issue261-strict-omin-cell.md`. This note resolves one further genuine
MB09 §6.2 bidirected-flow cell — the `o_min=3` degenerate restriction of
the same `AAATT` instance (`L=3`, full overlap `graph1` minus all three
cross edges, zero terminals) — with exact-rational verification in
`scripts/verify_261_omin3_cell.py`. It states no general maximality
criterion. Keep #261 and #255 open.

## Cell declaration

- **Candidates**: (F) nonnegative real edge flows satisfying the same
  signed-incidence balance equalities and vertex throughput lower bound `1`
  as `Feasible62`, restricted to the `o_min=3` surviving edge set (the AAA
  loop alone); and (I) the integer (`ℕ`-valued) sub-class. Both classes
  are empty on this cell (proved below). No spelled-circuit (C) or
  genome-spectrum (G) candidate can exist either, since both embed in (I).
- **Truth**: **not admitted** — the feasible set is empty, so no truth
  vector is a member of this cell.
- **Likelihood**: fixed external-`N` product-binomial (`N=5`, §6.1 second
  display, the objective §6.2 optimizes) — the same likelihood as the
  `o_min=1` witness, so the comparison is apples-to-apples. The likelihood
  is vacuous here (no candidates to score).
- **Length universe**: fixed `N=5` (inherited from the witness instance).

## Exact result (checked by `scripts/verify_261_omin3_cell.py`)

Using the same balance map
`(f1−f3, −f1+f2, −f2+f3)` and throughput map `(f0+f1, f2, f3)` as the
`o_min=1` candidacy verifier, with the absent edges
`f1 = f2 = f3 = 0` (overlap lengths `2, 1, 2` all `< 3`):

1. **Balance is vacuous.** On the loop-only graph every flow is
   `(f0, 0, 0, 0)` with balance `(0, 0, 0)` and throughput `(f0, 0, 0)`.
2. **Vertex bound 1 is unsatisfiable.** `AAT` and `TAA` throughputs are
   exactly `0 < 1` for every `f0 ≥ 0`, real or integer. The feasible set
   is **empty** in (F) and hence in (I), (C), (G).
3. **Maximality is vacuous, not refuted.** With no feasible candidate —
   truth included — there is no maximizer question to pose on this cell.
   This is an inadmissibility result, not a defeat witness.

## Candidate-set inclusion and no-transfer (explicit)

- Zero-extension embeds the degenerate edge set into the `o_min=2` and
  `o_min=1` edge sets, so `F_omin3 ⊆ F_omin2 ⊆ F_omin1` holds vacuously
  (all three restricted maps agree on the surviving loop edge). The
  issue's inclusion precondition is therefore satisfied in the
  degenerate-to-lax direction.
- But the `o_min=1` defeat witness (both integer endpoints and the real
  midpoint) carries flow exactly `1` on each of the three absent cross
  edges, so it is **not a member** of the degenerate cell. The
  full-overlap failure does **not** transfer upward to `o_min=3`: there
  is nothing to transfer to, since the target cell is empty. Conversely
  no positive maximality statement is made here, so none transfers
  downward either.
- Consequence for the axis matrix (`docs/issue261-axis-matrix-20261014.md`,
  "Sample realizability at arbitrary overlap"): that row stays OPEN in
  general; for this instance at thresholds `o_min=2` and `o_min=3` it is
  resolved negatively — realizability fails because feasibility itself
  fails.

## Status boundary

Resolved for this instance/threshold: the `o_min=1` witness family is
threshold-specific, and the degenerate cell is empty under vertex bound
`1`. Explicitly open: every general maximality criterion;
transitive-reduction invariance (this cell uses the unreduced surviving
edge set and invokes no `isReducibleB` identity, so it is unaffected by
the issue #284 graph-model blocker); orientation/RC classes;
half-integral-vs-full-real comparison; and all other overlap thresholds
and supports.
