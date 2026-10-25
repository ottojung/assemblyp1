# The #261 real-flow midpoint is none of integer flow, spelled circuit, or genome (#261)

This note classifies the real-relaxation witness of
`docs/issue261-real-relaxation-binomial-witness.md` (midpoint throughput
`(5/2,1,1)`, binomial ratio `625/576`) by candidate class. It answers the
delegation's candidacy question — flow vs spelled-circuit vs genome — for this
one exact small instance, with exact rational verification. It states no
general maximality criterion.

## Candidate classes

On the stated `AAATT` instance (`L=3`, `o_min=1`, full overlap `graph1`, zero
terminals, external `N=5`, read counts `x=(2,1,1)`):

- **(F) real flows**: nonnegative real edge flows satisfying the same
  signed-incidence balance equalities and vertex throughput lower bound `1` as
  `Feasible62`. Truth is admitted. This is the continuous relaxation.
- **(I) integer flows**: the Lean `BdFlow`-valued class (`ℕ`-valued edge maps);
  both `starFlow21` and `starFlow31` live here and are kernel-checked feasible.
- **(C) spelled single-circuit traversals**: closed walks spell a circular word;
  every such walk induces an `ℕ`-valued edge-multiplicity vector.
- **(G) circular genome spectra**: per-molecule-class window counts of a
  circular genome; every coordinate is a natural number and the coordinates sum
  to the genome length, itself a natural number.

## Exact classification (checked by `scripts/verify_261_real_flow_candidacy.py`)

The midpoint edge vector `(3/2, 1, 1, 1)` in coordinates
`(AAA loop, AAA→AAT, AAT→TAA overlap 1, TAA→AAA)`:

1. **Is in (F).** Nonnegative edge values, zero signed balances, throughputs
   `(5/2,1,1)` with minimum `≥ 1`, inside the binomial domain `0 ≤ d ≤ 5`.
   Feasibility follows by convexity: it is the average of the two feasible
   integer endpoint flows.
2. **Is not in (I).** The `AAA` loop value `3/2` is not a natural number; Lean
   `BdFlow` maps are `ℕ`-valued, so the point lies outside the formalized
   integer flow class entirely.
3. **Is not in (C).** Any closed walk traverses each edge an integer number of
   times; no spelled single circuit can produce the value `3/2` on the loop.
4. **Is not in (G).** The throughput `(5/2,1,1)` has a fractional coordinate
   and fractional total mass `9/2`; no circular genome of any (natural-number)
   length has this spectrum.
5. **Strictly beats the integer optimum.** The fixed-`N` product-binomial score
   ratio over either integer endpoint optimum is `625/576 > 1` (the two
   endpoint scores agree; the Lean `star_argmax` theorem says the integer
   optimum is exactly the `d_AAA ∈ {2,3}` pair).

## Status boundary

Resolved for this instance: the real relaxation strictly beats every integer
flow with a point that is itself neither an integer flow, nor a spelled
circuit, nor a genome spectrum — so the relaxation optimum cannot be read as
an ML genome without an additional rounding/projection rule, which §6.2 does
not supply.

Explicitly open: a general necessary-and-sufficient maximality criterion for
any of (F)/(I)/(C)/(G); the exact variable-length multinomial analogue;
invariance under a source-faithful transitive reduction; arbitrary
supports/overlap thresholds; orientation/RC classes; half-integral vs full
real relaxation. This witness uses only the full `graph1` and the convexity
of its constraints, so it invokes no reduction convention and is unaffected
by the issue #284 graph-model blocker (it does not rely on any `isReducibleB`
identity). Keep #261 and #255 open.
