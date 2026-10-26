# Issue #261: o_min = L-1 rule-out cell (AAATT, exact rational)

_Status: bounded exact-rational certificate, 2026-10-26. Independent of the
in-flight window-step bridge, loop half-incidence, reduction-survival, and
abstract flow-dominance fronts. All claims are labelled **source fact**,
**mathematical argument**, **verified computation**, or **open**._

## Cell parameters (explicit)

- Alphabet `{A,T}`, reverse-complement involution `A <-> T`.
- Read length `L = 3`, overlap threshold `o_min = 2 = L-1` (full overlap).
- Truth `S = AAATT` (`G = 5`); realized starts `(0,0,1,4)`, `n = 4`.
- Observed `x = {AAA:2, AAT:1, TAA:1}`; truth spectrum
  `d_S = {AAA:1, AAT:2, TAA:2}`.
- External known size `N = 5 = |S|`.
- Candidate domain: **integral** `Feasible62` flows on the o_min=2 bidirected
  overlap graph (vertex lower bound 1, edge lower bounds 0, zero
  super-terminals), reduced or not (the literal MB09 reduction is vacuous at
  `L = 3`; the longer-overlap reading removes only length-1 edges, of which
  there are none here).
- Likelihood: MB09 section 6.1 product-binomial with fixed external `N = 5`
  (zero-count factors retained).
- Truth admission: the truth window walk uses five length-2 steps, all present
  in the o_min=2 graph; the truth circuit is feasible (vertex LB >= 1, zero
  balance), verified in the script. [verified computation]

## Results

1. **No candidate-set inclusion from o_min=1.** The o_min=1 non-spelled
   optimizer's key edge (`AAT -> TAA`, overlap length 1) is present in the
   o_min=1 graph (28 edges) but absent from the o_min=2 graph (10 edges).
   Hence the `Section62NonSpelledFlow.starFlow21` witness is infeasible at
   `o_min = L-1`: the o_min=1 non-spelled-beats-truth cell does **not**
   transfer. [verified computation]
2. **Genome-level comparator is not a flow here.** The spelled same-length
   genome `D = AAATA` (`d_D = {AAA:2,AAT:1,ATA:1,TAA:1}`, ratio
   `B(d_D)/B(d_S) = 65536/50625 > 1`) needs the `AAT -> ATA` step, whose `ATA`
   strand belongs to no observed molecule (`strandsOf = verts ++ map rc
   verts`); that edge is absent from the observed-vertex graph. So `D` is a
   genome-level (and exact-iid-tied) comparator, not a feasible flow in this
   cell -- consistent with `spelledCandidate261_outside_observed_support`.
   [verified computation]
3. **Bounded rule-out.** Exhaustive enumeration over circuit-multiset flows
   with total flow <= 6 on the o_min=2 graph finds 2 feasible throughput keys;
   the beaters of the truth in scope are exactly the spelled key
   `(AAA:2,AAT:2,TAA:2)` (the `AAAATT` variable-length spelled genome, ratio
   `9/4`), and **no non-spelled feasible flow beats the truth** in scope.
   [verified computation, bounded; not a general theorem]

## Reproduce

```sh
python3 scripts/verify_261_omin2_nonspelled_ruleout.py
```

Exact `fractions.Fraction` arithmetic only; exits non-zero on any failure. No
Lean changes; no Mathlib build required.

## Open (unchanged)

General maximality criteria, unbounded spelling, half-integral/real-LP
relaxation, transitive-reduction invariance in general, RC/orientation-class
transfer, and the full genome-spelling axis remain **open**. Keep #261 and
#255 open.
