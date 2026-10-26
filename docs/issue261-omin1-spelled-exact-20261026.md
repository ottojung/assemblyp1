# Issue #261: o_min=1 spelled-circuit maximality failure (exact iid, variable length)

_Status: bounded exact-rational certificate, 2026-10-26. Distinct slice from the
o_min=2 non-spelled fixed-N cell (7e31395): here o_min=1, SPELLED closed-walk
circuits, EXACT iid likelihood, VARIABLE spelled-length universe. All claims are
labelled **source fact**, **mathematical argument**, **verified computation**,
or **open**._

## Cell parameters (explicit)

- Alphabet `{A,T}`, reverse-complement involution `A <-> T`.
- Read length `L = 3`, overlap threshold `o_min = 1 < L-1` (genuine
  variable-overlap graph: len-1 and len-2 edges; 28 edges on the six observed
  strands `{AAA,AAT,TAA,TTT,ATT,TTA}`).
- Truth `S = AAATT` (`G = 5`); realized starts `(0,0,1,4)`, `n = 4`.
- Observed `x = {AAA:2, AAT:1, TAA:1}` (molecule classes).
- Candidate domain: **spelled closed-walk circuits** with `m <= 6` steps
  (vertices may repeat); each walk spells its own circular genome of length
  `G = sum of advances` (variable length universe, `G` in 1..12 in scope).
  This class spells circular genomes (not bare flows): every candidate carries
  its own `N = G`.
- Likelihood: **exact iid** `prod_c (d_c/G)^{x_c}` with per-candidate `N = G`
  (cross-length comparable). Fixed-`N = 5` binomial is reported secondarily for
  the `G = 5` sub-universe only — it is undefined across lengths.
- Truth admission: the truth window walk (five len-2 steps) is a closed walk in
  `G1` spelling `AAATT`; verified in the script. [verified computation]
- This checkpoint verifies a **spelled-circuit** class only. It does not claim
  that every integer §6.2 flow is spellable or that its flow-throughput image is
  identical to the spelled spectra; the latter identity is refuted separately by
  `Section62SpelledFlowImageRefutation`. No implication from this likelihood
  winner to the unrestricted flow optimum follows without candidate-set
  inclusion.

## Results

1. **Spelled maximality FAILS at o_min=1 under exact iid (bounded scope).**
   Exhaustive closed-walk enumeration (`m <= 6`) yields 59 distinct
   `(G, spectrum)` outcomes; **16 spelled candidates beat the truth**
   (`4/625`), e.g. `AAAAAATT` (`G = 8`, score `1/64`) and `AAAATT` (`G = 6`,
   score `1/81`). So the truth is not the spelled-circuit ML genome in this
   cell. [verified computation, bounded; not a general theorem]
2. **Transitive reduction is non-vacuous and lossy here.** Reduction (keep the
   longest overlap per ordered pair) removes 8 shadowed len-1 edges (28 -> 20);
   reachable outcomes drop 59 -> 29 and beaters 16 -> 5, while the exact-iid
   winner (`AAAAAATT`) and the truth walk (all len-2 edges) both survive. So
   reduction changes the candidate outcome set without changing the winner in
   scope — winner-preservation without outcome-set preservation.
   [verified computation, bounded]
3. **No transfer to o_min = L-1.** The scope winner uses len-1 steps
   (`AAA->AAA`, `ATT->TAA`) absent from the o_min=2 graph (10 edges), so this
   beater is infeasible at full overlap: o_min=1 spelled failure does **not**
   transfer upward (no candidate-set inclusion). [verified computation]
4. **Length-universe note.** In the `G = 5` sub-universe the truth (`AAATT`)
   ties `AAAAT` under exact iid (`4/625` each); fixed-`N` binomial can only
   rank within one length, while exact iid compares across spelled lengths —
   the two likelihoods answer different questions on this axis. [verified
   computation, bounded]

## Reproduce

```sh
python3 scripts/verify_261_omin1_spelled_exact.py
```

Exact `fractions.Fraction` arithmetic only; exits non-zero on any failure. No
Lean changes; no Mathlib build required.

## Open (unchanged)

Unbounded spelling (`m > 6`), half-integral/real-LP relaxation at o_min=1,
general reduction-invariance criteria, RC/orientation-class transfer, and the
full genome-spelling axis remain **open**. Keep #261 and #255 open.
