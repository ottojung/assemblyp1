# Realizable-support census for #259: ternary read length 3 (binary-extension companion)

_Status: independent exact-integer Python verification, 2026-10-25
(`scripts/verify_realizable_census_T3_259.py`, exit 0). Bounded evidence only;
the kernel-checked theorem remains
`AssemblyP1/ProductBinomialRigidityNecessity.lean` (`robust_iff_unique`)._

This note extends the bounded census of
`docs/product-binomial-rigidity-necessity-259.md` (§4, binary `L in {2,3,4}`,
`1088` spectra) to a new realizable class: **ternary alphabet, read length
`L = 3`** (universe = 27 ternary 3-mers), circular genome lengths
`G in 3..7`. All truths and competitors are same-length realizable spectra
(ternary-necklace representatives); rigidity = uniqueness of the positive
balanced circulation of total `G` on the truth support; maximality over the
realizable class is decided by the merged `#259` covered-sample iff
(zero-weight / pointwise-domination branches), exact `int` arithmetic.

Model recap (unchanged): MB09 §6.1 fixed-external-`N` product-binomial
surrogate with `N = G`; candidate length fixed; normalization `N` fixed
external; support = truth 3-mer support; sample size `n` free above the
covered-sample bound; the extra `(1 - d(w)/N)^(n - x(w))` factors (including
zero-count coordinates and boundary 0/1 probabilities) are encoded in
`effectiveWeight`. Not the exact multinomial (`#256`); not §6.2 bidirected
flows (`#260`/`#261`).

## Result

| cell | count |
|------|-------|
| distinct realizable truth spectra (`G = 3..7`) | 513 |
| rigid & maximal | 429 |
| **rigid & NOT maximal** | **66** (all beaten by a new-support realizable candidate) |
| **non-rigid & maximal** | **0** (necessity holds on this class) |
| non-rigid & NOT maximal | 18 |

## Smallest explicit witness (exact integers)

`G = N = 6`, universe order = lexicographic ternary 3-mers
(`000, 001, 002, 010, …`):

- truth `A = [3,1,0,1,0,…,1,0,…]` (support `{000,001,010,100}`, realized e.g.
  by a 6-cycle spelling three `000` reads), rigid (unique positive
  circulation of total 6 on its support);
- competitor `B = [1,1,0,2,0,…,1,1,0,…]` (support adds 3-mer index 10, hence
  **new-support** and realizable by construction);
- on `supp A`: `effA = [296148833645101056000, 59229766729020211200,
  59229766729020211200, 59229766729020211200]`,
  `effB = [65810851921133568000, 65810851921133568000,
  164527129802833920000, 65810851921133568000]`, strict gain at three
  coordinates, no zero weight on `supp A` — so the covered-sample iff yields a
  covered `x` strictly preferring `B`.

Reproduce: `python3 scripts/verify_realizable_census_T3_259.py` (well under
a minute; deterministic).

## Scope

Covered here: ternary `L = 3`, `G ≤ 7`, same-length realizable class only.
Still open: `L ≥ 6` / alphabets `≥ 5`, full new-support maximality theorem;
the prior unverified `L6Q4` checkpoint claim (commit `4703a6f`, absent from
`origin/main` at `234f348`) is **not** relied on — this note re-establishes a
smaller checkable cell from scratch.
