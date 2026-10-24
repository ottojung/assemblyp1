# Issue #261 independent review: AGA/CTC (a844e88) and ACA/CAC (0108383) bounded cells

Non-author review of `origin/research/261-flow-agactc-x3mPXQAc-nuts @ a844e88`
and `origin/research/261-flow-next-5C5NsApbjQGtVxkZ6UcHo5-deduce @ 0108383`,
both branched from `origin/main 234f348`. No code copied; both verifiers
re-run from branch content in this runtime: PASS.

## What was checked

- Re-ran `scripts/verify_261_flow_cell_agactc.py` from a844e88: PASS
  (spelled `[(1,1),(2,2)]`, truth K=64, defeater (1,2) K=72).
- Re-ran `scripts/verify_261_flow_cell_aatt.py` from 0108383: PASS
  (same spectra and scores on ACA/CAC support).
- Hand-checked fixed-N binomial core N=4, x=(1,2), n=3:
  K(2,2)=2^1·2^2·2^2·2^1=64; K(1,2)=1·8·4·2=72;
  K(1,1)=1^1·3^2·1^2·3^1=9·3=27. Truth is
  spelled-maximal (64 > 27) and strictly beaten by the flow (72 > 64).
- Hand-checked DNA RC complements (A=0,C=1,G=2,T=3, rc=complement+reverse):
  rc(AGA)=(3,1,3)=TCT; rc(CTC)=(2,0,2)=GAG; rc(ACA)=(3,2,3)=TGT;
  rc(CAC)=(2,3,2)=GTG. No palindromes; representative convention consistent.
- Read `docs/issue261-flow-cell-agactc-20261024.md`: scope is explicit and
  bounded (complete 8-edge graph, zero terminals, vertex bound 1, spelled
  lengths 2..4, omit/fix-at-zero unobserved-coordinate convention). It does
  not claim transitive-reduction invariance, unbounded spelling, real-LP, or
  coordinate-convention adjudication. The "second RC support" claim is
  accurate relative to the ACA/CAC cells.

## Limits (not defects of the cells, but boundaries)

- Spelling universe is bounded (lengths 2..4); no unbounded-spelling transfer.
- Complete graph, not transitively reduced; reduction invariance stays OPEN.
- Integer 0/1-search witnesses; half-integral/real-LP relaxation stays OPEN.
- Unobserved-coordinate convention is stated, not source-adjudicated.
- a844e88 is UNSIGNED (author-declared); signed-commits CI is expected to
  fail for it. This review branch makes no claim about signatures.

## Verdict

APPROVE the mathematics of both cells as bounded exact witnesses: on two
distinct RC supports, a spelled-maximal truth is strictly beaten by a
balanced integer flow under the same fixed-N binomial objective. Recommend
exact-head CI before any merge; keep #261 and #255 open (general criterion,
reduction, LP, coordinates, PR #394 reconciliation all OPEN).
