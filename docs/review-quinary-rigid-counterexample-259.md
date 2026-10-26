# Independent check: rigid quinary truth beaten by a realizable candidate (#259)

The newest #259 checkpoint at `2ea71fc71b42ee18153915ee10a7f4bfe42aef4e`
reports a quinary length-3 realizable-spectrum census for `G=5,6`. I reran its
verifier and independently checked the first reported strict witness directly
over the full 125-type universe using exact `Fraction` arithmetic.

## Exact witness

* Alphabet: `{0,1,2,3,4}`; read length `L=3`.
* Candidate genome length and fixed external normalizer: `G=N=6`.
* Truth circular genome: `000001`, with spectrum
  `A(000)=3, A(001)=A(010)=A(100)=1`.
* Realizable candidate genome: `000101`, with spectrum
  `B(000)=B(001)=B(100)=B(101)=1, B(010)=2`.
  Thus `B` is an equal-length candidate with new support at `101`.
* The truth is rigid on its support: the only positive balanced integer
  circulation of total six on `{000,001,010,100}` is `(3,1,1,1)`.
* Covered observed counts: `x(000)=3, x(001)=33, x(010)=1, x(100)=1`, all other
  counts zero. The sample size is `n=38`, distinct from `N=6`, and
  `supp(x)=supp(A)` with `x≥A` there.
* For the MB09 §6.1 fixed-external-`N` product-binomial objective, retaining
  every `(N-D(v))` factor including zero-count classes,

  ```text
  F_B(x) / F_A(x)
    = 2000000000000000000000000000000000000
      / 1824800363140073127359051977856583921
    > 1.
  ```

The sample is a vector of observed read counts; it need not itself be the
length-`n` spectrum of a circular genome. Requiring that extra balance
condition would change the sampling model. The candidates themselves are both
verified circular spectra. This exact witness refutes rigidity sufficiency
when new-support equal-length realizable candidates are admitted; it does not
refute rigidity necessity or classify all realizable truths.

## Verification and scope

`python3 scripts/verify_quinary_rigid_counterexample_259.py` independently
constructs both spectra from their circular words, enumerates positive
same-support circulations to verify rigidity, checks coverage and `n=38`, and
computes the exact full-universe product-binomial ratio. It imports no existing
verifier and uses no floating-point comparisons. I also ran the checkpoint's
`verify_realizable_census_Q5L3_259.py`: it reports 3254 truth spectra, 60 rigid
but beaten truths, and no non-rigid maximal truths for quinary `L=3`, `G=5..6`.

This is MB09 §6.1's fixed-external-`N` product-binomial surrogate, not the exact
joint multinomial likelihood of #256 and not the §6.2 bidirected-flow model of
#260/#261. The finite quinary census is not an all-length or all-alphabet
classification. The exact witness is a new non-alternating, realizable
candidate counterexample; no claim that it is globally smallest is made here.
