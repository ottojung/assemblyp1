# Binary length-8 one-extra covered-sample probe (#259)

This exact-integer probe supplements the binary `L=G=N=8` census in
`scripts/verify_binary_L8_G8_one_extra_259.py`. It considers the same 36
realizable circular spectra, with a fixed read-type universe of all 256
8-mers. For every truth `A`, competitor `B`, and `i` in `supp(A)`, it checks
the covered sample `x=A+1_i`, whose sample size is `n=9` while the external
normalization remains `N=8`.

The tested objective is the MB09 §6.1 fixed-external-`N` **product of marginal
binomials**, not the exact joint multinomial and not the §6.2 bidirected-flow
objective. Its integer numerator is

```text
F_N(B,x) = ∏_{e in E} B_e^x_e (N-B_e)^(n-x_e),   n=∑_e x_e.
```

The verifier independently computes `∏_e q_N(B,e)^x_e`, where
`q_N(B,e)=B_e∏_{j≠e}(N-B_j)`, and confirms equality with the literal
all-coordinate numerator in 9,216 truth/competitor/supported-coordinate
checks. This includes the `x_e=0` coordinates. A separate non-vacuity control
uses the realizable binary 2-mer spectra `A=(2,1,1,0)`, `B=(1,1,1,1)` at
`N=4`, and `x=A+1_(00)` (`n=5`): deleting the zero-count coordinate's failure
factor changes the computed numerator.

This is a finite arithmetic consistency probe, not a classification or a new
theorem about graph rigidity. In particular, the one-extra samples do not
replace the all-covered-samples quantifier in the sample-uniform theorem.

Validation:

```text
python3 scripts/verify_binary_L8_G8_one_extra_259.py
binary L=G=N=8, spectra=36, universe=256
A,B,supported-coordinate one-extra samples checked=9216; exact numerator identities=9216
mutation control: L=2,G=N=4, A=(2, 1, 1, 0), B=(1, 1, 1, 1); omitting zero-count failure factors changes score (n=5)
All checks use integer arithmetic; OK
```
