# Binary L=8, G=N=9 one-extra covered-sample probe (#259)

This exact-integer probe extends the binary `L=G=N=8` one-extra probe to the
adjacent cell `L=8, G=N=9` (`scripts/verify_binary_L8_G9_one_extra_259.py`).
It enumerates the 60 realizable circular binary spectra of length 9 over the
fixed read-type universe of all 256 8-mers. For every truth `A`, competitor
`B`, and `i` in `supp(A)`, it checks the covered sample `x=A+1_i` (sample
size `n=10`, external normalization `N=9`).

The tested objective is the MB09 §6.1 fixed-external-`N` **product of marginal
binomials**, not the exact joint multinomial and not the §6.2 bidirected-flow
objective. Its integer numerator is

```text
F_N(B,x) = ∏_{e in E} B_e^x_e (N-B_e)^(n-x_e),   n=∑_e x_e.
```

The verifier independently computes `∏_e q_N(B,e)^x_e`, where
`q_N(B,e)=B_e∏_{j≠e}(N-B_j)`, and confirms equality with the literal
all-coordinate numerator (including `x_e=0` coordinates). It also records the
covered-uniform pointwise `q_e` decision per ordered pair. A separate
non-vacuity control uses the realizable binary 2-mer spectra
`A=(2,1,1,0)`, `B=(1,1,1,1)` at `N=4`, `x=A+1_(00)` (`n=5`): deleting the
zero-count coordinate's failure factor changes the computed numerator.

This is a finite arithmetic consistency probe, not a classification or a new
theorem about graph rigidity. The one-extra samples do not replace the
all-covered-samples quantifier in the sample-uniform theorem.

Validation:

```text
python3 scripts/verify_binary_L8_G9_one_extra_259.py
binary L=8 G=N=9 spectra=60 universe=256
pairs=3600 uniform_beats=3592 uniform_losses=8
one-extra samples=30720 exact identities=30720
mutation control: omitting zero-count failure factors changes score; OK
```

The 8 ordered pairs with a pointwise `q_e` loss are candidates for
follow-up exact covered-sample beating witnesses; no beating claim is made
here. #260/#261 flows untouched.
