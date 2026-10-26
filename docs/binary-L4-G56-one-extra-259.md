# Binary L=4, G=N=5..6 one-extra covered-sample probe (#259)

New non-duplicative census cell (`scripts/verify_binary_L4_G56_one_extra_259.py`;
no binary-L4 259 probe exists on main). It enumerates the realizable circular
binary spectra of lengths 5 (8 spectra) and 6 (14 spectra) over the fixed
read-type universe of all 16 4-mers. For every truth `A`, competitor `B`, and
`i` in `supp(A)`, it checks the covered sample `x=A+1_i` (sample size
`n=N+1`, external normalization `N=G`).

The tested objective is the MB09 §6.1 fixed-external-`N` **product of marginal
binomials**, not the exact joint multinomial and not the §6.2 bidirected-flow
objective. Its integer numerator is

```text
F_N(B,x) = ∏_{e in E} B_e^x_e (N-B_e)^(n-x_e),   n=∑_e x_e.
```

The verifier independently computes `∏_e q_N(B,e)^x_e`, where
`q_N(B,e)=B_e∏_{j≠e}(N-B_j)`, and confirms equality with the literal
all-coordinate numerator (including `x_e=0` coordinates). It also records the
covered-uniform pointwise `q_e` decision per ordered pair. For every
pointwise-loss pair it checks support-inclusion and runs an exact
one-extra/two-extra beating search. A separate non-vacuity control uses the
realizable binary 2-mer spectra `A=(2,1,1,0)`, `B=(1,1,1,1)` at `N=4`,
`x=A+1_(00)` (`n=5`): deleting the zero-count coordinate's failure factor
changes the computed numerator.

This is a finite arithmetic consistency probe, not a classification or a new
theorem about graph rigidity. The one-extra samples do not replace the
all-covered-samples quantifier in the sample-uniform theorem.

Validation:

```text
python3 scripts/verify_binary_L4_G56_one_extra_259.py
binary L=4 G=N=5 spectra=8 universe=16
  pairs=64 uniform_beats=62 uniform_losses=2 support_killed=2
  one-extra samples=256 exact identities=256
  genuine one/two-extra beating witnesses=0
binary L=4 G=N=6 spectra=14 universe=16
  pairs=196 uniform_beats=166 uniform_losses=30 support_killed=30
  one-extra samples=868 exact identities=868
  genuine one/two-extra beating witnesses=0
mutation control: omitting zero-count failure factors changes score; OK
TOTAL identities=1124 samples=1124 beats=228 losses=32 genuine=0
```

Follow-up lemma (8/8 prior L8/G9 loss pairs + 32/32 L4 loss pairs):
every pointwise-`q_e` loss pair in these cells has `supp(B)` missing a
truth-supported coordinate, so `F_N(B,x)=0` on every complete-support `x`
of `A`; none is a genuine truth-beaten witness on one-extra, two-extra,
or (L8/G9) bad-coordinate-concentrated (`t<=12`) covered samples. Pointwise
covered-uniform dominance is therefore not necessary for sample-uniform
maximality in these cells; support-inclusion already protects truth.
#260/#261 flows untouched.
