# Binary L=5, G in {5, 6} exact realizable census (#259)

This bounded cell is distinct from all covered cells (binary L6/L7/L8,
ternary L3-L6, quaternary L3/L4): binary alphabet at candidate length `L=5`.
It is computational evidence only; it makes no claim about arbitrary genome
lengths or alphabets.

## Model and conventions

Candidates are binary circular genomes of length `G` in {5, 6}, represented by
their 32-coordinate 5-mer count spectra (`L=5`). The normalization is fixed
externally at `N=G`; the truth sample is its complete observed spectrum
`x=A`, of sample size `n=sum(A)=G`. Truths and competitors range over all
realizable binary length-`G` circular spectra. Each truth has support equal to
its positive 5-mer coordinates; candidate support may differ, including new
types.

For a candidate `B`, the MB09 §6.1 fixed-external-`N` product-binomial
numerator is

```
F_B(x) = product_e B_e^(x_e) (N-B_e)^(n-x_e).
```

In particular, `(N-B_e)^(n-x_e)` remains for every zero-count coordinate.
This is the product of marginal binomials approximation, not the exact joint
multinomial likelihood used in #256, whose candidate-dependent numerator is
`product_e B_e^(x_e)` and omits unobserved-type factors. Boundary values 0 and
`N` are handled using exact integer powers, including exponent zero.

The sample-uniform comparison uses effective weights
`q_e(B)=B_e product_{j != e}(N-B_j)` over the full 32-type universe. For
covered samples `x >= A`, the established criterion checks `q_e(B) <= q_e(A)`
on every `e` in `supp(A)` (a zero competitor weight cannot beat the truth).
At `x=A`, the verifier separately computes the full fixed-sample integer
numerator, so axis (A) at a fixed observed count and axis (B) for every
realizable complete-support `x` are decided independently.

## Result

There are 8 distinct circular truth spectra at G=5 and 14 at G=6 (22 total).
Exact enumeration (`scripts/verify_binary_L5_G56_259.py`, integers only) gives:

- rigid & sample-uniform maximal: 16;
- rigid but beaten sample-uniformly: 6 (all at G=6; G=5 is an all-maximal cell);
- nonrigid & maximal: 0 (rigidity necessity holds in this cell);
- nonrigid & not maximal: 0.

Every one of the 6 rigid-but-beaten truths wins the fixed-x inequality at its
own truth sample `x=A` yet loses sample-uniformly: 6 live fixed-x vs
sample-uniform gap instances (win-at-own-sample=6, lose-at-own=0).

## Mutation control

The verifier pins the exact outcome counts
(`rigid_max=16, rigid_notmax=6, nonrigid_max=0`, gap split 6/6/0) and asserts a
non-trivial zero-count factor was observed (`zero_factor_seen`). A mutant
relaxing the strict effective-weight comparison (`>` to `>=`) yields
`rigid_max=13/rigid_notmax=9` and fails the pins, so the control is
non-vacuous. Genuine general bidirected flows are untouched (reserved for
#260-#261).
