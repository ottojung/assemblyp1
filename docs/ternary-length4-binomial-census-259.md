# Ternary circular 2-mer census at length 4 (#259)

**Status: exact finite census, not a general theorem.** This artifact extends
the length-3 census (`docs/ternary-length3-binomial-census-259.md`) to the
next open cell: ternary circular words of length 4. The objective is the MB09
§6.1 fixed-external-`N` product-binomial surrogate, not the exact multinomial
likelihood of #256 and not the §6.2 bidirected-flow objective of #260–#261.

## Model and exact criterion

Alphabet `{0,1,2}`, oriented 2-mer universe of size 9, circular candidate
length `G=4`, fixed normalization `N=G=4`, sample size `n=sum_w x(w)`. For a
count vector `B` of total `N`:

```
q_B(w) = B(w) * product_{v != w}(N-B(v)),
F_B(x) = product_w q_B(w)^x(w).
```

The binomial likelihood is `F_B(x)/N^(N*n)` times a data-only factor, so
likelihood comparison at fixed `x` uses `F_B`; the unobserved-coordinate
factors `(1-d(w)/N)^(n-x(w))` are retained inside `q`. Zero weights and
boundary probabilities `0/1` are included without logarithms or division.
The exact multinomial objective of #256 differs by replacing these
per-coordinate binomial factors with a joint multinomial coefficient; the
census below applies only to the fixed-`N` product-binomial surrogate.

For truth `A`, covered observations are `x(w)>=A(w)` on `supp(A)` and zero
off that support. The established covered-sample iff says `A` weakly
maximizes against `B` for every such complete-support `x` iff either `q_B`
vanishes on truth support, or `q_B(w)<=q_A(w)` for each `w` in truth support.
The verifier checks exactly this iff criterion, not a finite sample box.

## Census result

There are 81 ternary circular words of length 4, 24 distinct oriented 2-mer
spectra, and 495 integer count vectors of total 4 in the full candidate
simplex. Exhaustive exact-integer comparison finds **96 full-class**
(truth, competitor) violations and **6 realizable-class** violations. In
particular, sample-uniform maximality over all covered complete-support `x`
**fails** at length 4, unlike the length-3 case with zero violations.

Smallest realizable-class witness (indices over the 9 oriented 2-mers in
lexicographic order):

```
A = (0,0,0,0,0,1,0,1,2),  q_A = (0,0,0,0,0,24576,0,24576,73728),
B = (0,0,0,0,1,1,0,1,1),  q_B = (0,0,0,0,27648,27648,0,27648,27648).
```

Both spectra are realizable. On `supp(A)={5,7,8}`, `q_B` is nowhere zero and
`q_B(5)=27648 > 24576=q_A(5)`, so the iff criterion fails. Concretely, at
covered samples `x = A + t*e_5` (extra `t` counts on coordinate 5 only),
`F_B(x)/F_A(x) = 1.125^t * 0.177978...`, which exceeds 1 for `t >= 15`
(`n = 19`), so `B` strictly beats truth `A` on a covered complete-support
sample. The remaining 5 realizable-class violations are listed by the
verifier output.

Run:

```
python3 scripts/verify_ternary_length4_census_259.py
```

This finite enumeration is complete for this model point but proves nothing
for ternary lengths `G>=5`, alphabets of size 4 or more, or arbitrary
realizable truths. It does not by itself settle whether graph rigidity is
necessary for sample-uniform maximality in general; the witness above is a
concrete data point (a non-maximal realizable truth at a fixed model point),
not a general necessity theorem. No changes are made to #260–#261 flow
models.
