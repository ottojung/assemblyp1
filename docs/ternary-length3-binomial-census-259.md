# Ternary circular 2-mer census at length 3 (#259)

**Status: exact finite census, not a general theorem.** This artifact checks
the first ternary length-3 case requested by the remaining-scope matrix. The
objective is the MB09 §6.1 fixed-external-`N` product-binomial surrogate,
not the exact multinomial likelihood of #256 and not the §6.2 bidirected-flow
objective of #260–#261.

## Model and exact criterion

Take the alphabet `{0,1,2}`, oriented 2-mer universe of size 9, circular
candidate length `G=3`, and fixed normalization `N=G=3`. For a count vector
`B` of total `N`, define

```
q_B(w) = B(w) * product_{v != w}(N-B(v)),
F_B(x) = product_w q_B(w)^x(w).
```

The binomial likelihood is `F_B(x)/N^(N*n)` times a factor depending only on
the data, where `n=sum_w x(w)`. Thus likelihood comparison at a fixed sample
uses `F_B`; the unobserved-coordinate factors `(1-d(w)/N)^(n-x(w))` are
retained inside `q`. Zero weights and boundary probabilities are included
without logarithms or division.

For a truth `A`, covered observations are `x(w)>=A(w)` on `supp(A)` and zero
off that support. The established covered-sample iff says `A` weakly maximizes
against `B` for every such complete-support `x` iff either `q_B` vanishes on
truth support, or `q_B(w)<=q_A(w)` for each `w` in truth support. The verifier
checks exactly this iff criterion, not a finite sample box.

## Census result

There are 27 ternary circular words of length 3, 11 distinct oriented
2-mer spectra, and 165 integer count vectors of total 3 in the full candidate
simplex. Exhaustive exact-integer comparison finds that all 11 realizable
truths are covered-sample maximizers against all 165 competitors; in
particular there are zero full-class or realizable-class violations in this
case. The output lists each spectrum and its full-class violation count.

Run:

```
python3 scripts/verify_ternary_length3_transfer_gap_259.py
```

The finite enumeration is complete for this model point, but it proves
nothing for ternary lengths `G>=4`, alphabets of size at least 4, or arbitrary
realizable truths. It also does not establish the general rigidity criterion.
No changes are made to #260–#261 flow models.
