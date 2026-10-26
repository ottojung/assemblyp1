# Realizable-class transfer balance and the full-vs-realizable gap (#259)

Status: bounded exact-arithmetic evidence in
`scripts/verify_realizable_transfer_gap_259.py`; no Lean theorem claimed. This
addresses the remaining gap between the full count-vector classification and
the realizable (balanced-spectrum) restriction.

## Model and distinction

For a circular binary genome of length `G`, fixed read length `L`, and
`E={0,1}^L`, candidate spectrum `B` has `sum_e B_e=N=G`. The MB09 §6.1
fixed-external-`N` product-binomial objective, up to candidate-independent
factors, is

```
q_e(B) = B_e * product_{j != e}(N-B_j)
F_B(x) = product_e q_e(B)^x_e.
```

The product includes zero-observed coordinates; these are the extra
`(1-d(w)/N)^(n-x(w))` factors absent from the exact multinomial objective in
#256. Here `n=sum x` is arbitrary and samples are covered (`A<=x`, with no
counts off `supp A`). Candidates are restricted to circular-genome spectra of
the same length/read length. This is neither the full class of count vectors
nor the §6.2 bidirected-flow objective of #260/#261.

## Exact balance fact for a one-unit transfer

For distinct supported `L`-mers `i,j` with `A_j>=2`, consider
`B=A-e_j+e_i`. As a change to edge counts in the de Bruijn graph, this
preserves flow balance exactly when the endpoint multisets agree:

```
{pre(i), suf(j)} = {pre(j), suf(i)}.
```

Indeed the residual imbalance at vertex `v` is
`[v=pre(i)]-[v=pre(j)]-[v=suf(i)]+[v=suf(j)]`, which vanishes at all vertices
iff those two multisets agree. E.g. transferring between loops `00` and `11`
preserves balance, whereas `01 -> 10` does not. The script compares the
criterion with integer balance equations over 1,794 transfers on binary
necklace spectra (`L=2,3`, `G<=10`): 98 balanced, zero mismatches. This is a
general algebraic characterization; the enumeration only checks its encoding.

## Smallest full-vs-realizable gap found

At `L=2`, `G=N=4`, truth `A=(0,2,2,0)` is the spectrum of `0101`. The
full-class transfer beater `Bs=(0,1,3,0)` is not realizable: its `01` and `10`
counts differ, violating balance. Yet it strictly beats the truth at covered
sample `x=(0,2,4,0)` (`n=6`), by exact integer comparison of `F_Bs(x)>F_A(x)`.
Exhausting all length-4 binary necklace spectra shows none beats `A`, making
this truth realizable-maximal despite not being full-class maximal. `A` is rigid
on its support (`(2,2)` is its unique positive circulation).

Across binary `L in {2,3}`, `G<=10`, the verifier finds 50 maximal in both
classes, 216 beaten in both, and 14 full-class-beaten but realizable-maximal
truths; zero are skipped for nonpositive truth effective weights. This is a
finite census, not an all-length characterization. Alternating spectra suggest
an infinite family, but that remains conjectural.

## Verification and remaining scope

Run `python3 scripts/verify_realizable_transfer_gap_259.py`. It uses exact
integer score products and `Fraction`-based flooding to exhibit the strict
sample witness; the full-vs-realizable classification uses the established
covered-sample iff, hence quantifies over all covered samples, rather than a
bounded sample box. It also exhausts necklace spectra for the stated finite
cells. No Lean replay is claimed.

Still open: characterize all realizable balanced spectra (including non-binary
alphabets and non-necklace flow candidates), prove or refute the alternating
family for all lengths, and reconcile this axis with the complete #259
classification. Keep general bidirected flows in #260/#261.
