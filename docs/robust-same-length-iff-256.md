# The exact robust same-length ML iff (board issue #256, child of #255)

_Status: kernel-checked Lean theorem + explanation, 2026-10-10. The module is
`AssemblyP1/RobustSameLengthIff.lean`, imported by `AssemblyP1.lean`, so every
theorem below is checked by `lake build` and free of `sorry`/`admit`/`axiom`
(`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`)._

This note records the **exact** multinomial robust statement requested by issue
#256 and its formalization. It is the "end-to-end iff" for the strict oriented
same-length model; it does **not** merely restate the paper's §4 sketch, and it
does not close the issue by appeal to the sketch.

## 1. The statement

Fix a circular oriented truth `S` of length `G` and a read length `L` with
`G ≥ L ≥ 2`. Let

* `A w = spec_L(S)(w)` be the length-`L` spectrum (the truth's edge
  multiplicities), and `E = supp(A)` the edge set of the de Bruijn support graph
  `X_S` (nodes are the distinct length-`(L-1)` windows; edge `w` runs from
  `prefix_{L-1}(w)` to `suffix_{L-1}(w)`);
* `F` be the set of **all** positive integer balanced circulations `B : E → ℤ_{>0}`
  on `E` of total `G` (the same-length spelled-candidate class of the source
  note's Reduction R);
* admissible samples be the arbitrary finite count vectors `x : E → ℕ` that are
  positive on **every** edge of `E`.

The exact multinomial factor is `Lik(B;x) = ∏_{e∈E} (B e / G)^{x e}` (the
observation-only coefficient `n! / ∏_e x e!` is divided out; it is
candidate-independent, so it cannot move a comparison).

> **Theorem (issue #256).**
> `(∀ x, ∀ B ∈ F, Lik(B;x) ≤ Lik(A;x))  ↔  F = {A}.`

In Lean, the abstract form is `robust_iff_unique` and the model instance is
`robust_iff_unique_spectrum`.

## 2. Proof

**`⇐` (uniqueness ⇒ robustness).** If `F = {A}` then every `B ∈ F` is literally
`A`, so `Lik(B;x) = Lik(A;x)` and the inequality holds with equality. This is the
paper's "converse by equality of spectra".

**`⇒` (robustness ⇒ uniqueness), beatability.** Contrapositive. Suppose
`F ≠ {A}`. Since `A ∈ F` (below), some `B ∈ F` has `B ≠ A`. Both `A` and `B` are
positive with `∑_E A = ∑_E B = G`, so the difference is nonzero and sums to `0`;
hence there is an edge `w` with `A w < B w`.

Let `r = B w / A w > 1` and `C = ∏_{e ≠ w} (B e / A e) > 0`. Choose `M` with
`1/C < r^M` and take the admissible sample

```
x w = M + 1,   x e = 1  for e ≠ w.
```

The likelihood-ratio identity `Lik(B;x) = Lik(A;x) · ∏_e (B e / A e)^{x e}`
gives

```
Lik(B;x) / Lik(A;x) = r^{M+1} · C  >  (1/C) · r · C  =  r  >  1,
```

so `Lik(A;x) < Lik(B;x)`: the competitor `B` strictly beats the truth `A`, and
robustness fails. This is the paper §4 amplification, made fully constructive.

The formal witness is `exists_beating_sample`, which returns the concrete `x`
together with `(∀ e, 0 < x e)` and `Lik(A;x) < Lik(B;x)`.

> **Note on the direction of the inequality.** The issue text for deliverable (2)
> asks for `Lik(B;x) < Lik(A;x)`; that direction would not refute the robust
> statement (it says `B` is *worse*). The direction that refutes the `∀ x`
> hypothesis — and the one the paper's ratio-`>1` argument produces — is
> `Lik(A;x) < Lik(B;x)`, i.e. `B` strictly beats `A`. `exists_beating_sample`
> proves the latter.

## 3. What is kernel-checked

| theorem | content |
| --- | --- |
| `lik` | the exact multinomial factor `∏_e (B e / G)^{x e}` |
| `lik_pos` | positivity when `B > 0` on every edge and `G > 0` |
| `lik_mul_ratio` | `Lik(B;x) = Lik(A;x) · ∏_e (B e / A e)^{x e}` |
| `exists_beating_sample` | constructive sample `x` with `Lik(A;x) < Lik(B;x)` |
| `robust_iff_unique` | the abstract iff over an arbitrary finite edge type |
| `Edge`, `specVec` | the edge set `E = supp(A)` and the restricted truth spectrum |
| `IsPositiveCirculation`, `circulations` | the circulation class `F` on `E` |
| `specVec_pos`, `specVec_total`, `specVec_balanced` | `A` is positive, total `G`, balanced |
| `specVec_mem_circulations` | `A ∈ F` |
| `robust_iff_unique_spectrum` | the model iff, `E = supp(A)`, `F = circulations` |
| `extend`, `extend_support`, `extend_total`, `extend_balanced` | zero-extension of a circulation to all windows |
| `F_eq_singleton_of_rigidity` | no-long-triple-repeat ⇒ `F = {A}` |
| `robust_of_rigidity` | no-long-triple-repeat ⇒ the `∀ x` robust statement |

The only model-specific obligation is `A ∈ F`: the truth spectrum restricted to
`E` is positive (`truth_pos_on_support`), balanced (`truth_balanced`) and of total
`G` (`truth_total`). Everything else is the abstract arithmetic fact.

## 4. Relation to the rigidity chain

The abstract iff needs **no** balance, strong connectivity, repeat hypothesis or
`I_s`. Balance enters only through the *definition* of `F`, via `A ∈ F`. The
paper's rigidity result is what makes `F` a singleton: `F_eq_singleton_of_rigidity`
applies `OrientedFinal.oriented_same_length_spectrum_rigidity` to the
zero-extension of any `B ∈ F` and concludes `B = A`. Composing with the iff
recovers `robust_of_rigidity`: under "no Bresler triple repeat of length
`≥ L-1`" — which `BridgingBridge.informationFeasible_no_long_triple_repeat`
discharges from the source-faithful `I_s` — the truth spectrum is robustly
optimal over the whole circulation set.

Thus the iff *explains* the paper's §4 beatability criterion exactly:
non-rigidity (`F ≠ {A}`) is equivalent to beatability by an amplified sample.

## 5. Issue #256 deliverable-4 checks

* **Observation realizability.** Every admissible `x : E → ℕ` positive on `E` is
  realizable: each `w ∈ E` is a window of `S` (`mem_support_iff_window`), so
  drawing `x w` reads at a start spelling `w` produces exactly `x`. Reads are
  drawn independently and repeated latent starts are counted repeatedly
  (`OrientedSameLengthML.objective_depends_only_on_observation`), so no
  cross-edge consistency is imposed.
* **Zero-count factors.** Restricting to samples positive on *every* edge is
  exactly what removes zero-count factors: for `B ∈ F` and `x > 0` on `E`, every
  factor `(B e / G)^{x e}` has a positive base. The constructed beating sample is
  positive on every edge (`M + 1 ≥ 1` at `w`, `1` elsewhere), so it is a valid
  witness for the stated `∀ x`.
* **Fixed `G`.** `G` is fixed before `F` is formed and appears both in `∑ A = G`
  and in every `∑ B = G`; the length factors cancel in every ratio, so the
  comparison is independent of `G`. The paper's `n > G` phenomenon concerns
  *different* candidate lengths and does not occur on this same-length slice.
* **Precise quantifiers.** `∀ x` ranges over `E → ℕ` positive on every edge;
  `∀ B ∈ F` ranges over the positive balanced circulations of total `G` on `E`;
  `F = {A}` is set equality of the circulation set with the singleton spectrum.
* **Candidate extraction.** `F` is taken to be the circulation set directly, as
  the issue permits. The reduction "spelled same-length candidates ↔ positive
  circulations of total `G`" is the source note's Reduction R; the formal theorem
  is stated over the circulation set and therefore does not depend on the
  graph-theoretic circuit-to-candidate direction (the single-Eulerian-circuit
  requirement), which is **not** formalized. This is the only remaining
  model-boundary caveat: it concerns *what `F` denotes*, not the truth of the
  iff for the circulation set as defined.

## 6. Reproduction

```
lake build AssemblyP1.RobustSameLengthIff
lake env lean - <<'EOF'
import AssemblyP1
#print axioms AssemblyP1.RobustSameLengthIff.robust_iff_unique
#print axioms AssemblyP1.RobustSameLengthIff.exists_beating_sample
#print axioms AssemblyP1.RobustSameLengthIff.robust_iff_unique_spectrum
#print axioms AssemblyP1.RobustSameLengthIff.F_eq_singleton_of_rigidity
#print axioms AssemblyP1.RobustSameLengthIff.robust_of_rigidity
EOF
```

Each must report only `propext`, `Classical.choice`, `Quot.sound`. Independent
numerical evidence for the beating construction and the iff on small instances is
in `scripts/verify_robust_same_length_iff_256.py`.

## 7. Sources

Primary. Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
*Bioinformatics* 32(17) (2016) i494–i502, §4. Paul Medvedev, Michael Brudno,
*Maximum Likelihood Genome Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116,
§6.1–6.2.

Repository cross-references:
[`source-notes/oriented-se62-rigidity-theorem.md`](source-notes/oriented-se62-rigidity-theorem.md)
§4 (the beatability criterion),
[`oriented-same-length-ml-88.md`](oriented-same-length-ml-88.md),
[`ml-formalization-contract.md`](ml-formalization-contract.md).
