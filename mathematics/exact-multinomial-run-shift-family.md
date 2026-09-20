# The exact-multinomial run-shift family `S = A^p C^q`, `D = A^(p+1) C^(q-1)`

_Status: mathematical proofs + complete exact-rational search certificate. Not a
Lean result. 2026-09-20. Concerns the **fixed-length exact multinomial**
objective (Medvedev–Brudno §6.1 restricted to candidates of the true genome
length, the repository's variant E at `|D| = G`). It does not concern the
binomial approximation (variant A), the §6.2 flow feasible set, or the
unrestricted-length objective._

## 0. Summary

The source-faithful fixed-length exact-multinomial counterexample
`S = AAABB`, `D = AAAAB`, `L = 3` (`docs/fixed-length-exact-counterexample.md`,
kernel-checked in `AssemblyP1/FixedLengthExactCounterexample.lean`) is the
`p = 3`, `q = 2` member of the two-parameter run-shift family

```text
S(p,q) = A^p C^q,        D(p,q) = A^(p+1) C^(q-1),
```

in which the single symbol `C` is moved from the `C`-run to the `A`-run. The
natural question is whether this is an infinite family of fixed-length
exact-multinomial counterexamples satisfying the source bridging hypothesis
`R ∈ I_s`. The answer is:

> **The family is a genuine infinite family, but only on the one-dimensional
> slice `q = 2`, `p = L` (read length equals the `A`-run length), where the
> exact likelihood ratio is exactly `2^x` for `x` copies of the amplified
> read `A^L`. For `q >= 3` no member of the family can work: `I_s` forces an
> observed read type that `D` cannot represent. For `q = 1` coverage forces
> the same. For `q = 2` with `p != L` no member works either. The general
> two-parameter claim is therefore false.**

The results below are proved, not merely sampled, and the parameter range is
independently reproduced by a complete support search for `p+q <= 9`
(`scripts/verify_exact_run_family.py`, part B).

## 1. Model and conventions

- Circular truth `S` of length `G`, read length `L`, `N` error-free reads
  drawn uniformly from the `G` circular starts, observed type-count vector
  `x`.
- Fixed-length exact multinomial ordering (Medvedev–Brudno §6.1 with the
  candidate length constrained to `G`; the observation-only multinomial
  coefficient and the length denominators are candidate-independent):

  ```text
  L_exact(D | x) / L_exact(S | x) = prod_i ( d_D(i) / d_S(i) )^{x_i},
  ```

  with value `0` if an observed type has `d_D(i) = 0`.
- `I_s` is the Shomorony–Bresler hypothesis reconstructed in
  `docs/bridging-source-semantics.md`: coverage, every maximal triple repeat
  all-bridged, every interleaved pair of maximal repeat pairs bridged.
  Maximality is the source two-copy / three-copy condition; a copy is bridged
  when **a single read** covers at least one base strictly on each side of it.

Throughout `p, q >= 1`, `G = p + q`, `1 <= L <= G`. The family is
**same-length**:

```text
|D(p,q)| = (p+1) + (q-1) = p + q = |S(p,q)| = G.
```

This same-length property is why the family is a fixed-length counterexample
and why the exact ratio has the simple product form above (no `G/n` factor and
no multinomial coefficient appear).

## 2. Spectra and the exact ratio

Let `d_S`, `d_D` be the `L`-mer spectra of `S = A^p C^q` and
`D = A^(p+1) C^(q-1)`.

**Lemma 1.** `S` has `G` circular windows: `A^L` occurs `max(p-L+1, 0)` times;
`C^L` occurs `max(q-L+1, 0)` times; the remaining windows are the boundary
types `A^a C^c A^b` with `c >= 1` (mixed windows), each determined by its
numbers of `A`'s and `C`'s and its position relative to the two run
boundaries. In the **clean regime** `p, q >= L` the mixed types are
`A^j C^(L-j)` and `C^j A^(L-j)` for `j = 1, ..., L-1`, each occurring exactly
once in both `S` and `D`, and the spectra differ only by

```text
d_D(A^L) = d_S(A^L) + 1 = (p-L+2),      d_D(C^L) = d_S(C^L) - 1 = (q-L).
```

Consequently in the clean regime, for a sample concentrated on `A^L`
(`x_A` reads) and `C^L` (`x_C` reads),

```text
L(D)/L(S) = ((p-L+2)/(p-L+1))^{x_A} * ((q-L)/(q-L+1))^{x_C}.     (2.1)
```

In the boundary regime `p = L`, `q = L-1` (the slice of interest), the
spectra differ by `d_D(A^L) = 2` versus `d_S(A^L) = 1`, `D` drops the two
types `A C^(L-1)` and `C^(L-1) A`, and creates the wrap type
`A C^(L-2) A`; the common observed types `A^(L-1) C`, `C A^(L-1)` keep
multiplicity one in both. Hence for the sample
`{A^L : x, A^(L-1) C : 1, C A^(L-1) : 1}`,

```text
L(D)/L(S) = 2^x.                                                (2.2)
```

**Observation (why the clean regime does not give counterexamples).** Formula
(2.1) is correct likelihood algebra for all `p, q >= L`, but no clean-regime
member is an `I_s`-feasible counterexample. The `A`-run of length `p >= 3`
contains the maximal triple repeat `A^(p-2)`, whose middle copy has neighbours
`0` and `p-1`. A bridging read either stays on the `A`-side (which requires
length at least `p`, and to stay `D`-admissible must not enclose the whole
`C`-run, so needs `L >= p`) or takes the `C`-side arc, which contains the
entire `C`-run (all `q` `C`'s) and is therefore absent from `D`, whose `C`-run
is `q-1`. For `q >= 3` the separate obstruction of Theorem 4 rules out every
`I_s`-feasible `D`-admissible sample; for `q <= 2` the only surviving
parameters are the slice of §3. Hence the `I_s`-feasible slice is the opposite
boundary `p = L`, `q = 2`, not the clean regime.

## 3. The infinite slice `q = 2`, `p = L`

**Theorem 2 (infinite exact counterexample family).** For every `L >= 2`, set

```text
S = A^L C^2,              G = L + 2,
D = A^(L+1) C,
starts = (0 repeated x times), 1, G-1 = L+1,
observed = { A^L : x,  A^(L-1) C : 1,  C A^(L-1) : 1 }.
```

Then:

1. `|S| = |D| = L+2`;
2. `R ∈ I_s` (coverage, all maximal triple repeats all-bridged, no
   interleaved pair needing a bridge);
3. every observed type has positive multiplicity in both `S` and `D`;
4. `L_exact(D | x) / L_exact(S | x) = 2^x > 1` for every `x >= 1`.

Hence `D` strictly beats the truth under the fixed-length exact multinomial
objective. For `L = 1` the same construction gives ratio `2^(x-2)` (still
unbounded), and `p = 1, 2` with `q = 2`, `L = 1` are degenerate `I_s`
counterexamples as well.

**Proof.**

*Same length.* Immediate from §1.

*Coverage.* The reads at `0, 1, G-1` cover `0..L-1`, `1..L`, and
`L+1, 0, 1, ..., L-2` respectively (the last wraps); their union is
`{0, ..., L+1} = {0, ..., G-1}`.

*Repeats of `S`.* A length-`ell` window containing a `C` is determined by the
number of leading `A`'s and the run it lies in, and occurs at most once; the
only repeated windows are the all-`A` windows `A^ell` (`1 <= ell <= L-1`) and
the single symbol `C` (`ell = 1`, copies at starts `L, L+1`). The maximal
repeat pairs are therefore the `A`-pairs `{0, L-ell}` and the `C`-pair
`{L, L+1}`.

*All-bridged triple repeats.* `A^ell` has copies `0, 1, ..., L-ell`; it is a
maximal triple repeat exactly for `ell <= L-2` (the preceding symbols contain
the `C` at `G-1`, the following symbols contain the `C` at start `L`). A copy
at `t` is bridged by a single read containing `t-1` and `t+ell`:

- `t = 0`: the read at `G-1` covers `G-1, 0, ..., L-2`, containing `t-1 = G-1`
  and `t+ell = ell <= L-2`;
- `t = 1`: the read at `0` covers `0, ..., L-1`, containing `0` and
  `1+ell <= L-1`;
- `t >= 2`: the read at `1` covers `1, ..., L`, containing `t-1 >= 1` and
  `t+ell <= L`.

Every copy of `A^ell` (and hence every copy of every maximal triple repeat)
is thus bridged. (A maximal triple repeat of `A^ell` selects three of the
copies `0, 1, ..., L-ell`; the case split above covers every such copy, and
`L = 2` has no triple repeat at all.)

*Interleaved pairs.* Every `A`-pair `{0, L-ell}` contains the start `0`, so no
two distinct `A`-pairs have four distinct starts. The `C`-pair `{L, L+1}` is
not interleaved with any `A`-pair, because its two starts are consecutive and
cannot alternate with another pair. No two maximal repeat pairs are
interleaved, so the interleaved clause is vacuous.

*Admissibility of `D`.* In `D = A^(L+1) C` the observed types are
`A^L` (multiplicity `2`), `A^(L-1) C` (multiplicity `1`; requires
`L-1 <= L+1` and one `C`, available), and `C A^(L-1)` (multiplicity `1`).
All are positive.

*Ratio.* Only `A^L` differs between the observed spectra, with `d_D/d_S = 2`;
the other observed types contribute `1`. With `x` observed copies of `A^L`,
(2.2) gives `2^x`. ∎

**Corollary 3.** Setting `L = 3` recovers (up to renaming `B ↔ C`) the
kernel-checked fixed-length exact counterexample `S = AAABB`, `D = AAAAB` with
ratio `2`. The slice is a genuine infinite family in both parameters `(L, x)`:
the genome changes with `L` and, for fixed `L`, the ratio is unbounded in the
sample concentration `x`.

## 4. Obstruction: the general family fails for `q >= 3`

**Theorem 4.** Let `p >= 1`, `q >= 3`. Let `S = A^p C^q` and
`D = A^(p+1) C^(q-1)`. No read collection `R` with `R ∈ I_s` uses only types
that `D` represents. Hence `D` has exact likelihood `0` on every
`I_s`-feasible sample, and no member of the family with `q >= 3` is a
counterexample.

**Proof.** The `C`-run has length `q >= 3`, so the length-`(q-2)` window
`C^(q-2)` occurs at the three starts `p, p+1, p+2` and is a maximal triple
repeat: the preceding symbols are `A, C, C` (not all equal) and the following
symbols are `C, C, A` (not all equal). By `I_s`, every copy — in particular the
**middle** copy at `t = p+1` — must be bridged. Its neighbours are
`t-1 = p` and `t + (q-2) = p + q - 1`, the two ends of the `C`-run.

A single read bridges the copy only if its window contains both `p` and
`p+q-1`. On a circle there are exactly two arcs joining these positions.

- **`C`-side arc** (through the `C`-run): the window contains positions
  `p, p+1, ..., p+q-1`, hence at least `q` `C`'s. `D` has `C`-run `q-1`, so
  no window of `D` has `q` or more `C`'s.
- **`A`-side arc** (through the `A`-run): the window must traverse the
  entire `A`-run (it leaves the `C`-run at `p+q-1`, crosses all `p` `A`'s, and
  re-enters at `p`), so it contains exactly `p` `A`'s and has the form
  `C^a A^p C^b` with `a, b >= 1` (two separated `C`-blocks). The analogous
  two-block windows of `D`, which traverse `D`'s whole `A`-run, contain
  exactly `p+1` `A`'s. Since a read type is a linear word, `C^a A^p C^b` and
  `C^a A^(p+1) C^b` are distinct types, and `D` has no two-block type with
  exactly `p` `A`'s.

Every window bridging the middle copy is therefore absent from `D`; since
`I_s` requires at least one such window to be observed, the observed sample
assigns `D` a zero factor. ∎

(*The `C`-side count satisfies `c >= q`, and `D`'s maximum `C`-count is
`q-1`. On the `A`-side the `A`-count is forced to be exactly `p` in `S` but
exactly `p+1` in `D`. Thus in both cases the bridging type is absent. The probe
part (C) of the verification script enumerates all bridging types for several
`(p,q)` and confirms every one has `d_D = 0`.*)

## 5. The remaining cases: `q = 1` and `q = 2, p != L`

**Theorem 5.** Let `q = 1`. Then `D = A^(p+1)` contains no `C` at all.
`I_s` includes coverage of `S = A^p C`, so the sample observes a read
containing `C`, a type `D` does not represent. Hence `D` has likelihood `0`
on every `I_s`-feasible sample: no counterexample.

**Theorem 6.** Let `q = 2` and `p != L`. Then no member is a counterexample of
this form (same `D = A^(p+1) C`).

**Proof.** Fix `q = 2`, so `G = p+2`, `D = A^(p+1) C`, and the `D`-missing
types are exactly those containing both `C`'s. Assume `L >= 2`.

- `p > L`: then `p >= 3`, and the `A`-run of length `p` contains the maximal
  triple repeat `A^(p-2)` (copies at starts `0, 1, 2`; preceding `C, A, A` and
  following `A, A, C`). Its middle copy at start `1` has neighbours `0` and
  `p-1`, both `A`. A read containing both must either stay inside the `A`-run
  (hence be all-`A` or, if it extends one step to the `C`-run, have one `C`),
  which requires length at least `p`, or take the arc through the `C`-run,
  which contains both `C`'s and is `D`-missing. Since `L < p`, no admissible
  read bridges the middle copy, so `S` cannot satisfy `I_s`.
- `p = L-1`: `S = A^(L-1) C^2` has no all-`A` window of length `L`. Avoiding
  the `D`-missing two-`C` types, the only available read types are the common
  types `A^(L-1) C` and `C A^(L-1)` (plus their shifted one-`C` variants
  `A^a C A^(L-1-a)` that do not occur in `S`). The two common types have equal
  multiplicity one in `S` and `D`, so every sample has ratio `1`.
- `p <= L-2`: then `L >= p+2 = G`, so `L = G`: every read is the whole
  circular genome `S`, whose type contains both `C`'s and is `D`-missing. `D`
  is inadmissible.

This proves Theorem 6 for `L >= 2`. For `L = 1` the only surviving `q = 2`
members are `p in {1,2}` (no maximal triple repeat exists, so `I_s` reduces to
coverage), the degenerate exception recorded in Corollary 7. ∎

**Corollary 7 (parameter range).** For read length `L >= 2`, the family
`S = A^p C^q`, `D = A^(p+1) C^(q-1)` yields a fixed-length exact-multinomial
counterexample satisfying `I_s` **iff**

```text
q = 2  and  p = L,
```

with ratio `2^x`. The degenerate read length `L = 1` additionally admits
`q = 2`, `p in {1, 2}` (no maximal triple repeat exists and `I_s` reduces to
coverage), with ratio `((p+1)/p)^(x_A) (1/2)^(x_C)`, which exceeds `1` for
sufficiently many `A`-reads.

In particular the "clean regime" formula (2.1), which is valid for all
`p, q >= L` as likelihood algebra, is **not** compatible with `I_s`: the
`I_s`-feasible slice is the opposite boundary `p = L`, `q = 2`, where (2.2)
holds.

## 6. Computational certificate

`scripts/verify_exact_run_family.py` re-implements the semantics of
`docs/bridging-source-semantics.md` independently and checks, with
`fractions.Fraction`:

- **Part A:** for `L = 3, ..., 12`, the slice witness satisfies `|S| = |D|`,
  `I_s`, and exact ratio `2^x` (`x = 3`), all `True`.
- **Part B:** a complete support search over all `p, q <= 5`, `L <= 5`,
  `p+q <= 9` and all nonempty start sets. Since `I_s`, coverage, and the set
  of observed types depend only on the *set* of latent starts, this is a
  complete decision procedure for "does some `I_s`-feasible sample avoid
  `D`-missing types and admit an amplifying observed type" in that range. The
  only hits with `L >= 2` are `(p,q,L) = (2,2,2), (3,2,3), (4,2,4), (5,2,5)`,
  i.e. exactly `q = 2, p = L`. (The single `L = 1` hit besides `(1,2,1)` is
  `(2,2,1)`, matching Corollary 7.)
- **Part C:** for `(p,q) in {(2,3),(3,3),(3,4),(4,5),(5,3),(3,5)}` it
  enumerates every read type bridging the middle copy of `C^(q-2)` and
  reports that none has positive multiplicity in `D`, matching Theorem 4.

Run: `python3 scripts/verify_exact_run_family.py`.

## 7. Epistemic classification

| Claim | Class | Location |
|-------|-------|----------|
| Same-length property and exact ratio lemmas | mathematical proof | §1–§2 |
| Infinite slice `q=2, p=L` is an `I_s`-feasible exact counterexample with ratio `2^x` | mathematical proof | Thm 2, Cor 3 |
| `q >= 3` impossible (middle-copy obstruction) | mathematical proof | Thm 4 |
| `q = 1` impossible | mathematical proof | Thm 5 |
| `q = 2, p != L` impossible | mathematical proof | Thm 6 |
| Parameter range for `L >= 2` is exactly `q = 2, p = L` | mathematical proof | Cor 7 |
| Complete support search for `p+q <= 9` | exact-rational computation (complete in range) | §6 |
| Kernel-checked `L = 3` member (renamed) | Lean (existing) | `AssemblyP1/FixedLengthExactCounterexample.lean` |

## 8. What this does and does not claim

It proves that the run-shift family is a real infinite family of source-faithful
**fixed-length exact-multinomial** counterexamples, but only on the slice
`q = 2, p = L`; the two-parameter generalization `S = A^p C^q`,
`D = A^(p+1) C^(q-1)` with arbitrary `q` is false because of the `C^(q-2)`
middle-copy obstruction. It does not address the binomial approximation, the
unrestricted-length exact objective, or the §6.2 flow feasible set, and it does
not resolve which objective the published 2016 sentence intends.

## 9. Relations to existing repository notes

- The `L = 3` member is the kernel-checked witness of
  `docs/fixed-length-exact-counterexample.md` and the corrected note
  `docs/fixed-length-counterexample-correction.md`.
- The same genomes `S = A^L C^2`, `D = A^(L+1) C` appear as the *binomial*
  (variant A) junction-shift family in
  `docs/analysis/parametric-binomial-counterexample-family.md`
  (branch `agent/binomial-parametric`), where the ratio is
  `2^x (L/(L+1))^2 ((L+2)/(L+1))^(x+2) > 2^x`. The present note is the
  exact-multinomial analogue: the same slice is feasible, the ratio is the
  clean `2^x`, and the general-`q` generalization is ruled out.
- The `q >= 3` obstruction is an instance of the repository's repeated
  "bridging constrains the truth but the competitor must still realize the
  bridging reads" theme (`docs/bridging-likelihood-obstructions.md`,
  `docs/bridging-schemas-and-flow-feasibility-gaps.md`), here with an exact
  two-sided window argument.
