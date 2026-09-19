# Parametric family for the fixed-length product-of-binomial counterexample

_Status: mathematical analysis of the literal Medvedev–Brudno Section 6.1
product-of-binomial-marginals objective ("Variant A"). It generalizes the
`AAACC` / `AAAAC` witness of
[`docs/fixed-length-binomial-counterexample.md`](../fixed-length-binomial-counterexample.md)
to an explicit two-parameter family of source-faithful counterexamples. It does
**not** settle the source-ambiguous Shomorony et al. open question, and it does
not touch the exact multinomial (Variant E) or the Section 6.2 flow objective._

## 1. Scope and sources

Objective and source reading are those independently audited in the issue #32
notes `docs/audit-issue32-end-to-end.md` (branch `audit/issue32-end-to-end`)
and `docs/audit-binomial-marginals-issue32.md` (branch
`audit/issue32-binomial-marginals`), and in the merged
[`docs/fixed-length-binomial-counterexample.md`](../fixed-length-binomial-counterexample.md).
For a fixed external length `N`, read length `k`, `n` observed reads with
type-count vector `x`, and a length-`N` candidate `C` with type multiplicities
`d_C`, the literal objective is

```text
L_A(C) = prod_{tau in Sigma^k} C(n, x_tau)
             (d_C(tau)/N)^{x_tau} (1 - d_C(tau)/N)^{n - x_tau}.
```

Two source facts are used without reproving them here:

1. the product ranges over the whole read-type space and keeps the
   zero-count factors `(1 - d_C(tau)/N)^{n - x_tau}` (medvedev–brudno
   `M31`/`M33`, re-read in the issue #32 audit);
2. the fixed external `N` encodes the candidate length: for a candidate of
   length `M != N`, `d_C/N` is not the candidate's per-trial probability, so
   the source-faithful approximation universe is the length-`N` candidates
   (`sum_tau d_C(tau) = N`).

The family below lives entirely inside that fixed-length universe. It is
disjoint from the parametric families on branch
`analysis/parametric-fixed-length-formulas` (exact-multinomial objective,
`mathematics/parametric-fixed-length-exact-formulas.md`), which concerns a
different objective, and from the repository's fixed-length brute-force
searches.

## 2. Exact likelihood-ratio factorization

**Lemma 1 (ratio factorization).** _Let `S`, `D` be candidates of the same
length `N`, let `x` be the observed type-count vector with `n = sum_tau x_tau`,
and let `d_S`, `d_D` be their type multiplicities. Then_

```text
L_A(D)/L_A(S) = prod_{tau : d_D(tau) != d_S(tau)}
                    (d_D(tau)/d_S(tau))^{x_tau}
                    ((N - d_D(tau))/(N - d_S(tau)))^{n - x_tau},
```

_with the convention `0^0 = 1`; types with `d_D(tau) = d_S(tau)` contribute
exactly `1`._

_Proof._ The binomial coefficients `C(n, x_tau)` and the denominator
`N^{x_tau}` are candidate-independent, and every factor is positive on the
domain `0 <= d_C(tau) <= N`. Substituting

`(d/N)^x (1 - d/N)^{n-x} = N^{-n} d^x (N-d)^{n-x}`

gives the stated product after cancellation. `square`

The same substitution yields the source convex-cost identity: the objective is,
up to a candidate-independent constant,
`prod_tau d_C(tau)^{x_tau} (N - d_C(tau))^{n - x_tau}`, whose negative log is
`sum_tau c_tau` with `c_tau = -(x_tau log d_C(tau)) - (n - x_tau) log(N - d_C(tau))`,
matching Medvedev–Brudno `M33`.

## 3. Which count-spectrum changes can beat truth

Lemma 1 separates the change into independent per-type factors. Writing
`a = d_S(tau)`, `b = d_D(tau)`, the factor is

```text
rho(a,b,x) = (b/a)^x ((N-b)/(N-a))^{n-x}.
```

**Lemma 2 (sign dictionary).** _On `0 <= a,b <= N` with the `0^0` convention:_

| change of type `tau` | `x_tau` | factor | sign |
|---|---|---|---|
| amplify observed, `b > a > 0` | `x > 0` | `((a+1)/a)^x ((N-a-1)/(N-a))^{n-x}` | positive cap, binomial-failure penalty |
| suppress observed, `0 < b < a` | `x > 0` | inverse of the above | penalty |
| create zero-count, `b > a` | `x = 0` | `((N-b)/(N-a))^n` | `< 1` |
| delete zero-count, `b < a` | `x = 0` | `((N-a)/(N-b))^n` | `> 1` |

_Proof._ Immediate from Lemma 1: for `x = 0` the only surviving exponent is
`n`, and `N - d` is strictly increasing in `d`; for `x > 0` the two factors have
opposite monotonicity. `square`

Two consequences drive every example.

- **Observed amplification is discounted.** Raising an observed count by one
  also raises `d`, which shrinks the "failure" factor `(N-d)^{n-x}`. A unit
  moved onto an observed type is only profitable when the observed evidence `x`
  is large enough relative to `n - x`.
- **Deleting a zero-count unit is a pure gain.** With `a = 1`, deleting one
  unit from an unobserved type contributes `(N/(N-1))^n > 1`; creating one
  contributes `((N-1)/N)^n < 1`. A winning change therefore wants a net
  deletion of zero-count mass.

The unconstrained single-unit transfer `d_D = d_S + e_o - e_u` (with `x_o = x`,
`x_u = 0`) has factor

```text
((d_S(o)+1)/d_S(o))^x ((N-d_S(o)-1)/(N-d_S(o)))^{n-x}
    ((N-d_S(u)+1)/(N-d_S(u)))^n.                        (single transfer)
```

Realizability, however, forbids arbitrary transfers: the multiplicity vector of
a circular word is an Eulerian edge-multiplicity vector of the de Bruijn graph,
so it satisfies prefix/suffix degree balance. The family below realizes the
minimal balance-preserving version of a transfer.

## 4. The junction-shift family

Fix `L >= 3`, put `N = L + 2`, read length `k = L`, and set

```text
S(L) = A^L C^2,      D(L) = A^{L+1} C,
```

both circular of length `N`.

**Theorem 3 (count-spectrum change).** _The spectra of `S(L)` and `D(L)` agree
off the following types and differ exactly by_

- `A^L`: multiplicity `1 -> 2`;
- _deletion_ (`1 -> 0`) _of the `L - 1` zero-count types_

  `A^{L-2-i} C^2 A^{i}` for `i = 0, 1, ..., L - 2`;

- _creation_ (`0 -> 1`) _of the `L - 2` zero-count types_

  `A^{L-1-j} C A^{j}` for `j = 1, ..., L - 2`.

_The common types include `A^{L-1} C` and `C A^{L-1}`, each of multiplicity
one in both spectra._

_Proof._ Enumerate the `N` length-`L` circular windows of each word. In `S(L)`
the windows are `A^L`, `A^{L-1}C`, `A^{L-2}C^2`, then
`A^{L-s}C^2A^{s-2}` for `s = 3, ..., L`, then `C A^{L-1}`. In `D(L)` they are
`A^L` (twice), `A^{L-1}C`, then `A^{L+1-s}C A^{s-2}` for `s = 3, ..., L`, then
`C A^{L-1}`. A length-`L` window containing a `C` is determined by the number
of leading `A`'s, hence occurs at most once in either word; the only length-`L`
window that can repeat is the all-`A` window `A^L`, which occurs once in `S(L)`
and twice in `D(L)`. Comparing the two lists gives the claim, with
`1 + 1 + 1 + (L-2) + 1 = L+2 = N` windows on each side. `square`

**Corollary 4 (closed-form ratio).** _Take the observed read multiset_

```text
{ A^L : x,  A^{L-1} C : 1,  C A^{L-1} : 1 },     n = x + 2,
```

_realized by the true starts `0` (repeated `x` times), `1`, and `N - 1`. Then_

```text
R(L, x) = L_A(D(L)) / L_A(S(L))
        = 2^x ((N-2)/(N-1))^2 (N/(N-1))^{x+2}
        = 2^x (L/(L+1))^2 ((L+2)/(L+1))^{x+2}.
```

_Proof._ By Theorem 3, only `A^L` is an observed changed type; the `L - 1`
deletions and `L - 2` creations of zero-count units combine to
`(N/(N-1))^n`; the common observed types `A^{L-1}C`, `C A^{L-1}` contribute `1`.
Lemma 1 gives

```text
R = (2/1)^x ((N-2)/(N-1))^{n-x} (N/(N-1))^n,
```

and `n - x = 2`, `N = L + 2` give the stated form. `square`

**Corollary 5 (the competitor strictly beats truth, without bound).** _For all
`L >= 3` and all `x >= 1`, `R(L, x) > 2^x >= 2`. Hence `D(L)` is strictly more
likely than the truth `S(L)` under the literal product-of-binomial objective;
moreover `R(L, x) -> infinity` as `x -> infinity`._

_Proof._ Let `B(L,x) = (L/(L+1))^2 ((L+2)/(L+1))^{x+2}`, so `R = 2^x B`. For
`x >= 1`, `B(L,x) >= B(L,1) = (L/(L+1))^2 ((L+2)/(L+1))^3`, and

`L^2 (L+2)^3 - (L+1)^5 = L^4 + 2L^3 - 2L^2 - 5L - 1 > 0` for `L >= 3`,

so `B(L,1) > 1`, hence `B(L,x) > 1`. The `x -> infinity` claim is immediate
from `B(L,x) = ((L+2)/(L+1))^x B(L,0)` with `(L+2)/(L+1) > 1`. `square`

## 5. Source faithfulness of the family

The counterexample must satisfy the bridging hypothesis `R in I_s` of the
truth. With the start set `{0, 1, N-1}`, the realized reads are precisely the
observed multiset of Corollary 4.

**Theorem 6 (I_s certificate).** _For every `L >= 3`, the read set with starts
`0` (repeated `x` times), `1`, and `N-1` in `S(L) = A^L C^2` covers all `N`
positions and bridges every copy of every maximal triple repeat; there is no
interleaved repeat pair requiring an additional bridge._

_Proof._ Coverage: the reads at `0`, `1`, `N-1` cover respectively `0..L-1`,
`1..L`, and `N-1, 0, ..., L-2`, whose union is all of `0..N-1`.

Repeats: a length-`ell` window of `S(L)` containing a `C` is determined by the
number of leading `A`'s, so the only repeated windows of `S(L)` are the all-`A`
windows `A^ell` (`1 <= ell <= L-1`) and the single symbol `C` (`ell = 1`). The
copies of `A^ell` are the starts `0, 1, ..., L-ell`. For `ell <= L-2` this is
at least three copies and the group is maximal (the preceding symbols contain
the `C` at start `0`, and the following symbols contain the `C` at
`start + ell = L`), so it is a maximal triple repeat. A copy at `t` is bridged
by a read covering `t-1` and `t+ell`:

- `t = 0`: the read at `N-1` covers `N-1, 0, ..., L-2`, hence `t-1 = N-1` and
  `t+ell = ell <= L-2`;
- `t = 1`: the read at `0` covers `0, ..., L-1`, hence `1-1 = 0` and
  `1+ell <= L-1`;
- `t >= 2`: the read at `1` covers `1, ..., L`, hence `t-1 >= 1` and
  `t+ell <= (L-ell)+ell = L`.

So every copy of every triple repeat is bridged. The maximal repeat pairs are
`{0, L-ell}` for the distinct all-`A` windows `A^ell` (`1 <= ell <= L-1`),
together with the single-`C` pair `{L, L+1}`; every `A`-pair shares the start
`0`, and the `C`-pair lies on the complementary arc, so no two pairs have four
distinct alternating starts. Hence no interleaved pair needs a bridge.
`square`

The `L = 3` member is the repo witness: `S(3) = AAACC`, `D(3) = AAAAC`, and
`R(3,1) = 1125/512`, matching
[`docs/fixed-length-binomial-counterexample.md`](../fixed-length-binomial-counterexample.md)
exactly. Its bridging certificate is the one kernel-checked in
`AssemblyP1.FixedLengthExactCounterexample`; Theorem 6 identifies the
`(L, x) = (3, 1)` realization with starts `{0, 1, 4}`.

## 6. Systematic structure and minimality

The family answers the "infinite or systematic" question affirmatively on two
independent axes.

1. **Observation axis.** For each fixed `L >= 3`, every `x >= 1` gives a
   distinct observed multiset on the same truth `S(L)` with `R(L,x) > 2^x`.
   The ratio grows exponentially without bound, so even the single
   `AAACC`/`AAAAC` pair seeds an infinite family by concentrating reads on the
   amplified type.
2. **Genome axis.** Every `L >= 3` gives distinct same-length words `S(L)`,
   `D(L)` and a ratio `R(L, x) > 2^x`; the witness is the minimal member
   `L = 3`. The mechanism is a *junction shift*: one unit is moved onto the
   observed all-`A` run while `L-1` zero-count junction types are deleted and
   `L-2` new ones created, the net deletion of one zero-count unit being forced
   by Eulerian balance.

Minimality is genuine, not just aesthetic. The family is "critically scaled":
the run length equals the read length `k = L`. At a fixed read length `k = 3`,
the analogous run-length family `S = A^p C^2` (`p >= 4`) is *not*
source-faithful: `S` then contains at least three copies of the length-`2`
window `AA` with differing flanks, a maximal triple repeat, and a length-`3`
read cannot straddle a length-`2` copy, so no read set can satisfy the
all-bridged clause. Thus within read length `3`, `AAACC`/`AAAAC` is the unique
run-length member; the infinite family requires the read length to grow with
the run.

## 7. Epistemic classification

| Claim | Class |
|---|---|
| Lemma 1 ratio factorization, convex-cost identity | mathematical proof |
| Lemma 2 sign dictionary, single-transfer factor | mathematical proof |
| Theorem 3 count-spectrum change | mathematical proof |
| Corollary 4 closed form `R(L,x)` | mathematical proof |
| Corollary 5 `R(L,x) > 2^x`, unbounded | mathematical proof |
| Theorem 6 `I_s` certificate for all `L >= 3` | mathematical proof (hand); independently reproduced by `scripts/verify_parametric_binomial_family.py` |
| `AAACC`/`AAAAC` is the `(L,x) = (3,1)` member with `R = 1125/512` | mathematical proof, consistent with the existing audited/kernel-checked witness |
| Fixed-`k = 3`, run-length `p >= 4` family fails `I_s` | mathematical proof |
| Source-faithful counterexample to the literal §6.1 Variant A | mathematical proof within the fixed-length reading of §1 |
| Relation to Shomorony et al.'s intended objective | unresolved source ambiguity, not claimed |
| Variant E / Variant F / unrestricted length | out of scope, not claimed |

## 8. What this does and does not claim

It proves that the `AAACC`/`AAAAC` certificate is not isolated: it lies in an
explicit two-parameter family `(L, x)` of length-`N` product-of-binomial
counterexamples whose ratios are computed in exact closed form and which
strictly exceed `2^x`, all satisfying the same bridging hypothesis. It also
isolates the exact mechanism in the count spectrum: a directional junction
shift that deletes one more zero-count unit than it creates while amplifying one
observed type.

It does **not** claim that this approximation is the objective Shomorony et al.
intended, does not address tie or uniqueness semantics, does not kernel-check
the general `L` family in Lean, and does not address the exact multinomial or
the Section 6.2 flow feasible set.

## 9. Reproduce

```text
python3 scripts/verify_parametric_binomial_family.py
```

The script uses only exact `fractions.Fraction` arithmetic and asserts: the base
witness ratio `1125/512`; agreement of the full-type-space product, the
factorized product, and the closed form for `L = 3..8`, `x = 1..5`; the
`2^x` lower bound; the `(L-1, L-2)` spectrum-change counts; and the `I_s`
certificate for `L = 3..12` plus the kernel-checked witness starts `{0,1,4}`.
