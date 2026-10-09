# Oriented single-strand Section 6.2 with unrestricted candidate length: the truth is not the ML maximizer, in infinite families

_Status: mathematical proof + kernel-checked Lean certificate + exact-rational
verification, 2026-10-09, for board issue #210. Every claim is labelled
**source fact**, **mathematical fact**, **verified computation**,
**interpretation**, or **open**. This front is independent of the bidirected
(reverse-complement-collapsed) §6.2 counterexample
([`../bridging-se62-flow-ml-counterexample.md`](../bridging-se62-flow-ml-counterexample.md),
ratio `9/8`) and of the fixed-length theorem audits
([`oriented-se62-rigidity-theorem.md`](oriented-se62-rigidity-theorem.md));
it uses no result from either._

_Reproduce: `python3 scripts/verify_oriented_variable_length_se62.py` (the
growing-competitor family, `M = 0..4`, both objectives, exact
`fractions.Fraction`) and
`python3 scripts/verify_oriented_variable_length_se62_amplification.py` (the
fixed-competitor amplification families, `M = 0..200`, both objectives, plus
the amplification identities). Self-contained, exact, deterministic; exits
non-zero on any failed assertion. The Lean certificate is
`AssemblyP1/OrientedVariableLengthSe62.lean` (`lake build
AssemblyP1.OrientedVariableLengthSe62`; axiom audit `[propext,
Classical.choice, Quot.sound]` only)._

---

## 0. Verdict at a glance

Under the **source-faithful oriented single-strand** convention — read *types*
are the oriented length-`L` circular windows of the truth (no
reverse-complement collapse), and the only §6.2 feasibility constraint is the
per-vertex lower bound `1` (MB09 §6.2: "Each vertex has a lower bound of `1`
since it represents a read that must be present in the genome at least once")
— the truth need **not** be a §6.1 maximum-likelihood maximizer once the
candidate length is not pinned to `G`, **even though the bridging hypothesis
`I_s` holds and every candidate is genuinely §6.2-feasible** (per-vertex,
spelled support-equality, and single-circuit readings all at once).

The refutation is not a bounded search. Three **infinite families** of strict
counterexamples are proved, all sharing one explicit truth and (in two of the
three) one explicit competitor:

| Family | Competitor | Objective | Ratio at sample multiplicity `M` | Strict for |
|---|---|---|---|---|
| A (growing `D_M`) | `D_M = A^{3+M}TT` | exact, candidate-intrinsic | `(5/(5+M))^{5+M} · (1+M)^{1+M}` | every `M ≥ 1` |
| B (fixed `D`) | `D = AAAATT` | exact, candidate-intrinsic | `(3125/3888) · (5/3)^M` | every `M ≥ 1` |
| C (fixed `D`) | `D = AAAATT` | fixed-`N` binomial, `N = 5` | `(81/128) · 2^M` | every `M ≥ 1` |

Families B and C are the **amplification reduction** made concrete: the truth
and competitor are *fixed* and only the sample multiplicity `M` varies; each
extra observation of the truth read type `AAA` multiplies the exact-ML odds by
`p_D(AAA)/p_S(AAA) = (2/6)/(1/5) = 5/3 > 1` and the fixed-`N` binomial odds
by `Q_AAA = 2 > 1`. At `M = 0` the competitor *loses* (ratios `3125/3888 < 1`
and `81/128 < 1`); from `M = 1` on it wins, with the advantage diverging.
This is **sampling instability**: whether the truth is the maximizer depends
on the finite-sample read multiplicities, not only on the bridging hypothesis.
[mathematical fact, §3–§5; verified computation, §7]

The same-length rigidity theorem ([`oriented-se62-rigidity-theorem.md`](oriented-se62-rigidity-theorem.md))
shows the maximizer *is* forced when `|D| = G`; the families above show that
restriction is essential and sharp. [mathematical fact]

---

## 1. Conventions, stated exactly

These are the conventions the terminal result is stated under. Each is tagged.

- **Alphabet and read types.** Alphabet `{A, T}`. A read type is the
  *oriented* length-`L = 3` circular window of the truth, with **no
  reverse-complement collapse**; the eight oriented types are coded
  `AAA = 0, AAT = 1, ATA = 2, ATT = 3, TAA = 4, TAT = 5, TTA = 6, TTT = 7`.
  [source fact for the oriented single-strand convention: Shomorony et al. 2016
  §2 double-strand-to-single-strand reduction; the *choice* to study the
  oriented, non-collapsed type space is this front's, kept independent of the
  bidirected reading.]
- **Truth.** `S = AAATT`, circular, `G = |S| = 5`. Its length-`3` spectrum is
  `spec_3(S) = {AAA:1, AAT:1, ATT:1, TTA:1, TAA:1}` (total `5`). The maximal
  `A`-run has length exactly `L = 3`, so `spec_3(AAA) = A_0 = 1 < G` (the
  truth is not constant). [verified computation]
- **Sample multiplicity.** An observation is a finite multiset of realized
  read placements. The family uses **all `G = 5` starts once, plus `M` extra
  copies of the start whose window is `AAA`**, so the observed type counts are
  `x^{(M)} = spec_3(S) + M·e_AAA` and the total read count is
  `n = Σ_w x_w = 5 + M`. `M ≥ 0` is the **sample multiplicity** parameter;
  `M = 0` is the "one read per distinct start" observation. [choice: the
  multiplicity model is the source's — reads are sampled with replacement
  (MB09 §6.1: each trial samples a position uniformly from `D`), so arbitrary
  non-negative multiplicities are admissible observations of the truth.]
- **Support.** The observed support is
  `supp(x^{(M)}) = {AAA, AAT, ATT, TTA, TAA}` for every `M` (adding copies
  of an observed type does not change the support). The unobserved types
  `ATA, TAT, TTT` have `x_w = 0` and `d_w = 0` for every candidate below.
  Objectives are products over all eight types with the `0^0 = 1` convention;
  restricting to the support gives the same value. [mathematical fact]
- **Objective (E), exact.** The MB09 §6.1 exact global read-count multinomial
  with **candidate-intrinsic** length `N(D) = |D| = Σ_w d_w`:
  `L_E(d, x) = (n! / ∏_w x_w!) · ∏_w (d_w / t)^{x_w}`, where `t = Σ_w d_w`.
  Domain: every nonempty candidate (`t > 0`); there is **no upper bound** on
  `d_w` beyond `d_w ≤ t`. [source fact: MB09 §6.1 and Medvedev 2010 thesis
  Ch. 4 — the multinomial is defined on the slice `Σ_i d_i = N(D)`]
- **Objective (A), fixed-`N` binomial.** The §6.1 separable approximation with
  **external known** genome size `N`:
  `L_A(d, x) = ∏_w C(n, x_w) · (d_w/N)^{x_w} · ((N - d_w)/N)^{n - x_w}`.
  Domain: the source's `0 ≤ d_w ≤ N`; the log-cost form
  `c_i = -(x_i log d_i) - (n - x_i) log(N - d_i)` (MB09 §6.1, thesis) is
  defined only on the interior `0 < d_w < N`. Here `N = 5 = G` throughout.
  [source fact for the objective and domain; the choice `N = G` is the source's
  own "we assume that the genome size is known", MB09 §6.1.]
- **`N` domain.** For (E), `N(D) = |D|` is candidate-intrinsic, so a
  competitor of length `6 ≠ G` is admissible without any external `N`. For
  (A), `N = 5` is fixed externally; a candidate with some `d_w ≥ N` is
  inadmissible (the factor is `0` when `d_w = N < n - x_w`, and the log-cost
  is undefined at both `d_w = 0` and `d_w = N`). [source fact + mathematical
  fact]
- **Bridging hypothesis.** `I_s` is the Shomorony et al. (2016) Eq. (1)
  information-feasible set, transcribed with the Bresler et al. (2013) repeat
  definitions: coverage of the truth by the realized read starts, every
  Bresler triple repeat all-bridged, every interleaved pair of repeats
  bridged. It is a predicate on the **set** `R` of realized read starts, not
  on the sample multiplicities. [source fact; transcription in
  [`SourceFaithfulIs.lean`](../../AssemblyP1/SourceFaithfulIs.lean) and
  [`../bridging-source-semantics.md`](../bridging-source-semantics.md)]
- **§6.2 feasibility.** Three readings are kept distinct and all are
  discharged for every candidate below: (F1) the literal per-vertex lower
  bound `1` (every observed type occurs at least once) — the source bound;
  (F3) the strictly stronger spelled support-equality form
  (`supp(spec_L(D)) = supp(x)`); and (F4) the §6.2 **flow/circuit** form
  (the candidate is realized by a closed walk of the oriented read-overlap
  graph whose per-vertex read counts equal its spectrum — the literal §6.2
  object, restricted to the single-circuit case). [F1 is source fact; F3 and
  F4 are source-supported strengthenings, chosen so the witness survives every
  reading of "genuinely §6.2-feasible". The per-occurrence form `d ≥ x` is a
  *different, stronger* variant treated separately in §6.]
- **Variable genome length.** The candidate length `|D|` is a free parameter;
  it is **not** pinned to `G`. Families A lets `|D_M| = 5 + M` grow with the
  sample; Families B and C keep `|D| = 6 ≠ G` fixed. [choice: the published
  question (Shomorony et al. 2016) does not fix the candidate length; the
  fixed-`G` restriction is this front's independent contrast.]

---

## 2. The instance and the run-extension lemma

**Fact (run extension).** For `S = AAATT` and every `M ≥ 0`, the circular word
`D_M = A^{3+M}TT` (the truth with `M` extra `A`s inserted inside its maximal
`A^3` run) has spectrum

```text
spec_3(D_M) = spec_3(S) + M·e_AAA   (total 5 + M),
```

i.e. inserting `M` extra `A`s into the maximal `A^3` run adds exactly `M`
copies of the window `AAA` and preserves every other window. [verified
computation for `M = 0..6`, script §2; the Lean module kernel-checks the
`M = 1, 2` instances via `dD_eq`, `dD2_eq`. The general statement for all `M`
is the uniform closed pattern `spec_3(A^r TT) = {AAA: r-2, AAT:1, ATT:1,
TTA:1, TAA:1}` for `r ≥ 3`: the length-`3` windows of `A^r TT` are the `r-2`
all-`A` windows inside the run plus the four boundary windows `AAT, ATT, TTA,
TAA`, so only the `AAA` count depends on `r`, as `r - 2`. Each per-`M`
certificate is an instance of this one pattern, so no bounded search is
needed.]

Consequently the competitor's spectrum **equals the observation**: with
`x^{(M)} = spec_3(S) + M·e_AAA` we have `d_{D_M} = x^{(M)}` for every `M`.
[mathematical fact, from the run-extension lemma]

---

## 3. Theorem A: growing-competitor family, exact objective — strict for every `M ≥ 1`

**Theorem A (exact objective, variable length).** For every `M ≥ 1`, with
truth `S = AAATT`, observation `x^{(M)} = spec_3(S) + M·e_AAA`
(`n = 5 + M`), and competitor `D_M = A^{3+M}TT` (`|D_M| = 5 + M ≠ G`):

1. `R = {0,1,2,3,4}` (all five starts) lies in `I_s`. In fact the
   interleaved-repeat clause is vacuous on this truth (it has no interleaved
   pair of maximal repeats), and the unique maximal triple repeat — the
   length-`1` triple of `A`s at starts `(0,1,2)` — is all-bridged because
   `1 = L - 2`. [kernel-checked: `truth_information_feasible` in
   `OrientedVariableLengthSe62.lean`, discharged by `decide` on the shared
   `SourceFaithfulIs.InformationFeasible` predicate at full strength]
2. Both candidates are genuinely §6.2-feasible under F1, F3, and F4.
   [kernel-checked at `M = 1, 2` in the Lean module; the certificate is
   uniform in `M` — see §5]
3. The exact §6.1 ratio is

```text
L_E(d_{D_M}, x^{(M)}) / L_E(d_S, x^{(M)}) = (5/(5+M))^{5+M} · (1+M)^{1+M}  >  1
```

for every `M ≥ 1`. [mathematical fact; exact values kernel-checked at `M = 1`
(`15625/11664`) and `M = 2` (`2109375/823543`) in the Lean module]

**Proof.** The exact objective at fixed observation `x` is
`L_E(d, x) = C(x) · ∏_w (d_w/t)^{x_w}` with `C(x) = n!/∏x_w!` depending only
on `x`. The competitor has `d_{D_M} = x^{(M)}` and `t_{D_M} = 5 + M = n`, so
its normalized spectrum is exactly `x^{(M)}/n`, and therefore it **attains
the universal upper bound**

```text
L*(x) = C(x) · ∏_w (x_w/n)^{x_w}
```

(weighted AM-GM: `∏ p_w^{x_w} ≤ ∏ (x_w/n)^{x_w}` on the simplex
`{p ≥ 0, Σp = 1}`, with equality iff `p_w = x_w/n` for every `w`; strict for
`p` in the relative interior otherwise). The truth has normalized spectrum
`spec_3(S)/5`, and `spec_3(S)/5 = x^{(M)}/(5+M)` would require, at the `AAA`
coordinate, `1 = (5/(5+M))·(1+M)`, i.e. `M = 0`. So for every `M ≥ 1` the
truth's normalized spectrum differs from `x^{(M)}/n`, hence
`L_E(d_S, x^{(M)}) < L*(x^{(M)}) = L_E(d_{D_M}, x^{(M)})`. ∎

The closed form is the exact ratio: `L*(x^{(M)})/L_E(d_S, x^{(M)})`
`= ∏_w [ (x_w/n) / (d_S(w)/5) ]^{x_w}`; the four non-`AAA` coordinates
contribute `(5/(5+M))^4` (their total multiplicity is `n - (1+M) = 4`) and
the `AAA` coordinate contributes `(5(1+M)/(5+M))^{1+M}`; the product simplifies
to `(5/(5+M))^{5+M}·(1+M)^{1+M}`. [verified computation for `M = 0..4`, script
§4, including the closed form; the simplification is a rational-identity
check.]

**Consequence.** The ratio tends to `∞`. Indeed, with
`f(M) = (1+M)·log(1+M) - (5+M)·log(1+M/5)` (so `ratio = e^f`), we have
`f(0) = 0` and `f'(M) = log(5(1+M)/(5+M))`, which is positive for `M > 0`
and tends to `log 5 > 0`; hence `f` is strictly increasing with
`f(M) → ∞` (at least linearly in `M`), so the ratio diverges (at least like
`5^M`). The competitor's advantage is unbounded in the sample multiplicity.
[mathematical fact]

---

## 4. The amplification lemmas: the general mechanism

The following two lemmas are the **amplification reduction**. They explain
Families B and C and show the mechanism is not an artifact of the growing
competitor in Theorem A.

**Lemma 1 (exact-ML amplification).** Let `x` be an observation, `d_S`, `d_D`
spectra with `t_S = Σd_S`, `t_D = Σd_D` positive, and `w` a type with
`d_S(w) > 0` and `d_D(w) > 0`. For `m ≥ 0` put `x^{(m)} = x + m·e_w`. Then

```text
L_E(d_D, x^{(m)}) / L_E(d_S, x^{(m)})
  = [ L_E(d_D, x) / L_E(d_S, x) ] · ( p_D(w) / p_S(w) )^m,
  p_X(w) = d_X(w) / t_X.
```

*Proof.* The multinomial coefficient `C(x)` depends only on the observation
and is the same for both candidates, so it cancels in the ratio. The remaining
product `∏_u (d_u/t)^{x_u}` at `x^{(m)}` differs from its value at `x` only
at the coordinate `w`, where the exponent rises by `m`; every other coordinate
is unchanged. Hence the ratio of the products at `x^{(m)}` equals the ratio at
`x` times `(d_D(w)/t_D)^m / (d_S(w)/t_S)^m = (p_D(w)/p_S(w))^m`. ∎
[mathematical fact; verified computation of the identity for the instance,
`M = 0..200`, amplification script §2]

**Corollary 1 (sampling instability).** If `p_D(w) > p_S(w)` at some observed
type `w`, then the competitor strictly beats the truth for every
`m > log( L_E(d_S,x) / L_E(d_D,x) ) / log( p_D(w)/p_S(w) )`. In particular a
single strictly positive base ratio is amplified to divergence. [mathematical
fact]

**Lemma 2 (fixed-`N` binomial amplification).** Same setup, external `N`, with
`p_X(i) = d_X(i)/N`. Then

```text
L_A(d_D, x^{(m)}) / L_A(d_S, x^{(m)})
  = [ L_A(d_D, x) / L_A(d_S, x) ] · Q_w^m,
  Q_w = ( p_D(w)/p_S(w) ) · ∏_{i ≠ w} ( (1 - p_D(i)) / (1 - p_S(i)) ).
```

*Proof.* Adding `m` copies of `w` raises `n` and `x_w` by `m`, so `n - x_w`
is invariant; the binomial coefficients `C(n, x_i)` are the same for both
candidates and cancel. At coordinate `w` the multiplier is
`p_w^{x_w+m} (1-p_w)^{n-x_w} / [ p_w^{x_w} (1-p_w)^{n-x_w} ] = p_w^m`. At
each `i ≠ w` the multiplier is `(1-p_i)^{(n+m)-x_i} / (1-p_i)^{n-x_i}
= (1-p_i)^m`. Taking the ratio of the `D` and `S` multipliers gives `Q_w^m`.
∎ [mathematical fact; verified computation of the identity for the instance,
`M = 0..200`, amplification script §4]

**Monotonicity facts used by the reduction.** [mathematical facts, about the
source predicates]

- `I_s(R)` is monotone under adding reads to `R`: coverage is monotone; a copy
  is bridged if *some* read in `R` covers a base on both sides, so adding
  reads preserves "all-bridged" and "interleaved-bridged".
- The §6.2 feasibility forms F1, F3, F4 are properties of the candidate's
  spectrum `d_D` alone (not of the observation), so they are unaffected by
  adding observations. The per-occurrence form `d ≥ x` is **not** monotone in
  this sense and is treated separately (§6).

These are why the amplification preserves both the bridging hypothesis and
the competitor's §6.2 admissibility: only the sample changes.

---

## 5. Families B and C: fixed truth, fixed competitor, growing sample — strict for every `M ≥ 1`

Fix the truth `S = AAATT` and the single competitor `D = AAAATT`
(`|D| = 6 ≠ G`, `d_D = spec_3(S) + e_AAA = {AAA:2, AAT:1, ATT:1, TTA:1,
TAA:1}`). Both are genuinely §6.2-feasible (kernel-checked in the Lean module)
and `R = {0,1,2,3,4} ∈ I_s`. Only the observation grows:
`x^{(M)} = spec_3(S) + M·e_AAA`, `n = 5 + M`.

**Theorem B (exact objective, fixed competitor).** For every `M ≥ 1`,

```text
L_E(d_D, x^{(M)}) / L_E(d_S, x^{(M)}) = (3125/3888) · (5/3)^M  >  1.
```

*Proof.* At `M = 0` the ratio is `∏_w (d_D(w)/6)^{x_w} / (d_S(w)/5)^{x_w}`
with `x = spec_3(S)`: the four non-`AAA` coordinates give `(5/6)^4`, the
`AAA` coordinate gives `(2/6)/(1/5) = 5/3`, total `(5/6)^4·(5/3) = 3125/3888`.
Each further `AAA` observation multiplies by `p_D(AAA)/p_S(AAA) =
(2/6)/(1/5) = 5/3 > 1` (Lemma 1). At `M = 1` the ratio is
`15625/11664 > 1` (kernel-checked), and it diverges. ∎

**Theorem C (fixed-`N` binomial, `N = 5`).** For every `M ≥ 1`,

```text
L_A(d_D, x^{(M)}) / L_A(d_S, x^{(M)}) = (81/128) · 2^M  >  1.
```

*Proof.* At `M = 0` the ratio is `[(2/5)(3/5)^4] / [(1/5)(4/5)^4]
= 2·(3/4)^4 = 81/128`. All non-`AAA` coordinates of `d_D` and `d_S` coincide,
so `Q_AAA = (p_D(AAA)/p_S(AAA)) · 1 = (2/5)/(1/5) = 2` (Lemma 2). Each
further `AAA` observation doubles the odds. At `M = 1` the ratio is `81/64 >
1` (kernel-checked in the Lean module — this instance coincides with the
growing family at `M = 1`), at `M = 2` it is `81/32 > 1` (exact script
verification), and it diverges. ∎

**`N`-domain analysis (essential).** For Families B and C the candidates are
*fixed*, so `d_D(AAA) = 2` and `d_S(AAA) = 1` satisfy `0 < d_w < N = 5` at
**every** `M`: the families are admissible for all `M ≥ 1`, no domain cutoff.
For the *growing* family A under objective (A), `d_{D_M}(AAA) = 1 + M`, so
the source domain `d_w ≤ N` holds only for `M ≤ 4`; at `M = 4` the factor
`((N-d_w)/N)^{n-x_w}` is `0` (the candidate assigns probability `1` to `AAA`
yet other types were observed), and for `M ≥ 5` the candidate is outside the
domain entirely. Under objective (E) there is no such cutoff (the length is
candidate-intrinsic), which is why Theorem A holds for all `M`. [mathematical
fact + source fact about the domain]

---

## 6. The per-occurrence variant `d ≥ x` is a separate question (open)

The source §6.2 bound is the per-vertex `1`. The stronger per-occurrence form
`d_w ≥ x_w` is **not** the source bound and is treated as a separate,
optional variant. [source fact for the distinction; choice to keep them
separate, per the issue brief]

For the families above the variant is **silent**: at `M ≥ 1` the observation
has `x(AAA) = 1 + M > 1 = spec_3(S)(AAA)`, so the *truth itself* is not
`d ≥ x`-feasible and the comparison is vacuous. [verified computation, script
§4]

The nontrivial per-occurrence question — with `x ≤ spec_3(S)` (so the truth
is `d ≥ x`-feasible) and `R ∈ I_s`, can a `d ≥ x`-feasible competitor
strictly beat the truth? — was bounded-censused (truths over `{A,T}` of
length `≤ 6`, `L = 3`, every `I_s`-feasible start set, every observation
`T`-window-multiset `≤ x ≤ spec_3(S)` with `|x| ≤ G`, every circular binary
competitor of length `≤ G + 3`, filtered by a necessary flow-admissibility
condition): **no strict counterexample survives in scope**. [verified
computation, script §6 — **bounded evidence only, not a proof of absence**;
the variant remains **open** in both directions and is out of scope for this
front's terminal result, which is stated under the source per-vertex reading
(and survives the stronger F3/F4 readings).]

---

## 7. Verification map

| Claim | Certificate |
|---|---|
| `I_s` at full strength for `R = {0,1,2,3,4}`, `L = 3` | Lean `truth_information_feasible` (`decide` on `SourceFaithfulIs.InformationFeasible`), axiom-clean |
| F1/F3/F4 §6.2 feasibility, growing family `M = 1, 2` | Lean `truth_perVertex_feasible1/2`, `competitor_perVertex_feasible1/2`, `*_spelled_feasible1/2`, `*_section62_feasible1/2` (closed walks `walkS`, `walkD`, `walkD2` of the read-overlap graph) |
| Exact ratios `15625/11664` (`M=1`), `2109375/823543` (`M=2`), growing family | Lean `exact_ratio1/2`, `competitor_strictly_better_exact1/2`; script §4 exact `Fraction` |
| Binomial ratios `81/64` (`M=1`), `27/16` (`M=2`), growing family | Lean `binom_ratio1/2`, `competitor_strictly_better_binom1/2`; script §4 |
| Closed form `(5/(5+M))^{5+M}·(1+M)^{1+M}`, `M = 0..4` | script §4 (`check("M=%d: closed form")`) |
| `L*(x)` bound and attainment | Lean `exact_competitor*_attains_bound`, `exact_truth*_below_bound`; script §5 exhaustive over circular binary words of length `≤ 12` (bounded evidence for the bound, which Theorem A §3 proves for all `M`) |
| Amplification identities (Lemmas 1–2), `M = 0..200` | `verify_oriented_variable_length_se62_amplification.py` §2, §4 (exact `Fraction`) |
| Theorem B closed form `(3125/3888)(5/3)^M`, `M = 1..200` | amplification script §3 |
| Theorem C closed form `(81/128)2^M`, `M = 1..200` | amplification script §5 |
| `I_s` and F1/F3 admissibility preserved for `M = 1..200` | amplification script §6 (finite-predicate checks; the general monotonicity facts are proved in §4) |
| Truth not `d ≥ x`-feasible, `M = 1, 2, 3` | script §4 of `verify_oriented_variable_length_se62.py` |

All Lean theorems kernel-check with axioms `[propext, Classical.choice,
Quot.sound]` only; no `sorry`, `axiom`, or `admit`. [verified computation:
`#print axioms` on the endpoint theorems]

---

## 8. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| Oriented length-`L` windows are the read types; no reverse-complement collapse | source fact + this front's choice | Shomorony et al. 2016 §2; issue brief's "ORIENTED single-strand" |
| §6.2 feasibility = per-vertex lower bound `1` | source fact | MB09 §6.2 |
| Exact objective has candidate-intrinsic `N(D)`, no external `N` | source fact | MB09 §6.1; Medvedev 2010 thesis Ch. 4 |
| Fixed-`N` binomial objective, external known `N`, domain `0 ≤ d_w ≤ N` (log form: `0 < d_w < N`) | source fact | MB09 §6.1; thesis; [`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md) §2.2, §6 |
| `I_s` = coverage + triple-repeat all-bridged + interleaved bridged | source fact | Shomorony et al. 2016 Eq. (1); Bresler et al. 2013; [`../bridging-source-semantics.md`](../bridging-source-semantics.md) |
| `R ∈ I_s` for `R = {0,1,2,3,4}` | kernel-checked fact | Lean `truth_information_feasible` |
| Both candidates §6.2-feasible (F1, F3, F4) at `M = 1, 2` | kernel-checked fact | Lean module |
| Strict exact ratio at `M = 1, 2`; strict binomial ratio at `M = 1, 2` | kernel-checked fact | Lean module; script §4 |
| Theorem A strict for every `M ≥ 1`, closed form | mathematical fact | §3 proof (AM-GM + run extension); closed form verified `M = 0..4` |
| Theorems B, C strict for every `M ≥ 1`, closed forms | mathematical fact | §4–§5 proofs (Lemmas 1–2); identities verified `M = 0..200` |
| `I_s` and §6.2 admissibility are preserved under added observations | mathematical fact | §4 monotonicity facts |
| Per-occurrence variant: no strict counterexample in bounded scope | open (bounded evidence only) | script §6; not a proof of absence |
| The 2016 sentence intends the oriented per-vertex §6.2 reading with variable length | interpretation (not settled) | this front settles the mathematics *under* that reading; the referent question is [`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md) §8 and is not settled here |

**Scope.** This note settles the oriented single-strand variable-length §6.2
question under the source per-vertex feasibility reading (and the stronger F3/F4
readings), for both §6.1 objectives. It does not settle which Medvedev–Brudno
object the Shomorony et al. (2016) sentence intends, nor the bidirected
sub-case, nor the per-occurrence `d ≥ x` variant, nor the fixed-length
rigidity theorem (which it uses only as contrast). The conclusion semantics
(truth-is-a-maximizer vs. all-maximizers-are-truth) is untouched: the
counterexamples refute even the weakest reading (truth is *a* maximizer), since
the truth is beaten strictly.

---

## 9. Independent re-measurement addendum (2026-10-09, second pass)

The inherited committed state (commit `7d48eab`) was re-measured by execution,
not trusted. All claims below are tagged **[fact]** (verified by execution or
kernel), **[inference]** (derived here), or **[choice]** (this pass's action).

1. **Scripts re-run, exact `Fraction` arithmetic, self-contained.**
   `python3 scripts/verify_oriented_variable_length_se62.py` →
   `ALL ASSERTIONS PASSED`, exit `0` **[fact]**.
   `python3 scripts/verify_oriented_variable_length_se62_amplification.py` →
   `ALL ASSERTIONS PASSED`, exit `0` **[fact]**.
2. **Lean kernel check.** `lake build AssemblyP1.OrientedVariableLengthSe62`
   → success, exit `0` (8925 jobs) **[fact]**. `leanchecker` kernel replay of
   the module → exit `0` **[fact]**. `#print axioms` on
   `oriented_variable_length_se62_counterexample`,
   `oriented_variable_length_se62_counterexample'`,
   `truth_information_feasible`, `competitor_strictly_better_exact1`,
   `competitor_strictly_better_binom1` → each depends on exactly
   `[propext, Classical.choice, Quot.sound]`, no `sorryAx` **[fact]**.
   `grep -nE "sorry|admit|axiom|native_decide"` over the module → no matches
   **[fact]**.
3. **Repository verification script.**
   `python3 scripts/check-research-docs.py` → passed, exit `0` **[fact]**.
4. **Full-library build.** `lake build --wfail` → exit `1` **[fact]**, but
   only in modules this front does not touch and does not import:
   `AssemblyP1.BBTTripleBridge`, `AssemblyP1.Issue94Transposition`,
   `AssemblyP1.Issue94ComponentAlignedSwaps`, and the aggregator
   `AssemblyP1.lean` (a `KShort` namespace collision). These failures are
   pre-existing at the branch point `cc0aa8a` (this branch's diff vs `cc0aa8a`
   is exactly the four new files; the aggregator does not import this module)
   **[fact]**, and `origin/main` has since repaired them in commits `0ea7b44`,
   `913ec4a`, `3e972e2` (not in this branch) **[fact]**. The failures are not
   attributable to front #210 **[inference]**.
5. **Independent arithmetic re-derivation** (fresh `Fraction` code sharing no
   code with the front's scripts): spectra of `AAATT`, `AAAATT`, `AAAATTA`;
   exact ratios `15625/11664` (`M=1`) and `2109375/823543` (`M=2`); binomial
   ratios `81/64` (`M=1`) and `27/16` (`M=2`); Theorem A closed form
   `(5/(5+M))^{5+M}(1+M)^{1+M}` matching the computed ratio at `M = 1..6`, all
   strict `> 1`; Theorems B and C closed forms matching at `M = 1..5` — all
   reproduced exactly **[fact]**.
6. **Rotation observation (cosmetic, no effect).** The note's Theorem A writes
   the growing competitor as `D_M = A^{3+M}TT`; the Python
   `witness_competitor(M)` and the Lean `competitor2` use `A^{M+2}TTA` (e.g.
   `AAAATTA` at `M=2`), a cyclic rotation of `A^{5}TT = AAAAATT`. Spectra and
   both objectives are invariant under cyclic rotation, so every value in this
   note is unaffected **[fact + inference]**. Kept as-is; recorded here so
   future readers are not confused by the notation mismatch **[choice]**.
7. **Source-fidelity spot check.** The MB09 §6.2 quote ("Each vertex has a
   lower bound of `1` since it represents a read that must be present in the
   genome at least once") and the §6.1 objective/domain quotes match the
   repository provenance records
   ([`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md)
   §4.4, [`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md));
   the shared `SourceFaithfulIs.InformationFeasible` predicate is the
   full-strength `I_s` (coverage + all-bridged triple repeats + bridged
   interleaved pairs), matching the front's Python transcription **[fact]**.
    The per-occurrence `d ≥ x` variant remains a separate, open question; the
    bounded census in script §6 is bounded evidence only, not a proof of
    absence **[fact, unchanged from the inherited classification]**.

---

## 10. Erratum (closure verification, 2026-10-09): precise divergence rate

§3's consequence states the ratio "diverges (at least like `5^M`)". The
divergence itself is correct and proved there (`f` strictly increasing,
`f(M) → ∞`), but the parenthetical overstates the rate. Since
`f'(M) = log(5(1+M)/(5+M))` approaches `log 5` *from below*, one has
`f(M) < M·log 5`, hence `ratio(M) < 5^M` for every `M ≥ 1`. The precise
asymptotic, from `f(M) = (1+M)log(1+M) − (5+M)log(1+M/5)`, is

```text
f(M) = M·log 5 − 4·log M + (5·log 5 − 4) − 12/M + O(1/M²),
```

so `ratio(M) = Θ(5^M / M⁴)`: exponential divergence with rate `log 5`, but
strictly slower than `5^M`. (Verified: `f(M) − M·log 5 + 4·log M + 12/M →
5·log 5 − 4` at `M = 100, 1000, 10000`; `ratio(M) < 5^M` for `M = 1..59`.)
This correction affects only the supplementary divergence remark in §3; the
verdict, the strict-improvement bounds of Theorems A/B/C (`ratio > 1` for
every `M ≥ 1`), and the kernel-checked certificate are unchanged. **[fact:
correction found and verified during closure verification of branch
`agent/board-210-e8b6b2`; the underlying proof in §3 is correct as written.]**
