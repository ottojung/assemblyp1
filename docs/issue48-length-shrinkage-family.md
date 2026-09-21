# Issue #48: a length-shrinkage family refuting every candidate-intrinsic repair with unknown length

_Status: mathematical proofs (family, primitivity, `P1`/`P2` admissibility,
`I_s` certificate, exact ratio) + exact-rational computation over a wide
parameter range, with cross-checks against the two existing independent
implementations. Not a Lean result. This note attacks the **additional repaired
formulation** of issue #48 (free candidate length, replace the true-length axiom
by candidate-intrinsic checks); it does not reinterpret or weaken any
literature-derived fixed-length result and does not settle the source-ambiguous
Shomorony et al. open question._

_Reproduction: `python3 scripts/verify_issue48_length_shrinkage_family.py`
(self-contained exact `fractions.Fraction` arithmetic, plus cross-checks)._

---

## 0. Direct answer

The finite repaired statement of issue #48 — *replace the true-length axiom by a
candidate-intrinsic structural admissibility predicate, optionally with
primitiveness, under the free-length exact Medvedev–Brudno multinomial* — is
false, and it fails in its **strongest** intrinsic form. The obstruction is not a
residual repeat ambiguity: it is the **length factor** `(G/n)^N`, which no
predicate that depends only on the candidate can see.

The note records a single explicit two-parameter family
(`S = A^(L-1) B B C`, `D = A^(L-1) B C`, read length `L`, sample multiplicity
`x`) that

* contains the issue's headline witness `AABBC -> AABC` as the member `L = 3`;
* has `S` and `D` both **primitive** and both **STRONG** (`P1`: no `(L-1)`-mer
  occurs twice), hence also `WEAK` (`P2`) and admissible in the strongest
  candidate-intrinsic class;
* has a truth `S` that satisfies the strict source `I_s`, **non-vacuously** for
  every `L >= 4` (so the bridging hypothesis is genuinely used, not vacuous);
* has exact free-length likelihood ratio `((L+2)/(L+1))^(x+1) > 1`, i.e.
  `(G/n)^N`, unbounded in the sample multiplicity `x` for fixed `L`.

The reason is structural and is isolated in §2–§3: the free-length objective
factorizes into a **length factor** `(G/n)^N` and a spectrum-fit factor, and
`P1`, `P2`, and primitivity constrain only the spectrum-fit side. This note
sharpens the diagnosis already recorded in
[`issue48-intrinsic-admissibility-counterexample.md`](issue48-intrinsic-admissibility-counterexample.md)
and [`issue48-intrinsic-candidate-checks.md`](issue48-intrinsic-candidate-checks.md)
into one clean parameterized family with a complete proof for every `L`.

---

## 1. Exact conventions attacked

These are fixed for every claim below and are stated so the result cannot be
read as covering a different model.

**Objective (Variant E, free candidate length).** The exact Medvedev–Brudno
read-count multinomial
([`ml-formalization-contract.md`](ml-formalization-contract.md) `:22-28`, Variant
E). For a circular candidate `D`, let `d_D(w)` be the number of circular
length-`L` windows equal to the read type `w`, `N(D) = len(D)`, and `x_w` the
observed count among `N` reads. Then

```text
L_exact(D | x) = N! / (∏_w x_w!) · ∏_w ( d_D(w) / N(D) )^{x_w},
```

so for two candidates the observation-only coefficient cancels:

```text
L(D)/L(S) = ∏_{w : x_w > 0} ( G · d_D(w) / ( n · d_S(w) ) )^{x_w},   G = len(S), n = len(D),
```

with value `0` if some observed `w` has `d_D(w) = 0`. This is the literal
candidate-dependent-length exact multinomial of Medvedev–Brudno §6.1. It is
**not** the fixed-length binomial approximation (Variant A), not the §6.2
flow-feasible set (Variant F), and no reverse-complement collapse is used
(single-strand oriented panel, as in [`bridging-source-semantics.md`](bridging-source-semantics.md)).

**Truth hypothesis `I_s` (source).** `R ∈ I_s` iff (1) `R` covers `S`; (2) every
Bresler triple repeat of `S` is all-bridged by `R`; (3) every interleaved pair of
maximal repeat pairs of `S` is bridged by `R`. Bridging is strict two-sided
extension on an integer lift: a length-`ℓ` copy at lifted start `t` is bridged by
a read at lifted start `r` iff `r < t` and `t + ℓ < r + L`, equivalently
`r = t - d` for some `1 <= d <= L - ℓ - 1`. The `ℓ >= L - 1` case is
unbridgeable. This is the corrected strict predicate (not the exploratory flank
test), matching the source quote in
[`bridging-source-semantics.md`](bridging-source-semantics.md); see also the
standing source-correction note `copy-bridging-predicate-correction.md`.

**Candidate-intrinsic predicates.** A predicate is *candidate-intrinsic* when it
is a function of the candidate circular word and `L` alone. The three used here
are:

* `P1` = `STRONG(D)`: no `(L-1)`-mer of `D` occurs twice.
* `P2` = `WEAK(D)`: every triple repeat of `D` has length `<= L-2` and every
  interleaved maximal-repeat pair has a constituent of length `<= L-2` (the
  full-read-set `I_s` shadow).
* `primitive(D)`: `D` is not a nontrivial power `w^m`, `m >= 2`.

`P1 => P2` (issue #48 comment 1, §3) and `P1 => primitive`; `P2` does not imply
primitivity. `P1` is the strongest natural repeat predicate matched to the
source `I_s`.

**Tie semantics.** The conclusion "the ML sequence is the true sequence" has a
maximizer-only reading and a uniqueness-up-to-equivalence reading
([`ml-formalization-contract.md:80-96`](ml-formalization-contract.md)). The
family gives a **strict** competitor (`L(D) > L(S)`), so it refutes both for
every equivalence relation and every tie rule. Equivalence conventions are
therefore irrelevant to the refutation.

---

## 2. The length factor

**Lemma 1 (free-length factor).** Let `S`, `D` be circular candidates with
observed read-type multiplicities `x_w` supported on a set `W`, and suppose
`d_D(w) = d_S(w) >= 1` for every `w ∈ W`. Then

```text
L(D | x) / L(S | x) = ( G / n )^N,        N = Σ_w x_w,
```

where `G = len(S)` and `n = len(D)`.

**Proof.** Substitute `d_D(w)/d_S(w) = 1` into the ratio formula of §1; every
factor equals `G/n`, and there are `Σ_w x_w = N` of them. ∎

The factor `(G/n)^N` is a function of the two **lengths** and the number of
reads. It is not a function of the candidate word alone, nor of any repeat
structure shared by `S` and `D`. That is the entire obstruction, and §4 makes it
the load-bearing explanation.

The fixed-length positive theorem
([`issue48-intrinsic-admissibility-counterexample.md`](issue48-intrinsic-admissibility-counterexample.md)
Proposition 2) is the `G/n = 1` case: with candidate length pinned to `G`, `P1`
forces `d_D(w) <= 1` and every observed factor is `<= 1`, so the truth is a
maximizer. The family below shows that once the length pin is removed, exactly
the `(G/n)^N` factor appears and `P1` cannot bound it.

---

## 3. The family

**Proposition 2 (length-shrinkage family).** Fix integers `L >= 3` and `x >= 1`
and put

```text
S = A^(L-1) B B C        (truth,   G = L + 2)
D = A^(L-1) B C          (competitor, n = L + 1)
R = (0 repeated x times, then L)     (latent read starts on S).
```

Then:

1. `|S| = G = L + 2`, `|D| = n = L + 1`;
2. `S` and `D` are primitive;
3. `S` and `D` are `P1` (STRONG), hence also `P2` (WEAK) and in the strong class
   `primitive ∧ P1`;
4. `R ∈ I_s` for `S`; for every `L >= 4`, the triple-repeat clause is
   **non-vacuous**;
5. the exact free-length ratio is

   ```text
   L(D | x) / L(S | x) = ( G / n )^(x+1) = ((L+2)/(L+1))^(x+1) > 1,
   ```

   unbounded in `x` for fixed `L`.

For `L = 3` this is exactly the issue's headline witness `AABBC -> AABC` with
ratio `25/16`.

**Proof.**

*Lengths.* Immediate from the definitions.

*Primitivity.* `S` and `D` each contain exactly one `C`. If a circular word
`W` with exactly one `C` were a nontrivial power `u^m`, `m >= 2`, then `C` would
occur `m >= 2` times. So both are primitive. (This is why the family carries a
`C`; it also makes the same argument uniform in `L`.)

*`P1` for `S`.* Index `S` as `A` at `0..L-2`, `B` at `L-1`, `B` at `L`, `C` at
`L+1`. Classify each length-`(L-1)` window by `(#B, has C)`, all of which are
recoverable from the window content:

| `#B` | `C`? | window | start |
|------|------|--------|-------|
| 0 | no | `A^(L-1)` | `0` |
| 1 | no | `A^(L-2) B` | `1` |
| 2 | no | `A^(L-3) B^2` | `2` |
| 2 | yes | `A^p B^2 C A^q`, `p+q = L-4` | `L-1-p` |
| 1 | yes | `B C A^(L-3)` | `L` |
| 0 | yes | `C A^(L-2)` | `L+1` |

All six rows carry distinct `(#B, C)` labels, so windows from different rows
differ; within the fourth row the leading-`A` count `p` is recovered from the
content, so the start `L-1-p` is recovered; within each remaining row the
content determines the start. (For `L = 3` the fourth row is empty,
`A^(L-3) B^2 = B^2`, and the table is the windows `AA, AB, BB, BC, CA` of
`AABBC`.) Hence every `(L-1)`-mer occurs once.

*`P1` for `D`.* `D = A^(L-1) B C` has one `B` and one `C`; its length-`(L-1)`
windows are `A^(L-1)` (start `0`), `A^(L-2) B` (start `1`), `B C A^(L-3)`
(start `L-1`), and `C A^(L-2)` (start `L`), classified by `(#B, C)` and
distinct. Hence `P1`, so by issue #48 comment 1 §3 the word is also `P2` and
primitive.

*`I_s`.* Coverage: the read at `0` covers `0..L-1`; the read at `L` covers
`L, L+1, 0, ..., L-3`; their union is `{0, ..., L+1}`. Repeated windows of `S`
must avoid the unique `C`, so they lie in the `A`-run or end at the `B`-run; the
maximal repeat pairs are the boundary pairs `{0, L-1-ℓ}` of `A^ℓ`
(`ℓ = 1, ..., L-2`) and the `B`-pair `{L-1, L}`. Every `A`-pair contains start
`0`, so two of them cannot alternate; the `B`-pair has consecutive starts and
cannot alternate with any pair. Hence there is **no** interleaved pair, and the
interleaved clause is vacuous.

For the triple-repeat clause, a maximal triple repeat of `S` is an `A^ℓ` with
three copies, which forces `ℓ <= L-3` (there are `L - ℓ` copies in the `A`-run).
A copy at start `t` is bridged by a single read containing `t-1` and `t+ℓ`:

* `1 <= t <= L-1-ℓ`: the read at `0` covers `0..L-1`, containing `t-1 >= 0`
  and `t+ℓ <= L-1`;
* `t = 0`: the read at `L` covers `L, L+1, 0, ..., L-3`, containing
  `t-1 = L+1` and `t+ℓ = ℓ <= L-3`.

So every copy of every maximal triple repeat is bridged. For `L >= 4` the
window `A^1` has at least three copies in the `A`-run; the triple of copies at
starts `0, 1, L-2` is Bresler-maximal (preceding symbols `C, A, A`, following
symbols `A, A, B`), so the triple-repeat clause is non-vacuous. For `L = 3`
there is no triple repeat and `I_s` reduces to coverage.

*Ratio.* The two observed types, from starts `0` and `L`, are

```text
u = A^(L-1) B      (start 0)
v = B C A^(L-2)    (start L).
```

In `S`, `u` occurs once (the only run of `L-1` consecutive `A`s is `0..L-2`) and
`v` occurs once (occupying `L, L+1, 0, ..., L-3`). In `D`, `u` occurs once
(start `0`) and `v` occurs once (start `L-1`). Hence `d_S = d_D = 1` on the
observed support `{u, v}`, and Lemma 1 applies with `N = x+1`:

```text
L(D|x)/L(S|x) = (G/n)^(x+1) = ((L+2)/(L+1))^(x+1).
```

In particular the ratio exceeds `1` for every `x >= 1` and tends to infinity as
`x -> infinity`. ∎

**Corollary 3 (unbounded in the samples).** For each fixed `L >= 3` the
realizations are `I_s`-feasible for every `x`, so there is no uniform-in-`N`
likelihood-ratio bound and no worst-case finite repair by any candidate-intrinsic
predicate that admits this family. (As in the concurrent packets, these
realizations put reads on a proper subset of the start positions and therefore
have probability exponentially small in `N` under i.i.d. uniform sampling; the
population limit concentrates on the proportional spectrum, where the truth is
optimal. The finite negative and a population positive are compatible.)

**Corollary 4 (coherence).** The truth `S` lies in the candidate class
`primitive ∧ P1` (and `P1 => P2`), so the refutation is in the coherent regime
where the assembler's candidate class contains the truth; it is not obtained by
an over-strong predicate that excludes the truth.

---

## 4. Why `P1`/`P2` plus primitivity cannot repair it: length-blindness

**Lemma 1** is the whole explanation, and it is worth stating as a barrier.

**Barrier (candidate-intrinsic predicates are length-blind).** By Lemma 1 the
free-length ratio depends on the ordered pair `(S, D)` only through the observed
multiplicities and the two lengths `G, n`. A candidate-intrinsic predicate is a
function of one candidate word and `L`; it can constrain the multiplicities
(`P1` forces `d_D(w) <= 1` on the support) but it never sees `G`, the truth
length, and so it can never constrain the ratio `G/n`. In the family of
Proposition 2 the observed multiplicities are already equal (`d_S = d_D` on the
support), the competitor is primitive, and both words satisfy `P1` — the
strongest natural repeat predicate — so every candidate-intrinsic repeat
condition in this family reports `"admissible"` and the ratio is still
`(G/n)^(x+1)`. A condition strong enough to reject `D = A^(L-1) B C` while
admitting `S = A^(L-1) B B C` is not a repeat/read-length property at all; it is
using length- or word-specific information.

Concretely:

* The free-length objective factorizes as
  `(length factor (G/n)^N) × (spectrum-fit factor ∏ (d_D/d_S)^x)`.
* `P1`, `P2` and primitivity are properties of the candidate word alone; they
  constrain the spectrum-fit factor's **fibre** (identity and proportional
  scale: `P1` gives `d_D(w) <= 1`; primitivity removes `D = S^m`), and they never
  compare `n` with the truth length `G`, because the assembler is precisely not
  allowed to know `G`.
* The fixed-length positive theorem (`P1` + known length `G`) has no length
  factor and is true; the family's ratio is *exactly* the missing length factor.
  Hence the length axiom was doing the entire work, and replacing it by
  candidate-intrinsic checks cannot work.

This is why the issue's roadmap condition points to issue #45. The residual
obstruction after the intrinsic structural repair is finite sampling plus the
length factor, not structural non-identifiability. A finite repair must add an
**extrinsic** length constraint tied to the data (known length, or a
data-derived feasible length bound such as the §6.2 flow feasible set), or move
to a typicality/population statement; further strengthening the candidate-intrinsic
repeat predicate cannot help.

---

## 5. Relation to the other issue-#48 packets

* The `L = 3` member is the issue's headline witness `AABBC -> AABC` (`25/16`),
  independently reproduced in
  [`issue48-intrinsic-candidate-checks.md`](issue48-intrinsic-candidate-checks.md)
  §4 and by `scripts/issue48_intrinsic_candidate_search.py`.
* `AABC -> ABC` (the `P_weak` vacuous-`I_s` family of that packet, ratio
  `(4/3)^N`) and `ABACABC -> ABAC` (its non-vacuous `P_strong` family, ratio
  `(7/4)^k (7/8)^2`) both also have equal observed multiplicities and ratio
  `(G/n)^N`; the family here unifies the mechanism and supplies, for every
  `L >= 4`, a non-vacuous-`I_s`, `P1`+primitive witness. Unlike
  `ABACABC -> ABAC`, the truth `A^(L-1) B B C` is `STRONG` for **every** `L`, so
  the family lives in the strongest intrinsic class with the truth inside it.
* The isolated non-vacuous `P1` witness `AABACC -> AABAC` (`G=6`, ratio
  `216/125`) of the concurrent packet is the `L = 3` "extra symbol appended"
  sibling of this family; the family here is uniform in `L`.
* The population results (the population-identifiability note on concurrent
  branch `agent/issue48-circqgram-source-0921`, reconciled in issue #48
  comments 2–3) are about **one** normalized `L`-spectrum; the family here is a
  **cross-spectrum** finite-sample ranking, so the positive population statement
  and this finite negative are compatible, exactly as recorded in the concurrent
  packets.

---

## 6. Computational certificate

`scripts/verify_issue48_length_shrinkage_family.py` is self-contained (exact
`fractions.Fraction`) and checks the family for `L = 3..14` and
`x ∈ {1, 2, 3, 5, 8, 13}`:

* `R ∈ I_s` (strict two-sided bridging, coverage, all-bridged triples, no
  interleaved pair);
* `S`, `D` primitive; `S`, `D` `STRONG` and `WEAK`;
* ratio exactly `((L+2)/(L+1))^(x+1)` and `> 1`;
* the number of maximal triple repeats (`C(L-2, 2)`, `0` at `L = 3`) to display
  non-vacuity.

It then cross-checks the same instances against the two existing independent
implementations, `scripts/issue48_intrinsic_candidate_search.py` and
`scripts/verify_issue48_intrinsic_admissibility.py`, agreeing on `I_s`, the
predicates, and the exact ratio. All checks pass.

Run:

```bash
python3 scripts/verify_issue48_length_shrinkage_family.py
```

The `L = 3` member is also kernel-checked (free-length exact multinomial) in
`AssemblyP1/Issue48AabbcCounterexample.lean`, whose bundled theorem
`AssemblyP1.Issue48.issue48_aabbc_aabc_counterexample` proves, by computation
over `ℚ` and `decide`, coverage, no triple repeat, `Strong`/`IsPrimitive` on both
`AABBC` and `AABC`, and `likelihood5 truth5 < likelihood5 competitor4` with
exact values `1/25 < 1/16` (ratio `25/16`). The companion file
`AssemblyP1/Issue48FreeLengthCounterexample.lean` kernel-checks the slightly
smaller `S = AABB`, `D = AAB` witness.

---

## 7. What this does and does not establish

**Established.**
* An explicit two-parameter (`L`, `x`) family of free-length exact-multinomial
  counterexamples in the strongest candidate-intrinsic class
  `primitive ∧ P1` (hence `primitive ∧ P2`), with a truth that satisfies the
  strict source `I_s` non-vacuously for `L >= 4`.
* Exact ratio `(G/n)^N`, unbounded in `N`, with a proof for every `L >= 3` and an
  exact computational certificate over a wide range.
* The mechanism: candidate-intrinsic predicates are length-blind; the entire
  failure is the `(G/n)^N` factor that the fixed-length positive theorem sets to
  `1`.

**Not established / non-claims.**
* No claim under the fixed-`N` binomial approximation (Variant A) or the §6.2
  flow-feasible set (Variant F).
* No claim on the reverse-complement/molecule panel.
* The bounded finite statements are exact; the family itself is proved, not just
  searched.
* This does not settle the published Shomorony et al. question; it settles the
  explicitly additional repaired formulation of issue #48.

---

## 8. Epistemic classification

| Claim | Class | Basis |
|---|---|---|
| Lemma 1: equal observed multiplicities ⇒ ratio `(G/n)^N` | **mathematical proof** | §2 |
| Prop. 2: family primitive / `P1` / `P2` / `I_s` / ratio | **mathematical proof** | §3 |
| Non-vacuous `I_s` for `L >= 4` | **mathematical proof** | §3, §6 |
| Barrier: candidate-intrinsic predicates cannot bound the length factor | **mathematical proof + structural explanation** | §2, §4 |
| Family holds for `L = 3..14`, `x ∈ {1,2,3,5,8,13}` | **exact computation** | §6 |
| Cross-check against two independent implementations | **exact computation** | §6 |
| `L = 3` member (`AABBC -> AABC`, ratio `25/16`) kernel-checked | **Lean** | `AssemblyP1/Issue48AabbcCounterexample.lean` |
| `L = 3` smaller witness (`AABB -> AAB`) kernel-checked free-length | **Lean (existing)** | `AssemblyP1/Issue48FreeLengthCounterexample.lean` |

---

## 9. Sources and repository anchors

| Item | Source / anchor |
|---|---|
| Exact free-length multinomial (Variant E) | Medvedev–Brudno 2009 §6.1; `docs/ml-formalization-contract.md:22-28` |
| Ratio formula `∏ (G d_D / (n d_S))^x` | issue #48 comments; `docs/issue48-intrinsic-candidate-checks.md` §1 |
| `I_s` (coverage, all-bridged triples, bridged interleaved) | Shomorony et al. 2016 Eq. (1); `docs/bridging-source-semantics.md` |
| Strict bridging start interval | Bresler et al. 2013, Fig. 5; `docs/copy-bridging-predicate-correction.md` |
| Repeats / triples / interleaving / maximality | Bresler et al. 2013; `docs/bridging-source-semantics.md` |
| `P1` = STRONG, `P1 => P2`, `P1 => primitive` | issue #48 comment 1 §3; `docs/issue48-intrinsic-admissibility-counterexample.md` |
| Fixed-length `P1` positive theorem | issue #48 comment 3; `docs/issue48-intrinsic-admissibility-counterexample.md` Proposition 2 |
| Headline witness `AABBC -> AABC` (`25/16`) | issue #48 comment 1 §4; `docs/issue48-intrinsic-candidate-checks.md` §4 |
| `AABC -> ABC`, `ABACABC -> ABAC` families | `docs/issue48-intrinsic-candidate-checks.md` §3 |
| Population positive | population note on branch `agent/issue48-circqgram-source-0921`; issue #48 comment 2 |
| Data-regime repair (#45) | issue #48 comment 4 |
| Verification script | `scripts/verify_issue48_length_shrinkage_family.py` |
| Kernel check of the `L = 3` member | `AssemblyP1/Issue48AabbcCounterexample.lean` |
