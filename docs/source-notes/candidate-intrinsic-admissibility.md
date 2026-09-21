# Candidate-intrinsic repeat/read-length admissibility: the structural boundary, the support semantics, and the role of primitiveness

_Status: new **repaired model** analysis for issue #48, 2026-09-21, on top of
`origin/main` at `f60ca5f`. This note does **not** reinterpret the literature and
does **not** settle the published open problem. It separates source facts from
the repaired model, fixes exact candidate-intrinsic predicates, proves their
relations, exhibits small examples and counterexamples, and records bounded
computational evidence. Every claim is labelled **source fact**,
**mathematical proof**, **verified computation (bounded)**, or **open**. It does
not select which Medvedev–Brudno (2009) likelihood layer the Shomorony et al.
(2016) sentence intends, and it does not touch tie/equivalence semantics beyond
what the repaired question forces._

_Reproduce: `python3 scripts/verify_intrinsic_admissibility.py` (quick) and
`python3 scripts/verify_intrinsic_admissibility.py --full` (wider exhaustive
scopes). Self-contained, exact `fractions.Fraction`, deterministic; exits
non-zero only if the documented findings fail to reproduce._

---

## 0. Direct answer

Work under the strict oriented single-strand convention of
[`oriented-se62-rigidity-theorem.md`](oriented-se62-rigidity-theorem.md) (the
read types are the oriented length-`L` circular windows, no reverse-complement
collapse). The structural assembly boundary of Shomorony/Bresler says a length-`L`
read can bridge a repeat copy only if the repeat has length `ell <= L-2`
([`../bridging-source-semantics.md`](../bridging-source-semantics.md)). Applied
to the candidate itself, that boundary yields the following.

1. **The weakest candidate-intrinsic repeat predicate justified by the boundary
   is `STRUCT_L`:** the candidate has no Bresler triple repeat of length
   `>= L-1` and no interleaved pair of *maximal* repeats whose two constituents
   both have length `>= L-1`. These are exactly the two obstructions that make a
   sequence unresolvable at read length `L` (Bresler et al.; Ukkonen–Pevzner
   spectrum classification). [source fact + mathematical proof]

2. **Neither conjunct can be dropped *as a resolvability condition*.** A
   primitive, triple-repeat-free candidate can be unresolvable through an
   interleaved pair (`D = AABABB`, `L = 3`), and an interleaved-free candidate
   through a triple repeat (`D = AAAATT`, `L = 3`). [verified computation]

3. **Primitiveness does not follow from `STRUCT`.** `D = (ACGT)^2` is `STRUCT`
   for `L = 2` and non-primitive. [mathematical proof]

4. **Primitiveness is not needed for the maximizer schema, but is separately
   needed for the uniqueness schema.** If a non-primitive candidate `D = P^m`
   strictly beats the truth, its primitive root `P` has the same normalized
   length-`L` spectrum and strictly beats the truth too (root reduction). So a
   maximizer theorem over primitive `STRUCT` candidates automatically covers all
   `STRUCT` candidates. But for the primitive `STRUCT` truth `S = ACGT`
   (`L = 2`), the word `S^2` is `STRUCT` and ties `S` for every observation while
   being a distinct circular genome, so without a primitiveness restriction (or a
   proportional-spectrum quotient) the truth is not the *unique* maximizer.
   [mathematical proof + verified computation]

5. **The structural repeat condition alone does *not* settle the finite ML
   question; the support semantics does.** Under the per-vertex/§6.2
   lower-bound reading (`supp(spec_L(D)) superseteq supp(spec_L(S))`), even
   `PRIM & STRUCT` admits strict counterexamples: `S = AAAB`, `D = AAABAB`
   (`L = 3`) is primitive and `STRUCT`, contains every observed type, and
   strictly beats the truth on a skewed observation. The extra (unobserved)
   type `BAB` lets `D` inflate its normalized frequency of the observed type
   `ABA`. This failure is *not* structural non-identifiability of `D` (it is
   resolvable) but extra-support frequency amplification. [verified computation]
   Under the spelled-circuit reading (`supp(spec_L(D)) = supp(spec_L(S))`, the
   §6.2 candidate), the weaker triple-repeat clause `TRF` alone has **no**
   counterexample in the searched scopes. [verified computation, bounded]

**Bottom line.** The structural boundary gives `STRUCT` as the weakest
candidate-intrinsic *resolvability* predicate, and primitiveness is an
independent conjunct needed only for uniqueness. But `STRUCT` is not sufficient
for the finite maximizer statement unless the candidate universe also fixes the
support (spelled-circuit/§6.2 equality). With support equality the triple-repeat
clause `TRF` is the effective predicate (bounded evidence); with mere containment
no repeat predicate suffices, and the repair must add a support constraint or
move to the population regime (issue #45).

---

## 1. Source facts versus the new repaired model

| Item | Status | Basis |
|---|---|---|
| Oriented length-`L` circular read types; no reverse-complement collapse | **source fact** | Shomorony et al. 2016 §2, §4.1 |
| Circular truth of length `G`; reads drawn uniformly from `G` starts | **source fact** | Shomorony et al. 2016 §2 |
| A length-`L` read bridges a repeat copy of length `ell` iff it strictly extends on both sides, so `ell <= L-2` | **source fact** | Bresler et al. 2013 (Fig. 5); Shomorony §3 |
| `I_s` = coverage ∧ all triple repeats all-bridged ∧ all interleaved pairs bridged | **source fact** | Shomorony Eq. (1), inheriting Bresler |
| Repeat/triple-repeat maximality conditions; interleaved pair has alternating starts, "length = shorter repeat" | **source fact** | Bresler et al. 2013, [`../bridging-source-semantics.md`](../bridging-source-semantics.md) |
| `I_s` is realizable on `S` iff `(T)` no triple repeat of length `>= L-1` and `(I)` no interleaved maximal-repeat pair with both lengths `>= L-1` | **mathematical proof** (repository) | [`oriented-se62-rigidity-theorem.md`](oriented-se62-rigidity-theorem.md) §1, §3 |
| MB09 §6.1 exact multinomial with candidate-intrinsic `N(D)=|D|`; §6.2 per-vertex lower bound `1` on observed reads | **source fact** | Medvedev–Brudno 2009 §6.1–6.2 |
| Spectrum uniqueness ⟺ absence of the triple/interleaved obstructions | **source fact** | Ukkonen 1992; Pevzner 1995; Çelikkanat et al. 2024 Thm 3.1 |
| Candidate class defined by *intrinsic* checks; no true-length axiom | **new repaired model (issue #48)** | not a source statement |
| Restricting to primitive candidates (or quotienting proportional spectra) | **new repaired model (issue #48)** | not a source statement |

The repaired model is a *new formulation*. It is not a rereading of `I_s` and
must not be retrofitted into historical statements.

---

## 2. Exact definitions

Fix an alphabet `Sigma`, a read length `L >= 2`, and a circular word
`D = D_0 ... D_{n-1}` of length `n = |D| >= L`, indices mod `n`.

- `spec_L(D)(w) = #{ i : D_i ... D_{i+L-1} = w }`; `supp(spec_L(D))` is the set of
  present length-`L` windows.
- An observation is a count vector `x` with `x_w >= 0`, `sum_w x_w = N`. The
  exact MB09 §6.1 objective is
  `E(D | x) = prod_w (spec_L(D)(w) / |D|)^{x_w}` (the observation-only
  multinomial coefficient is constant).

**Candidate-intrinsic predicates.**

- `PRIM(D)`: `D` is primitive, i.e. its minimal period is `|D|`; equivalently `D`
  is not a nontrivial whole-number repetition of a shorter circular word.
- `TRF_L(D)`: `D` has no Bresler triple repeat of length `>= L-1`. (A triple
  repeat is three selected copies of a length-`ell` window whose preceding
  symbols are not all equal and whose following symbols are not all equal.)
- `ILF_L(D)`: `D` has no interleaved pair of maximal repeats whose two
  constituents both have length `>= L-1`. A maximal repeat is a pair of equal
  length-`ell` windows maximal on **both** sides (preceding symbols differ and
  following symbols differ); interleaved means the four selected starts
  alternate cyclically, per Bresler.
- `SW_L(D)`: every length-`(L-1)` window of `D` occurs at most twice.
- `STRUCT_L(D) := TRF_L(D) ∧ ILF_L(D)` — the structural assembly boundary.

`STRUCT` is exactly the intrinsic form of `I_s`-realizability: a circular word
`S` admits some read collection `R in I_s` iff `STRUCT_L(S)` holds, by the
`(T) ∧ (I)` reduction above. This is the sense in which `STRUCT` is *justified by*
the structural assembly boundary rather than invented.

**Support semantics.** Two candidate-universe readings are kept explicit.

- *Containment* (per-vertex/§6.2 lower bound): `supp(spec_L(S)) subseteq
  supp(spec_L(D))`, i.e. every observed read occurs in `D`; `D` may have extra
  windows.
- *Equality* (spelled circuit): `supp(spec_L(D)) = supp(spec_L(S))`.

**Strict-beating criterion.** For the exact objective, a candidate `D` beats a
truth `S` on some observation `x` with `supp(x) = supp(spec_L(S))` (the
coverage-consistent case forced by `I_s`) iff there is an observed type `w` with

```text
spec_L(D)(w) / |D|  >  spec_L(S)(w) / |S| .
```

*Why.* Concentrating additional reads on such a `w` makes the ratio
`E(D|x)/E(S|x)` grow without bound; if no such `w` exists the ratio never exceeds
`1`. [mathematical proof]

---

## 3. Predicate relations

**Proposition 1 (`SW => TRF`).** For every `D`, `SW_L(D)` implies `TRF_L(D)`.
*Proof.* A triple repeat of length `ell >= L-1` has three equal length-`(L-1)`
prefixes, so that `(L-1)`-window occurs at least three times. ∎

**Proposition 2 (`PRIM`: `TRF <=> SW`).** For primitive `D`, `TRF_L(D)` iff
`SW_L(D)`. *Proof.* `SW => TRF` is Proposition 1. Conversely, if a primitive `D`
has a length-`(L-1)` window occurring at least three times, then `D` has a
Bresler triple repeat of length `>= L-1` (repository Lemma B, proved from the
maximal-extension argument). ∎

**Proposition 3 (independence).**
(a) `TRF` does not imply `PRIM`: `D = (ACGT)^2`, `L = 2`.
(b) `PRIM` does not imply `TRF`: `D = AAAATT`, `L = 3`.
(c) `STRUCT` does not imply `PRIM`: same as (a).
(d) `TRF` does not imply `ILF`: `D = AABABB`, `L = 3` (for `L = 2` the
implication does hold in the searched scopes).
(e) `ILF` does not imply `TRF`: `D = AAAAB`, `L = 3`.
All five are verified by direct computation in the script. ∎

**Proposition 4 (root reduction).** Let `D = P^m` with `P` primitive and
`m >= 2`. Then

1. `spec_L(D)(w) = m * spec_L(P)(w)` for every `w`, so `D` and `P` have the same
   normalized length-`L` spectrum and `E(D | x) = E(P | x)` for every `x`;
2. `supp(spec_L(D)) = supp(spec_L(P))`;
3. `STRUCT_L(D)` implies `STRUCT_L(P)`.

*Proof.* (1)–(2): each position of `D` reduces to a position of `P` mod `|P|`, and
each `P`-window is hit exactly `m` times. (3): a Bresler triple or interleaved
pair in `P` lifts to `D` at the same start positions; since `D` is `|P|`-periodic
and `|P|` divides `|D|`, the circular flanking symbols agree, so maximality and
alternation are preserved. ∎

**Corollary 4a (primitiveness is redundant for the maximizer schema).** If some
`STRUCT` candidate `D` strictly beats `S`, then some primitive `STRUCT` candidate
(`D`'s root) strictly beats `S`. Hence a theorem "no primitive `STRUCT` candidate
strictly beats an `I_s` truth" extends verbatim to all `STRUCT` candidates.
[mathematical proof]

**Proposition 5 (primitiveness is necessary for uniqueness).** `STRUCT` is not
closed under whole-number repetition: `S = AAAB` (`L = 3`) is `STRUCT` while
`S^2` is not. Nevertheless there are primitive `STRUCT` truths whose repetitions
are again `STRUCT`. For `S = ACGT` (`L = 2`), `S^2 = ACGTACGT` is `STRUCT`, has
the same support and the same normalized spectrum as `S` (so
`E(S^2 | x) = E(S | x)` for every `x`), and is not a cyclic shift of `S`. Hence
for this `I_s`-realizable truth the truth is not the unique maximizer up to
cyclic shift unless candidates are restricted to primitive words (or genomes are
identified by their primitive root / proportional spectrum). ∎

---

## 4. Small examples and counterexamples

All arithmetic below is exact and checked by
`scripts/verify_intrinsic_admissibility.py`.

| # | role | truth `S` | candidate `D` | `L` | `PRIM(D)` | `TRF(D)` | `ILF(D)` | `supp(D)` | result |
|---|---|---|---|---|---|---|---|---|---|
| A | `STRUCT` insufficient under containment | `AAAB` | `AAABAB` | 3 | yes | yes | yes | `⊋ supp(S)` | `D` strictly beats `S` |
| B | `ILF` alone insufficient | `AAAB` | `AAAAB` | 3 | yes | **no** | yes | `= supp(S)` | `D` strictly beats `S` |
| C | `PRIM` alone insufficient | `AAATT` | `AAAATT` | 3 | yes | **no** | yes | `= supp(S)` | `D` strictly beats `S` |
| D | primitiveness needed for uniqueness | `ACGT` | `(ACGT)^2` | 2 | **no** | yes | yes | `= supp(S)` | `D` ties `S` for every `x` |

**Counterexample A (the structural predicate does not close extra-support
amplification).** `S = AAAB` is `I_s`-realizable (`STRUCT` true: its only long
maximal repeat is `AA`, with no interleaved partner). `D = AAABAB` is primitive,
`TRF`, and `ILF` (its maximal repeats are `AA` at starts `0,1` and `ABA` at
starts `2,4`, which do not interleave), so `D` is `STRUCT`. `D` contains every
observed type and one extra type `BAB`. With `x = spec_3(S) + M * e_ABA`,

```text
E(D | x) / E(S | x) = (32/81) * (4/3)^M ,
```

which exceeds `1` from `M = 4` (at `M = 4`: `8192/6561 > 1`). This refutes
`PRIM & STRUCT` under support containment. The mechanism is the extra window
`BAB`, which contributes no likelihood weight (`x_BAB = 0`) but lets `D` raise
`spec_3(D)(ABA)/|D|` above `spec_3(S)(ABA)/|S|`. [verified computation]

**Example A' (support equality removes counterexample A).** `AAABAB` is not a
spelled candidate for the observation `spec_3(AAAB)`, because `BAB` is
unobserved. In the `--full` support-equality search, `TRF` alone has **zero**
strict counterexamples; the triple-repeat clause is the effective predicate
there. [verified computation, bounded]

**Counterexample B (`ILF` alone is not enough).** `D = AAAAB` is primitive and
`ILF`, but the length-`(L-1) = 2` window `AA` occurs three times, so `TRF` fails.
With `x = spec_3(AAAB) + M * e_AAA`, the ratio is `(512/625) * (8/5)^M > 1` at
`M = 1`. [verified computation]

**Counterexample C (`PRIM` alone is not enough).** `D = AAAATT` is primitive but
`TRF` fails; this is the strict oriented variable-length witness already recorded
in [`oriented-se62-rigidity-theorem.md`](oriented-se62-rigidity-theorem.md) §5.2.
At `M = 1` the exact ratio is `15625/11664 > 1`. [verified computation]

**Example D (whole-genome proportional-spectrum tie).** `S = ACGT` is primitive
and `STRUCT`; `D = (ACGT)^2` is `STRUCT`, has support
`{AC, CG, GT, TA}` and normalized spectrum `(1/4, 1/4, 1/4, 1/4)`, identical to
`S`'s. Hence `E(D | x) = E(S | x)` for every observation, and `D` is a distinct
circular genome. This is the pure scale ambiguity that primitiveness removes.
[verified computation + Proposition 4]

---

## 5. Bounded computational evidence

The repaired finite conjecture under test is:

> **Repaired conjecture (issue #48).** If the truth `S` is `I_s`-realizable
> (`STRUCT_L(S)`), then no candidate `D` satisfying the chosen intrinsic
> predicate and the chosen support constraint strictly beats `S` under the exact
> candidate-intrinsic multinomial, for any observation `x` with
> `supp(x) = supp(spec_L(S))`.

The script enumerates, exhaustively in scope, all `I_s`-realizable truths (as
necklaces), all candidates of length `<= |S| + extra` (as necklaces), and applies
the strict-beating criterion of §2. Quick scopes: binary `L = 2`, `G <= 9`;
binary `L = 3`, `G <= 8`; ternary `L = 2`, `G <= 7` (`extra` 2–3). `--full`
scopes: binary `L = 2`, `G <= 11`; binary `L = 3`, `G <= 10`; ternary `L = 2`,
`G <= 8`; ternary `L = 3`, `G <= 7` (`extra` 2–3).

| candidate predicate | contain (quick) | contain (`--full`) | equal (quick) | equal (`--full`) |
|---|---|---|---|---|
| `PRIM` | 964 | 1887 | 236 | 617 |
| `ILF` | 354 | 1057 | 194 | 575 |
| `TRF` | 30 | 206 | **0** | **0** |
| `PRIM & TRF` | 30 | 206 | **0** | **0** |
| `STRUCT = TRF & ILF` | 22 | 186 | **0** | **0** |
| `PRIM & STRUCT` | 22 | 186 | **0** | **0** |

Two robust findings:

- **Containment fails even for `STRUCT`.** The first hit is counterexample A
  (`S = AAAB`, `D = AAABAB`); `ILF` removes only a few of the `TRF` hits, not the
  extra-support mechanism.
- **Equality succeeds with `TRF`.** Under the §6.2 spelled-circuit support
  equality, the triple-repeat clause alone has no counterexample in either scope;
  `ILF` adds nothing there.

The per-scope transcript is committed as
[`results/intrinsic_admissibility_full.txt`](../../results/intrinsic_admissibility_full.txt).
The zeros are **evidence, not proof**; the variable-length `TRF` sufficiency
under support equality remains **open** in general. [verified computation,
bounded]

A separate exhaustive check confirms the root-reduction identities of
Proposition 4 over `G <= 10`, `L = 3`: 115 non-primitive words, zero normalized
spectrum mismatches, zero failures of `TRF(D) => TRF(root(D))`. [verified
computation, bounded]

---

## 6. Relation to the rigidity theorem and to the issue #48 questions

- **Same-length slice is a theorem and needs only `TRF`.** The rigidity theorem
  proves that an `I_s`-realizable truth's length-`L` spectrum is the unique
  positive circulation of total `G` on its window-support graph, so every
  same-length spelled candidate ties. The interleaved clause is *not* used there.
  [mathematical proof]
- **Variable length with support equality.** The same-length circulation argument
  does not apply, but the bounded search finds that `TRF` already removes every
  strict counterexample. This is the natural positive repaired model: intrinsic
  `TRF` (no long triple repeat) plus the §6.2 spelled-candidate support.
  [verified computation, bounded + open]
- **Variable length with support containment.** Even `STRUCT` fails, via
  counterexample A. The failure is extra-support frequency amplification, not
  structural non-identifiability of the candidate. Per the issue #48 decision
  tree this is a **support/candidate-universe** failure, not a finite-multiplicity
  failure of the truth's own identifiability: the repair should first add the
  support (spellability) constraint before changing the data regime, and only
  then consider issue #45. [verified computation]
- **Compatibility with the antecedent.** `STRUCT` is exactly the `(T) ∧ (I)`
  realizability form of `I_s`, so every `I_s`-realizable truth is admitted; and
  by Proposition 4 the primitive root of an admitted truth is admitted too. The
  repaired candidate predicate therefore does not exclude the truth.
  [mathematical proof]
- **What the repair buys / does not buy.** Under support equality the repair
  needs no privileged true-length axiom and no population limit, and (boundedly)
  the truth is a maximizer among intrinsically checkable `TRF` candidates. It
  does not by itself give uniqueness: for that, primitiveness (or a
  proportional-spectrum quotient) is required by Proposition 5.

---

## 7. Open questions and next tests

1. **Prove or refute variable-length `TRF` sufficiency under support equality**
   (the central open item). The bounded zero is not a proof.
2. **Make the support-equality repair explicit.** Spellability is not a
   repeat-intrinsic condition, so the repaired model must state it separately;
   test whether any purely intrinsic strengthening of `STRUCT` can replace it.
3. **Quantify the extra-support mechanism.** Characterize when adding an
   unobserved window lets a `STRUCT` candidate raise an observed type's
   normalized frequency.
4. **Uniqueness semantics.** Decide whether to restrict to primitive candidates
   or to quotient by proportional spectrum; the two give the same maximizer
   statement but different uniqueness statements.
5. **Finite-multiplicity frontier (issue #45).** If `TRF` plus support equality
   is proved, test whether the maximizer statement survives without the
   `I_s`-coverage support restriction.

---

## 8. Epistemic classification

| Claim | Status |
|---|---|
| `STRUCT` is the intrinsic `(T) ∧ (I)` form of `I_s`-realizability | mathematical proof (repository reduction) |
| `SW => TRF`; `PRIM` makes `TRF <=> SW` | mathematical proof (Prop. 1, 2) |
| `PRIM`, `TRF`, `ILF` are pairwise independent in the relevant directions | mathematical proof + verified computation (Prop. 3) |
| Root reduction: non-primitive candidates reduce to their primitive root | mathematical proof (Prop. 4) |
| Primitiveness is redundant for maximizer, necessary for uniqueness | mathematical proof (Cor. 4a, Prop. 5) |
| Counterexample A: `PRIM & STRUCT` fails under support containment | verified computation |
| Counterexamples B, C, D with exact ratios | verified computation |
| Under support equality, `TRF` alone has no strict counterexample in scope | verified computation, bounded |
| Under containment, no tested repeat predicate suffices | verified computation, bounded |
| Variable-length `TRF` sufficiency under support equality in general | **open** |

---

## 9. Sources and cross-references

Primary. Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
*Bioinformatics* 32(17) (2016) i494–i502, §2, §3, §4.1, Eq. (1), DOI
`10.1093/bioinformatics/btw450`. Guy Bresler, Ma'ayan Bresler, David Tse,
*Optimal assembly for high throughput shotgun sequencing*, *BMC Bioinformatics*
14(Suppl 5):S18 (2013), DOI `10.1186/1471-2105-14-S5-S18`. Paul Medvedev,
Michael Brudno, *Maximum Likelihood Genome Assembly*, *J. Comput. Biol.* 16(8)
(2009) 1101–1116, §6.1–6.2, PMC3154397. E. Ukkonen, *Approximate string-matching
with q-grams and maximal matches*, *Theoret. Comput. Sci.* 92(1) (1992) 191–211.
P. A. Pevzner, *DNA physical mapping and alternating Eulerian cycles in colored
graphs*, *Algorithmica* 13(1–2) (1995) 77–105. A. Çelikkanat, A. R. Masegosa,
T. D. Nielsen, *Revisiting K-mer Profile for Effective and Scalable Genome
Representation Learning*, NeurIPS 2024, arXiv:2411.02125, Theorem 3.1.

Repository. [`oriented-se62-rigidity-theorem.md`](oriented-se62-rigidity-theorem.md)
(the same-length rigidity theorem and the `(T) ∧ (I)` reduction);
[`../bridging-source-semantics.md`](../bridging-source-semantics.md) (Bresler
maximality, bridging threshold, `I_s`); [`../open-problem.md`](../open-problem.md)
(the published sentence); [`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md)
(negative transfer across candidate classes); issue #48 (this repaired model),
#45 (the later data-regime repair), #46 (master synthesis).
