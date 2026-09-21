# Candidate-intrinsic repeat/read-length admissibility: the structural boundary and the role of primitiveness

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
scopes). Self-contained, exact `fractions.Fraction`, deterministic, exits
non-zero on any failed assertion._

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
   `>= L-1` and no interleaved pair of maximal repeats whose two constituents
   both have length `>= L-1`. These are exactly the two obstructions that make a
   sequence unresolvable at read length `L` (Bresler et al.; Ukkonen–Pevzner
   spectrum classification). [source fact + mathematical proof]

2. **Neither conjunct can be dropped.** A primitive, triple-repeat-free candidate
   can still strictly beat an `I_s`-realizable truth through an interleaved
   repeat (`S = AAAB`, `D = AAABAB`, `L = 3`), and an interleaved-free candidate
   can beat it through a triple repeat (`S = AAATT`, `D = AAAATT`, `L = 3`).
   [verified computation]

3. **Primitiveness does not follow from `STRUCT`, and is not implied by it.**
   `D = (ACGT)^2` is `STRUCT` for `L = 2` and non-primitive. [mathematical proof]

4. **Primitiveness is not needed for the maximizer schema, but is separately
   needed for the uniqueness schema.** If a non-primitive candidate `D = P^m`
   strictly beats the truth, then its primitive root `P` has the same normalized
   length-`L` spectrum and strictly beats the truth too (root reduction). So a
   maximizer theorem over primitive `STRUCT` candidates automatically covers all
   `STRUCT` candidates. But `S^2` is `STRUCT` and ties any primitive `STRUCT`
   truth `S` for every observation, so without a primitiveness restriction (or a
   proportional-spectrum quotient) the truth is never the *unique* maximizer.
   [mathematical proof]

5. **Bounded evidence.** Over exhaustive small scopes the number of strict
   counterexamples to "the `I_s` truth is a maximizer among candidates satisfying
   predicate `P`" is (`--full` in parentheses): `PRIM` 454 (1131), `ILF` 128
   (323), `TRF` 22 (162), `PRIM & TRF` 22 (162), `STRUCT` **0 (0)**,
   `PRIM & STRUCT` **0 (0)**. The variable-length sufficiency of `STRUCT` is
   therefore a well-tested conjecture, not a theorem; the same-length slice is a
   theorem (rigidity), and it needs only `TRF`. [verified computation]

**Bottom line.** The repaired candidate predicate should be `STRUCT` (no long
triple repeat, no long interleaved pair). Primitiveness is an *independent*
conjunct: it is unnecessary for strict beating / maximizer, and necessary only to
rule out the whole-genome proportional-spectrum ties.

---

## 1. Source facts versus the new repaired model

| Item | Status | Basis |
|---|---|---|
| Oriented length-`L` circular read types; no reverse-complement collapse | **source fact** | Shomorony et al. 2016 §2, §4.1 |
| Circular truth of length `G`; reads drawn uniformly from `G` starts | **source fact** | Shomorony et al. 2016 §2 |
| A length-`L` read bridges a repeat copy of length `ell` iff it strictly extends on both sides, so `ell <= L-2` | **source fact** | Bresler et al. 2013 (Fig. 5); Shomorony §3 |
| `I_s` = coverage ∧ all triple repeats all-bridged ∧ all interleaved pairs bridged | **source fact** | Shomorony Eq. (1), inheriting Bresler |
| Repeat/triple-repeat maximality conditions; interleaved pair has alternating starts, "length = shorter repeat" | **source fact** | Bresler et al. 2013, [`../bridging-source-semantics.md`](../bridging-source-semantics.md) |
| `I_s` is realizable on `S` iff `(T)` no triple repeat of length `>= L-1` and `(I)` no interleaved pair with both lengths `>= L-1` | **mathematical proof** (repository) | [`oriented-se62-rigidity-theorem.md`](oriented-se62-rigidity-theorem.md) §1, §3 |
| MB09 §6.1 exact multinomial with candidate-intrinsic `N(D)=|D|`; §6.2 per-vertex lower bound `1` | **source fact** | Medvedev–Brudno 2009 §6.1–6.2 |
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
  constituents both have length `>= L-1`. (Interleaved = the four selected starts
  alternate cyclically, per Bresler.)
- `SW_L(D)`: every length-`(L-1)` window of `D` occurs at most twice.
- `STRUCT_L(D) := TRF_L(D) ∧ ILF_L(D)` — the structural assembly boundary.

`STRUCT` is exactly the intrinsic form of `I_s`-realizability: a circular word
`S` admits some read collection `R in I_s` iff `STRUCT_L(S)` holds, by the
`(T) ∧ (I)` reduction above. This is the sense in which `STRUCT` is *justified by*
the structural assembly boundary rather than invented.

**Strict-beating criterion.** For the exact objective, a candidate `D` beats a
truth `S` on *some* observation whose support is contained in
`supp(spec_L(S))` and which is `I_s`-realizable (so every truth type is observed
at least once, forcing `supp(spec_L(S)) subseteq supp(spec_L(D))`) iff

```text
there is an observed type w in supp(spec_L(S)) with
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
(b) `PRIM` does not imply `TRF`: `D = AAA`, `L = 2` (or `D = AAAATT`, `L = 3`).
(c) `STRUCT` does not imply `PRIM`: same as (a).
(d) `TRF` does not imply `ILF`: `D = AAABAB`, `L = 3`.
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

**Proposition 5 (primitiveness is necessary for uniqueness).** Let `S` be a
primitive `STRUCT` word. Then `S^2` is `STRUCT`, has the same support and the same
normalized spectrum as `S` (so `E(S^2 | x) = E(S | x)` for every `x`), and is not
a cyclic shift of `S`. Hence the truth is not the unique maximizer up to cyclic
shift unless candidates are restricted to primitive words (or genomes are
identified by their primitive root / proportional spectrum). ∎

---

## 4. Small examples and counterexamples

All arithmetic below is exact and checked by
`scripts/verify_intrinsic_admissibility.py`.

| # | role | truth `S` | candidate `D` | `L` | `PRIM(D)` | `TRF(D)` | `ILF(D)` | result |
|---|---|---|---|---|---|---|---|---|
| A | `TRF` insufficient (interleaved needed) | `AAAB` | `AAABAB` | 3 | yes | yes | **no** | `D` strictly beats `S` |
| B | `ILF` insufficient (triple needed) | `AAAB` | `AAAAB` | 3 | yes | **no** | yes | `D` strictly beats `S` |
| C | `PRIM` insufficient | `AAATT` | `AAAATT` | 3 | yes | **no** | yes | `D` strictly beats `S` |
| D | primitiveness needed for uniqueness | `ACGT` | `(ACGT)^2` | 2 | **no** | yes | yes | `D` ties `S` for every `x` |

**Counterexample A (the interleaved obstruction is essential at variable
length).** `S = AAAB` is `I_s`-realizable (`STRUCT` true: the only long maximal
repeat is `AA`, and there is no interleaved pair). `D = AAABAB` is primitive,
`TRF`, and `SW`, but has the interleaved maximal repeats `ABA` (starts `2,4`)
and `BA` (starts `3,5`), so `ILF(D)` is false. With
`x = spec_3(S) + M * e_ABA`,

```text
E(D | x) / E(S | x) = (32/81) * (4/3)^M ,
```

which exceeds `1` from `M = 4` (at `M = 4`: `8192/6561 > 1`). This is a witness
that `TRF` — even together with `PRIM` and `SW` — does not suffice; the
interleaved clause of the structural boundary is doing real work.
[verified computation]

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

## 5. Bounded computational evidence for the repaired conjecture

The repaired finite conjecture under test is:

> **Repaired conjecture (issue #48).** If the truth `S` is `I_s`-realizable
> (`STRUCT_L(S)`), then no `STRUCT_L` candidate `D` with
> `supp(spec_L(D)) ⊇ supp(spec_L(S))` strictly beats `S` under the exact
> candidate-intrinsic multinomial, for any observation `x` with
> `supp(x) subseteq supp(spec_L(S))`.

The script enumerates, exhaustively in scope, all `I_s`-realizable truths (as
necklaces), all candidates of length `<= |S| + extra` (as necklaces), and applies
the strict-beating criterion of §2. Quick scopes: binary `L = 2`, `G <= 9`;
binary `L = 3`, `G <= 8`; ternary `L = 2`, `G <= 7` (`extra` 2–3). `--full`
scopes: binary `L = 2`, `G <= 11`; binary `L = 3`, `G <= 10`; ternary `L = 2`,
`G <= 8`; ternary `L = 3`, `G <= 7` (`extra` 2–3).

| candidate predicate | strict cex (quick) | strict cex (`--full`) |
|---|---|---|
| `PRIM` | 454 | 1131 |
| `ILF` | 128 | 323 |
| `TRF` | 22 | 162 |
| `PRIM & TRF` | 22 | 162 |
| `STRUCT = TRF & ILF` | **0** | **0** |
| `PRIM & STRUCT` | **0** | **0** |

The `TRF`-only hits are all interleaved obstructions (e.g. counterexample A).
Adding `PRIM` changes nothing, consistent with Corollary 4a. `STRUCT` has no hit
in either scope. The per-scope transcript is committed as
[`results/intrinsic_admissibility_full.txt`](../../results/intrinsic_admissibility_full.txt).
The zero is **evidence, not proof**, and the variable-length sufficiency of
`STRUCT` remains **open** in general. [verified computation, bounded]

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
- **Variable-length slice is where the interleaved clause matters.** On the
  different-length slice the same-length circulation argument does not apply, and
  counterexample A shows the interleaved clause is necessary. `STRUCT` removes
  every bounded counterexample found. [verified computation + open]
- **Compatibility with the antecedent.** `STRUCT` is exactly the `(T) ∧ (I)`
  realizability form of `I_s`, so every `I_s`-realizable truth is admitted; and
  by Proposition 4 the primitive root of an admitted truth is admitted too. The
  repaired candidate predicate therefore does not exclude the truth.
  [mathematical proof]
- **What the repair buys / does not buy.** If the repaired conjecture is proved,
  the theorem needs no privileged true-length axiom and no population limit, and
  the truth is a maximizer among intrinsically checkable candidates. It does not
  by itself give uniqueness: for that, primitiveness (or a proportional-spectrum
  quotient) is required by Proposition 5.

---

## 7. Open questions and next tests

1. **Prove or refute the variable-length `STRUCT` conjecture** (the central open
   item of this note). The bounded zero is not a proof; a larger-instance search
   or a structural argument is needed.
2. **Sharpen `ILF`.** The source boundary gives "both constituents `>= L-1`";
   test whether the "both" can be weakened for the maximizer statement without
   readmitting counterexample A.
3. **Support semantics.** The repaired model as tested uses support containment
   (`supp(x) subseteq supp(spec_L(D))`), the §6.2 per-vertex reading. Re-run the
   search under support *equality* (spelled-circuit reading) to see whether
   `TRF` alone suffices there.
4. **Uniqueness semantics.** Decide whether to restrict to primitive candidates
   or to quotient by proportional spectrum; the two give the same maximizer
   statement but different uniqueness statements.

---

## 8. Epistemic classification

| Claim | Status |
|---|---|
| `STRUCT` is the intrinsic `(T) ∧ (I)` form of `I_s`-realizability | mathematical proof (repository reduction) |
| `SW => TRF`; `PRIM` makes `TRF <=> SW` | mathematical proof (Prop. 1, 2) |
| `PRIM`, `TRF`, `ILF` are pairwise independent in the relevant directions | mathematical proof + verified computation (Prop. 3) |
| Root reduction: non-primitive candidates reduce to their primitive root | mathematical proof (Prop. 4) |
| Primitiveness is redundant for maximizer, necessary for uniqueness | mathematical proof (Cor. 4a, Prop. 5) |
| Counterexamples A, B, C, D with exact ratios | verified computation |
| `TRF` alone admits strict counterexamples; `STRUCT` has none in quick scopes | verified computation, bounded |
| Variable-length `STRUCT` sufficiency in general | **open** |

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
