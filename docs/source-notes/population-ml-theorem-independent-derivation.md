# The population/infinite-read ML theorem: an independent derivation

_Status: independent mathematical derivation + exact-arithmetic verification for
issue #45, 2026-09-21. It re-derives the population (i.i.d. infinite-read)
maximum-likelihood statement from scratch, states the exact candidate
assumptions, proves the KL identity and its equality condition, isolates exactly
what uniqueness reduces to, and checks the edge cases (zero support, variable
candidate length, oriented vs molecule read types, genome equivalence). It is a
repaired/additive population model; it is **not** a reinterpretation of
Shomorony et al. (2016) or Medvedev–Brudno (2009), and it does **not** settle the
2016 finite-data open question._

_Reproduce: `python3 scripts/verify_population_ml_theorem_independent.py` (about
7 s) and `python3 scripts/verify_population_ml_theorem_independent.py --full`
(about 100 s). Self-contained, exact integer / `fractions.Fraction` arithmetic,
deterministic, exits non-zero on any failed assertion._

_Independence. This note was derived without using the concurrently produced
branch result `docs/population-identifiability-intrinsic-genomes.md` on
`agent/issue48-population-independent-0921`; §9 reconciles the two. The proof of
the cross-length step here is sharper than the one sketched in the issue-#45
comment of 2026-09-21 06:59 (that sketch silently needs a one-sided
identifiability statement; §4 removes the need for it). The interleaving
convention check in §7 is new._

---

## 0. Answer at a glance

Fix an alphabet `Σ`, a read length `L ≥ 2`, and a circular true word `S` of
length `G ≥ L`. Let `p_S(w) = d_S(w)/G` be the normalized population `L`-mer
spectrum and, for a circular candidate `D`, `p_D(w) = d_D(w)/|D|`. Define the
per-read population log-likelihood

```text
ell_S(D) = Σ_w p_S(w) log p_D(w)      (-∞ if p_D misses a truth-positive type).
```

Then:

1. **KL/Gibbs maximizer (no structural hypothesis).** `ell_S(D) ≤ ell_S(S)` for
   *every* candidate `D`, of any length and support, under either strand
   convention. Equality holds **iff `p_D = p_S`**, i.e. iff the normalized
   `L`-mer spectra are equal. So the whole statistical content of the population
   repair is: *truth is automatically an ML maximizer; the interesting question
   is only injectivity of `D ↦ p_D` on the chosen candidate class.* [mathematical
   proof, §3]
2. **Cross-length exclusion (uses only `TRF` + primitivity).** If `S` and `D` are
   both **primitive** and **`TRF`** (no `(L−1)`-mer occurs three times), then
   `p_D = p_S` forces `|D| = G` and `d_D = d_S`. No interleaving hypothesis is
   needed for this step. [mathematical proof, §4]
3. **Equal-length uniqueness (`WEAK` = `TRF ∧ ILF`).** If `S` is `WEAK`-admissible
   and `d_D = d_S`, then `D` is a cyclic shift of `S`. This is the `K = L−1`
   instance of Bresler–Bresler–Tse (2013), Theorem 3, with the circular
   Eulerian-cycle reading. [source theorem, §5]
4. **Population theorem (oriented panel).** If `S` is primitive and
   `WEAK`-admissible, then over the class of primitive `TRF` circular words the
   maximizers of `ell_S` are exactly the cyclic shifts of `S`. If the candidate
   class is restricted to length `G`, primitivity/`TRF` on the rival are not
   needed: the maximizers are exactly the cyclic shifts of `S`. [mathematical
   proof + source theorem, §6]
5. **The hypotheses are each necessary, and the molecule panel is a genuine
   boundary.** Drop primitivity, drop candidate-side `TRF`, or switch to
   reverse-complement (molecule) read types and the uniqueness half fails; §7
   gives exact witnesses.

---

## 1. Setup and conventions

**Read types (oriented panel).** For a circular word `D` of length `n`, the
oriented read types are the `n` cyclic length-`L` windows
`W_i = D_i D_{i+1} … D_{i+L−1}` (indices mod `n`). The **`L`-mer spectrum** is
`d_D(w) = #{ i : W_i = w }`, with `Σ_w d_D(w) = n`. The **population read law**
is `p_D(w) = d_D(w)/n`. This is the `n → ∞` i.i.d.-uniform-start law and is what
the empirical read histogram converges to. [modeling choice, matching Shomorony
et al. 2016 §2: circular truth, uniform start, oriented windows]

**Molecule panel (boundary convention).** Read types are reverse-complement
classes; `d_D` counts classes, and `p_D` is the class law. The genome equivalence
then becomes dihedral. [source fact; see
[`equivalence-and-tie-wellposedness.md`](equivalence-and-tie-wellposedness.md)
Fact 4 and §7 below]

**Candidate class.** A class `C` of nonempty circular words over `Σ` containing
`S`. The population objective `ell_S` depends on `D` only through `p_D`, hence
only through `(|D|, d_D)`. [mathematical fact]

**Intrinsic predicates** (candidate-intrinsic shadows of Shomorony's `I_s`;
[Bresler–Bresler–Tse 2013] conventions, as recorded in
[`bridging-source-semantics.md`](../bridging-source-semantics.md)):

- `TRF(D,L)`: no Bresler triple repeat of `D` has length `≥ L−1`. For
  **primitive** `D` this is equivalent to "every `(L−1)`-mer of `D` occurs at
  most twice" (Lemma 2.1; the equivalence can fail for periodic words, e.g.
  `AAA` at `L = 2`, where all flanks are equal so the maximal triple is
  vacuous).
- `ILF(D,L)`: no interleaved pair of maximal repeats of `D` has both
  constituents of length `≥ L−1`, where a pair of maximal repeats `(t₁,t₃)` and
  `(t₂,t₄)` is interleaved when `t₁ < t₂ < t₃ < t₄` or `t₂ < t₁ < t₄ < t₃`.
  The two repeats may be **different** words. [source fact: Bresler–Bresler–Tse
  2013, "Ukkonen's condition" paragraph]
- `WEAK(D,L) = TRF(D,L) ∧ ILF(D,L)` (also written `P2`).
- `primitive(D)`: `D` is not `U^k` for a shorter circular `U` and `k ≥ 2`.

**Equivalence.** Oriented panel: cyclic shift. Molecule panel: cyclic shift plus
reverse complement (dihedral). The panel and the equivalence are one coupled
choice, not two. [mathematical fact; `equivalence-and-tie-wellposedness.md`]

---

## 2. Two elementary counting facts

**Fact 2.1.** For a circular word `D`, let `mult_D(v)` be the number of
occurrences of the `(L−1)`-mer `v`. Then

```text
mult_D(v) = Σ_{w : prefix_{L−1}(w) = v} d_D(w).
```

_Proof._ Both sides count the start positions whose length-`(L−1)` window is
`v`, since each such start determines a unique length-`L` window with prefix
`v`. ∎ [mathematical proof]

**Lemma 2.2 (`TRF` ⟺ multiplicity ≤ 2, for primitive words).** If `D` is
primitive then `TRF(D,L)` holds iff `mult_D(v) ≤ 2` for every `(L−1)`-mer `v`.

_Proof._ (⟹) Three equal `(L−1)`-windows extend maximally to the right to a
common length `ℓ`; extend maximally to the left to a total length `ℓ₀ ≥ L−1`.
Maximality makes the three following symbols not all equal and the three
preceding symbols not all equal, which is exactly a Bresler triple repeat of
length `ℓ₀ ≥ L−1`, contradicting `TRF`. The extension cannot reach the full
length `n`: three equal length-`n` windows at distinct starts would give `D` a
nontrivial period, contradicting primitivity. (⟸) A triple repeat of length
`≥ L−1` contains three equal `(L−1)`-prefixes, so some multiplicity is `≥ 3`.
∎ [mathematical proof; independently verified exhaustively for primitive words
in §8 B]

---

## 3. The KL identity and the equality condition

**Lemma 3.1 (KL / Gibbs).** For every circular candidate `D` (any length, any
support, oriented or molecule panel),

```text
ell_S(D) ≤ ell_S(S),    with equality iff p_D = p_S.
```

_Proof._ Both `p_S` and `p_D` are probability vectors supported on finitely many
read types. If some truth-positive `w` has `p_D(w) = 0`, then `ell_S(D) = −∞ <
ell_S(S)` (which is finite, `= −H(p_S)`). Otherwise

```text
ell_S(S) − ell_S(D) = Σ_w p_S(w) log(p_S(w)/p_D(w)) = KL(p_S ‖ p_D) ≥ 0
```

by Gibbs' inequality, with equality iff `p_S = p_D`. ∎ [mathematical proof]

**Corollary 3.2 (population objective).** Per read, the exact Medvedev–Brudno
§6.1 multinomial satisfies, as `n → ∞` with the empirical law `→ p_S`,

```text
(1/n) log L_exact(D | x)  →  ell_S(D)
```

(the candidate-independent multinomial coefficient drops), so any objective
whose per-read limit is `ell_S` has the same population maximizers as `ell_S`.
In particular the **exact multinomial** objective is covered. This note makes no
independent claim about the fixed-`N` §6.1 binomial approximation beyond
noting that its per-read limit is a different functional. [mathematical proof
for the exact objective]

**Corollary 3.3 (tie set).** For any class `C ∋ S`, the set of population
maximizers of `ell_S` over `C` is exactly

```text
{ D ∈ C : p_D = p_S }
 = { D ∈ C : d_D(w)/|D| = d_S(w)/G for every w }
 = { D ∈ C : d_D = c · d_S for c = |D|/G }.
```

So the population repair reduces **entirely** to a fibre-injectivity
(identifiability) question for the normalized-spectrum map `D ↦ p_D` on `C`.
No bridging hypothesis appears in this reduction. [mathematical proof]

---

## 4. Cross-length exclusion (Lemma 2 of the issue comment, repaired)

The issue-#45 comment of 2026-09-21 06:59 writes `|D|/|S| = a/b` in lowest
terms, divides `d_S` by `b`, spells the quotient by a word `T`, and then applies
the two-sided spectrum-identifiability theorem to `S` and `T^b`. That last step
silently needs the *one-sided* statement "any word with the same spectrum as the
admissible `S` is a rotation of `S`", because `T^b` need not itself be
admissible. The following argument removes that gap and needs no source theorem
at all.

**Lemma 4.1 (cross-length exclusion).** Let `S` and `D` be primitive circular
words, both `TRF` at read length `L`, with `p_D = p_S`. Then `|D| = |S|` and
`d_D = d_S`.

_Proof._ Write `p_D = p_S` as `d_D = c · d_S` for the rational `c = |D|/|S| > 0`.
Let `A_v = mult_S(v)`, `B_v = mult_D(v)` for `(L−1)`-mers `v`. By Fact 2.1,
`B_v = c · A_v`. By Lemma 2.2 (`TRF` + primitive), `A_v ≤ 2` and `B_v ≤ 2`.

First suppose `c > 1`. For every `v` in the common support, `A_v ≥ 1`, so
`1 ≤ A_v = B_v/c ≤ 2/c < 2`, hence `A_v = 1` and `B_v = c`. Since `B_v` is a
positive integer `≤ 2`, `c = 2`. Thus every `(L−1)`-mer of `S` occurs exactly
once, hence every `L`-mer of `S` occurs exactly once (a repeated `L`-mer would
repeat its `(L−1)`-prefix); the `L`-mer de Bruijn support of `S` is then a single
directed cycle with one distinct outgoing edge per vertex. Since `d_D = 2 d_S`,
every edge on that cycle has multiplicity `2`, so every vertex still has a
unique distinct outgoing edge and `D`'s Eulerian circuit is forced to traverse
the cycle twice: `D = U²` for the cycle word `U`, contradicting primitivity
of `D`. Hence `c ≯ 1`. If `c < 1`, swap the roles of `S` and `D` (both primitive
and `TRF`) to get the same contradiction. Therefore `c = 1`. ∎ [mathematical
proof]

**Corollary 4.2.** For primitive `TRF` `S`, any primitive `TRF` candidate `D`
with the same population law has the same length and the same integer spectrum.
Only `TRF` (the multiplicity-`≤2` half) is used; `ILF` is not used here.

---

## 5. Equal-length uniqueness is the classical `q`-gram characterization

**Lemma 5.1 (source theorem).** If `S` is `WEAK`-admissible and `D` is any
circular word with `|D| = |S|` and `d_D = d_S`, then `D` is a cyclic shift
of `S`.

This is Bresler–Bresler–Tse (2013), Theorem 3 at `K = L−1`, under the circular
Eulerian-cycle reading: `WEAK(S,L)` says exactly "no triple repeat or
interleaved pair of maximal repeats of length `≥ L−1`", the hypothesis of that
theorem; the conclusion is a unique Eulerian cycle spelling `S`. The
interleaving must be read as a pair of maximal repeats that may be **different**
words; §7 shows this convention is essential. [source theorem + reading;
see [`circular-qgram-identifiability-and-Is-threshold-2026-09-21.md`](../literature/circular-qgram-identifiability-and-Is-threshold-2026-09-21.md)]

---

## 6. The clean population ML theorem

**Theorem 6.1 (oriented panel, unrestricted primitive `TRF` class).** Let
`S` be a primitive `WEAK`-admissible circular word of length `G`, and let `C` be
the class of all primitive `TRF` circular words over `Σ` whose read model is
defined. Then `S ∈ C`, `S` maximizes `ell_S` over `C`, and the maximizers are
exactly the cyclic shifts of `S`.

_Proof._ `S` is primitive `TRF`, so `S ∈ C`. Lemma 3.1: `S` maximizes and every
maximizer `D` satisfies `p_D = p_S`. Lemma 4.1 gives `|D| = G`, `d_D = d_S`.
Lemma 5.1 gives that `D` is a rotation of `S`. Conversely rotations of `S` have
`p_D = p_S`, hence tie. ∎ [mathematical proof + source theorem]

**Corollary 6.2 (same-length class; no primitivity/`TRF` on the rival).** Let
`S` be `WEAK`-admissible and let `C` be the class of all circular words of length
`G` whose read model is defined. Then `S` maximizes `ell_S` over `C` and the
maximizers are exactly the cyclic shifts of `S`.

_Proof._ A maximizer has `p_D = p_S`; equal lengths make this `d_D = d_S`; apply
Lemma 5.1 directly. No primitivity or `TRF` of `D` is needed because the length
is fixed by the class. ∎ [mathematical proof + source theorem]

**Remark 6.3 (where bridging enters).** Lemma 3.1 needs no hypothesis at all;
`WEAK`/`I_s` enters only through Lemma 5.1 (and `TRF` through Lemma 4.1). So the
population repair *isolates* the role of the repeat-resolution/bridging
condition to exactly the combinatorial injectivity of the spectrum map. This is
the "clean separation" the issue asked for. [mathematical fact]

**Remark 6.4 (what uniqueness reduces to).** By Corollary 3.3 and Theorem 6.1,
uniqueness up to rotation is *equivalent* to: on the candidate class, the fibre
of `D ↦ p_D` over `p_S` is the rotation class of `S`. Concretely it reduces to
two independent statements:

1. **Scale rigidity** (no `D` with `d_D = c d_S`, `c > 1`): supplied by
   `TRF` + primitivity (Lemma 4.1). Without primitivity it is false
   (`D = S^k`); without candidate-side `TRF` it is false (§7.2).
2. **Spectrum injectivity at equal length**: supplied by BBT Theorem 3 when
   `S` is `WEAK` (Lemma 5.1). Without `ILF` it is false (§7.1).

There is no other residue. [mathematical fact]

---

## 7. Edge cases and sharpness

### 7.1 `ILF` is genuinely needed, and the interleaving convention matters

The classical obstruction must be read on **pairs of maximal repeats**, which
may be different words. A naive same-word reading is insufficient. Consider

```text
L = 3
W  = A A C C A A G C C G      (length 10)
W' = A A C C G A A G C C      (length 10)
```

Then `W` and `W'`:

- have the **same** 3-mer spectrum (ten distinct 3-mers, each once);
- are **not** cyclic shifts of each other;
- are both primitive;
- satisfy `TRF` (the only repeated 2-mers are `AA` and `CC`, each exactly
  twice);
- are **not** `ILF`: the maximal repeat `AA` at positions `(0,4)` and the
  maximal repeat `CC` at positions `(2,7)` satisfy `0 < 2 < 4 < 7`, an
  interleaved pair of length `2 = L−1`.

So `TRF` alone does not give equal-length uniqueness, and the two words are
correctly excluded by `ILF` under the Bresler–Bresler–Tse "pair of repeats"
convention. Under an (incorrect) same-word-only reading of "interleaved", `W`
and `W'` would look `WEAK` and would be a false counterexample to Lemma 5.1.
[verified computation, §8 D2]

### 7.2 Primitivity and candidate-side admissibility are necessary

- **Primitivity:** `S = AAB` (`L = 3`) is primitive `WEAK`; `D = S² = AABAAB` is
  `WEAK` and has `p_D = p_S` but is not a rotation of `S`. Tandem repetition is
  the exact scale ambiguity, and primitive forces `c = 1` in Lemma 4.1.
- **Candidate-side `TRF`:** the primitive `WEAK` truth `S = AAAB` (`L = 3`) and
  the primitive-but-not-`TRF` `D = AAAABAAB` have `p_D = p_S` and are not
  rotations. Lemma 4.1 fails for `D` because `B_v` can exceed `2`. [verified
  computation, §8 C]

### 7.3 Zero support and short candidates

If `D` misses a truth-positive type, `ell_S(D) = −∞` and the candidate is never
a maximizer. This is exactly the mechanism removed by population data. Example
(the issue-#48 finite witness): `S = AABBC`, `L = 3`, realized reads
`{AAB, BCA}`, competitor `D = AABC`. At population, `p_D` is supported on
`{AAB, ABC, BCA, CAA}` and misses the truth types `ABB`, `BBC`, so
`ell_S(D) = −∞`; the finite-sample strict win `(5/4)² > 1` cannot survive.
[verified computation, §8 E] Note the finite ratio there is not a scale effect:
it is a support/frequency effect, orthogonal to §4. [mathematical fact]

Candidates of length `m < L` are still scored by the wrapping window law; in the
primitive `TRF` class they are excluded by Lemma 4.1 whenever they tie, and for
the source regime one assumes `2 ≤ L ≤ G`. The case `L = 1` is degenerate
(`(L−1) = 0`-mers) and is outside the source model. [modeling choice]

### 7.4 Oriented vs molecule read types

On the molecule panel the maximizer half of Lemma 3.1 still holds (it is
panel-independent), but the uniqueness half **fails**: with
`S = AACAGT`, `D = AACTGT`, `L = 3`, both are primitive and `STRONG` (all
2-mers distinct), their reverse-complement-class 3-mer laws are equal, yet they
are neither rotations nor reverse-complement rotations of each other.

```text
molecule law: each of the six rc-classes has weight 1/6 in both
```

So the molecule panel supports only "truth is a maximizer", not
"maximizers are the truth up to dihedral equivalence". The oriented panel's
positive theorem is therefore genuinely coupled to the oriented read-type
choice. [verified computation, §8 F]

### 7.5 Equivalence is forced, not optional

The population law is rotation-invariant, so the uniqueness conclusion can only
be "up to cyclic shift". Under molecule types it is additionally
reverse-complement-invariant, so the equivalence must be dihedral. This is the
same coupling proved in
[`equivalence-and-tie-wellposedness.md`](equivalence-and-tie-wellposedness.md).
[mathematical fact]

---

## 8. Verification

`scripts/verify_population_ml_theorem_independent.py`:

| Section | Check | Scope (default / `--full`) | Result |
|---|---|---|---|
| A | KL maximizer and `tie ⟺ p_D = p_S` | `σ ≤ 3`, `G ≤ 4/5`, candidates of length `2..G+2` | pass |
| B | primitive: `TRF ⟺ (L−1)`-mult `≤ 2` (maximal-extension definition) | `σ ≤ 3`, `G ≤ 7/10` | pass |
| C | no cross-length proportional collision for primitive `TRF` | 17 398 / 1 075 318 words | 0 collisions |
| D1 | `WEAK` `⇒` `L`-spectrum determines the word up to rotation | 6 092 / 101 754 words | 0 failures |
| D2 | `W`/`W'` sharpness pair and its interleaved pair | exact | pass |
| E | #48 finite witness is a population support failure | exact | pass |
| F | molecule panel boundary `AACAGT`/`AACTGT` | exact | pass |

The exhaustive scopes are finite evidence; all structural claims are also proved
above or attributed to the cited source theorem.

---

## 9. Reconciliation with the concurrent branch result

The branch artifact `docs/population-identifiability-intrinsic-genomes.md` on
`agent/issue48-population-independent-0921` reaches the same positive oriented
conclusion with the same `WEAK`/`TRF` vocabulary after Theorem P and the
Bresler–Bresler–Tse `K = L−1` identification. This note agrees with it and makes
three sharpenings:

1. the cross-length step is proved directly from the multiplicity bound
   (Lemma 4.1) without any appeal to spectrum uniqueness, so the issue comment's
   one-sided-identifiability gap is closed;
2. the equal-length step (`Corollary 6.2`) is stated for the same-length class
   with no primitivity or `TRF` requirement on the rival;
3. the interleaving-convention sharpness pair §7.1 is new and pins the
   "pair of possibly distinct maximal repeats" reading.

The branch's Lemma L* is a special case of Lemma 2.2. No disagreement was found.
[reconciliation]

---

## 10. What this does and does not settle

- It settles the population/infinite-read analogue requested by issue #45:
  truth is always an ML maximizer, and under the intrinsic admissibility +
  primitivity hypotheses the maximizers are exactly its cyclic shifts
  (oriented single-strand panel).
- It does **not** repair the finite-data statement of issue #48.
- It does **not** settle the published 2016 finite-sample open question, nor
  select which Medvedev–Brudno likelihood layer that sentence intends.
- It makes no claim about the §6.2 flow-feasible class, non-uniform or
  non-i.i.d. sampling, or the fixed-`N` binomial objective beyond the
  observation that its per-read limit differs from `ell_S`.
- As required by the modeling contract, the candidate class, candidate length
  semantics, strand convention, and genome equivalence are all explicit in
  Theorem 6.1 and Corollary 6.2.

---

## 11. Sources and cross-references

Primary: Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
*Bioinformatics* 32(17) (2016) i494–i502, §2, DOI `10.1093/bioinformatics/btw450`.
Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome Assembly*,
*J. Comput. Biol.* 16(8) (2009) 1101–1116, §6.1, DOI `10.1089/cmb.2009.0047`.
Guy Bresler, Ma'ayan Bresler, David Tse, *Optimal assembly for high throughput
shotgun sequencing*, *BMC Bioinformatics* 14(Suppl 5):S18 (2013), DOI
`10.1186/1471-2105-14-S5-S18`. E. Ukkonen, *Theoret. Comput. Sci.* 92(1) (1992)
191–211; P. A. Pevzner, *Algorithmica* 13(1–2) (1995) 77–105.

Repository: [`open-problem.md`](../open-problem.md),
[`ml-formalization-contract.md`](../ml-formalization-contract.md),
[`source-notes/equivalence-and-tie-wellposedness.md`](equivalence-and-tie-wellposedness.md),
[`source-notes/medvedev-brudno-candidate-class.md`](medvedev-brudno-candidate-class.md),
[`source-notes/oriented-se62-rigidity-theorem.md`](oriented-se62-rigidity-theorem.md),
[`literature/circular-qgram-identifiability-and-Is-threshold-2026-09-21.md`](../literature/circular-qgram-identifiability-and-Is-threshold-2026-09-21.md)
(branch artifact), `docs/population-identifiability-intrinsic-genomes.md`
(branch `agent/issue48-population-independent-0921`).
