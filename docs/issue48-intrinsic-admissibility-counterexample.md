# Issue #48: the finite repaired theorem with candidate-intrinsic admissibility is false

_Status: exact-arithmetic counterexample, independently re-derived, with a
bounded kernel check of the decisive instance in
`AssemblyP1/Issue48FreeLengthCounterexample.lean` (`lake build`; only the
standard Mathlib axioms `propext`, `Classical.choice`, `Quot.sound`). This note
does **not** reinterpret or weaken any literature-derived fixed-length result;
it attacks an explicitly additional repaired formulation. It does **not** settle
the source-ambiguous Shomorony et al. open question — the free-length exact
Medvedev–Brudno multinomial is one reading of that question, and this note
records exactly which reading it covers._

_Reproduction: `python3 scripts/verify_issue48_intrinsic_admissibility.py`
(witnesses) and `... --search` (bounded exhaustive search). Exact rational
arithmetic throughout (`fractions.Fraction`)._

## 0. Direct answer

Let the truth satisfy the **source-faithful sampled-read** condition `I_s` for
its realized read placement, and let the candidate universe be the circular
genomes admissible under a **candidate-intrinsic** structural repeat/read-length
check (optionally restricted to primitive genomes). Without assuming equal
candidate length, the truth need **not** be maximum-likelihood. The repaired
finite theorem is **false**, and it fails in its strongest intrinsic form:

* even if the competitor is required to be primitive and to satisfy the
  **strongest** intrinsic condition `STRONG` ("no `(L−1)`-mer occurs twice"),
  a strictly more likely competitor exists;
* the truth in the decisive smallest witness is itself primitive and `STRONG`,
  so the candidate class contains the truth;
* the competitor's likelihood is **strictly** greater, so the refutation is
  independent of every genome-equivalence and tie convention.

The failure mechanism is not residual repeat ambiguity. The intrinsic checks
remove exactly the proportional/`S²` scale and long-compressed-run competitors;
they do not constrain the truth-vs-competitor **ranking across different
`L`-mer spectra** under the free-length normalizing factor `G/N(D)`. The
competitor wins by choosing a shorter genome that concentrates the observed
read multiset, which is precisely what the free-length exact objective rewards.

A positive theorem does survive, and it is exactly where the length axiom was
doing the work: **fixed candidate length `= G` plus `STRONG` admissibility
makes the truth a maximizer** (Proposition 2 below). So the repaired formulation
has a clean positive/negative frontier: `STRONG` is enough with the length
axiom, and insufficient without it.

## 1. Exact conventions attacked

These are fixed for every claim in this note. They are stated so the result
cannot be read as covering a different model.

**Underlying model (source facts).** Shomorony et al. (2016) work with a
circular true sequence `s` of length `G`; error-free reads of common length `L`
are drawn independently and uniformly from the `G` circular start positions;
the target is `s` **up to cyclic shift**. This is the single-strand, oriented
panel. Bresler et al.'s repeat/triple-repeat/interleaving/bridging definitions
(attributed by Eq. (1)) are used as recorded in
[`bridging-source-semantics.md`](bridging-source-semantics.md).

**Objective (Variant E, free candidate length).** The exact Medvedev–Brudno
read-count multinomial ([`ml-formalization-contract.md`](ml-formalization-contract.md)
Variant E; MB09 §6.1) with candidate-intrinsic length `N(D)`. For a circular
candidate `D`, let `d_D(w)` be the number of circular length-`L` windows equal
to read type `w`, and let `x_w` be the observed count of `w`. Then

```text
L_exact(D | x) = n! / (∏_w x_w!) · ∏_w (d_D(w) / N(D))^{x_w},
```

and for two candidates the observation-only coefficient cancels:

```text
L(D)/L(S) = ∏_{w : x_w > 0} ( N(S)·d_D(w) / (N(D)·d_S(w)) )^{x_w}      (free length),
L(D)/L(S) = ∏_{w : x_w > 0} ( d_D(w) / d_S(w) )^{x_w}                  (fixed/common length).
```

This is the free-length reading in which `N(D)` is the candidate's own length
(`N(D) = Σ_w d_D(w) = len(D)`). The quoted issue #48 comments use the same
formula. The fixed-length `N`-binomial approximation is a different, separately
named objective and is **not** used here.

**Strand / read-type convention.** Single-strand oriented reads; no
reverse-complement collapse. Genome equivalence is cyclic shift (Shomorony
panel). Reverse complement is not used (it is irrelevant here because the
refutation is strict; see §4).

**Correctness hypothesis on the truth (source `I_s`).** `R ∈ I_s` iff
(1) the realized reads `R` cover `S`; (2) every Bresler triple repeat of `S` is
all-bridged by `R`; (3) every interleaved pair of maximal repeat pairs of `S`
is bridged by `R`. Bridging is strict two-sided extension on an integer lift of
the circle: a length-`ℓ` copy at lifted start `t` is bridged by a read at
lifted start `r` iff `r < t` and `t + ℓ < r + L`.

**Candidate-intrinsic admissibility of a candidate `D` (properties of `D` and
`L` only).**

* `STRONG(D)`: no `(L−1)`-mer of `D` occurs twice.
* `WEAK(D)`: every triple repeat of `D` has length `≤ L−2`, and every
  interleaved pair has a constituent repeat of length `≤ L−2`. This is the
  candidate-intrinsic shadow of source `I_s` at the full read set.
* `primitive(D)`: `D` is not a nontrivial power `w^m`, `m ≥ 2`.

**Tie semantics.** The conclusion schema "the ML sequence is the true sequence"
has two literal readings (`truthIsML` vs `mlIsTruthUpToEquiv` in
[`ml-formalization-contract.md`](ml-formalization-contract.md)). A **strict**
competitor (`L(D) > L(S)`) refutes both for **every** equivalence relation and
every tie rule, because it fails the weaker maximizer conjunct. Equivalence and
tie conventions are therefore not needed to state or check the refutation.

## 2. The repaired theorem under attack

> **(R)** If the realized sequencing `R` satisfies source `I_s` for the truth
> `S`, and `S` is itself admitted by the chosen intrinsic candidate predicate,
> then `S` is maximum-likelihood among the candidates admitted by that
> predicate **of arbitrary length**.

By §1 the truth need not be assumed `STRONG`; the natural intrinsic predicate
matched to `I_s` is `WEAK`, and `I_s` forces the truth to be `WEAK` (Lemma 1),
so (R) with `WEAK` already contains the truth. We refute (R) with `WEAK` and
then again with the strictly stronger `STRONG` predicate.

## 3. Truth compatibility: `I_s` implies intrinsic `WEAK` admissibility

**Lemma 1.** If `R ∈ I_s` for a truth `S`, then the full read set (one read at
every start) is in `I_s`, and hence `S` is `WEAK`-admissible.

**Proof.** `I_s` is monotone in `R`: adding reads preserves coverage and can
only turn an unbridged copy into a bridged one; the three conjuncts are
componentwise monotone. The full read set contains `R`, so it is in `I_s`. By
the full-read reduction
([`../mathematics/bridging-and-spectrum-uniqueness.md`](../mathematics/bridging-and-spectrum-uniqueness.md)
§1), a copy of length `ℓ` is bridgeable at the full read set iff `ℓ ≤ L−2`; thus
the full read set is in `I_s` iff every triple repeat has length `≤ L−2` and
every interleaved pair has a constituent of length `≤ L−2`, i.e. `WEAK(S)`. ∎

_Epistemic class: mathematical proof (using the repository's full-read reduction
and the monotonicity of bridging)._

So the candidate class in (R) contains the truth, and there is no gap between
"truth satisfies `I_s`" and "truth is a candidate."

## 4. Counterexamples

All rows are checked by the self-contained script with exact rationals. The
`I_s` certificate (coverage plus every required bridging) is checked from the
source definitions, not quoted.

| # | universe | truth `S` | `G` | `L` | starts `R` | competitor `D` | `n` | `D` primitive | `D` STRONG | ratio `L(D)/L(S)` |
|---|----------|-----------|-----|-----|-----------|----------------|-----|---------------|------------|-------------------|
| 1 | `WEAK`, free | `AAB` | 3 | 2 | `(1,2)` | `AB` | 2 | yes | yes | `9/4` |
| 2 | `STRONG`+prim, free | `AABB` | 4 | 3 | `(0,3)` | `AAB` | 3 | yes | yes | `16/9` |
| 3 | `STRONG`+prim, free | `AABB` | 4 | 3 | `(0,0,3)` | `AAB` | 3 | yes | yes | `64/27` |
| 4 | `STRONG`+prim, free | `AABBC` | 5 | 3 | `(0,3)` | `AABC` | 4 | yes | yes | `25/16` |
| 5 | `WEAK` (non-vacuous `I_s`), free | `ABACABC` | 7 | 3 | `(1,1,1,3,6)` | `ABAC` | 4 | yes | yes | `16807/4096` |

In rows 2–4 the truth is primitive and `STRONG`, so it lies in the strongest
candidate class; in row 1 the truth is primitive and `WEAK` but not `STRONG`
(and the truth of row 5 is primitive and `WEAK`, not `STRONG`). In every row the
competitor is primitive and `STRONG`,
hence also `WEAK`; the observed read types all occur in both genomes (the
ratios are finite and `> 1`).

**Smallest possible shape.** A `STRONG` competitor can never strictly beat the
truth at equal length (Proposition 2), so a strict free-length win needs
`n = len(D) ≠ G` with `n ≥ L`; the smallest admissible shape is therefore
`G = 3, L = 2, n = 2`, realized by row 1. Row 2 (`G = 4, L = 3`) is the
exhaustive minimum once the truth is also required to be `STRONG`: exhaustive
search over `G = 3` finds none, and rows 2/3 are the two-read/three-read
instances at `G = 4`.

**Row 5 is non-vacuous for both nontrivial `I_s` conjuncts.** The truth
`ABACABC` has a triple repeat `A@(0,2,4)` (all copies bridged) and an
interleaved pair `A@(2,4) ‖ CAB@(3,6)` (bridged via the `A@(2,4)` copy); this is
the witness recorded in
[`fixed-length-interleaved-counterexample.md`](fixed-length-interleaved-counterexample.md),
reused here as the *truth* of a free-length counterexample. Its candidate
`ABAC` is primitive and `STRONG`.

**Why the free-length factor is essential.** The only competitor mechanism used
is length shrinkage. Write the free-length ratio as
`(G/n)^{Σx_w} · ∏ (d_D(w)/d_S(w))^{x_w}`. Even when the spectrum factor is `1`
(rows 1–4 have `d_D(w) = d_S(w) = 1` on the observed support), the length
factor `(G/n)^{N}` is `> 1`. This is exactly the tandem/scale freedom the
intrinsic predicates were meant not to need but also cannot penalize: `WEAK`
and `STRONG` constrain the **fibre** of `D ↦ d_D` (identity and proportional
scale), while the exact multinomial ranks candidates **across fibres** using the
length normalization. A candidate-intrinsic repeat condition is invariant under
changing `N(D)` alone, so it cannot repair the ranking.

## 5. The complementary positive theorem (fixed length + `STRONG`)

**Proposition 2.** Fix the candidate universe to primitive `STRONG`-admissible
genomes of the true length `G`. Then for every observed read multiset coming from
a truth of length `G`, the truth is a maximum-likelihood maximizer. No bridging
hypothesis is needed.

**Proof.** `STRONG(D)` forbids a repeated `(L−1)`-mer; an `L`-mer occurring
twice would have its `(L−1)`-prefix occurring twice, so `d_D(w) ≤ 1` for every
`w`. Every observed `w` has `d_S(w) ≥ 1`. With equal candidate length the length
factor is `1`, so each factor in `L(D)/L(S)` is `d_D(w)/d_S(w) ≤ 1/1`; hence
`L(D) ≤ L(S)`. ∎

_Epistemic class: mathematical proof. This is the fixed-length `STRONG` result
of issue #48 comment 3 (§2), re-proved here; it is independent of `I_s`._

So `STRONG` is exactly the crossover: with the length axiom it is sufficient,
without it demonstrably insufficient.

## 6. Bounded exhaustive search

The script's `--search` mode enumerates, exactly and exhaustively over the
stated finite ranges, all coherent counterexamples: truth primitive +
`WEAK`-admissible and `I_s`-feasible for some realized read multiset, competitor
primitive + `STRONG`, free-length ratio `> 1`. Alphabet `{A,B,C}`, `G ≤ 6`,
`L ≤ 3`, `N ≤ 4` (plus `{A,B}`).

| alphabet | truth predicate | hits | smallest (`G`, `L`, `S`, `R`, `D`, ratio) |
|---|---|---|---|
| `{A,B}` | `WEAK` | 240 | `3, 2, AAB, (1,2), AB, 9/4` |
| `{A,B}` | `WEAK` + truth `STRONG` | 120 | `4, 3, AABB, (0,0,3), AAB, 64/27` |
| `{A,B,C}` | `WEAK` | 17268 | `3, 2, AAB, (1,2), AB, 9/4` |
| `{A,B,C}` | `WEAK` + truth `STRONG` | 11160 | `4, 3, AABB, (0,0,3), AAB, 64/27` |

This is bounded computational evidence (exact within the stated ranges), not a
proof of absence beyond them. The named witnesses in §4 are individually exact,
and the `G = 3` minimum is exhaustively settled within the search.

## 6b. Kernel check of the decisive instance

`AssemblyP1/Issue48FreeLengthCounterexample.lean` kernel-checks row 2
(`truth = AABB`, `competitor = AAB`, `L = 3`, observed `{AAB, BAA}`,
realized starts `0, 3`). It proves, by computation over `ℚ` and finite
`decide`:

* `Covers truth 3` and `NoTripleRepeat truth` (the non-vacuous part of the
  `I_s` certificate for this instance; the interleaved conjunct is vacuous here
  because the only maximal repeat pairs are `A@(0,1)` and `B@(2,3)`, whose four
  starts are not alternating);
* `Strong truth 3`, `Strong competitor 3`, `IsPrimitive truth`,
  `IsPrimitive competitor`;
* `likelihood truth < likelihood competitor`, with `likelihood truth = 1/16`
  and `likelihood competitor = 1/9` for the free-length exact multinomial.

The bundled theorem is `AssemblyP1.Issue48.issue48_free_length_counterexample`.
The general `I_s` / interleaving check for this and the non-vacuous witness is
performed by the script (§6), following the repository precedent of leaving
some instance-specific finite checks to the accompanying note rather than
building general repeat/interleaving infrastructure.

## 6c. Reconciliation with the concurrent packet

A concurrent packet,
[`issue48-intrinsic-candidate-checks.md`](issue48-intrinsic-candidate-checks.md),
answers the same finite-data question with an independent implementation
(`scripts/issue48_intrinsic_candidate_search.py`). The two packets agree on the
answer, on the objective, on strict source `I_s`, and on the witness set:
that script independently reproduces `AABB → AAB` (`16/9`),
`AABBC → AABC` (`25/16`), and `ABACABC → ABAC` (`16807/4096`).

Predicate correspondence: this note's `STRONG` is that packet's `RRF` (no
repeated `(L−1)`-mer); this note's `WEAK` is the full-read-set `I_s` shadow.
That packet's headline class `P_weak = primitive ∧ SR` (spectrum-resolvable)
is *weaker* than `primitive ∧ WEAK` wherever `WEAK ⇒ SR` (Conjecture 4 of
`mathematics/bridging-and-spectrum-uniqueness.md`), so its `P_weak`
refutation does not subsume the one here; the two are complementary
strengthenings (this note's `WEAK` is a syntactic candidate condition, that
packet's `SR` is a spectral-uniqueness condition).

**One point where this packet is stronger.** The concurrent packet's
`P_strong` is reported with the caveat that its non-vacuous-`I_s` truth
`ABACABC` is *not* `RRF`, so `P_strong` excludes the truth from its own
candidate class. That defect does not apply to the decisive row-2 witness here:
`S = AABB` is primitive **and** `STRONG` (`RRF`), and the competitor `AAB` is
primitive and `STRONG`, so the strongest intrinsic class is refuted with the
truth **in** the class, not merely by an over-strong variant. The same holds for
rows 3–4. The non-vacuous row 5 is the only witness whose truth is `WEAK` but
not `STRONG`, and it is used only for the `WEAK`-universe refutation.

**Unbounded families.** The concurrent packet adds exact families with ratio
`(G/n)^N → ∞` (`AABC → ABC`, and the non-vacuous `ABACABC → ABAC` with
`k` copies of `BAC`), so the finite failure has no uniform-in-`N` likelihood
bound. This is consistent with, and not reproduced by, the named witnesses
here.

## 7. What this does and does not establish

**Established.**
* The repaired finite formulation (R) is false with free candidate length, under
  the exact Medvedev–Brudno multinomial, single-strand oriented reads, with
  cyclic-shift equivalence, for both the `WEAK` (source-`I_s` shadow) and the
  strictly stronger `STRONG` candidate predicates, even with primitiveness.
* The refutation is by a **strict** likelihood gap, so it is insensitive to the
  maximizer-vs-uniqueness and equivalence/tie ambiguities.
* Truth compatibility: any `I_s` truth is `WEAK`-admissible (Lemma 1), so the
  counterexamples are in the coherent regime where the candidate class contains
  the truth.
* A positive fixed-length `STRONG` theorem (Proposition 2).

**Not established / non-claims.**
* This does not settle the published Shomorony et al. question; it settles one
  explicitly additional free-length repaired formulation (issue #48).
* No claim under the fixed-`N` binomial approximation (Variant A), the §6.2
  flow-feasible set (Variant F), or the reverse-complement/molecule panel. On
  the molecule panel the population uniqueness statement is already false under
  `STRONG` (issue #48 comment 2, `AACAGT`/`AACTGT`), a separate limitation.
* Minimality statements are exact for the named instances and bounded-exhaustive
  otherwise.

**Diagnosis and handoff.** Because the residual obstruction is finite sampling
and the free-length normalization rather than structural non-identifiability,
the natural next repair is the population / infinite-read regime tracked by
issue #45, not a further strengthening of the candidate-intrinsic predicate.
The population statement "primitive + `WEAK` admissible genomes with the same
normalized `L`-spectrum are equal up to cyclic shift" was proved in issue #48
comments 2–3 (paper proof) but is a statement about one spectrum; it does not
lift to the finite cross-spectrum maximization attacked here.

Qualifier (in agreement with the concurrent packet §0/§6): the named witnesses
put all reads on a proper subset of the start positions, so under i.i.d. uniform
sampling their probability is exponentially small in `N`; the population limit
concentrates on the proportional spectrum, where the truth is optimal. The
finite negative and a population positive are therefore compatible. What fails
is any *worst-case, uniform-in-`N`* finite statement; the repair must be
probabilistic (typicality), not a stronger candidate-intrinsic predicate.

## 8. Epistemic summary

| Claim | Status | Evidence |
|---|---|---|
| Lemma 1: `I_s` truth is `WEAK`-admissible | **Proven** | monotonicity + full-read reduction |
| Proposition 2: fixed length + `STRONG` ⇒ truth ML | **Proven** | counting; no bridging needed |
| (R) with `WEAK` universe is false | **Refuted** | row 1 exact, `9/4` |
| (R) with `STRONG` + primitive universe is false | **Refuted** | row 2/3/4 exact, smallest `G=4` |
| Non-vacuous-`I_s` refutation | **Refuted** | row 5 exact, `16807/4096` |
| Minimality of `G=3` (`WEAK`) and `G=4` (`STRONG`) | **Exhaustive + exact witnesses** | §6, bounded |
| Failure is cross-spectrum length shrinkage, not repeat non-identifiability | **Interpretation supported by the witnesses** | §4, §7 |
| Population one-spectrum uniqueness under primitive + `WEAK` | not re-proved here | issue #48 comments; paper proof |

## 9. Sources and repository anchors

| Item | Source / anchor |
|---|---|
| `I_s` (coverage, all-bridged triples, bridged interleaved) | Shomorony et al. 2016 Eq. (1); `docs/bridging-source-semantics.md` |
| Repeat/triple/interleaving/maximality | Bresler et al. 2013; `docs/bridging-source-semantics.md` |
| Strict two-sided bridging | `docs/bridging-source-semantics.md:20-28` |
| Exact multinomial `d_i/N(D)`, candidate-intrinsic length | Medvedev–Brudno 2009 §6.1; `docs/ml-formalization-contract.md` Variant E |
| Free-length ratio formula | issue #48 comments; derived from MB09 §6.1 |
| Full-read reduction `I_s` shadow (`WEAK`) | `mathematics/bridging-and-spectrum-uniqueness.md` §1 |
| Two conclusion schemas | `docs/ml-formalization-contract.md:80-96` |
| Fixed-length `STRONG` positivity | issue #48 comment 3 §2; Proposition 2 here |
| Non-vacuous interleaved truth `ABACABC` | `docs/fixed-length-interleaved-counterexample.md` |
| Verification script | `scripts/verify_issue48_intrinsic_admissibility.py` |
| Kernel check of decisive instance | `AssemblyP1/Issue48FreeLengthCounterexample.lean` |
| Concurrent independent packet | `docs/issue48-intrinsic-candidate-checks.md`; `scripts/issue48_intrinsic_candidate_search.py` |
