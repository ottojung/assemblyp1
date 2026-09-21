# Structural ambiguity and the two failure modes

_Status: focused constituent note for the issue-#46 synthesis “Maximum-likelihood
models for genome assembly,” 2026-09-21. It supplies the synthesis's **opening
counterexample** (failure mode 1) and reconciles the finite-data results
currently on `main` into the intended two-failure-mode organization. It is not
the synthesis document itself, does not select which Medvedev–Brudno (2009)
objective the Shomorony et al. (2016) sentence intends, and deliberately does
**not** develop the infinite-read repair (that is issue #45). Every claim is
labelled **source fact**, **mathematical proof**, **verified computation**,
**kernel-checked**, or **open**._

_Reproduce: `python3 scripts/verify_structural_ambiguity_opening.py`. The script
is self-contained, exact-integer, deterministic, and exits non-zero on any
failed assertion._

---

## 0. Why this note

Issue #46 asks for a synthesis organized around two failure modes:

1. **structural ambiguity** from repeats/read length, present before any
   bridging boundary is imposed; and
2. **finite-sample frequency fluctuation** after that boundary is imposed.

The repository already contains the mode-2 witnesses (the finite-data
counterexamples on `main`) and the source/convention reconciliation around them,
but it had no durable statement of the mode-1 opening or of how the two modes
relate. This note supplies both. It does not introduce the population-level
(infinite-read) repair; per issue #45 that is deferred until the finite
formulations are settled.

---

## 1. The opening counterexample (failure mode 1)

### 1.1 Model

Shomorony et al. (2016), §2: a circular DNA genome `s` of length `G`; error-free
reads of common length `L` drawn independently and uniformly from the `G`
circular length-`L` windows. The observable datum is the read multiset, i.e. the
read-type count vector `x`. [source fact]

Any likelihood that is a function of the observed read-type counts — the exact
candidate-intrinsic multinomial of MB09 §6.1, the fixed-`N` product of binomial
marginals, or the §6.2 spelled-circuit objectives — therefore induces the *same*
ordering for two genomes with the same length-`L` window multiset. This section
uses only that elementary consequence. [mathematical proof]

### 1.2 The witness

Take the DNA alphabet and read length `L = 2`, and the two circular words

```text
S = AACAG
D = AAGAC
```

of length `G = 5`. Their length-2 circular window multisets are equal:

```text
spec_2(S) = spec_2(D) = { AA:1, AC:1, CA:1, AG:1, GA:1 } .
```

They are genuinely different circular genomes: `D` is neither a cyclic shift of
`S` nor a cyclic shift of the reverse complement of `S`. (Verified computation;
see `scripts/verify_structural_ambiguity_opening.py` §A.)

### 1.3 Consequence: an exact, infinite-data tie

Because the two spectra coincide, **every** observed read multiset `R` has
exactly the same likelihood under `S` and under `D`, for every candidate
objective that depends only on `(spec_L(·), x)`. In particular this is true for
the full population (`x = spec_2(S)`, the infinite-read/noiseless-spectrum
observation) and for every finite skewed sample alike. The maximum-likelihood
principle can never select the true genome here, no matter how much error-free
data is collected. This is the first failure mode. [mathematical proof]

### 1.4 Mechanism and the read-length boundary

`S` and `D` both contain a **Bresler-maximal triple repeat of the single symbol
`A` at starts `{0, 1, 3}`**: the three copies carry the same length-1 window, the
preceding symbols are `G, A, C` (not all equal), and the following symbols are
`A, C, G` (not all equal). This is a genuine maximal triple repeat, not a triple
count of a plain substring. [verified computation; definitions from
[`bridging-source-semantics.md`](bridging-source-semantics.md), attributed by
Shomorony et al. to Bresler, Bresler & Tse (2013)]

The ambiguity is exactly a **critical repeat/read-length** phenomenon. A read
occupying `[r, r + L)` bridges a copy `[t, t + ℓ)` only when `r < t` and
`t + ℓ < r + L`, so a read bridges a length-`ℓ` copy only if `ℓ ≤ L - 2`.
[source fact; [`bridging-source-semantics.md`](bridging-source-semantics.md)] At
`L = 2` the triple repeat has `ℓ = 1 = L - 1`, so **no length-2 read can bridge
any copy** of it, and the all-bridged triple-repeat clause of `I_s` necessarily
fails. [verified computation]

The boundary is real and easy to see: at `L = 3` the two spectra separate,

```text
spec_3(S) = { AAC, ACA, CAG, AGA, GAA }
spec_3(D) = { AAG, AGA, GAC, ACA, CAA } ,
```

so longer reads resolve precisely the ambiguity that length-2 reads cannot.
[verified computation] The ambiguity is thus not an artifact of the likelihood
objective or the candidate universe; it is a property of the read length versus
the repeat structure.

### 1.5 Minimality

Exhaustive enumeration over the DNA alphabet shows:

- no pair of distinct circular words of length `G ≤ 4` collides on length-`L`
  spectra for any `L ≥ 2`; and
- the first collision is at `G = 5, L = 2`, and every minimal collision pair is
  a symbol relabeling and cyclic rotation of the witness above (uniquely, the
  equality pattern has a triple of one symbol with two copies adjacent).

[verified computation, exhaustive in scope] This is, up to relabeling and
rotation, the smallest circular DNA ambiguity that two reads of length ≥ 2 can
fail to resolve. It is the natural opening example: it needs five bases, two-base
reads, and one short repeat.

The same phenomenon is what Bresler, Bresler & Tse (2013) state abstractly:
an all-unbridged problematic interleaved/triple repeat yields a distinct
same-length genome with equal read likelihood. See
[`literature-status.md`](literature-status.md) §3. This note realizes the
phenomenon with a single concrete minimal instance.

---

## 2. The two failure modes

The repository's results separate cleanly once the boundary is named.

**Failure mode 1 — structural ambiguity from repeats/read length.** Two genuinely
different circular genomes have identical read spectra (or, more generally, the
reads leave a repeat arrangement unresolved). The consequent likelihood tie is
exact and persists at every sample size, including the infinite-data/population
limit. The witness is §1. Cause: a repeat at the critical length `ℓ ≥ L - 1`
that no read can bridge. Repair: the repeat/read-length boundary — coverage plus
all-bridged triple repeats and bridged interleaved pairs (`I_s`), which
Shomorony et al. prove is sufficient for exact reconstruction up to cyclic shift,
and which the oriented §6.2 rigidity theorem sharpens on the same-length slice.
[source fact + mathematical proof]

**Failure mode 2 — finite-sample frequency fluctuation.** The structural
boundary holds (`I_s` is satisfied), yet the observed read *multiplicities* are
skewed relative to the true spectrum, and an incorrect candidate has strictly
greater likelihood. This is a distinct phenomenon: it is not an unbridgeable
repeat, it requires a finite sample, and it disappears in the population limit.
The witnesses are the finite-data counterexamples reconciled in §3. Repair: an
infinite-read/population-level model, which is the subject of issue #45 and is
not developed here. [mathematical proof + kernel-checked finite witnesses;
population repair open]

The modes are logically independent: mode 1 can occur with `I_s` false and with
an exact tie; mode 2 can occur with `I_s` true and with a strict inequality.
Neither implies the other.

---

## 3. Reconciliation of the finite-data results on `main`

The table places every finite-data result currently on `main` into the two-mode
story. “Ratio” is the competitor-to-truth likelihood ratio; all mode-2 entries
have `I_s` satisfied, which is what distinguishes them from mode 1.

| witness | objective | candidate universe | lengths | index / strand | ratio | status |
|---|---|---|---|---|---|---|
| `AACAG ↔ AAGAC` | any `(spec_L, x)` objective | all circular candidates | `5 = 5` | oriented (also under rc) | `1` (tie, all `n`) | **mode 1**, verified computation |
| `ACGT → ACACGT` | exact multinomial, candidate-intrinsic `N(D)` | all circular candidates | `4 → 6` | oriented | `32/27` | **mode 2**, kernel-checked |
| `AAABB → AAAAB` | exact multinomial, same length | length-`5` circular candidates | `5 = 5` | oriented | `2` | **mode 2**, kernel-checked |
| `AAACC → AAAAC` | literal §6.1 product of binomial marginals, fixed `N` | length-`5` circular candidates | `5 = 5` | oriented | `1125/512` | **mode 2**, kernel-checked |
| `AAATAT → AAAAAT` | §6.1 fixed-`N`, and exact | §6.2 spelled, per-vertex bound | `6 = 6` | molecule (rc classes) | `5` / `3` | **mode 2**, kernel-checked |
| `AAATT → AAAATT` | §6.1 fixed-`N` | §6.2 spelled, per-vertex bound | `5 → 6` | molecule (rc classes) | `9/8` | **mode 2**, kernel-checked |
| `AAATT → AAAATT` | exact, and §6.1 fixed-`N` | §6.2 spelled, oriented | `5 → 6` | oriented | `81/64` (at `n = 6`) | **mode 2**, verified computation |
| (any `S`, `L`) | any `(spec_L, x)` objective | §6.2 spelled, `I_s`, **same length** | `G = G` | oriented | `1` (rigid) | **mode 2 absent**, mathematical proof |

References for the mode-2 rows, in order:
[`exact-variant-e-counterexample.md`](exact-variant-e-counterexample.md) (Lean:
`AssemblyP1/ExactVariantECounterexample.lean`);
[`fixed-length-exact-counterexample.md`](fixed-length-exact-counterexample.md)
(Lean: `AssemblyP1/FixedLengthExactCounterexample.lean`);
[`fixed-length-binomial-counterexample.md`](fixed-length-binomial-counterexample.md)
(Lean: `AssemblyP1/FixedLengthBinomialCounterexample.lean`);
[`section62-same-length-bidirected-counterexample.md`](section62-same-length-bidirected-counterexample.md)
(Lean: `AssemblyP1/SameLengthSection62Counterexample.lean`);
[`bridging-se62-flow-ml-counterexample.md`](bridging-se62-flow-ml-counterexample.md)
(Lean: `AssemblyP1/Section62BridgingCounterexample.lean`); and
[`source-notes/oriented-se62-rigidity-theorem.md`](source-notes/oriented-se62-rigidity-theorem.md)
for the final positive row.

Two reconciliation facts are easy to miss and are worth stating explicitly.

1. **Candidate length is not fixed by the source.** The MB09 §6.1 approximation
   knows the true genome size `N`, but “known `N`” is a likelihood parameter, not
   a constraint that every candidate assembly have length `N`; §6.2 flows have no
   fixed-total-length constraint. The `|D| = G` row is therefore an *added*
   candidate restriction, not a consequence of the source. [source fact +
   reconciliation; see [`source-notes/medvedev-brudno-candidate-class.md`](source-notes/medvedev-brudno-candidate-class.md)]
2. **Strand/index convention changes which mode-2 witnesses apply.** The
   `AAATAT → AAAAAT` same-length §6.2 witness lives under the reverse-complement
   *molecule-class* indexing that §6.2 forces; under strict oriented single-strand
   indexing the observed `TAT` is absent from the competitor and the witness
   inverts. The two readings are kept separate. [source fact + verified
   computation; see [`source-notes/mb09-se61-index-orientation-resolution.md`](source-notes/mb09-se61-index-orientation-resolution.md)]

---

## 4. The candidate-length boundary inside mode 2

The final row of §3 is the reason the synthesis should not say “all materially
source-supported finite formulations are negative.”

Under strict oriented single-strand types, the §6.2 spelled-candidate class, and
the **same-length** restriction, the `main` result
[`source-notes/oriented-se62-rigidity-theorem.md`](source-notes/oriented-se62-rigidity-theorem.md)
proves:

> If some realization `R ∈ I_s`, then `spec_L(S)` is the unique positive integer
> circulation of total `G` on the truth's window-support graph `X_S`. Hence every
> same-length §6.2 spelled candidate has exactly the truth's spectrum, every
> `(spec_L, x)`-objective ratio is `1`, and no strict same-length counterexample
> exists for any `G`, `L`, or alphabet. Only the triple-repeat clause of `I_s` is
> used. [mathematical proof]

So on that slice **mode 2 is absent**: the truth is a maximizer (ties allowed;
uniqueness of the *sequence* additionally needs Shomorony's Eulerian-cycle
uniqueness, not just circulation uniqueness). Candidate length is exactly the
boundary: relaxing `|D| = G` restores a strict mode-2 failure even in the
oriented §6.2 setting (`AAATT → AAAATT`, last-but-one §3 row). The mechanism of
the relaxation is not exotic — it is the finite-sample frequency fitting
described in §2, now with the extra degree of freedom that the candidate's
length is free.

This is also where the necessity of the boundary shows up. The minimal
same-length **non-rigid** pair is `AAAAB / AABAB` (`G = 5, L = 2`): the truth
`AAAAB` has `spec_2 = {AA:3, AB:1, BA:1}`, the competitor `AABAB` has
`spec_2 = {AA:1, AB:2, BA:2}`, and once the observation is skewed the truth is
beaten. That truth carries a long Bresler triple repeat, so it is not
`I_s`-admissible; the triple-repeat clause is precisely what excludes it. (This
pair is *not* a §1-style tie: its two spectra differ, so the observation can in
principle distinguish them.) [mathematical proof + verified computation; see
[`source-notes/oriented-se62-rigidity-theorem.md`](source-notes/oriented-se62-rigidity-theorem.md) §5.1]

---

## 5. What this note does and does not settle

**Does.** It supplies the minimal, source-faithful **mode-1** opening
counterexample and proves the mode-1 tie is exact and infinite-data-persistent;
it exhibits the critical repeat-length/read-length mechanism; and it organizes
the existing `main` finite-data results into the intended two failure modes,
marking the one positive finite slice (oriented §6.2, same length) and the
candidate-length/strand axes that separate positive from negative.

**Does not.** It does not create the full issue-#46 synthesis, does not select
which MB09 objective the 2016 sentence intends, does not settle the
strand/equivalence/tie conventions, and does not formulate or prove the issue-#45
population-level repair. In particular, “mode 2 disappears in the population
limit” is here a description of the surviving candidate direction, not a proved
theorem; proving an appropriate version is issue #45.

---

## 6. Reproduce

```sh
python3 scripts/verify_structural_ambiguity_opening.py
```

The script checks: the witness's distinctness and identical `L = 1, L = 2`
spectra; the exact likelihood tie on representative samples; the `L = 3`
separation; the exhaustive `G ≤ 4` minimality and the `G = 5, L = 2` collision
with its unique equality pattern; and the maximal length-1 triple repeat together
with the impossibility of bridging it at `L = 2` (positive control at `L = 3`).

---

## 7. Epistemic status

| claim | status |
|---|---|
| Shomorony circular model, uniform error-free length-`L` reads, observable read multiset | source fact |
| Bridging requires `ℓ ≤ L - 2`; Bresler triple-repeat/maximality definitions | source fact (via [`bridging-source-semantics.md`](bridging-source-semantics.md)) |
| `AACAG`, `AAGAC` distinct circular words with equal `L = 1, 2` spectra | verified computation |
| Equal spectra ⇒ equal likelihood for every `(spec_L, x)`-objective and every sample | mathematical proof |
| The ambiguity is caused by a maximal length-1 triple repeat unbridgeable at `L = 2` | verified computation (definition from source) |
| Minimality: no `G ≤ 4, L ≥ 2` collision over DNA; minimal pair at `G = 5, L = 2`, unique up to relabeling/rotation | verified computation, exhaustive in scope |
| Reconciliation of the `main` finite-data witnesses into mode 1 / mode 2, with ratios and conventions | verified computation (per cited notes) + reconciliation |
| Oriented §6.2 same-length rigidity (no strict same-length counterexample under `I_s`) | mathematical proof (cited note) |
| Which MB09 objective the 2016 sentence intends; strand/equivalence/tie conventions; the infinite-read repair | open |

---

## 8. Sources

Primary. Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
*Bioinformatics* 32(17) (2016) i494–i502, §2–§5, DOI
`10.1093/bioinformatics/btw450`. Paul Medvedev, Michael Brudno, *Maximum
Likelihood Genome Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116,
§6.1–6.2, PMC3154397. Guy Bresler, Ma'ayan Bresler, David Tse, *Optimal
assembly for high throughput shotgun sequencing*, *BMC Bioinformatics*
14(Suppl 5):S18 (2013), DOI `10.1186/1471-2105-14-S5-S18`.

Repository cross-references (on `main`):
[`open-problem.md`](open-problem.md),
[`bridging-source-semantics.md`](bridging-source-semantics.md),
[`literature-status.md`](literature-status.md),
[`ml-formalization-contract.md`](ml-formalization-contract.md),
[`exact-variant-e-counterexample.md`](exact-variant-e-counterexample.md),
[`fixed-length-exact-counterexample.md`](fixed-length-exact-counterexample.md),
[`fixed-length-binomial-counterexample.md`](fixed-length-binomial-counterexample.md),
[`section62-same-length-bidirected-counterexample.md`](section62-same-length-bidirected-counterexample.md),
[`bridging-se62-flow-ml-counterexample.md`](bridging-se62-flow-ml-counterexample.md),
[`source-notes/oriented-se62-rigidity-theorem.md`](source-notes/oriented-se62-rigidity-theorem.md),
[`source-notes/medvedev-brudno-candidate-class.md`](source-notes/medvedev-brudno-candidate-class.md),
[`source-notes/mb09-se61-index-orientation-resolution.md`](source-notes/mb09-se61-index-orientation-resolution.md),
[`source-notes/same-length-witnesses-candidate-set-inclusion.md`](source-notes/same-length-witnesses-candidate-set-inclusion.md).
