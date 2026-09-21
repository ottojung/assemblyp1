# Adversarial audit: `AAATAT → AAAAAT` against the Shomorony/Bresler `I_s` antecedents

_Status: from-scratch exact recomputation + primary-source reading, 2026-09-21.
Not a Lean result, and it does not change any kernel-checked theorem. It audits
the **bridging** antecedents (not the MB09 §6.2 feasibility antecedent) of the
integrated same-length witness on `main`
([`section62-same-length-bidirected-counterexample.md`](section62-same-length-bidirected-counterexample.md),
PR #43, `AssemblyP1/SameLengthSection62Counterexample.lean`) under
source-faithful **single-strand** semantics._

_Reproduction: `python3 scripts/audit_aaatat_bridging_single_strand.py` (exact
integer/`Fraction` arithmetic, deterministic, non-zero exit on any failed
assertion)._

## 0. Verdict at a glance

| question | answer |
|---|---|
| Does `S = AAATAT` satisfy the published `I_s` under the strict source predicate? | **Yes** — coverage, all-bridged triple repeats, the single interleaved pair bridged [verified computation] |
| Is the integrated kernel certificate's `bridgedCopy` the published predicate? | **No** — it is the repository flank-coverage predicate, and it **over-reports** bridging on this very truth's length-3 `ATA@(2,4)` repeat [verified computation] |
| Does that over-report flip the `I_s` verdict for this witness? | **No** — every `I_s`-constrained copy is length-1, where the two predicates agree [verified computation] |
| Is `AAATAT → AAAAAT` a counterexample under source-faithful single-strand semantics? | **No** — the competitor `AAAAAT` has **zero** likelihood (the observed oriented read `TAT` is absent); the reported ratios `3` / `5` require reverse-complement-collapsed read types [verified computation] |

## 1. The published antecedents (source fact)

Bresler, Bresler & Tse (2013), PMC3706340, "Lower bounds" + "Towards optimal
assembly", exact wording re-retrieved 2026-09-21:

- a **repeat** of length `ℓ` at starts `t₁,t₂` requires equal windows and
  maximality: `s(t₁−1) ≠ s(t₂−1)` and `s(t₁+ℓ) ≠ s(t₂+ℓ)`;
- a **triple repeat** of length `ℓ` at `t₁,t₂,t₃` requires equal windows and
  *not all* of the `s(tᵢ−1)` equal and *not all* of the `s(tᵢ+ℓ)` equal;
- a pair of repeats is **interleaved** iff `t₁ < t₂ < t₃ < t₄` or
  `t₂ < t₁ < t₄ < t₃` (four distinct starts);
- a copy at `t` of length `ℓ` is **bridged** iff some read start lies in the
  preceding interval of length `L−ℓ−1`: `r = t−d`, `1 ≤ d ≤ L−ℓ−1`;
  if `L−ℓ−1 ≤ 0` the copy is **unbridgeable**;
- **Theorem 6** (MULTIBRIDGING, the `I_s` of Shomorony et al. Eq. (1)):
  all interleaved repeats bridged, all triple repeats all-bridged, sequence
  covered.

This matches [`bridging-source-semantics.md`](bridging-source-semantics.md) and
[`copy-bridging-predicate-correction.md`](copy-bridging-predicate-correction.md).

## 2. Independent single-strand recomputation (`S = AAATAT`, `L = 3`)

### 2.1 Maximal repeats

| length `ℓ` | word | starts | maximal on both sides |
|---|---|---|---|
| 1 | `A` | `0, 2` | yes |
| 1 | `A` | `1, 4` | yes |
| 2 | `AA` | `0, 1` | yes (`s(2)=A ≠ s(3)=T`) |
| 3 | `ATA` | `2, 4` | yes |

The length-2 `AA@(0,1)` repeat is **new** relative to the integrated note's prose
(which lists only the `A` repeats and the length-3 `ATA` repeat). It is a
genuine Bresler repeat, not a triple and not interleaved, so it does not enter
`I_s`.

### 2.2 Triple repeats and interleaving

Exactly four triple repeats, all length-1 `A`: `A@(0,1,2)`, `A@(0,1,4)`,
`A@(0,2,4)`, `A@(1,2,4)`. Exactly one interleaved pair:
`A@(0,2) × A@(1,4)` (starts `0 < 1 < 2 < 4`). The length-3 `ATA@(2,4)` shares a
start with each `A` repeat and so is not interleaved with anything.

### 2.3 Bridging

For `ℓ = 1` the bridge start is exactly `t−1` (since `L−ℓ−1 = 1`):

| copy | read start that bridges it |
|---|---|
| `A@0` | `5` |
| `A@2` | `1` |
| `A@1` | `0` |
| `A@4` | `3` |

All four `A` copies are bridged, so every `A` triple is all-bridged and the
interleaved pair is bridged. The reads `(0,0,1,3,5)` cover all six positions, so
**`I_s` holds under the strict source predicate** [verified computation]. This
confirms the integrated note's verdict and corrects its earlier (already-fixed)
interleaving prose.

The length-2 `AA@(0,1)` and length-3 `ATA@(2,4)` copies are **unbridgeable**
(`L−ℓ−1 ≤ 0`). They are neither triple repeats nor part of the interleaved pair,
so `I_s` imposes no obligation on them. This is the exact boundary between
`I_s`/Theorem 6 (holds) and Bresler's GREEDY Theorem 2 ("**every** repeat
bridged", which fails here) — the same boundary already recorded for
`AAABB → AAAAB`.

## 3. Mismatch: the integrated kernel certificate uses the flank predicate

`AssemblyP1/SameLengthSection62Counterexample.lean:208` defines

```text
bridgedCopy e t := readStarts.any (fun r => inRead r (t + 5) && inRead r (t + e))
```

i.e. a copy is "bridged" iff some read covers **both** flanking positions
`(t−1) mod 6` and `(t+e) mod 6`. That is the repository flank-coverage test, not
the source preceding-interval test. On this truth the two disagree:

| copy | strict source | repo flank (Lean `bridgedCopy`) |
|---|---|---|
| `A@0, A@1, A@2, A@4` (`ℓ=1`) | bridged (`r = t−1`) | bridged |
| `AA@0, AA@1` (`ℓ=2`) | unbridgeable | not bridged |
| `ATA@2` (`ℓ=3`) | **unbridgeable** | **"bridged" by read `5`** (`{5,0,1}`) |
| `ATA@4` (`ℓ=3`) | **unbridgeable** | **"bridged" by read `1`** (`{1,2,3}`) |

The over-report happens exactly when `L ≥ G−ℓ` and the read reaches the two
flanks through the complementary arc without containing the copy. The
disagreements are `(ℓ,t) = (3,2), (3,4)`; both are demonstrated in the audit
script.

**Consequence.** The kernel-checked `SourceCertificate` is a `Bool` equation
whose `bridgedCopy` is the flank test. Its conclusion is still correct, because
every copy actually constrained by `tripleAllBridgedB` and `interleavedB` has
`ℓ = 1`, and there strict and flank agree. But the certificate does **not**, as
written, establish the published Bresler predicate; it establishes a strictly
weaker predicate that happens to agree on the constrained copies of this
instance. This contradicts
[`copy-bridging-predicate-correction.md`](copy-bridging-predicate-correction.md)
§5's row claiming the kernel witnesses use the strict condition: that row covers
the `AAABB`/`AAACC` files (which do use `(r+1) mod G = t`), not the §6.2 file.
The §6.2 file should either import the strict relation or rename `bridgedCopy` to
name the flank predicate.

## 4. Mismatch: the witness is not single-strand

Under source-faithful single-strand semantics the observed reads are the oriented
windows of `AAATAT` at starts `(0,0,1,3,5)`:

```text
x_ss = { AAA:2, AAT:1, TAT:1, TAA:1 }
d_S  = { AAA:1, AAT:1, ATA:2, TAA:1, TAT:1 }
d_D  = { AAA:3, AAT:1, ATA:1, TAA:1 }        (competitor AAAAAT)
```

`AAAAAT` contains **no** `TAT`, so both the exact same-length product
`∏ d_D(w)^{x_w}` and the literal §6.1 product of binomial marginals are **exactly
zero** for the competitor (the marginal for an observed type with `d = 0` is
`0^{x}`). The truth's likelihood is positive. Hence under single-strand
semantics the competitor is *worse*, not better, and the pair refutes nothing
[verified computation].

The documented ratios `3` (exact) and `5` (§6.1) require collapsing
`TAT ∼ ATA` into one MB09 `k`-molecule class, which turns `x` into
`{AAA:2, AAT:1, ATA:1, TAA:1}` and `d_S` into `{AAA:1, AAT:1, ATA:3, TAA:1}`.
That collapse is MB09's read-type convention; it is **not** the convention of
the bridging source Bresler et al. (whose own double-strand extension maps to a
length-`2G` concatenation with duplicated reads, not a read-type quotient) nor
of Shomorony et al. (single-strand, cyclic-shift-only). So the witness is a
**cross-source panel artifact**: single-strand `I_s` on the hypothesis side,
MB09 molecule classes plus the per-vertex lower bound on the candidate side.
This was already recorded in
[`source-notes/reverse-complement-strand-convention.md`](source-notes/reverse-complement-strand-convention.md)
§5; this audit makes the single-strand likelihood collapse exact for this
instance.

## 5. Materially new exact results

1. The complete single-strand maximal-repeat inventory of `AAATAT` includes the
   length-2 `AA@(0,1)` repeat, unbridgeable at `L = 3`; the integrated prose
   omitted it.
2. The strict source predicate and the repository flank predicate
   (`bridgedCopy`) **differ on this truth**, at `ATA@(2,4)`, because
   `L = 3 ≥ G − ℓ`. The on-`main` §6.2 certificate therefore does not establish
   the source predicate by itself; the prior correction note's "unaffected"
   claim does not cover this file.
3. `I_s` nevertheless holds for `AAATAT` under the strict predicate, so the
   counterexample's bridging antecedent is sound; only the certificate's
   predicate is not source-faithful.
4. Under single-strand semantics the competitor `AAAAAT` has exactly zero
   likelihood under both same-length objectives; the `3`/`5` ratios are
   artifacts of reverse-complement class collapse.

## 6. What this changes and what it does not

**Changes.** The provenance of the §6.2 certificate: its `bridgedCopy` is not
the published bridging predicate, and the claim that all kernel witnesses use
the strict condition is too broad. Recorded here and reproducible.

**Does not change.** The kernel-checked theorem
`samelength_se62_counterexample` remains true; its `SourceCertificate` is a
kernel-checked `Bool` fact. The witness remains a valid counterexample to the
same-length **cross-source** statement (MB09 revcomp-collapsed molecule types +
per-vertex lower bound + single-strand `I_s`). Nothing here addresses the MB09
§6.2 graph-feasibility antecedent, the per-occurrence strengthening, or the
source ambiguity over which object Shomorony et al. (2016) intends.

## 7. Epistemic status

| claim | status |
|---|---|
| Bresler repeat/triple/interleaved/bridging definitions | **source fact** (PMC3706340) |
| `AAATAT` maximal repeats `{A@(0,2), A@(1,4), AA@(0,1), ATA@(2,4)}` | **verified computation** |
| Four length-1 `A` triple repeats; one interleaved pair `A@(0,2)×A@(1,4)` | **verified computation** |
| `I_s` holds under the strict source predicate | **verified computation** |
| Lean `SameLengthSection62Counterexample.bridgedCopy` is the flank predicate | **repository fact** (source read) |
| Strict vs flank disagree at `ATA@(2,4)`; no `I_s`-constrained copy is affected | **verified computation** |
| Competitor has zero single-strand likelihood; `3`/`5` need revcomp collapse | **verified computation** |
| Which object the 2016 open question intends | **unresolved source ambiguity** |

## 8. Reproduction

```sh
python3 scripts/audit_aaatat_bridging_single_strand.py
```

Primary sources: Guy Bresler, Ma'ayan Bresler, David Tse, *Optimal assembly for
high throughput shotgun sequencing*, BMC Bioinformatics 14(Suppl 5):S18 (2013),
PMC3706340; Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
Bioinformatics 32(17) (2016) i494–i502, Eq. (1); Paul Medvedev, Michael Brudno,
*Maximum Likelihood Genome Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116,
§6.1–6.2.
