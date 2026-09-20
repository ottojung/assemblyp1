# Adversarial source-fidelity audit: `AAATAT → AAAAAT` under Shomorony/Bresler

_Status: independent from-scratch recomputation + primary-source re-read,
2026-09-20, against `origin/main` at `8b2f0fc`. Every claim is labelled
**source fact**, **mathematical fact**, **verified computation**, **bounded
computation**, **repository fact**, or **open**. This note does not settle the
2016 open problem and does not re-litigate the §6.2 graph/flow feasibility of
the witness; it audits the witness against the **exact bridging hypotheses** of
the model that defines them._

_Reproduce:_

```sh
python3 scripts/audit_same_length_aaatat_source_fidelity.py   # exits non-zero on failure
```

---

## 0. Verdict

The instance

```text
truth S = AAATAT (G = 6)      competitor D = AAAAAT (|D| = 6, SAME LENGTH)
L = 3      realized starts (0, 0, 1, 3, 5)      n = 5 reads
```

**satisfies the exact Shomorony/Bresler bridging hypotheses `I_s`** — coverage,
every maximal triple repeat all-bridged, every interleaved pair bridged. The
counterexample therefore does **not** fail on the bridging side.

It fails on the **read-type side**, and this is the concrete source-fidelity
failure:

> The competitor only beats the truth after collapsing reverse complements into
> Medvedev–Brudno `k`-molecule classes (`TAT ~ ATA`). That collapse is **not** a
> read type of the model that defines `I_s`: Shomorony et al. (2016) §2 and
> Bresler et al. (2013) use **oriented** length-`L` substrings of a single
> circular strand. Under those oriented read types the observed read `TAT`
> (start `3`) is absent from `AAAAAT`, so the competitor cannot have generated
> the data and its likelihood is exactly `0`.

Hence the witness refutes no statement in the Shomorony/Bresler model. It refutes
only a **cross-source panel** — Shomorony/Bresler placement-based `I_s` grafted
onto a Medvedev–Brudno reverse-complement molecule likelihood — which no located
primary source instantiates. [source fact + verified computation]

---

## 1. Exact source definitions used

**Source fact, Shomorony et al. (2016), §2.** The model is a single circular
sequence `s` of length `G`; reads are drawn "from the set of length-`L`
substrings of `s`". Reverse complement appears only as §4.1 experimental
preprocessing ("we preprocess the set of reads to include each read and its
reverse complement"), which *adds* orientation nodes; it never identifies a read
with its reverse complement. The open question is stated at p. i501.

**Source fact, Bresler, Bresler & Tse (2013), repeat paragraph after Fig. 4**
(retrieved from `PMC3706340`). With `s_t^ℓ` the length-`ℓ` subsequence at `t`:

- a *repeat* of length `ℓ` is a pair of positions `t₁, t₂` with `s_{t₁}^ℓ =
  s_{t₂}^ℓ` that is *maximal*: `s(t₁−1) ≠ s(t₂−1)` and `s(t₁+ℓ) ≠ s(t₂+ℓ)`;
- a *triple repeat* is three positions `t₁,t₂,t₃` with equal windows such that
  `s(t₁−1)=s(t₂−1)=s(t₃−1)` does **not** hold and `s(t₁+ℓ)=s(t₂+ℓ)=s(t₃+ℓ)`
  does **not** hold;
- a *pair of repeats* is *interleaved* if `t₁ < t₂ < t₃ < t₄` or
  `t₂ < t₁ < t₄ < t₃`.

**Source fact, Bresler et al., Fig. 5 caption and preceding paragraph.**

> "A subsequence `s_t^ℓ` is bridged if and only if there exists at least one read
> which covers at least one base on both sides of the subsequence, i.e. the read
> arrives in the preceding length `L−ℓ−1` interval."

Equivalently, on a zero-based half-open lift, a read `[r, r+L)` bridges the copy
`[t, t+ℓ)` iff `r < t` and `t + ℓ < r + L`. A repeat/triple repeat is *bridged*
if at least one copy is bridged; a *triple repeat* is *all-bridged* if every
copy is bridged; an interleaved pair is bridged if at least one of its two
repeats is bridged. `I_s` = coverage ∧ all triple repeats all-bridged ∧ all
interleaved pairs bridged.

**Source fact, Bresler et al., "Discussions and extensions".** The paper's own
double-strand treatment does **not** quotient read types by reverse complement:
it defines `s` as the length-`2G` concatenation `u · ũ`, transforms each read
into itself and its reverse complement (so `2N` reads), and applies the
single-strand `I_s` to that length-`2G` `s`.

---

## 2. Independent recomputation of the instance

Read placements `(start, word)`:

```text
(0, AAA)  (0, AAA)  (1, AAT)  (3, TAT)  (5, TAA)
```

### 2.1 `I_s` (verified computation)

- **Coverage.** The reads cover `{0,1,2} ∪ {1,2,3} ∪ {3,4,5} ∪ {5,0,1} = all six
  positions`. Holds.
- **Maximal triple repeats.** The length-`1` `A` copies at `{0,1,2,4}` produce
  four maximal triples: `{0,1,2}`, `{0,1,4}`, `{0,2,4}`, `{1,2,4}`. Every copy
  `A@0, A@1, A@2, A@4` is bridged (witness reads `5, 0, 1, 3` respectively).
  There are no other triple repeats of any length. **All-bridged holds.**
- **Interleaved pair.** The only maximal repeat pairs are `A@{0,2}`, `A@{1,4}`
  (length `1`), `AA@{0,1}` (length `2`), and `ATA@{2,4}` (length `3`). The only
  four-start alternating combination is `A@{0,2}` with `A@{1,4}` (cyclic label
  pattern `0,1,0,1`). Both repeats are fully bridged, so the pair is bridged.
  The interleaving conjunct is **non-vacuous**. **Holds.**

`I_s` holds. This confirms the independent rechecks already recorded on
unmerged branches and the merged witness note. [verified computation]

### 2.2 Read-type spaces and the objective (verified computation)

| space | `x` | `d_S` | `d_D` | same-length exact ratio `L(D)/L(S)` |
|---|---|---|---|---|
| oriented (Shomorony/Bresler) | `AAA:2, AAT:1, TAT:1, TAA:1` | `AAA:1, AAT:1, ATA:2, TAT:1, TAA:1` | `AAA:3, AAT:1, ATA:1, TAA:1` | **`0`** |
| molecule (MB09) | `AAA:2, AAT:1, ATA:1, TAA:1` | `AAA:1, AAT:1, ATA:3, TAA:1` | `AAA:3, AAT:1, ATA:1, TAA:1` | **`3`** |

The oriented ratio is `0` because the observed oriented type `TAT` occurs in
`x` and in `d_S` but not in `d_D`. The molecule ratio is `3` and equals
`(d_D(AAA)/d_S(AAA))^{x_AAA} · (d_D(ATA)/d_S(ATA))^{x_ATA}` `= (3/1)^2·(1/3)`;
the extra copy `d_S(ATA)=3` comes **only** from merging `TAT` (one oriented
copy at start `3`) with `ATA` (two oriented copies at starts `2,4`).

---

## 3. Why this is a source-fidelity failure, stated precisely

The witness is sometimes cited as evidence that Shomorony/Bresler bridging does
not force the MB09 maximum-likelihood sequence to be the truth. The audit
shows the citation is **convention-mixed**:

1. **Hypothesis side** (`I_s`): Shomorony/Bresler, defined on oriented reads of
   one circular strand. The witness satisfies it. [source fact + verified
   computation]
2. **Conclusion side** (the competitor's improvement): requires MB09
   reverse-complement molecule classes, which are a *different* read-type space
   from the one in (1). Under (1)'s space the competitor has likelihood `0`, so
   the conclusion is not even violated. [source fact + verified computation]
3. **No single located source** combines (1) with (2). Bresler et al.'s own
   double-strand extension keeps oriented reads and maps the **hypothesis** to a
   length-`2G` sequence with `2N` reads; Shomorony et al.'s own second-strand
   handling adds orientation nodes rather than quotienting read types. The
   "`(revcomp, per-type)`" panel is a named cross-source construction, as
   `docs/source-notes/same-length-witnesses-candidate-set-inclusion.md` and the
   merged witness note already state. [source fact]

A uniform source-faithful statement must therefore either (i) use Shomorony's
oriented read types, in which case this witness is not a counterexample, or
(ii) use MB09 molecule read types together with MB09's own hypothesis-side
machinery, in which case `I_s` is not the hypothesis. The witness cannot serve
as a source-faithful refutation under either uniform convention.

**Secondary consistency observation (not load-bearing).** If one tries to make
the molecule likelihood uniform with Bresler's own double-strand extension, the
hypothesis becomes `I_s` on the length-`2G` concatenation with duplicated
reads. That concatenation is a *linear* representation (reads crossing the cut
between `u` and `ũ` have no contiguous image), so it does not faithfully
transport a circular witness; the instance's read at start `5` (`TAA`) crosses
the `u`-origin. The remap is therefore not a clean alternative convention, and
`I_s`-satisfiability of the `2G` sequence is not the condition the witness
verified. This is recorded as a modeling caveat, not as a refutation.
[mathematical fact + open]

---

## 4. What this does and does not establish

**Does.** Independent confirmation that the `AAATAT → AAAAAT` instance satisfies
the exact `I_s` bridging hypotheses; exact demonstration that its winning
competitor exists only under reverse-complement-collapsed molecule read types,
and has likelihood `0` under the oriented read types of the model that defines
`I_s`; and the precise reason the witness is not a source-faithful refutation.

**Does not.** It does not prove or refute the Shomorony et al. open question; it
does not address the §6.2 graph/flow feasibility of the witness (independently
confirmed elsewhere); it does not decide which MB09 layer the 2016 sentence
intends; and it does not search for a witness that satisfies `I_s` **and** the
conclusion under one uniform source convention.

---

## 5. Epistemic status

| Claim | Status |
|---|---|
| Shomorony 2016 model is oriented single-strand length-`L` reads; revcomp only as §4.1 preprocessing | source fact |
| Bresler 2013 repeat/triple/interleaved/bridging definitions as quoted | source fact (`PMC3706340`) |
| Bresler double-strand extension is a length-`2G` concatenation with duplicated reads, not a revcomp quotient | source fact |
| `AAATAT`, starts `(0,0,1,3,5)`, satisfies coverage + all-bridged maximal triple repeats + bridged interleaved pair | verified computation |
| Oriented read `TAT` is observed and is absent from `AAAAAT`; oriented ratio `0` | verified computation |
| Molecule-collapsed ratio is `3`, driven by `TAT ~ ATA` | verified computation |
| The witness is a cross-source panel, not a source-faithful refutation | source fact + mathematical argument |
| Whether any uniform-convention witness exists | open |

Primary sources: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116, §3.1, §4.1, §6.1–6.2,
`PMC3154397`; Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C.
Tse, *Information-optimal genome assembly via sparse read-overlap graphs*,
*Bioinformatics* 32(17) (2016) i494–i502, §2, §4.1, §5, DOI
`10.1093/bioinformatics/btw450`; Guy Bresler, Ma'ayan Bresler, David Tse,
*Optimal assembly for high throughput shotgun sequencing*, *BMC Bioinformatics*
14(Suppl 5):S18 (2013), `PMC3706340` (repeat/bridging definitions; Fig. 5;
"double strand" extension).
