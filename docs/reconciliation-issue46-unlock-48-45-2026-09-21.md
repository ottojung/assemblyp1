# Reconciliation: does #48's finite negative evidence unlock #45's population repair?

_Status: independent reconciliation note for issue #46 (master synthesis), written
against `origin/main` at `f60ca5f`. It does **not** edit the synthesis, because
two of the dependencies it identifies are unresolved. It compares the finite
negative packets of issue #48 with the population packets prepared for issue #45
and states, proposition by proposition, what is settled, what is objective- or
universe-conditional, and what the synthesis must not yet assert._

_Every claim is labelled **source fact**, **mathematical proof**, **verified
computation**, **kernel-checked**, or **open**. Bounded searches are evidence for
the tested ranges only; they are not proofs of absence._

_Reproduction of the new computations in this note:
`python3 scripts/verify_reconciliation_48_45.py` (exact `fractions.Fraction`,
deterministic, non-zero exit on any failed assertion)._

---

## 0. Question and answer

**Question.** Is the finite negative evidence produced under issue #48 (intrinsic
candidate checks fail to restore finite-data ML) strong enough to unlock issue
#45 (population / infinite-read repair)? And if so, what exactly is the failure
mechanism and where is the model boundary?

**Answer (summary).**

- The finite *phenomenon* is real and independent: a finite sample can strictly
  favour a wrong candidate even when the truth satisfies the source `I_s`
  condition and every candidate satisfies the strongest intrinsic check.
  [verified computation; #48]
- The mechanism is **not** structural repeat non-identifiability. It is
  **cross-spectrum fitting under candidate-length shrinkage**: the competitor
  has a different length-dependent support, and the candidate-length-normalized
  multinomial rewards the shorter candidate by a factor `(G/|D|)^N`. At the
  population law this factor and the support mismatch both vanish/decay.
  [mathematical proof for the objective decomposition; verified computation for
  the witnesses]
- **Unlock verdict: guarded yes.** #45's literal entry condition ("finite
  sampled read multiplicities can still favor the wrong candidate") is met for
  the sequence-level intrinsic model and for the free-length §6.2 spelled-candidate
  (`FLOW`) model **under the candidate-length-normalized objective**. It is
  **not** met unconditionally across objectives: under the fixed-`N`
  §6.1 objective that drops zero-count factors, the identified `FLOW` finite
  failures collapse to ties, and primitive/`STRONG` candidates provably never
  beat the truth. [mathematical proof + verified computation]
- Two dependencies are unresolved: (D1) which finite objective the source
  sentence intends, and (D2) whether the repaired candidate universe is
  sequence-level (`SEQ`) or §6.2 spelled (`FLOW`). A third (D3, the oriented
  versus molecule-class source fork) decides whether the population repair can
  work at all. **The synthesis must therefore not be edited yet.**

---

## 1. Vocabulary (aligned across the packets)

- `OR` / `MOL` — oriented single-strand read types / reverse-complement
  molecule classes. [source fact]
- `SEQ` — circular candidate words (support-contained in the observations);
  `FLOW` — §6.2 spelled candidates with `supp(spec_L(D)) = supp(x)`. [repository
  derivation]
- `FIXED` — every candidate has length `|D| = G`; `FREE` — any length. `N` is a
  fixed-`N` binomial denominator and is **not** a length constraint. [source
  fact]
- `STRONG` (P1) — no `(L-1)`-mer of `D` occurs twice. `WEAK` (P2) — no long
  triple repeat and no long interleaved-repeat pair, i.e. the candidate-intrinsic
  shadow of `I_s`. `WEAK` is the weakest intrinsic predicate that admits every
  `I_s`-feasible truth; `STRONG` excludes some `I_s`-feasible truths. [source
  fact + repository derivation]
- objectives: `PO` = candidate-intrinsic exact multinomial with per-candidate
  length `N(D)=|D|`; `FN` = fixed-`N` §6.1 product of binomial marginals
  **with** the zero-count factors; `FN0` = fixed-`N` ratio with zero-count
  factors dropped (the objective used for the ratio tables). [source fact for
  `FN`; modeling decision for `PO`/`FN0`]

---

## 2. Normalized propositions compared

**N1 (issue #48 headline; STRONG, FREE, `SEQ`).** `S = AABBC`, `D = AABC`,
`L = 3`, `R = (0,3)`, `x = {AAB:1, BCA:1}`. Both primitive and `STRONG`,
`S` satisfies `I_s`; `PO` ratio `25/16 > 1`. [verified computation; independently
reproduced here]

**N2 (issue #48 minimal coherent; WEAK truth, FREE, `SEQ`).** `S = AABB`,
`D = AAB`, `L = 3`, `R = (0,3)`, `x = {AAB:1, BAA:1}`; both primitive and
`STRONG`; `PO` ratio `16/9`. [verified computation]

**N3 (issue #48 minimal WEAK-universe; FREE).** `S = AAB`, `D = AB`, `L = 2`,
`R = (1,2)`, `x = {AB:1, BA:1}`; `S` primitive + `WEAK` + `I_s`-feasible, `D`
primitive + `WEAK` + `STRONG`; `PO` ratio `9/4`. [verified computation]

**N4 (issue #48 FIXED; WEAK, `SEQ`).** `S = AABBC`, `D = ABABC`, `L = 2`,
`R = (1,3,4)`, `x = {AB:1, BC:1, CA:1}`; both primitive + `WEAK`; ratio `2`
under both `PO` and `FN0`. [verified computation]

**N5 (oriented §6.2 rigidity; `FLOW`, `FIXED`).** Under `OR + FLOW + FIXED +
I_s(S,R)`, `spec_L(S)` is the unique positive circulation of total `G`, so every
same-length `FLOW` candidate has the truth spectrum and ties it under any
`(spec_L, x)` objective. [mathematical proof; `origin/main` `cf6c357`]

**N6 (fixed-length `STRONG` maximizer; `SEQ`, `FIXED`).** Every `STRONG`
candidate has `d_D(w) ∈ {0,1}`; since every observed type has `d_S(w) ≥ 1`, the
`FN0` ratio is `≤ 1` on the observed support and the truth is a maximizer (weak
schema). Its cost is truth-compatibility: `STRONG` excludes `I_s`-feasible
truths such as `AAATT` (`L=3`). [mathematical proof]

**P1 (population ML; any length).** For `x = c·d_S`, every candidate has
`ℓ_pop(D) ≤ ℓ_pop(S)`, with equality iff `d_D = (|D|/G) d_S` on `supp(d_S)`.
[mathematical proof; #45 comments; independently re-derived in the population
packet]

**P2 (population scale rigidity, cross-length).** For primitive `TRF`/`WEAK`
`S,T` with `d_T = c·d_S` (rational `c>0`), necessarily `c = 1`. The equal-length
case `c = 1` is the classical circular `q`-gram characterization. [mathematical
proof for `c=1` cross-length; **conditional/open** for the equal-length step,
pending the circular Ukkonen–Pevzner/Çelikkanat statement and a kernel check]

**P3 (molecule-panel boundary).** On `MOL`, `S = AACAGT` and `T = AACTGT`
(`L = 3`) are primitive + `STRONG`, have identical normalized molecule spectra,
and are dihedrally inequivalent. [verified computation]

---

## 3. The independent findings this note adds

**F1 — the `PO`/`FN0` split is load-bearing, and the `FN0` part is a theorem.**
[mathematical proof + verified computation]

For a candidate `D` with `d_D(w) = 1` on every observed type (`w ∈ supp(x)`) —
in particular any `STRONG` candidate whose support contains `supp(x)` — the
zero-count-dropped fixed-`N` ratio is

```text
∏_{w ∈ supp(x)} (d_D(w)/d_S(w))^{x_w} ≤ 1,
```

because `d_D(w) = 1 ≤ d_S(w)`. Hence under `FN0` the truth is always a
maximizer for that candidate class, at **any** candidate length; free length
cannot create a strict `FN0` failure for `STRONG` candidates. The entire
`25/16` of N1 (and the `9/4` of N3) is carried by the `PO` factor
`(G/|D|)^N`: removing it turns both into exact ties (`1`). [verified computation]

**F2 — the finite witnesses that pass the intrinsic checks are not `FLOW`, but a
`FLOW` witness does exist, and it is also objective-dependent.**
[verified computation, bounded]

- N1/N2/N4 have `supp(D) ≠ supp(x)` (and `supp(D) ≠ supp(S)`), so they refute a
  **sequence-level** intrinsic repair, not the §6.2 `FLOW` repair. This is the
  conflation already flagged for the synthesis as `C4`.
- However N3 **does** satisfy `supp(D) = supp(x)`, so `D = AB` is a legal same-
  or free-length §6.2 spelled candidate. It is a genuine `OR + FLOW + FREE +
  WEAK` finite counterexample under `PO` (ratio `9/4`), with an `I_s`-feasible
  truth.
- Bounded exact search over `{A,B}`/`{A,B,C}`, `G ≤ 6`, `L ≤ 3`, `N ≤ 4`,
  candidate primitive + `WEAK`/`STRONG`, `supp(D) = supp(x)`: there are `PO`
  strict hits (smallest N3), but **zero** strict hits under `FN0`. If the truth
  is additionally required `STRONG`, there are no `FLOW` hits under either
  objective (consistent with F1 and the simple-cycle argument of the population
  packet). This is finite evidence, not a proof.

**F3 — the population ML-maximizer statement is automatic, so #45 is an
identifiability/scale repair, not an ML rescue.** P1 holds with no bridging,
primitivity, or admissibility assumption. P1 says that #45's only nontrivial
content is P2 plus the panel's equivalence notion. [mathematical proof]

---

## 4. Proposition-level reconciliation

| proposition | status after reconciliation |
|---|---|
| #48 finite negative for `SEQ` intrinsic model | **accepted** (`N1`–`N4`), with objective tag: `N2`/`N4` also strict under `FN0`; `N1`/`N3` are `PO`-only |
| #48 finite negative for `FLOW` intrinsic model | **accepted for `PO`** (`N3`, `F2`); **not established for `FN0`** (bounded zero hits); **false/absent when truth is `STRONG`** (`F1` simple-cycle argument) |
| "the finite failures are finite-sampling noise that population removes" | **partly refuted as stated**: the removed factor is the candidate-length normalization `(G/|D|)^N`, an objective/model term, not a sampling fluctuation; population also removes the support mismatch. Under `FN0` no strict finite failure was found in the tested `FLOW` scope |
| #45 entry condition | **met under `PO`** (and for the `SEQ` model); **guarded under `FN0`** |
| P1 (population truth is a maximizer) | **accepted**, but it is trivial and independent of #48 |
| P2 cross-length `c=1` | **accepted** (primitive + `TRF` suffices) |
| P2 same-length `c=1` | **open/conditional** on the classical circular `q`-gram characterization; must not be presented as proved |
| P3 molecule panel | **accepted**; population uniqueness is panel-conditional |
| #45 as "primary repair" | **not accepted**; population is an identifiability characterization, not an ML rescue |

No substantive contradiction was found between the packets after normalizing
universe, length, objective, and panel. The disagreements are **assumption
mismatches** (`SEQ` vs `FLOW`, `PO` vs `FN0`, `OR` vs `MOL`) and one **strength
difference** (population ML maximality vs the stronger uniqueness claim).

---

## 5. Model boundary (exact)

The truth value of "finite intrinsic bridging→ML holds" is a function of:

1. **universe** — `SEQ` (negative) vs `FLOW`/§6.2 spelled (negative under `PO`,
   not under `FN0` in bounded scope);
2. **length** — `FIXED` (positive on `OR+FLOW+I_s`, P-N5) vs `FREE` (where the
   `PO` failures live);
3. **objective** — `PO` (strict failures) vs `FN0` (no strict `FLOW` failure
   found; theorem for `STRONG`) vs `FN` (literal product of binomial marginals,
   distinct kernel-checked same-length `SEQ` failures);
4. **panel** — `OR` (positive population identifiability) vs `MOL` (population
   uniqueness fails even for primitive `STRONG`, P3);
5. **predicate** — `STRONG` (excludes `I_s`-feasible truths, so cannot be the
   truth-side repair) vs `WEAK` (the source-compatible one).

The clean finite **positive** rows are `OR + FLOW + FIXED + I_s` (N5), a
tie/spectrum-rigidity theorem rather than word uniqueness, and `SEQ + FIXED +
STRONG` (N6), which buys maximality at the cost of truth-compatibility (`STRONG`
excludes some `I_s`-feasible truths). The clean finite **negative** rows for the
*intrinsic repair* are `SEQ` (both objectives) and `OR + FLOW + FREE + WEAK`
under `PO` only.

---

## 6. Unresolved dependencies (why the synthesis is not edited)

- **D1 — objective.** Which finite objective the Shomorony→MB09 sentence intends:
  `PO`, `FN0`, or the literal `FN` product. This decides whether the `FLOW`
  finite failure exists at all (F1/F2). [open]
- **D2 — universe.** Whether #48's intrinsic repair targets `SEQ` candidates or
  the §6.2 `FLOW` candidates of the theorem it is repairing. The strongest
  intrinsic witnesses are `SEQ`; the repaired positive theorem is `FLOW`.
  [open]
- **D3 — source panel fork.** Whether the 2016 sentence intends the oriented
  Shomorony observation model or MB09's reverse-complement molecule §6.2 object
  (the `q_*` pushforward). If `MOL`, P3 shows the population repair cannot
  deliver uniqueness. [open]
- **D4 — classical equal-length step.** The same-length `c=1` population step is
  the circular `q`-gram characterization (`Conjecture 4`); it is not
  kernel-checked and its circular indexing is unpinned. [open]
- **D5 — source-liveness of `FIXED`.** Whether `oriented + same-length + §6.2`
  is source-selected (then the finite positive theorem belongs in the main
  story) or an added restriction (then #45 may be needed). [open]

---

## 7. Next-step recommendation

1. **Do not merge or edit the #46 synthesis yet.** Add the `PO`/`FN0`/`FN`
   objective axis and the `SEQ`/`FLOW` universe axis to its row schema; the
   current rows conflate them.
2. **Restate #48's conclusion** as "decisive for the sequence-level intrinsic
   model under any objective; decisive for `FLOW` only under the
   candidate-length-normalized objective; under `FN0` the tested `FLOW` counter-
   examples tie and `STRONG` candidates provably never win." Reclassify the
   earlier "strongest intrinsic repair fails" wording accordingly.
3. **Record F1** (zero-count-dropped fixed-`N` no-beat lemma for `STRONG`
   candidates at free length) as a positive finite repaired result, and F2's
   `FLOW` witness (`S=AAB`, `D=AB`, ratio `9/4`) as the objective-conditional
   counterexample.
4. **For #45, split the deliverable into two layers:** (i) the population ML
   lemma P1 (proved, trivial, no hypotheses); (ii) the scale-rigidity/
   identifiability theorem (cross-length proved; same-length conditional). Do
   not call #45 a rescue of ML maximality.
5. **Resolve D3 before any population claim is promoted.** A population
   uniqueness theorem is `OR`-only; the `MOL` panel has an explicit primitive
   `STRONG` collision (P3).
6. **Kernel-check or pinned-source the equal-length `q`-gram step (D4)** before
   the synthesis states a word-uniqueness conclusion.

---

## 8. Ready-to-post issue comment (issue #46)

> **Reconciliation of #48's finite negative evidence against the #45 unlock
> condition (independent; no synthesis edits).**
>
> The finite failures are real, but they are **objective-conditional**, and the
> objective axis is missing from the current rows.
>
> 1. All currently recorded intrinsic finite witnesses that pass `STRONG`/`WEAK`
>    (`AABBC→AABC` `25/16`, `AABB→AAB` `16/9`, `AABBC→ABABC` `2`) have
>    `supp(D) ≠ supp(x)`: they are **sequence-level (`SEQ`)**, not §6.2 `FLOW`.
>    The §6.2 positive theorem they are meant to repair is `FLOW`. — `C4`
>    confirmed by independent computation.
> 2. A `FLOW`-compatible free-length witness does exist: `S=AAB`, `D=AB`,
>    `L=2`, `R=(1,2)`, `x={AB,BA}`, `supp(D)=supp(x)`, truth primitive+`WEAK`+
>    `I_s`, candidates primitive+`WEAK`/`STRONG`, ratio `9/4`. So #45's literal
>    entry condition is met under the candidate-length-normalized objective.
> 3. But the `9/4` (and the `25/16`) is carried entirely by the
>    candidate-length factor `(G/|D|)^N`. Under the fixed-`N` §6.1 ratio with
>    zero-count factors dropped, every `FLOW` candidate with `d_D=1` on the
>    observed support — in particular every `STRONG` candidate — has ratio
>    `∏ d_D/d_S^{x} ≤ 1`, so the truth is always a maximizer at **any** length.
>    Bounded exact search (`{A,B}`/`{A,B,C}`, `G≤6`, `L≤3`, `N≤4`) found **zero**
>    strict `FLOW` `FN0` counterexamples.
> 4. Population side: the ML-maximizer statement is automatic (KL), so #45's
>    only content is normalized-spectrum identifiability. Cross-length `c=1` is
>    proved; same-length `c=1` is the classical circular `q`-gram
>    characterization and is **not** yet proved/kernel-checked; and the molecule
>    panel has an explicit primitive-`STRONG` population collision
>    (`AACAGT`/`AACTGT`).
>
> **Verdict.** Guarded unlock: proceed with #45 only after fixing (D1) the finite
> objective and (D2) the candidate universe, and treat the population result as
> an `OR`-panel identifiability theorem, not an ML rescue. Do not edit the
> synthesis until D1–D3 are settled; add the objective axis (`PO`/`FN0`/`FN`) to
> the result matrix.
>
> **Recommended concrete steps.** Restate #48 as objective-conditional; record
> the `FN0` no-beat lemma for `STRONG` candidates; split #45 into the trivial ML
> lemma plus the conditional scale-rigidity theorem; resolve the `OR`/`MOL`
> source fork before promoting any population uniqueness claim.

---

## 9. Epistemic summary

| claim | status | basis |
|---|---|---|
| N1–N4 finite witnesses and ratios | **verified computation** | §2; independent repro, `scripts/verify_reconciliation_48_45.py` |
| N1/N2/N4 are `SEQ` (support-unequal) | **verified computation** | §3 F2 |
| N3 is `FLOW` (support-equal) | **verified computation** | §3 F2 |
| N6 fixed-length `STRONG` maximizer (N6) | **mathematical proof** | §2 N6 |
| `FN0` no-beat for `STRONG`/support-contained-at-1 candidates | **mathematical proof** | §3 F1 |
| `FN0` zero strict `FLOW` hits, bounded scope | **verified computation, bounded** | §3 F2 |
| Population ML maximality is automatic (P1) | **mathematical proof** | population packet; §3 F3 |
| Cross-length `c=1` (Theorem P) | **mathematical proof** | population packet |
| Same-length `c=1` (circular `q`-gram) | **open / conditional** | population packet §5 |
| `MOL` panel collision | **verified computation** | population packet §7 |
| D1–D5 dependencies | **open** | §6 |
