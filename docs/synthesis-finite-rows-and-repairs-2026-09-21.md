# Synthesis stress-test: rigorous finite rows, hidden conflations, and what #48 must establish

_Status: agent-authored reconciliation note for issue #46 (the master synthesis),
2026-09-21, written against `origin/main` at `f60ca5f`. It is a stress-test of the
synthesis architecture, not a settlement of the published open problem. It does
not re-prove the rigidity theorem; it fixes the vocabulary needed to compare the
existing rows, states which finite rows are rigorous and with what scope, records
the conflations that currently make the story ambiguous, and isolates the exact
obligation left to issue #48._

_Every claim is labelled **source fact**, **mathematical proof**, **repository
derivation**, **verified computation**, **interpretation**, or **open**. Paths
that are on `origin/main` are links; artifacts that currently live only on a
branch or in the working tree are named in `code` and marked "(branch/working
tree, not on `origin/main`)"._

_Reproduction of the new computations in this note:
`python3 scripts/verify_synthesis_rows.py` (exact `fractions.Fraction`, exhaustive
in the stated scopes, non-zero exit on any failed assertion)._

---

## 0. Why this note exists

Issues #46/#48/#45 form a three-part architecture:

- **#46** is the master synthesis: naive ML intuition → structural repeat
  obstruction → finite boundary-conditioned ML → a strong positive same-length
  theorem alongside negative neighbours → relax the true-length axiom (#48) →
  only if finite sampling still fails, pass to a population model (#45).
- **#48** is the model/axiom repair: replace privileged knowledge of the true
  target length with intrinsic, candidate-checkable conditions.
- **#45** is the data-regime repair: remove finite-sample fluctuations.

The architecture is sound as a *narrative*, but the current durable record does
not yet separate five axes sharply enough for the rows to compose: (i) the
external likelihood parameter `N` versus a candidate-length restriction
`|D| = G`; (ii) the candidate *universe* (sequence-level versus §6.2 spelled
support-equality); (iii) three inequivalent "structural admissibility"
predicates; (iv) the strand convention; and (v) maximizer versus spectrum-tie
versus word-uniqueness. This note separates them and states what follows.

---

## 1. Vocabulary fixed (so the rows can be compared)

Let `S` be a circular truth of length `G = |S|`, `L` a read length, and
`d_S(w)` the number of cyclic occurrences of the length-`L` word `w`.

**Read-type conventions.**

- `OR` — **oriented single-strand**: read types are the oriented length-`L`
  windows, no reverse-complement collapse. This is Shomorony et al. (2016)
  §2 and Bresler et al. (2013). [source fact]
- `MOL` — **reverse-complement molecule classes**: a read type is an unordered
  `{w, rc(w)}` pair. This is Medvedev–Brudno (2009) §1.1/§3.1. [source fact]

**Candidate universes.**

- `SEQ` — circular words of any composition, support-contained in the observed
  types.
- `SEQ_supp=` — sequence-level words whose `L`-mer support equals the observed
  support.
- `FLOW` — §6.2 spelled candidates: a spelled circular word that walks only on
  observed read vertices, with the source per-vertex lower bound `1`, i.e.
  `supp(spec_L(D)) = supp(x)`. [source fact + repository derivation; see the
  rigidity note §1 and `docs/source-notes/mb09-se61-index-orientation-resolution.md`]

**Length conventions.** `FIXED` means `|D| = G` for every candidate; `FREE`
means any `|D|`. `N` (a fixed-`N` binomial denominator) is *not* a length
constraint: it is a likelihood parameter. [source fact; MB09 §6.1 approximation
and §8.2]

**Candidate-intrinsic predicates.** For a circular word `D` and read length `L`:

- `P1` / **STRONG**: no length-`(L-1)` window occurs twice in `D`.
- `P2` / **WEAK**: no Bresler triple repeat of `D` has length `>= L-1`, and no
  interleaved maximal-repeat pair of `D` has both constituents of length
  `>= L-1`.
- `I_s(S,R)`: the truth-relative Shomorony condition on `(S, realized reads R)`.

**Facts used below.**

- **Fact 1 (repository derivation).** With the full read set, `S` admits some
  `R in I_s` iff `P2(S)` holds. [repository derivation from the Bresler
  bridging predicate; `mathematics/bridging-and-spectrum-uniqueness.md` §1
  (branch/working tree, not on `origin/main`)]
- **Fact 2 (mathematical proof).** `P1 => P2`, not conversely: `AABAB`
  (`G = 5`, `L = 3`) is `P2`-admissible but not `P1` (its `(L-1)`-mer `AB`
  occurs twice). [mathematical proof + verified computation, `scripts/verify_synthesis_rows.py`]
- **Fact 3 (mathematical proof).** `P1` is equivalent to "every length-`L`
  window of `D` occurs at most once". [rigidity note, Lemma 1]

---

## 2. Which finite rows are rigorous

### 2.1 Positive rows

**P-R1 — same-length oriented §6.2 rigidity (a *tie* theorem).**
[mathematical proof; `docs/source-notes/oriented-se62-rigidity-theorem.md`,
`origin/main` `cf6c357`]

Under `OR` + `FLOW` + `FIXED` + `I_s(S,R)`: `spec_L(S)` is the unique positive
circulation of total `G` on its window-support graph `X_S`, so every same-length
`FLOW` candidate has `spec_L(D) = spec_L(S)` and ties `S` under **any**
`(spec_L, x)` objective (exact multinomial and fixed-`N` §6.1 alike). Only the
triple-repeat clause of `I_s` is used. Scope: `OR`, `FLOW`, `FIXED`,
`I_s(S,R)`.

**P-R2 — fixed-length sequence-level `P1` maximizer.** [mathematical proof;
#48 comment of 2026-09-21 04:51, restated]

Under `SEQ` + `FIXED` with candidates required to be `P1`: every `L`-mer of a
`P1` candidate occurs at most once (Fact 3), so `d_D(w) in {0,1}`; since every
observed type has `d_S(w) >= 1`, each factor `d_D(w)/d_S(w) <= 1` and
`L(D|x) <= L(S|x)`. So `S` is a maximizer (weak schema); uniqueness may still
fail. Scope: `SEQ`, `FIXED`, candidates `P1`.

### 2.2 Negative rows

| id | universe / length | strand | objective | witness | status |
|---|---|---|---|---|---|
| **N-R1** | `SEQ` / `FREE`, candidates `P1` | `OR` | exact multinomial, `N(D)=|D|` | `S=AABBC`, `D=AABC`, `L=3`, `R=(0,3)`, `x={AAB:1,BCA:1}`, ratio `25/16` | verified computation; #48 |
| **N-R2** | `SEQ` / `FIXED`, candidates `P2` | `OR` | exact multinomial | `S=AABBC`, `D=ABABC`, `L=2`, `R=(1,3,4)`, `x={AB:1,BC:1,CA:1}`, ratio `2` | verified computation; #48 |
| **N-R3** | `FLOW` / `FREE`, truth `I_s` | `OR` | exact multinomial | `S=AAATT`, `D=AAAATT`, `L=3`, `x=spec_3(S)+e_AAA`, ratio `15625/11664` | verified computation; rigidity note §5.2 |
| **N-R4** | `FLOW` / `FIXED` | `MOL` | exact + fixed-`N` | `S=AAATAT`, `D=AAAAAT`, `G=6`, ratios `3` / `5` | kernel-checked certificate; `docs/section62-same-length-bidirected-counterexample.md` |
| **N-R5** | `SEQ` / `FIXED` | `OR` | exact / fixed-`N` | `S=AAABB`, `D=AAAAB` etc. | kernel-checked; `docs/fixed-length-exact-counterexample.md`, `docs/fixed-length-binomial-counterexample.md` |

All of N-R1–N-R5 are **strict** inequalities, so they are decisive under every
tie/equivalence convention. What differs is the **scope**: N-R1/N-R2 are
sequence-level (`SEQ`), while the positive theorem P-R1 is §6.2 `FLOW`;
N-R3 is `FLOW`; N-R4 is the only `MOL` row and is a cross-source panel (see C4).

### 2.3 The two positive rows are *not* the same kind of statement

P-R1 proves uniqueness of the **spectrum / circulation**, which is exactly a
**tie** statement; it does **not** prove uniqueness of the sequence. Explicitly
(`scripts/verify_synthesis_rows.py`, check B): `AABABB` and `AABBAB`
(`G=6`, `L=3`) have the *same* spectrum (hence the same circulation, hence tie)
but are not cyclic shifts, and both are `P2`-inadmissible via an interleaved
pair. So "spectrum rigid" and "the ML sequence is the truth" are different
claims; the gap is word-uniqueness (C2).

---

## 3. Hidden conflations

**C1 — external `N` versus `|D| = G`.** MB09's known genome size `N` is a
likelihood parameter (the binomial denominator), and §6.2 imposes no candidate
length equation. P-R1's `FIXED` assumption is an *added* candidate restriction
with no source statement. The synthesis must not derive `FIXED` from "the genome
size is known". [source fact; already flagged in #46 comments of 2026-09-21
02:59 and 03:36]

**C2 — spectrum/circulation uniqueness versus word uniqueness.** P-R1 gives the
former only, i.e. a tie. Word uniqueness is the classical
Ukkonen–Pevzner / Çelikkanat-et-al. spectrum-identifiability statement (the
repository's Conjecture 4), still open in the circular form. Any synthesis
sentence of the form "ML recovers the truth" must say which of the three it
means: (a) truth is *a* maximizer; (b) every same-length maximizer has the
truth's spectrum (tie); (c) every maximizer is the truth up to genome
equivalence. P-R1 gives (b), not (c). [mathematical proof + open]

**C3 — three inequivalent "structural admissibility" predicates.** `P1`,
`P2`, and truth-relative `I_s` are not interchangeable:
`I_s`-realizability `<=>` `P2` (Fact 1); `P1 => P2` but not conversely
(Fact 2, `AABAB`). In particular **`P1` excludes `I_s`-feasible truths**: a
truth satisfying the source bridging condition need not satisfy the candidate
check. This is the "compatibility with the antecedent" obligation #48 names.
[repository derivation + mathematical proof]

**C4 — candidate universe `SEQ` versus `FLOW`.** The motivating positive
theorem P-R1 lives in `FLOW` (support equality). The #48 witnesses N-R1/N-R2
live in `SEQ` (support-contained): `D=AABC` has support
`{AAB,ABC,BCA,CAA}`, while `S=AABBC` has support
`{AAB,ABB,BBC,BCA,CAA}`; `D=ABABC` has support `{AB,BA,BC,CA}`, while
`S=AABBC` has `{AA,AB,BB,BC,CA}`. Neither competitor has the truth's support,
so neither is a legal §6.2 spelled candidate; N-R1/N-R2 refute the
*sequence-level* repair, not the `FLOW` one. Conversely N-R3 is a genuine `FLOW` free-length
counterexample. The synthesis must tag every row with its universe.
[verified computation]

**C5 — strand convention.** P-R1 and N-R3 are `OR`; N-R4 requires `MOL`
(`TAT` must collapse to `ATA`). Under `OR` the N-R4 competitor `AAAAAT` has
**zero** likelihood because the observed oriented read `TAT` is absent from it.
No located primary source combines single-strand `I_s` with MB09's
reverse-complement molecule likelihood; that pairing is a named cross-source
panel. [verified computation; `docs/source-notes/uniform-strand-convention-search-2026-09-20.md`,
and the branch/working-tree strand audit]

**C6 — two inequivalent "infinite-data" regimes.** "Population / infinite
reads" is ambiguous between:

- **uniform full-spectrum population**: `x = c · d_S`, i.e. the empirical
  distribution converges to the truth's own `L`-mer distribution `d_S/G`;
- **concentrated infinite reads**: `x_k = n` for one type `k` with the other
  counts fixed, i.e. the empirical distribution converges to a point mass
  `delta_k`.

These have opposite limits. Under the first, the truth is always a maximizer
(Lemma 4.1 below). Under the second, the ratio `(G/L)^n` grows without bound and
the truth loses (`docs/variable-length-ml-analysis.md` §5.3 (branch/working tree,
not on `origin/main`)). #45's stated intuition ("remove finite-sample frequency
fluctuations") is the **first**; citing the second against #45 is a conflation.

---

## 4. What the population regime actually adds

**Lemma 4.1 (proportional-sample optimality).** [mathematical proof, reproduced
here; a branch/working-tree note `docs/unrestricted-length-proportional-reduction.md`
Theorem 1 proves the same statement] Let `x = c · d_S` for a rational `c > 0`.
Then for **every** nonempty circular word `D` of **any** length `n`,

```text
L_exact(D | x) <= L_exact(S | x),
```

with equality iff `d_D(i)/n = d_S(i)/G` on `supp(d_S)` (and `d_D = 0` off it).

_Proof._ The observation-only multinomial coefficient cancels. With `w_i := d_S(i)`
and `W := G`, the weighted AM–GM/Jensen inequality for `log` gives
`sum_i w_i log(d_D(i)/w_i) <= W log((sum_i d_D(i))/W) = G log(n/G)`. Substituting
into the log-ratio yields `log(L_exact(D|x)/L_exact(S|x)) = c[sum_i w_i log(d_D(i)/w_i) - G log(n/G)] <= 0`.
Equality iff `d_D(i)/w_i` is constant on `w_i > 0`, i.e. `d_D = (n/G) d_S` there. ∎

**Consequences.**

1. **#45's weak schema is trivial.** Under the uniform full-spectrum population,
   the truth is a maximizer over *all* candidate lengths and *all* candidate
   classes — no bridging, no primitivity, no admissibility. So the population
   repair does not "rescue" a statistical optimum; that optimum is automatic.
   [mathematical proof]
2. **The real population content is scale rigidity, not ML.** By Lemma 4.1 the
   population ties are exactly the proportional-spectrum candidates
   `d_D = (n/G) d_S`. The population statement is therefore *equivalent* to:
   which candidates have a spectrum proportional to `d_S`? Cross-length
   (`n != G`), the repository's Theorem P (`P2` + primitivity ⇒ `c = 1`) rules
   them out; same-length (`c = 1`) is word-uniqueness (C2 / Conjecture 4).
   [mathematical proof + open]
3. **The finite failures are sample-skew, and vanish at population.** N-R1's
   ratio `25/16` and N-R3's ratio are finite-sample phenomena: with
   `x = d_S`, N-R1's competitor `AABC` omits the truth's types `ABB`, `BBC`
   and has likelihood exactly `0`. [verified computation]

So #45 is not a second, independent "repair of the ML theorem"; it is the
observation that the finite failures are sample-skew plus the (already known)
reduction of the remaining question to spectrum/scale rigidity.

---

## 5. What #48 must establish — and what it cannot

#48's main finite question is: *if the truth satisfies the source bridging
condition, is it ML among candidates satisfying intrinsic admissibility checks?*
The issue explicitly adds the obligation to **verify that the chosen intrinsic
condition admits the truth** ("ideally prove that a truth satisfying the relevant
bridging condition is itself admitted").

**Proposition 5.1 (no truth-compatible intrinsic finite repair).**
[mathematical proof, from Fact 1, Fact 2, N-R1, N-R2] Let `Q` be any
candidate-intrinsic predicate such that every `I_s`-feasible truth satisfies
`Q`. Then `Q` cannot make the finite `SEQ` theorem true, at either `FIXED` or
`FREE` length.

_Proof._ `I_s`-feasibility of a truth is `P2` (Fact 1), so the condition is
`P2 => Q`; the strongest such `Q` is `Q = P2` itself. But `P2` already admits
the `FIXED` counterexample N-R2 (`S=AABBC`, `D=ABABC`, both `P2`, ratio `2`) and
the `FREE` counterexample N-R1 (both `P1`, hence `P2`, ratio `25/16`). Weakening
`Q` only enlarges the candidate class, so it cannot restore the theorem. ∎

**Consequences for #48.**

- The preferred finite repair — intrinsic candidate checks, no target-length
  knowledge, finite data, and truth-compatibility — **does not exist** as a
  `SEQ` statement. The only positive finite rows recorded here are (i) P-R1, which uses
  `FIXED` + `FLOW` (and is a tie), and (ii) P-R2, which uses `FIXED` + `P1`
  and therefore *drops truth-compatibility* (it excludes `I_s`-feasible truths
  such as `AABAB`).
- Hence #48's next durable step is not another predicate search. It is a
  **decision** among three options, each with a stated cost:
  1. keep `FIXED` + `P1` and label the result a narrowing/control that may
     exclude the truth (cost: truth-compatibility);
  2. keep truth-compatibility (`P2`) and move to the population regime (cost:
     changes the data regime, and the weak schema becomes trivial — see §4);
  3. keep finite data and truth-compatibility but accept a **strict** negative
     result (cost: no positive ML statement).
- Under option 2, #48 should state that its "population uniqueness" claim is
  exactly scale rigidity (cross-length proved; same-length = word-uniqueness /
  classical spectrum identifiability), not a new ML-maximality theorem.

---

## 6. Reproduction

```sh
python3 scripts/verify_synthesis_rows.py
```

The script re-derives, from scratch and with exact arithmetic: Fact 2
(`AABAB` is `P2` but not `P1`); the spectrum-tie / word-nonuniqueness example of
§2.3; N-R1's finite `25/16` versus its population value `0`; the absence of
cross-length proportional collisions and of same-length same-spectrum collisions
among primitive `P2` words in the tested scopes; and the population value of the
N-R3 witness.

---

## 7. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| P-R1: `OR`+`FLOW`+`FIXED`+`I_s` ⇒ unique positive circulation / every same-length candidate ties | **mathematical proof** | `docs/source-notes/oriented-se62-rigidity-theorem.md` (`origin/main` `cf6c357`) |
| P-R2: `SEQ`+`FIXED`+`P1` ⇒ truth is a maximizer | **mathematical proof** | Fact 3 + #48 computation |
| N-R1: `SEQ`+`FREE`+`P1` strict counterexample, ratio `25/16` | **verified computation** | this note, script |
| N-R2: `SEQ`+`FIXED`+`P2` strict counterexample, ratio `2` | **verified computation** | this note, script |
| N-R3: `FLOW`+`FREE`+`I_s` strict counterexample | **verified computation** | rigidity note §5.2 |
| N-R4: `FLOW`+`FIXED`+`MOL` strict counterexample | **kernel-checked certificate** | `docs/section62-same-length-bidirected-counterexample.md` |
| `I_s`-realizability ⇔ `P2` | **repository derivation** | bridging/spectrum note §1 (branch/working tree) |
| `P1 ⇒ P2`, not conversely (`AABAB`) | **mathematical proof + verified computation** | this note, script |
| Spectrum-rigid ⇏ word-unique (`AABABB`/`AABBAB`) | **verified computation** | this note, script |
| Lemma 4.1: `x = c d_S` ⇒ truth ML over all lengths | **mathematical proof** | this note; same as branch note Theorem 1 |
| #45 weak schema is trivial at population | **mathematical proof** | Lemma 4.1 |
| Population ties ⇔ proportional spectra | **mathematical proof** | Lemma 4.1 equality case |
| Cross-length proportional spectrum `c>1` impossible for primitive `P2` | **mathematical proof** (#48 Theorem P) + independent **verified computation** | this note, script |
| Proposition 5.1: no truth-compatible intrinsic `SEQ` finite repair | **mathematical proof** | Fact 1, Fact 2, N-R1, N-R2 |
| Which MB09 referent / strand / length the 2016 sentence intends | **open** | `docs/source-notes/conclusion-semantics-determination.md` |

## 8. Cross-references

On `origin/main`: [`docs/open-problem.md`](open-problem.md),
[`docs/bridging-source-semantics.md`](bridging-source-semantics.md),
[`docs/source-notes/oriented-se62-rigidity-theorem.md`](source-notes/oriented-se62-rigidity-theorem.md),
[`docs/source-notes/mb09-se61-index-orientation-resolution.md`](source-notes/mb09-se61-index-orientation-resolution.md),
[`docs/source-notes/conclusion-semantics-determination.md`](source-notes/conclusion-semantics-determination.md),
[`docs/source-notes/equivalence-and-tie-wellposedness.md`](source-notes/equivalence-and-tie-wellposedness.md),
[`docs/source-notes/uniform-strand-convention-search-2026-09-20.md`](source-notes/uniform-strand-convention-search-2026-09-20.md),
[`docs/section62-same-length-bidirected-counterexample.md`](section62-same-length-bidirected-counterexample.md),
[`docs/fixed-length-exact-counterexample.md`](fixed-length-exact-counterexample.md),
[`docs/fixed-length-binomial-counterexample.md`](fixed-length-binomial-counterexample.md).

Branch/working-tree artifacts referenced by name (not links):
`docs/source-notes/oriented-same-length-se62-source-liveness.md`,
`docs/source-notes/s62-oriented-broad-search-2026-09-20.md`,
`docs/source-notes/reverse-complement-strand-convention.md`,
`docs/source-notes/conclusion-semantics-equivalence-and-length.md`,
`docs/audit-aaatat-single-strand-bridging-2026-09-21.md`,
`docs/unrestricted-length-proportional-reduction.md`,
`docs/variable-length-ml-analysis.md`,
`mathematics/bridging-and-spectrum-uniqueness.md`.

---

## 9. Addendum: the objective axis and the population KL reduction

_Status: addendum to §1–§8, written on `synthesis/population-objective-frontier-0921`
based at `d028141`. It composes the two packets that matured after the stress-test:
the issue-#48 finite intrinsic packet
(`docs/issue48-intrinsic-admissibility-counterexample.md`,
`docs/issue48-intrinsic-candidate-checks.md`,
`docs/reconciliation-issue46-unlock-48-45-2026-09-21.md`) and the population
identifiability packet
(`docs/population-identifiability-intrinsic-genomes.md`,
`docs/issue48-population-independent-verification-2026-09-21.md`,
`docs/literature/circular-qgram-identifiability-and-Is-threshold-2026-09-21.md`).
It extends §4 (which stated the population KL observation as Lemma 4.1) and supplies
the objective axis that §2's row table was missing; it corrects one objective tag in
the reconciliation. It does not re-prove the rigidity theorem, does not add a Lean
statement, and does not settle `docs/open-problem.md`._

_New reproduction: section G of `scripts/verify_synthesis_rows.py`._

### 9.1 The finite objective axis

§2 listed witnesses without naming the finite objective, so two rows could be
compared only loosely. Three objectives must be kept separate [**source fact** for the
MB09 §6.1 likelihood; **modeling decision** for the free-length reading]:

- **`PO`** — candidate-intrinsic exact multinomial with per-candidate length
  `N(D) = |D|` (Variant E, free-length reading):
  `L(D)/L(S) = ∏_{w : x_w > 0} ( |S| d_D(w) / (|D| d_S(w) ) )^{x_w}`.
- **`FN`** — fixed-`N` §6.1 product of binomial marginals *with* the zero-count
  factors.
- **`FN0`** — fixed-`N` ratio with the zero-count factors dropped:
  `∏_{w : x_w > 0} ( d_D(w) / d_S(w) )^{x_w}`. This is the ratio the §2/N-R tables
  compute.

**Lemma F1 (`FN0` no-beat for support-contained unit candidates).** [mathematical
proof] Let `D` satisfy `supp(x) ⊆ supp(d_D)` and `d_D(w) = 1` for every
`w ∈ supp(x)`. Then the `FN0` ratio is `∏_{w : x_w > 0} 1 / d_S(w)^{x_w} ≤ 1`,
because `d_S(w) ≥ 1` on observed types. Every `STRONG` candidate whose support
contains `supp(x)` meets the hypothesis, since `d_D(w) ∈ {0, 1}` everywhere. So
**free candidate length cannot create a strict `FN0` failure for `STRONG`
candidates**: the truth is a maximizer over that class at any length. ∎

**Objective-conditional reclassification of the finite witnesses.** [verified
computation; section G] Evaluating both ratios exactly:

| witness | truth / candidates | universe | length | panel | `PO` | `FN0` |
|---|---|---|---|---|---|---|
| `S=AABBC`, `D=AABC`, `L=3`, `x={AAB,BCA}` | `P1` / `P1` | `SEQ` | `FREE` | `OR` | `25/16` **strict** | `1` tie |
| `S=AABB`, `D=AAB`, `L=3`, `x={AAB,BAA}` | `P2` / `P1` | `SEQ` | `FREE` | `OR` | `16/9` **strict** | `1` tie |
| `S=AAB`, `D=AB`, `L=2`, `x={AB,BA}` | `I_s`/`P2` / `P1` | **`FLOW`** | `FREE` | `OR` | `9/4` **strict** | `1` tie |
| `S=AABBC`, `D=ABABC`, `L=2`, `x={AB,BC,CA}` | `P2` / `P2` | `SEQ` | `FIXED` | `OR` | `2` **strict** | `2` **strict** |
| `S=AAATT`, `D=AAAATT`, `L=3`, `x=spec_3(S)+e_AAA` | `I_s` / — | `FLOW` | `FREE` | `OR` | `15625/11664` | `4` **strict** |

The #48 headline (`25/16`) and the only support-equal `FLOW` witness located in
the bounded scope (`AAB→AB`, `9/4`) are **`PO`-only**: their entire excess is the
factor `(|S|/|D|)^{N}`, and
removing it gives an exact tie. `AABBC→ABABC` is strict under both because its
competitor *repeats* an observed type. Consequently the reconciliation's §4 phrase
"`N2`/`N4` also strict under `FN0`" is a typo for "`N4`": for `N2`
(`AABB→AAB`) the reconciliation's own `ratio_fixed` prints `1`, and F1 applies
(the competitor is `STRONG` and support-contained). [verified computation]

So the objective axis is load-bearing. For `SEQ` the negative is not an artifact
of choosing `PO`: `AABBC→ABABC` is strict under both `PO` and `FN0` (even though
the other `SEQ` witnesses are `PO`-only). For `FLOW` the only support-equal
witness located in the bounded scope is `PO`-only; under `FN0` the same pair ties.

**Two naming collisions to keep explicit.** The two packets reuse different
witness numbering: the stress-test's `N-R2` is `AABBC→ABABC`, whereas the
reconciliation's `N2` is `AABB→AAB` and its `N4` is `AABBC→ABABC`. The
reconciliation's `N2` and the stress-test's `N-R2` are *not* the same instance.
§9 uses names, not indices. The stress-test's `P1`/`P2` are the population
packet's `STRONG`/`WEAK`; the independent intrinsic packet's `SR`/`RRF`/`P_weak`
are a *third*, separately-defined family (its §6) and must not be silently
identified with `P1`/`P2`.

### 9.2 The population KL reduction

Fix a read length `L` and let `p = d_S/G`, `q_D = d_D/|D|` be the normalized
`L`-spectra. [mathematical proof; isolates and extends Lemma 4.1]

**Proposition 1 (population ML is automatic).** For every circular candidate `D`
of any length,
```text
ell_pop(D) := Σ_w p(w) log q_D(w) = -H(p) - KL(p ‖ q_D) ≤ -H(p) = ell_pop(S),
```
with equality iff `q_D = p` on `supp(p)`, i.e. `d_D = (|D|/G) d_S`; and
`ell_pop(D) = -∞` if some `p`-positive type is absent from `D`. (Gibbs'
inequality; the observation-only multinomial coefficient is
candidate-independent and drops.)

Two consequences, both already latent in §4:

1. **No hypotheses are used.** Proposition 1 holds with no bridging,
   primitivity, or admissibility assumption and over all candidate *lengths*.
   So `#45`'s weak schema ("the truth is a population maximizer") is
   automatic; it is not a repaired ML theorem. Calling `#45` a "population
   repair" is therefore a **conflation** with the first of C6's two
   infinite-data regimes.
2. **Only identifiability has content.** By Proposition 1 the population ties
   are exactly the proportional-spectrum candidates `d_D = c · d_S`,
   `c = |D|/G > 0`. So the whole population question is whether
   `D ↦ p_D` is injective on the candidate class up to genome equivalence.
   Proposition 1 is a statement about the *limit* law; it puts nothing on top of
   the finite §6.1 objective, and it is not a settlement of the 2016 question.

### 9.3 Population identifiability theorem (oriented panel)

**Theorem P (cross-length exclusion).** [mathematical proof; independently
re-proved on the population branch] Let `S, T` be primitive circular words, both
`TRF`-admissible at read length `L`, with `d_T = c · d_S`, `c ∈ Q_{>0}`. Then
`c = 1`. The proof needs only the triple-repeat half of `WEAK` on the larger
side: Lemma L* (primitive + `TRF` ⇒ every `(L−1)`-mer occurs at most twice)
forces `c ≤ 2` on the shared `(L−1)`-support, and `c = 2` forces the support to
be a simple directed cycle traversed twice, i.e. a nontrivial power, contradicting
primitivity.

**Equal-length residue.** For `c = 1` the statement "the `L`-mer multiset
determines a `WEAK` word up to cyclic shift" is the repository's Conjecture 4,
now claimed as the `K = L−1` instance of **Bresler–Bresler–Tse 2013, Theorem 3**
under the maximal-repeat definitions (their Ukkonen condition at `K = L−1` is
literally `WEAK = TRF ∧ ILF`; the bridging threshold `ℓ ≤ L−2` makes
"unbridgeable" and "Ukkonen-obstructing" the same length condition). [**source
theorem** modulo the circular Eulerian-cycle reading, *not* an independent proof;
see the circular-qgram note §3.2 for the residual reading caveats and the
condensed-graph nuance. The earlier Çelikkanat-et-al. anchor was a linear,
non-maximal restatement and is not used.]

**Sharpness.** [verified computation; population packet §6]
- Primitivity cannot be dropped: `AAB` / `AABAAB = S²` (`L=3`) are both `WEAK`
  with equal population law and are not rotations.
- Candidate-side admissibility cannot be dropped: the primitive `WEAK` truth
  `AAAB` and the primitive-not-`TRF` mate `AAAABAAB` (`L=3`) have equal population
  law and are not rotations.
- `TRF` alone is not enough for the equal-length step:
  `AABABB`/`AABBAB` (`L=3`) share a spectrum, are primitive and `TRF`, are not
  rotations, and both fail `ILF`.

**Panel boundary.** [verified computation] The positive statement is
`OR`-conditional. On the molecule/`MOL` panel `S = AACAGT`, `T = AACTGT`
(`L=3`) are primitive and `STRONG` (hence `WEAK`), have identical normalized
molecule-class `3`-spectra, and are dihedrally inequivalent. So the panel's
equivalence/read-type choice is a genuine input (this is C5), and the population
uniqueness theorem cannot be exported to `MOL`.

### 9.4 What the population regime does not do

1. **It is not an ML rescue.** Proposition 1 already makes the truth a
   maximizer; there is nothing left for bridging/admissibility to repair at the
   population level.
2. **It is not the primary repair of the 2016 question.** The population packet
   says so explicitly (§8: "not claimed"). The finite §6.1/`PO` question is
   about a different objective, on an objective-dependent candidate universe,
   and remains open.
3. **It does not settle the equal-length step by itself.** That step is a
   published combinatorial theorem under a circular reading; the repository has
   not re-proved it and has not kernel-checked it. Do not present it as a fresh
   proof or as a Lean result.
4. **It does not remove the objective ambiguity.** Population reclassifies the
   finite `PO`-only failures as finite-sample/normalization effects, but it does
   not decide whether the source's finite sentence intends `PO`, `FN0`, or `FN`.

### 9.5 Corrected frontier

After the finite intrinsic packet and the population KL reduction the architecture
reads as follows.

- **Finite data (the actual open problem).** Intrinsic admissibility does not
  restore the finite theorem. For `SEQ` the negative does not depend on choosing
  `PO`: `AABBC→ABABC` is strict under both `PO` and `FN0` (the `FREE` witnesses
  `AABB→AAB`, `AABBC→AABC` are `PO`-only). For `FLOW` it is `PO`-conditional: a
  support-equal witness exists under `PO` (`AAB→AB`, `9/4`), but under `FN0` no
  strict `FLOW` witness was found in the bounded scope and Lemma F1 proves none
  exists for `STRONG` candidates. The
  clean finite positive rows remain `OR + FLOW + FIXED + I_s` (P-R1, a tie) and
  `SEQ + FIXED + STRONG` (P-R2, buys maximality by excluding `I_s`-feasible
  truths).
- **Population (a different regime).** ML maximality is automatic; the content
  is the `OR`-panel identifiability theorem (cross-length proved; equal-length
  source theorem; `MOL` false).
- **Therefore `#45` is unlocked only as an identifiability characterization, not
  as a repair of ML maximality**, and only after fixing the source-level
  dependency `D1` (finite objective) and `D2` (candidate universe `SEQ` vs
  `FLOW`). `D4` (equal-length `q`-gram) is now a source theorem rather than an
  open conjecture; `D3` (source panel `OR` vs `MOL`) decides whether population
  uniqueness can be claimed at all; `D5` (source-liveness of `FIXED`) is
  untouched. `docs/open-problem.md` remains open.

### 9.6 Added epistemic rows

| Claim | Status | Basis |
|---|---|---|
| Lemma F1: support-contained unit candidate ⇒ `FN0` ratio `≤ 1` | **mathematical proof** | §9.1; section G |
| #48 `SEQ` neg. has a witness strict under both `PO` and `FN0`; `FLOW` neg. is `PO`-only | **verified computation** | §9.1 table; section G |
| Reconciliation's "`N2` strict under `FN0`" | **corrected** (`N2` ties; `N4` is strict) | §9.1; section G |
| `PO`-only excess is the factor `(|S|/|D|)^{N}` | **mathematical proof** | ratio identity; §9.1 |
| Proposition 1: population ML is automatic (`KL`) | **mathematical proof** | Gibbs; §9.2 |
| Theorem P: primitive + `TRF` ⇒ `c = 1` | **mathematical proof** | population packet; §9.3 |
| Equal length ⇒ cyclic shift for `WEAK` (`OR`) | **source theorem** (BBT Thm 3, `K=L−1`, circular reading) | circular-qgram note; §9.3 |
| Primitivity / candidate admissibility / `ILF` all necessary | **verified computation** | population packet §6; §9.3 |
| `MOL` positive transfer is false (`AACAGT`/`AACTGT`) | **verified computation** | population packet §7; section G |
| Population is the primary repair | **not accepted** | §9.4 |

### 9.7 Reproduction

```sh
python3 scripts/verify_synthesis_rows.py
```

Section G of that script re-derives, with exact `Fraction` arithmetic: the `PO`
and `FN0` values of the five witnesses of §9.1 (including the `N2` correction and
the `PO`-only status of `AAB→AB`); a bounded exhaustive check of Lemma F1; the
`FLOW` support-equality of `S=AAB`/`D=AB`; and the `MOL` collision
`AACAGT`/`AACTGT`. Sections A–F are unchanged.

### 9.8 Cross-reference additions

Branch/working-tree artifacts referenced by name (not links):
`docs/issue48-intrinsic-admissibility-counterexample.md`,
`docs/issue48-intrinsic-candidate-checks.md`,
`docs/reconciliation-issue46-unlock-48-45-2026-09-21.md`,
`docs/population-identifiability-intrinsic-genomes.md`,
`docs/issue48-population-independent-verification-2026-09-21.md`,
`docs/literature/circular-qgram-identifiability-and-Is-threshold-2026-09-21.md`,
`docs/literature/substring-spectrum-identifiability-2026-09-20.md`.
