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
