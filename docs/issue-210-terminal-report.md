# Issue #210 terminal report

_Status: TERMINAL — the oriented variable-length §6.2 finite front is closed at
the level of the claims it makes. Branch `agent/board-210-e8b6b2`, worktree
`/workspace/assemblyp1-finite-210`, pushed to `origin`. The board report below
was posted verbatim on issue #210 at 2026-10-09T10:25:52Z (author
`openclaw@marceline-dev`) via the Antonina board CLI
(`antonina board comment --id 210`; the GitHub REST API and `gh` are
unavailable on this host — repository is private, no token — but the Antonina
board has its own CLI with a working write path)._

**Verdict: REFUTED.** Under the source-faithful oriented single-strand
per-vertex §6.2 feasibility reading (and the strictly stronger spelled
support-equality and single-circuit readings), with the bridging hypothesis
`I_s` at full strength and variable candidate length, the truth need not be the
§6.1 maximum-likelihood maximizer. Three infinite families of strict
counterexamples are proved; the strongest (Family A) is backed by a kernel-
checked Lean certificate and an exact-rational AM-GM attainment argument.
Every claim below is tagged **[fact]** (kernel-checked, executed, or directly
cited to the source), **[inference]** (derived in this pass), or **[choice]**
(this front's modeling decision).

---

## 1. The terminal result (what is claimed)

**Instance (all [fact], kernel-checked in
`AssemblyP1/OrientedVariableLengthSe62.lean`).** Truth `S = AAATT` circular,
`G = 5`; read length `L = 3`; oriented (non-collapsed) length-3 read types;
observation `x^{(M)} = spec_3(S) + M·e_AAA` — all five starts once plus `M`
extra copies of the `AAA` start, total reads `n = 5 + M`; support
`{AAA, AAT, ATT, TTA, TAA}` for every `M`; external known genome size `N = 5`
for the binomial objective.

**Family A (growing competitor, exact objective).** Competitor
`D_M = A^{3+M}TT`, `|D_M| = 5 + M ≠ G`. For every `M ≥ 1`:

```text
L_E(d_{D_M}, x^{(M)}) / L_E(d_S, x^{(M)}) = (5/(5+M))^{5+M} · (1+M)^{1+M} > 1
```

**[fact: mathematical proof, note §3]** The competitor's spectrum equals the
observation (`d_{D_M} = x^{(M)}`, run-extension lemma), so its normalized
spectrum is exactly `x/n` and it attains the weighted-AM-GM upper bound
`L*(x) = C(x)·∏(x_w/n)^{x_w}` of the exact objective; the truth's normalized
spectrum differs from `x/n` for every `M ≥ 1`, so it is strictly below the
bound. The ratio diverges (at least like `5^M`). **[fact: kernel-checked at
`M = 1, 2`** — ratios `15625/11664` and `2109375/823543`, bound attainment and
strict truth-below-bound, in the Lean module; closed form verified exactly for
`M = 0..4` by the script and independently re-derived for `M = 1..6` in this
pass.**

**Families B and C (fixed truth, fixed competitor `D = AAAATT`, `|D| = 6 ≠ G`,
growing sample).** For every `M ≥ 1`:

```text
exact:      L_E ratio = (3125/3888) · (5/3)^M > 1   (Theorem B)
binomial:   L_A ratio = (81/128) · 2^M > 1         (Theorem C, N = 5)
```

**[fact: mathematical proof, note §4–§5 via the amplification Lemmas 1–2;**
each extra `AAA` observation multiplies the exact odds by
`p_D(AAA)/p_S(AAA) = (2/6)/(1/5) = 5/3` and the binomial odds by `Q_AAA = 2`.
At `M = 0` the competitor loses (ratios `3125/3888 < 1`, `81/128 < 1`); from
`M = 1` on it wins, diverging. Identities verified exactly for `M = 0..200` by
the amplification script; `M = 1` values `15625/11664` and `81/64` coincide
with the kernel-checked growing-family instance.] This is sampling instability,
not a bounded search. **[fact]**

**Hypotheses discharged [fact, kernel-checked].** `R = {0,1,2,3,4} ∈ I_s` —
the shared `SourceFaithfulIs.InformationFeasible` predicate at full strength
(coverage, every maximal triple repeat all-bridged, every interleaved pair of
repeats bridged), discharged by `decide`; both candidates genuinely §6.2-
feasible under all three readings at once: F1 per-vertex lower bound `1`
(the literal MB09 §6.2 bound), F3 spelled support equality, F4 single closed
walk of the oriented read-overlap graph realizing the candidate's spectrum
(`walkS`, `walkD`, `walkD2`); both candidates inside the source's binomial
domain `0 ≤ d_w ≤ N` (`N = 5`).

**Independence [fact].** Uses no result from the bidirected counterexample
(#212/#213) or the fixed-length rigidity audit (#211); the fixed-length theorem
is cited only as contrast (it shows the `|D| = G` restriction is sharp).

## 2. Re-measurement of the inherited state (this pass, 2026-10-09)

The inherited commit `7d48eab` was re-measured by execution, not trusted:

| Check | Command | Result | Exit |
|---|---|---|---|
| Exact script (growing family, `M = 0..4`, both objectives, `L*(x)` census) | `python3 scripts/verify_oriented_variable_length_se62.py` | `ALL ASSERTIONS PASSED` | `0` **[fact]** |
| Amplification script (identities + closed forms, `M = 0..200`) | `python3 scripts/verify_oriented_variable_length_se62_amplification.py` | `ALL ASSERTIONS PASSED` | `0` **[fact]** |
| Lean build of the certificate module | `lake build AssemblyP1.OrientedVariableLengthSe62` | success (8925 jobs) | `0` **[fact]** |
| Kernel replay | `lake env leanchecker AssemblyP1.OrientedVariableLengthSe62` | clean | `0` **[fact]** |
| Axiom audit (5 endpoint theorems) | `#print axioms` | exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx` | `0` **[fact]** |
| `sorry`/`admit`/`axiom`/`native_decide` scan | `grep -nE …` on the module | no matches | `1` (no match) **[fact]** |
| Repository docs integrity | `python3 scripts/check-research-docs.py` | passed | `0` **[fact]** |
| Full-library build | `lake build --wfail` | **fails** | `1` **[fact]** |

**Full-library failure analysis [fact + inference].** The failures are confined
to `AssemblyP1.BBTTripleBridge`, `AssemblyP1.Issue94Transposition`,
`AssemblyP1.Issue94ComponentAlignedSwaps`, and the aggregator `AssemblyP1.lean`
(a `KShort` namespace collision). This branch's diff vs its branch point
`cc0aa8a` is exactly four new files; the aggregator does not import this front's
module; the failing sources are byte-identical at `cc0aa8a`. The failures are
therefore pre-existing at the branch point, and `origin/main` has since
repaired them (commits `0ea7b44`, `913ec4a`, `3e972e2`, none in this branch).
They are not attributable to front #210 and do not touch any artifact this
front produces. **[inference]**

**Independent arithmetic re-derivation [fact].** A fresh exact-`Fraction`
re-implementation sharing no code with the front's scripts reproduced: the
three spectra; exact ratios `15625/11664` (`M=1`), `2109375/823543` (`M=2`);
binomial ratios `81/64` (`M=1`), `27/16` (`M=2`); Theorem A closed form at
`M = 1..6` (all strict); Theorems B and C closed forms at `M = 1..5`.

**Source-fidelity spot check [fact].** The MB09 §6.2 per-vertex lower-bound
quote and the §6.1 objective/domain quotes match the repository provenance
records (`shomorony-mb-formulation-provenance.md` §4.4,
`mb-formulation-referent-reconciliation.md`); the shared
`SourceFaithfulIs.InformationFeasible` predicate is full-strength `I_s`,
matching the front's Python transcription. The per-vertex reading is the
source reading; `d ≥ x` is correctly segregated as a stronger optional
variant.

**Cosmetic observation (no effect) [fact + inference].** The note's Theorem A
writes `D_M = A^{3+M}TT`; the Python and Lean use the cyclic rotation
`A^{M+2}TTA` (e.g. `AAAATTA` at `M=2`). Spectra and both objectives are
rotation-invariant; all values are unaffected. Recorded in note §9; left
as-is. **[choice]**

## 3. Commits on this front

- `7d48eab` (inherited): the refutation — Lean certificate, two exact scripts,
  note. Re-measured by this pass; all its executable claims reproduce.
- `57669dd` (second pass): re-measurement of the inherited state by execution;
  addendum (note §9) and this terminal report.
- third-pass commit (this commit): records the verbatim board posting (§5).

## 4. Precise unresolved blockers and open scope

1. **Per-occurrence variant `d ≥ x` — OPEN in both directions [fact, bounded
   evidence only].** For these families the variant is silent: at `M ≥ 1` the
   truth itself is not `d ≥ x`-feasible (`x(AAA) = 1+M > 1 = spec_3(S)(AAA)`).
   The nontrivial question — with `x ≤ spec_3(S)` and `R ∈ I_s`, can a
   `d ≥ x`-feasible competitor strictly beat the truth? — was bounded-censused
   (truths over `{A,T}` of length `≤ 6`, every `I_s`-feasible start set, every
   observation `T`-window-multiset `≤ x ≤ spec_3(S)` with `|x| ≤ G`, every
   circular binary competitor of length `≤ G + 3`, filtered by a necessary
   flow-admissibility condition): no strict counterexample survives in scope.
   This is **not a proof of absence**; the variant is out of scope for this
   terminal result, which is stated under the source per-vertex reading (and
   survives the stronger F3/F4 readings). **[fact]**
2. **Referent question — OPEN [fact].** Which Medvedev–Brudno object the
   Shomorony et al. (2016) sentence intends (exact vs binomial approximation,
   per-vertex vs per-occurrence feasibility) is not settled here; see
   `mb-formulation-referent-reconciliation.md` §8. This front settles the
   mathematics *under* the source-faithful oriented per-vertex reading with
   variable length. **[fact]**
3. **Full-library build red at the branch point [fact]** — pre-existing,
   unrelated modules, repaired on `origin/main` after the branch point; see
   §2. Not a blocker for this front's artifacts, which build and kernel-check
   cleanly. **[inference]**

## 5. Board report (posted verbatim on issue #210, 2026-10-09T10:25:52Z, author `openclaw@marceline-dev`)

> **state: TERMINAL** — issue #210, oriented variable-length §6.2 finite
> front. Worktree `/workspace/assemblyp1-finite-210`, branch
> `agent/board-210-e8b6b2` (2 commits ahead of `cc0aa8a`, pushed to `origin`).
>
> **Verdict: REFUTED.** Under the source-faithful oriented single-strand
> per-vertex §6.2 feasibility reading (and the stronger spelled support-
> equality and single-circuit readings), with `I_s` at full strength and
> variable candidate length, the truth need not be the §6.1 ML maximizer.
> Three infinite families of strict counterexamples, truth `S = AAATT`
> (`G = 5`, `L = 3`), observation `x^{(M)} = spec_3(S) + M·e_AAA`
> (`n = 5 + M`, support `{AAA, AAT, ATT, TTA, TAA}`):
>
> - **A (growing `D_M = A^{3+M}TT`, exact objective):** ratio
>   `(5/(5+M))^{5+M}(1+M)^{1+M} > 1` for every `M ≥ 1`; `d_{D_M} = x^{(M)}`
>   attains the AM-GM bound `L*(x)`; the truth is strictly below it.
>   Diverges at least like `5^M`.
> - **B (fixed `D = AAAATT`, exact):** ratio `(3125/3888)(5/3)^M > 1` for
>   every `M ≥ 1`.
> - **C (fixed `D = AAAATT`, fixed-`N` binomial, `N = 5`):** ratio
>   `(81/128)2^M > 1` for every `M ≥ 1`.
>
> At `M = 0` the competitor loses; from `M = 1` on it wins, with the
> advantage diverging — sampling instability, not a bounded search.
>
> **Certificates [fact, kernel-checked]:** Lean
> `AssemblyP1/OrientedVariableLengthSe62.lean` — `I_s` at full strength by
> `decide` on the shared `SourceFaithfulIs.InformationFeasible`; F1/F3/F4
> §6.2 feasibility (closed walks of the read-overlap graph); strict exact
> ratios `15625/11664` (`M=1`), `2109375/823543` (`M=2`); strict binomial
> ratios `81/64` (`M=1`), `27/16` (`M=2`); AM-GM bound attainment; axioms
> exactly `[propext, Classical.choice, Quot.sound]`, no `sorry`/`admit`/
> `axiom`. Exact scripts: `verify_oriented_variable_length_se62.py`
> (`M = 0..4`, both objectives, `L*(x)` census) and
> `verify_oriented_variable_length_se62_amplification.py` (identities,
> `M = 0..200`) — both `ALL ASSERTIONS PASSED`, exit `0`. Note:
> `docs/source-notes/oriented-variable-length-se62.md` (conventions,
> Theorems A/B/C with proofs, amplification Lemmas 1–2, epistemic table).
>
> **Re-measurement of the inherited commit `7d48eab` by execution [fact]:**
> both scripts exit `0`; `lake build` of the module exits `0`; `leanchecker`
> kernel replay exits `0`; `#print axioms` on all endpoint theorems is exactly
> `[propext, Classical.choice, Quot.sound]`; `check-research-docs.py` exits
> `0`; an independent fresh-`Fraction` re-derivation reproduces every ratio
> and closed form. `lake build --wfail` (full library) exits `1`, confined
> to pre-existing failures at the branch point in `BBTTripleBridge`,
> `Issue94Transposition`, `Issue94ComponentAlignedSwaps`, and the aggregator
> — modules this front does not touch or import, since repaired on
> `origin/main` (`0ea7b44`, `913ec4a`, `3e972e2`); not attributable to #210.
>
> **Precise unresolved blocker [fact]:** the per-occurrence `d ≥ x` variant is
> open in both directions (bounded census only, not a proof of absence; these
> families are silent on it because the truth itself is not `d ≥ x`-feasible
> for `M ≥ 1`). The referent question (which MB09 object the 2016 sentence
> intends) is likewise open; this front settles the mathematics under the
> source-faithful oriented per-vertex reading with variable length.
> Independent of the bidirected cases (#212/#213) and the fixed-length audit
> (#211).
