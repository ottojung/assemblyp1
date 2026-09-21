# A broadened exhaustive search for a same-length strict-oriented §6.2 counterexample

_Status: independent from-scratch computation, 2026-09-20/21, against `origin/main`
(`f60ca5f`; the rigidity proof arrived in `cf6c357`). Every claim is labelled
**source fact**, **mathematical argument**, **verified computation (exhaustive in
scope)**, or **open**. The computation is **not** a proof: no finite scan is a
proof of absence beyond its stated scope._

_Reproduce: `python3 scripts/broad_se62_oriented_search.py --selftest` then
`python3 scripts/broad_se62_oriented_search.py --full` (single process, several
hours; `--jobs N` parallelises when RAM allows). The per-scope transcript is
committed as
[`results/s62_oriented_broad_scan_2026-09-20.txt`](../../results/s62_oriented_broad_scan_2026-09-20.txt)._

_This note is computational evidence about one precisely delimited reading. It
does not select which Medvedev–Brudno (2009) likelihood layer the Shomorony et
al. (2016) sentence intends, and does not touch tie/equivalence semantics._

---

## 0. Direct answer

Under the **strict-oriented single-strand** reading (oriented length-`L` read
types, no reverse-complement collapse) with the source's §6.2 **per-vertex
lower bound `1`**, the broadened scan finds **zero** same-length
support-feasible counterexamples in every one of **82 exhaustive scopes**
covering:

```text
binary      L=3 up to G=30,  L=4 up to G=30,  L=5 up to G=28,
            L=6 up to G=28,  L=7 up to G=26,  L=8 up to G=24,  L=2 up to G=10
ternary     L=3 up to G=18,  L=4 up to G=18,  L=5 up to G=16,  L=6 up to G=14
four-letter L=3 up to G=14,  L=4 up to G=14,  L=5 up to G=13
```

This strictly extends the earlier oriented single-strand zero (binary `L=3`
`G<=18`, `L=4` `G<=18`, `L=5` `G<=16`; ternary `L=3` `G<=12`, `L=4` `G<=11`;
four-letter `L=3` `G<=10`). The largest single scope enumerated **35 792 568**
binary necklaces (`G=30`) and **21 524 542** ternary necklaces (`G=18`).
[verified computation, exhaustive in scope]

The zero is consistent with, and is the finite-search shadow of, the *rigidity
theorem* now on `main`:
[`oriented-se62-rigidity-theorem.md`](oriented-se62-rigidity-theorem.md)
(commit `cf6c357`; independently re-proved earlier on the unmerged branches
`research/oriented-se62-rigidity-audit` and
`research/uniform-oriented-strand-2026-09-20`) states that an `I_s`-realizable
truth has a unique positive circulation on its window-support graph, so no
same-length support-feasible competitor can differ. **The proof is that note's,
not this one's.** This note is an independent finite check of the theorem's
prediction over scopes well beyond the theorem verifier's, and it relies on no
part of that proof.

---

## 1. The object searched, exactly

- **Truth.** A circular word `S` of length `G = |S|` over an alphabet of size
  `sigma`; `spec_L(S)(w) = #{i : S_i ... S_{i+L-1} = w}` with cyclic indexing,
  and `V = supp(spec_L(S))`. [source fact: Shomorony et al. §2 circular model]
- **Read types.** Oriented length-`L` words, no reverse-complement collapse.
  [source fact: Shomorony et al. §2; in §4.1 reverse complements are added as
  preprocessing, not identified]
- **`I_s`.** Shomorony et al. Eq. (1): coverage, every triple repeat all-bridged,
  every interleaved pair bridged. A length-`L` read can bridge a copy of a
  repeat of length `ell` only if `ell <= L-2`. Adding reads is monotone, so
  `I_s` is realizable on `S` iff:
  - **(T)** no Bresler triple repeat of `S` has length `>= L-1`, and
  - **(I)** no interleaved maximal-repeat pair has **both** lengths `>= L-1`.
  [source fact + mathematical argument; cross-checked below]
- **§6.2 candidate.** The source's per-vertex lower bound is `1`: a spelled
  candidate must contain every observed read at least once. For a spelled
  molecule `D` this is support equality `supp(spec_L(D)) = supp(x)`. With the
  natural observation `x = spec_L(S)` (realizable by `I_s`), the truth is
  admissible and a competitor must satisfy
  `supp(spec_L(D)) = supp(spec_L(S)) = V`. [source fact: MB09 §6.2,
  Observation 7; source-supported inference]
- **Same length.** `|D| = |S| = G`. Under the exact same-length multinomial the
  objective with `N(D) = N(S) = G` depends on `(spec_L(D), x)` and is constant
  on equal spectra. [source fact: MB09 §6.1]
- **Strict.** A competitor must improve the objective strictly.

**Reduction (mathematical argument).** For fixed `G, L, sigma` a same-length
strict §6.2-support-feasible counterexample exists **iff** there is a circular
truth `S` with (A) `I_s` realizable and (B) `spec_L(S)` **non-rigid on its
support**: some circular `D` of length `G` has `supp(spec_L(D)) = V` while
`spec_L(D) != spec_L(S)`.

*Why.* (<=) Take `x = spec_L(S)` (all starts once), which is `I_s`-realizable by
(A) and has support `V`; by (B) there is a same-length `D` with support `V` and
`spec_L(D) != spec_L(S)`. Some type `w0` has `d_D(w0) > d_S(w0)`. Adding `M`
further reads of type `w0` keeps `supp(x) = V` and makes the exact same-length
multinomial ratio

```text
E(d_D)/E(d_S) = prod_w (d_D(w)/d_S(w))^{x_w}
              = (d_D(w0)/d_S(w0))^M * (const in M) -> +infinity,
```

so `D` strictly beats `S` for large `M`. (=>) A counterexample supplies (A) and
the differing same-support candidate (B). Since a different-spectrum
same-support same-length `D` must exist for *any* objective to improve, (B) is
necessary for all `(spec,x)`-objectives simultaneously. In particular, if the
support is rigid the ratio is `1` for every objective. [mathematical argument]

**Consequence for this scan.** It is enough to count `I_s`-realizable truths
whose length-`L` support is non-rigid. Non-rigidity is decided exactly and
exhaustively by enumerating circular truths up to rotation and grouping by the
set of present window types: a support is non-rigid exactly when two distinct
window-count vectors share it.

---

## 2. Independence and method

The search is a fresh implementation that shares no code with
`scripts/verify_oriented_ss_se62_same_length.py` or
`scripts/support_feasibility_search.py`:

- **Rotation reduction.** All circular truths are enumerated as
  **necklaces** (Fredricksen–Kessler–Maiorana), one representative per rotation
  class, instead of all `sigma^G` linear words. Support and spectrum are
  rotation invariant, so the reduction is exact and removes a factor of about
  `G`, which is what makes `G=30` reachable.
- **Support representation.** A support is an integer bitmask over window codes,
  and spectra are compared through a 128-bit `blake2b` digest of the exact
  count vector (the digest is only an equality key; a collision could only hide
  a non-rigid support, never invent a counterexample). The reference scopes in
  `--selftest` compare exact tuples.
- **Own `I_s` routine.** Triple repeats and interleaved pairs are computed from
  scratch from the definitions, with a first-pass shortcut
  `max_w #occurrences of length-(L-1) windows < 3 => no long triple repeat`.

`--selftest` cross-validates both the `I_s` routine (13 025 words across six
small scopes: exact agreement with the reviewed reference) and the non-rigid
support counts on nine scopes (exact agreement). [verified computation]

---

## 3. Scope and results

All 82 scopes in `--full` report `cex-candidates = 0`; see the committed
transcript for the per-scope necklace counts, non-rigid-support counts and
times. Headline extended rows (all exhaustive over **all** necklaces of the
stated length):

| alphabet | `L` | `G` | necklaces | non-rigid supports | candidates |
|---|---|---|---|---|---|
| binary | 3 | 30 | 35 792 568 | 21 | **0** |
| binary | 4 | 30 | 35 792 568 | 900 | **0** |
| binary | 5 | 28 | 9 587 580 | 85 886 | **0** |
| binary | 6 | 28 | 9 587 580 | 195 150 | **0** |
| ternary | 3 | 18 | 21 524 542 | 204 095 | **0** |
| ternary | 4 | 18 | 21 524 542 | 364 034 | **0** |
| four-letter | 3 | 14 | 19 175 140 | 405 022 | **0** |
| four-letter | 4 | 14 | 19 175 140 | 36 550 | **0** |

No truncation, sampling, or time cap was applied within a listed scope; every
row completed with a zero candidate count. Total scan time across all rows is
about 5 826 s single-threaded. [verified computation, exhaustive in scope]

### 3.1 A direct multiset cross-check on small scopes

The reduction assumes that the all-starts observation `x = spec_L(S)` is the
right probe and that no multiplicity effect escapes it. To test that
assumption directly, the pre-existing `scripts/support_feasibility_search.py`
(unmerged branch artifact; different algorithm: it enumerates **read multisets
over starts** with multiplicity and evaluates the objectives on the fly) was
run with the `I_s` hypothesis and both the support-contained and per-occurrence
constraints. It reports `support-contained cex = 0` and `per-occurrence F* cex =
0` (max ratio `1`) for `(G,L,alpha,N) = (6,3,2,6)`, `(6,4,2,6)`, `(5,3,3,5)`,
and `(6,3,2,6)` with `--complete-only`. This is an independent route to the same
zero and confirms that multiplicity effects do not escape the reduction.
Separately, `--selftest` reproduces the reference scan counts. [verified
computation]

---

## 4. What the zero does and does not mean

**Does (in scope).** It rules out, by exhaustive enumeration, every
`I_s`-realizable circular truth with a non-rigid length-`L` support within the
82 scopes. Since a same-length counterexample requires such a truth, there is no
counterexample in scope, for **every** objective that is a function of
`(spec_L(D), x)`, not only the two named objectives.

**Does not.** It is not a proof that no counterexample exists at other `G, L,
sigma`. It does not resolve the source ambiguity of the 2016 sentence, the
reverse-complement convention, the per-occurrence strengthening, or tie
semantics. The finite pattern (non-rigid supports exist, but none is
`I_s`-realizable) is evidence for the rigidity mechanism, not a verification of
it.

---

## 5. Epistemic status

| Claim | Status |
|---|---|
| Read model is oriented single-strand; §6.2 per-vertex bound is `1`; support equality is the spelled-candidate condition | **source fact** (Shomorony §2; MB09 §3.1, §4.1, §6.2, Obs. 7) |
| `I_s` realizable <=> (T) and (I) | **mathematical argument**, cross-checked on 13 025 words |
| `I_s` + non-rigid support <=> same-length strict support-feasible counterexample | **mathematical argument** (reduction) |
| No candidate in the 82 listed scopes | **verified computation, exhaustive in scope** |
| No candidate at unlisted `G, L, sigma` | **open for this script**; settled in general by the rigidity theorem below |
| Rigidity theorem explaining the zero | **mathematical proof on `main`** ([`oriented-se62-rigidity-theorem.md`](oriented-se62-rigidity-theorem.md), `cf6c357`); independently re-proved on two unmerged branches; not re-proved here |

Primary sources: Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C.
Tse, *Information-optimal genome assembly via sparse read-overlap graphs*,
*Bioinformatics* 32(17) (2016) i494–i502, Eq. (1), §2, §4.1, §5; Paul Medvedev,
Michael Brudno, *Maximum Likelihood Genome Assembly*, *J. Comput. Biol.* 16(8)
(2009) 1101–1116, §3.1, §4.1, §6.1–6.2, PMC3154397.

Cross-references:
[`oriented-se62-rigidity-theorem.md`](oriented-se62-rigidity-theorem.md)
(the merged proof this scan independently checks over wider scopes;
`scripts/verify_oriented_se62_rigidity.py` is its verifier),
[`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md)
(negative transfer across candidate classes),
[`../section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md)
(the molecule/bidirected witness, which inverts under oriented types).

Unmerged branch artifacts (not on `main`): the earlier oriented single-strand
note `docs/source-notes/oriented-single-strand-se62-same-length-2026-09-20.md`
and its reference script `scripts/verify_oriented_ss_se62_same_length.py`, whose
narrower per-scope zeros this scan strictly extends and whose golden counts
`--selftest` reproduces.
