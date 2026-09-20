# Do the strongest ML counterexample witnesses satisfy the *source* repeat/bridging conditions?

_Status: source reconstruction + exact finite computation, 2026-09-20. One
self-contained verifier, independent of every exploratory repository script.
Not a Lean result. Does not settle the source-ambiguous Shomorony et al. open
question._

_Reproduction: `python3 scripts/verify_source_bridging_reconstruction.py`
(exact integer/rational arithmetic; exits non-zero on any failed assertion)._

## 0. Verdict

The repository's strongest maximum-likelihood counterexample witnesses **do
satisfy** the published information-feasible bridging hypothesis `I_s`, when
`I_s` is reconstructed directly from the primary prose rather than from any
repository helper. The witnesses tested are:

| Witness (repository anchor) | Truth `S` | Realized starts | `L` | source `I_s` |
|---|---|---|---|---|
| fixed-length exact, kernel-checked (#31) | `AAABB` | `0,1,4` | 3 | **holds** |
| fixed-length binomial, kernel-checked (#32) | `AAACC` | `0,1,4` | 3 | **holds** |
| interleaved, fixed-length | `ABACABC` | `1,1,1,3,6` | 3 | **holds** |
| interleaved, unrestricted (`16807/4096`) | `ABACABC` | `1,1,1,3,6` | 3 | **holds** |
| read-tiled | `AAABCBC` | `0,0,0,1,2,5,6` | 3 | **holds** |
| §6.2 non-spellable | `AAATT` | `0,0,1,4` | 3 | **holds** |
| §6.2 "strongest" ratio `2187/512` | `AATAT` | `0,0,2,4` | 3 | **holds** |
| §6.2 per-type | `AAATAT` | `0,0,1,3,5` | 3 | **holds** |
| unrestricted, kernel-checked | `ACGT` | `0,0,2` | 2 | **holds** (vacuous) |

Two distinct things had to be gotten right for this to be a meaningful test,
and both are documented below:

1. **The bridging predicate must be the strict source predicate.** A copy is
   bridged iff a read extends strictly beyond it on *both* sides. The
   repository's existing exploratory scripts used a flank-coverage test that
   can over-report bridging; this was already corrected in
   [`../copy-bridging-predicate-correction.md`](../copy-bridging-predicate-correction.md).
   The verifier here re-derives the strict predicate from the primary text and
   does not import those scripts.

2. **`I_s` does not require every maximal repeat to be bridged.** Only *triple*
   repeats must be all-bridged and only *interleaved pairs* must be bridged.
   The strongest witness deliberately leaves other maximal repeat pairs
   unbridged, and they are exempt. Reading "bridging conditions" as Bresler's
   separate GREEDY sufficient condition ("every repeat is bridged") would
   wrongly reject it, but that is not `I_s` / MultiBridging.

The one witness class that genuinely **fails** the hypothesis is the
unbounded-ratio "universality" family built on single-read-type samples
`{k:n}`: its reads share one latent start, so they **fail the coverage clause**
and are not `I_s` counterexamples. A nearby coverage-corrected witness, on the
same `AAABB` truth, satisfies `I_s` and retains an unbounded ratio `2^k`. This
is recorded below.

## 1. Source definitions used

The accepted Shomorony et al. (2016) paper attributes Eq. (1)'s
information-feasible set to Bresler, Bresler & Tse (2013), so the repeat /
interleaving / bridging definitions are taken from that primary text
(`PMC3706340`, retrieved 2026-09-20):

> "A repeat of length `l` is a subsequence appearing twice, at some positions
> `t1, t2` (so `s_t1^l = s_t2^l`) that is maximal (i.e. `s(t1 - 1) ≠ s(t2 - 1)`
> and `s(t1 + l) ≠ s(t2 + l)`). Similarly, a triple repeat of length `l` is a
> subsequence appearing three times, at positions `t1, t2, t3`, such that
> `s_t1^l = s_t2^l = s_t3^l`, and such that neither of
> `s(t1 - 1) = s(t2 - 1) = s(t3 - 1)` nor
> `s(t1 + l) = s(t2 + l) = s(t3 + l)` holds. (Note that a subsequence that is
> repeated `f` times gives rise to `C(f,2)` repeats and `C(f,3)` triple
> repeats.) … A pair of repeats refers to two repeats, each having two copies.
> A pair of repeats, one at positions `t1, t3` with `t1 < t3` and the second at
> positions `t2, t4` with `t2 < t4`, is interleaved if `t1 < t2 < t3 < t4` or
> `t2 < t1 < t4 < t3`."

> Figure 5: "A subsequence `s_t^l` is bridged if and only if there exists at
> least one read which covers at least one base on both sides of the
> subsequence, i.e. the read arrives in the preceding length `L-l-1` interval."

> "we will call a repeat or a triple repeat bridged if at least one copy of the
> repeat is bridged, and a pair of interleaved repeats bridged if at least one
> of the repeats is bridged."

> MultiBridging (Theorem 6): "(a) all interleaved repeats are bridged; (b) all
> triple repeats are all-bridged; (c) the sequence is covered by the reads."

The verifier implements exactly this. Bridging is evaluated on an integer lift
of the circle, so the choice of origin cannot create or destroy a bridge. The
maximality check uses the circular predecessor/successor, matching the circular
genome model of the 2016 paper; the accepted text introduces no competing
repeat convention.

## 2. What the strict predicate is, and what it is not

For a length-`ℓ` copy at `t`, a length-`L` read starting at `r` bridges it iff,
after lifting,

```text
r < t   and   t + ℓ < r + L .
```

Equivalently the read start `r` is `t - d (mod G)` for some
`1 ≤ d ≤ L - ℓ - 1`; if `L - ℓ - 1 ≤ 0` the copy is unbridgeable. This is the
strict two-sided extension, not "the read covers the two flanking positions"
(a read can cover both flanks via the complementary arc without containing the
copy). The verifier uses the strict form.

## 3. The strongest witnesses satisfy `I_s`

Run `scripts/verify_source_bridging_reconstruction.py`. For each witness the
script reports coverage, every maximal triple repeat (with per-copy bridging),
and every interleaved pair (with bridged / unbridged). All nine witnesses in
the table pass. Representative exact ratios reproduced independently:

- `AAABB → AAAAB`, fixed-length exact: `L_exact(D)/L_exact(S) = 2`.
- `AAACC → AAAAC`, literal §6.1 product of binomial marginals,
  external `N = 5`: `1125/512`.
- `ABACABC → ACABACB`, fixed-length exact: `2`;
  `ABACABC → ABAC`, unrestricted exact: `16807/4096` (note `(7/4)^3 (7/8)^2`).
- `ACGT → ACACGT`, unrestricted exact: `32/27`.

### The interleaved witness is genuinely non-vacuous

`S = ABACABC` has maximal repeat pairs `A@{0,2}`, `A@{2,4}`, `CAB@{3,6}`, a
maximal triple repeat `A@{0,2,4}`, and one interleaved pair
`A@{2,4} ‖ CAB@{3,6}` whose four starts alternate cyclically
`2,3,4,6`. All three `A` copies are strictly bridged by the reads at starts
`6`, `1`, `3`, so the triple repeat is all-bridged and the interleaved pair is
bridged (its `CAB` constituent is length `3 = L` and unbridgeable, but `I_s`
requires only one constituent repeat of the pair to be bridged). Coverage holds.
This witness exercises *both* non-vacuous conjuncts of `I_s` simultaneously.

## 4. The exempt-repeat nuance (why "unbridged repeats" are not a failure)

`I_s` is not the conjunction "every maximal repeat is bridged". The script
prints the unbridged maximal repeat pairs of the two main witnesses:

```text
S = AAABB, starts 0,1,4, L=3:  unbridged maximal pairs  B@{3,4}, AA@{0,1}
S = AATAT, starts 0,0,2,4, L=3: unbridged maximal pairs  ATA@{1,3}
```

None of these pairs is a maximal triple repeat, and none is a constituent of an
interleaved pair, so `I_s` imposes no bridging obligation on them. In particular
the length-`2` `AA@{0,1}` of `AAABB` can never be bridged by a length-`3` read
(`L - ℓ - 1 = 0`), yet it is irrelevant to `I_s`.

Bresler et al. state a *separate*, strictly stronger sufficient condition for
the GREEDY algorithm — "every repeat is bridged" (their Theorem 2) — which
`AAABB` does violate. That condition is not the information-feasible hypothesis
of Eq. (1) / MultiBridging, and the published open-question sentence refers to
the ML formulation in the context of the MultiBridging feasibility conditions.
Conflating the two would spuriously reject the strongest witness.

## 5. The one family that fails: `{k:n}` coverage, and the nearby correction

The repository's unbounded-ratio "universality" construction (in
`../variant-e-variable-length-systematic.md` §2 and
`../parametric-variant-e-generalization.md`) fixes a repeat-free truth `S`,
observes `n` copies of one read type `k`, and uses the monomial competitor
`k^m` to obtain ratio `(G/L)^n`. Correctly reconstructed, that sample has a
**single latent start** `t` with `window(S,t,L) = k`. For `G > L` the reads
cover only `{t, …, t+L-1} ⊊` the circle, so **coverage fails** and the instance
is not `I_s`-feasible. The script demonstrates this for `(ACGT, AC)` and
`(AACGT, AA)`.

The nearby witness that succeeds is the coverage-corrected family on the same
truth: take `k` reads at start `0` and one read each at starts `1` and `4`, so
the reads cover the circle while the dominant type is still observed `k` times.
Then `I_s` holds (coverage, all-bridged triple repeat `A@{0,1,2}`, no
interleaved pair) and the fixed-length exact ratio against `AAAAB` is exactly
`2^k`. The script checks `k = 1, 2, 5, 8` (`ratio = 2, 4, 32, 256`). This is
the same mechanism recorded independently in
[`../bridging-consequences-lemmas.md`](../bridging-consequences-lemmas.md)
(Theorem 1) and
[`../unrestricted-length-proportional-reduction.md`](../unrestricted-length-proportional-reduction.md)
§5.2; the calculation here is a third, self-contained reproduction.

## 6. Epistemic status

| Claim | Status | Evidence |
|---|---|---|
| Repeat / triple-repeat / interleaving / bridging definitions above are the Bresler et al. prose | **Source fact** | `PMC3706340`, retrieved 2026-09-20 |
| Shomorony Eq. (1) delegates `I_s` to those definitions | **Source fact** | 2016 accepted text, cited in `../bridging-source-semantics.md` |
| Each of the nine listed witnesses satisfies source `I_s` | **Verified computation** | `scripts/verify_source_bridging_reconstruction.py`, exact arithmetic |
| `AAABB` has unbridged maximal pairs `B@{3,4}`, `AA@{0,1}`, both exempt from `I_s` | **Verified computation** | §4 |
| Bresler's "every repeat bridged" (GREEDY) is strictly stronger than `I_s` and is violated here | **Source fact + verified** | Bresler Theorem 2; §4 |
| The `{k:n}` unbounded-ratio family fails `I_s` coverage | **Verified computation + source fact** | §5 |
| The coverage-corrected `2^k` witness satisfies `I_s` | **Verified computation** | §5 |
| Which MB layer the 2016 sentence denotes, and candidate-length/tie semantics | **Open** | `../ml-formalization-contract.md`, `../source-notes/shomorony-mb-formulation-provenance.md` |

This note does not change the epistemic status of any counterexample; it
confirms that the strongest ones clear the hypothesis side under a
from-primary-source reconstruction, and isolates the one construction that does
not.

## 7. Relation to existing notes

- [`../copy-bridging-predicate-correction.md`](../copy-bridging-predicate-correction.md)
  first identified the repository's flank-coverage over-reporting and argued the
  kernel-checked witnesses are unaffected; §2–§3 here re-derive the strict
  predicate from the source and confirm that conclusion with a separate
  implementation.
- [`../unrestricted-length-proportional-reduction.md`](../unrestricted-length-proportional-reduction.md)
  §4 already uses the non-vacuously `I_s`-feasible interleaved witness for the
  unrestricted objective; §3 here reproduces its `I_s` certificate and ratio.
- [`../bridging-likelihood-obstructions.md`](../bridging-likelihood-obstructions.md)
  and [`../exhaustive-small-instance-search-v2.md`](../exhaustive-small-instance-search-v2.md)
  document the search-level asymmetry; this note is confined to testing named
  witnesses against the source hypothesis and does not re-run those searches.

## 8. Reproduce

```bash
python3 scripts/verify_source_bridging_reconstruction.py
```
