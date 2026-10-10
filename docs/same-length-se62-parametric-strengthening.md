# Parametric strengthening of the same-length Section 6.2 counterexample

_Status: independent optional strengthening, 2026-10-09. Companion to
`docs/section62-same-length-bidirected-counterexample.md` and to the
kernel-checked module `AssemblyP1.SameLengthSection62Parametric`. It does not
replace or edit the already-proven `k = 0` theorem; it packages the whole
family._

_Reproduction:_

```sh
python3 scripts/verify_samelength_se62_parametric.py
lake build --wfail AssemblyP1.SameLengthSection62Parametric
lake env leanchecker AssemblyP1.SameLengthSection62Parametric
```

_The Python script is self-contained, exact (`fractions.Fraction`),
deterministic, and exits non-zero on any failed assertion. The Lean module
contains no `sorry`, `axiom`, `admit`, or `native_decide`; the endpoint theorem
`AssemblyP1.SameLengthSection62Parametric.parametric_se62_counterexample`
depends only on `propext`, `Classical.choice`, and `Quot.sound`._

---

## 0. Verdict at a glance

Fix the genuine, already kernel-checked MB09 molecule-flow witness

```text
truth             S = AAATAT   (G = 6)
competitor        D = AAAAAT   (|D| = G = 6, SAME LENGTH)
read length       L = 3
external size     N = 6
realized starts   (0, 0, 1, 3, 5)          (n = 5 reads; start 0 twice)
observed          x = { AAA:2, AAT:1, ATA:1, TAA:1 }
truth spectrum    d_S = { AAA:1, AAT:1, ATA:3, TAA:1 }
competitor spec   d_D = { AAA:3, AAT:1, ATA:1, TAA:1 }
```

For arbitrary `k : Nat`, add `k` extra **actual** `AAA` reads at start `0`. The
sampling becomes

```text
starts(k) = (0 repeated 2 + k times, 1, 3, 5)     n = 5 + k
x(k)      = { AAA:2 + k, AAT:1, ATA:1, TAA:1 }
```

The set of realized *placements* (distinct sampled starts) is still
`{0, 1, 3, 5}` and the observed read *types* are unchanged, so the inputs of
every coverage/bridging hypothesis are **literally unchanged** from the `k = 0`
module:

* `readStartsK_toFinset` proves `(readStartsK k).toFinset = {0,1,3,5}` and
  `obsK_support` proves the observed support is `{AAA, AAT, ATA, TAA}` for every
  `k`; on this witness the historical matching-position set `MatchStarts`
  (Shomorony et al. 2016 supplement §6.4) is *exactly* the sampled placement
  set, so it too is unchanged;
* `truth_information_feasible_k` is the old placement-based project `I_s`
  (`SourceFaithfulIs.InformationFeasible`, the base-coverage model — **not** the
  canonical literal historical `I_s` of §6.4) on the parameterized placement
  set;
* `readStartsK_toFinset_eq` restates the placement-set invariance against the
  `k = 0` distinct-start set `readStarts.toFinset`, and
  `truth_historical_literal_information_feasible_k` transfers the **canonical
  literal §6.4 historical `I_s`**
  (`AssemblyP1.HistoricalCovers.HistoricalInformationFeasibleLiteral`, all
  three-occurrence repeats bridged) to every `k` from the `k = 0` certificate
  `AssemblyP1.HistoricalCoverageSameLength.W1.w1_historical_literal_information_feasible`
  (module `AssemblyP1.HistoricalCoverageSameLengthWitnesses`);
  the literal predicate consumes only the distinct sampled start set, so no new
  historical model is introduced;
* the §6.2 feasibility theorems of the base module (`truth_spelled_feasible62`,
  `competitor_spelled_feasible62`) are reused verbatim, since neither the read
  molecules, the overlap graph, nor the spectra `d_S`, `d_D` depend on `k`.

Only the multiplicity entering the two likelihood objectives changes.

The two same-length objectives become

```text
candidate-intrinsic exact multinomial     L_exact(D)/L_exact(S) = 3 ^ (k + 1)
literal §6.1 fixed-N product of binomials L_6.1(D)/L_6.1(S)    = 5 ^ (k + 1)
```

with `5 ^ (k + 1) > 1` and `3 ^ (k + 1) > 1` for every `k`.
[verified computation + kernel-checked]

At `k = 0` this is exactly the published `3` and `5` of the base witness.

## 1. Lean endpoints

All in `AssemblyP1.SameLengthSection62Parametric`:

| theorem | statement |
| --- | --- |
| `obsK_eq_countP` | `obsK k` is the genuine observed class count of `readStartsK k` |
| `obsK_support` | the observed support is independent of `k` |
| `readStartsK_toFinset` | `(readStartsK k).toFinset = realizedStarts = {0,1,3,5}` |
| `readStartsK_toFinset_eq` | `(readStartsK k).toFinset = readStarts.toFinset` (the `k = 0` distinct-start set) |
| `truth_information_feasible_k` | the old placement-based project `I_s` (`SourceFaithfulIs.InformationFeasible`, base-coverage model) holds for the parameterized placement set |
| `truth_historical_literal_information_feasible_k` | the canonical literal §6.4 historical `I_s` (`HistoricalInformationFeasibleLiteral`) holds for every `k`, transferred from the `k = 0` W1 certificate |
| `exactLik_ratio` | `exactLik dD (obsK k) / exactLik dS (obsK k) = 3 ^ (k + 1)` |
| `likN_ratio` | `likN (5+k) (obsK k) dD / likN (5+k) (obsK k) dS = 5 ^ (k + 1)` |
| `exactLik_competitor_strictly_better` | `exactLik dS (obsK k) < exactLik dD (obsK k)` |
| `likN_competitor_strictly_better` | `likN (5+k) (obsK k) dS < likN (5+k) (obsK k) dD` |
| `parametric_se62_historical_literal_counterexample` | combined endpoint under the canonical literal historical `I_s`: literal `I_s` + same length + both §6.2 flows + both strict ratios |
| `parametric_se62_counterexample` | combined endpoint, old placement-based project `I_s` variant: `InformationFeasible` + same length + both §6.2 flows + both strict ratios |

The §6.1 product `likN n x d = ∏_{c : Fin 8} marginalN n x d c` is over **all
eight** molecule-class codes, so the zero-count factors are present (each equals
`1`).

## 2. Exact algebra (MB09 §6.1)

The per-class §6.1 marginal is

```text
marginalN(n, x, d, c) = C(n, x_c) · (d_c / N)^{x_c} · (1 − d_c / N)^{n − x_c},   N = 6,
```

and the common binomial coefficient `C(n, x_c)` cancels in every class ratio.
The four relevant class ratios are

```text
AAA (d_S = 1, d_D = 3, x = 2 + k, n − x = 3):
    (3/1)^{2+k} · ((1/2)/(5/6))^3 = 3^{2+k} · (3/5)^3
AAT (d_S = d_D = 1, x = 1):                       1
ATA (d_S = 3, d_D = 1, x = 1, n − x = 4 + k):
    (1/3) · ((5/6)/(1/2))^{4+k} = (1/3) · (5/3)^{4+k}
TAA (d_S = d_D = 1, x = 1):                       1
```

Their product is

```text
3^{2+k} · (3/5)^3 · (1/3) · (5/3)^{4+k}
  = [3^2 · (3/5)^3 · (1/3) · (5/3)^4] · [3^k · (5/3)^k]
  = 5 · 5^k
  = 5^{k+1},
```

using `3^k · (5/3)^k = 5^k`. This is formalized as `arith_binom`. The exact
multinomial ratio is immediate: `exactLik dS (obsK k) = 3` for all `k` (the
extra reads land where `d_S AAA = 1`), while `exactLik dD (obsK k) = 3^{2+k}`,
so the ratio is `3^{2+k}/3 = 3^{k+1}`.

Equivalently, the increment `k → k + 1` multiplies the exact ratio by `3`
(`d_D AAA / d_S AAA = 3`) and the binomial ratio by `3 · (5/3) = 5`; the factor
`5/3` is the `ATA` complement shift, and the `3` is the `AAA` shift.

## 3. Scope

This is a statement about one finite instance family. It does **not** settle
which Medvedev–Brudno (2009) object the Shomorony et al. (2016) sentence
intends, nor the per-occurrence strengthening or the single-strand reading.
The §6.2 flow certificates are in the strict whole-genome full-overlap
subcase `oMin = L − 1 = 2` (every consecutive read pair overlaps in `L − 1`
bases); no claim is made about the general variable-overlap graph domain, nor
about the single-strand reading. It is independent of the `#247c` / `#247f`
worktrees and does not touch them.
