# Same-length transfer of the merged §6.2 bridging counterexample: an I-projection obstruction, and the non-uniform escape

_Status: mathematical analysis with proofs + exact-rational verification,
2026-09-20. This note is about whether the merged **unequal-length** witness
`AAATT → AAAATT` (`|S| = 5`, `|D| = 6`, `N = 5`) can be converted into a
**same-length** counterexample (`|D| = |S| = N`) preserving bridging (`I_s`),
source-faithful bidirected feasibility, and a strict literal §6.1 advantage. All
claims are labelled **source fact**, **mathematical proof**, **verified
computation**, **bounded search**, **modeling choice**, or **open**._

_Reproduction: `python3 scripts/verify_same_length_lift.py` (self-contained,
exact `fractions.Fraction`, deterministic, a few seconds; exits non-zero on any
failed assertion)._

_Relation to prior work: assumes the notation and results of
[`bridging-se62-flow-ml-counterexample.md`](bridging-se62-flow-ml-counterexample.md)
and the exact graph certificate of
[`section62-mb09-bidirected-graph-audit.md`](section62-mb09-bidirected-graph-audit.md).
The bounded fixed-length search it does not duplicate is
`docs/section62-fixed-length-bidirected-counterexample.md` (unmerged branch
`analysis/se62-peroccurrence-slice-obstruction`, commit `d428506`), whose
per-type witness is independently reproduced here as §5._

_Update to [`bridging-se62-flow-ml-counterexample.md`](bridging-se62-flow-ml-counterexample.md)
§10 open question 2 (fixed length / `|D| = N`)._

---

## 0. Verdict at a glance

1. **The merged witness does not same-lengthify while its data are held fixed.**
   For the merged observation vector `x = {AAA:1, AAT:1, TAA:1}` (`n = 3`) with
   external `N = G = 5`, **no** same-length candidate of length `5` — spelled
   molecule or general §6.2 flow — can strictly beat the truth `AAATT`. The
   reason is exact and symmetric: the §6.1 log-objective is strictly concave
   with unique real maximizer `t_w = N x_w / n = 5/3`, and the balanced lattice
   partition of `5` into `3` positive parts is `{2,2,1}`, which is precisely the
   multiset of `d_S = {AAA:1, AAT:2, TAA:2}`. The truth already sits at a lattice
   maximum. [mathematical proof + verified computation, §3–§4]

2. **Length padding does not escape.** The two literal one-letter paddings of
   `AAATT` to length `6` are `AAATTA`, whose spectrum is exactly `d_D = (2,2,2)`
   (a tie), and `AAATTT`, whose `I_s` bridging forces one read per copy of its
   two maximal triple repeats `A^3`, `T^3`, hence `n ≥ 6 = G`. A bounded
   exhaustive search over all length-`G` words with the merged class support
   `{AAA, AAT, TAA}` (`G = 6, 7`), every `I_s`-admissible read multiset, and
   every same-length competitor finds **no** strict improvement. [bounded
   search, §5; no proof of absence for `G ≥ 8`]

3. **The escape is non-uniformity, not length.** The same-length obstruction
   disappears as soon as the observed multiset is non-uniform, because then
   `t = N x / n` is not permutation-symmetric. Under the source's per-vertex
   lower bound `1` (not the stronger per-occurrence bound), the same-length
   witness
   `S = AAATAT`, `D = AAAAAT`, `G = N = 6`, `L = 3`, starts `(0,0,1,3,5)`
   is `I_s`, both molecules are spelled bidirected §6.2 circuits, and the §6.1
   ratio is `5 > 1` (exact fixed-length multinomial ratio `3`). Here
   `t = (12/5, 6/5, 6/5, 6/5)` and `d_D = (3,1,1,1)` is the lattice
   I-projection of `t`. This is not a padding of `AAATT`; it changes the sample.
   [verified computation + mathematical proof, §5; independently reproduces the
   unmerged branch witness]

4. **Status of the same-length question.** Under the **per-vertex (per-type)
   bidirected** reading the same-length statement is **false** (§5). Under the
   **per-occurrence** reading it remains **open**: the §5 witness fails
   per-occurrence feasibility (`d_S(AAA) = 1 < x_AAA = 2`), and the bounded
   per-occurrence search recorded on the unmerged branch finds zero. The merged
   witness is a per-occurrence-feasible instance whose *fixed data* are
   obstructed (§3). [open]

---

## 1. Setup and the same-length simplex

Fix an alphabet with a reverse-complement involution (`A ↔ T` here), read
length `L`, a circular truth `S` of length `G`, a read-start multiset `R`, and
the observed read-molecule count vector

```text
x_w = #{reads of molecule class w},   n = Σ_w x_w.
```

Write `d_S` for the length-`L` window-molecule-class spectrum of `S`
(`Σ_w d_S(w) = G`), and `d_D` for that of a circular candidate `D`
(`Σ_w d_D(w) = |D|`). The **literal Medvedev–Brudno §6.1** separable binomial
with external genome length `N` is

```text
L_6.1(d) = ∏_w C(n, x_w) (d_w / N)^{x_w} (1 − d_w / N)^{n − x_w},   0 ≤ d_w ≤ N.
```

The constant `∏ C(n,x_w)` cancels in every comparison. **Same length** means
`|D| = N`; the relevant external size is the truth length, so in the merged
instance `N = G = 5`.

Because a §6.2 candidate flow only visits observed read vertices, its throughput
`d` has support `⊆ supp(x)`; the source's per-vertex lower bound `1` forces
`d_w ≥ 1` on `supp(x)`, i.e. **support equality** for spelled molecules. The
objective depends on the candidate only through `d`. [source fact; MB09 §6.1–6.2,
`bridging-se62-flow-ml-counterexample.md` §1, `section62-mb09-bidirected-graph-audit.md` §1]

Throughout, `d` is treated as **integral**: §6.2's `d_i` is the number of times
the walk visits read `i` (Observation 7), i.e. a count. [modeling choice; see §4.3]

---

## 2. The objective is a separable concave function of the throughput

**Lemma 1 (I-divergence form).** With `q_w = x_w / n` and `p_w = d_w / N`,

```text
log L_6.1(d) = const − n · Σ_w KL(q_w ‖ p_w),
```

where `KL(q‖p) = q log(q/p) + (1−q) log((1−q)/(1−p))` is the Bernoulli
divergence, strictly convex in `p`. [mathematical proof; standard Bernoulli
calculus; already recorded in `docs/section62-kkt-and-bridging-family.md` §2]

**Theorem 1 (same-length I-projection criterion).** Fix `x`, `n`, `N`. On the
real simplex

```text
Δ = { d : d_w ≥ 1 for w ∈ supp(x); d_w = 0 otherwise; Σ_w d_w = N },
```

the function `ℓ(d) = log L_6.1(d)` is strictly concave and has the unique
maximizer

```text
t_w = N x_w / n          (w ∈ supp(x)),        t = 0 off supp(x).
```

Therefore every same-length candidate `d` (support `supp(x)`, `Σd = N`) satisfies
`ℓ(d) ≤ ℓ(t)`, with equality iff `d = t`; and:

- **(sufficiency)** if some admissible same-length candidate has `ℓ(d) > ℓ(d_S)`,
  the truth is not a same-length maximizer;
- **(necessity/obstruction)** if `d_S` is a maximizer of `ℓ` over the admissible
  integral throughputs, no same-length candidate strictly beats it.

_Proof._ Each coordinate contributes a strictly concave function of `d_w`
(Lemma 1), so `ℓ` is strictly concave. A stationary point in the relative
interior of `Δ` solves `x_w/d_w = λ` for all `w`, i.e. `d_w = x_w/λ`; summing,
`N = n/λ`, so `λ = n/N` and `d_w = N x_w/n`. Strict concavity gives uniqueness;
the endpoint coordinate cases `x_w = 0` are excluded by support equality.
∎

Two consequences drive everything below. First, the **same-length question is a
finite lattice I-projection problem**: enumerate the integral points of `Δ` and
compare. Second, the target `t` is symmetric under permutations of the observed
classes **iff** `x` is uniform on its support. The merged witness has uniform
`x`, and the symmetry is what blocks the transfer.

---

## 3. The merged instance is obstructed (uniform observations)

**Corollary 2 (uniform-observation obstruction).** Suppose `x_w ≡ c` for all
`k = |supp(x)|` classes (so `n = c k`). Then `ℓ` is invariant under permutations
of the coordinates and, by strict concavity, its integral maximizers on `Δ` are
exactly the **balanced partitions** of `N` into `k` positive parts (parts
differing by at most `1`). If the truth multiset `{d_S(w)}` is balanced, then
`d_S` is a lattice maximizer and no same-length candidate can strictly beat it.

_Proof._ Permutation invariance is immediate from `t` being constant. For the
lattice claim, if two parts differ by `≥ 2`, moving one unit from the larger to
the smaller strictly increases `ℓ` because the two coordinates carry the *same*
strictly concave function; iterating yields the balanced partition, which is
unique up to permutation. ∎

**Application 3.1 (merged `AAATT → AAAATT`).** The merged data are
`x = {AAA:1, AAT:1, TAA:1}` (`k = 3`, `c = 1`, `n = 3`), `N = G = 5`, and
`d_S = {AAA:1, AAT:2, TAA:2}`. The balanced partition of `5` into `3` positive
parts is `{2,2,1}`, which is exactly the multiset of `d_S`. Hence:

> **No same-length candidate of length `5` — in particular no spelled molecule
> and no general §6.2 flow — strictly beats `AAATT` for this read multiset and
> `N = 5`.** The merged witness cannot be same-lengthified while `(S, R, N)` are
> held fixed. [mathematical proof; verified exhaustively over the two
> compositions in `scripts/verify_same_length_lift.py` (A)]

The enumeration is unconditional: it maximizes over *all* integral same-length
throughputs with support `supp(x)`, so it is robust to exactly which such
throughputs the §6.2 cycle cone realises (the feasible set is a subset).

### 3.1 The obstruction is not "bridging"

Corollary 2 uses only `x`, `n`, `N`, and `d_S`; it does not use `I_s`, the read
overlap graph, or the fact that `AAATT` is a spelled circuit. The merged witness
is blocked by the coincidence that a **uniform sample's I-projection is
symmetric** and the truth already attains the balanced lattice point. This is
the same "slice" phenomenon that makes the `n = N = G` search zero a theorem
(`mathematical/section62-peroccurrence-search-degeneracy.md`, Theorem 3), here
appearing one level up: not because `n = N`, but because the observations are
uniform.

---

## 4. Why the unequal-length witness works, said in the same language

For the merged instance the competitor `D = AAAATT` has spectrum
`d_D = (2,2,2)` and `|D| = 6 = N + 1`. Its throughput is *not* constrained to
`Δ` because the candidate length is not fixed to `N`; the extra unit of length
lets `d_D` overshoot the balanced point in every coordinate. Relative to
`d_S = (1,2,2)`, only `AAA` changes (`1 → 2`), giving the `9/8` factor. Within
`Δ` (length `N = 5`) that same move must remove a unit elsewhere, and the exact
objective returns precisely to `1`:

```text
(2,2,1) :  φ_1(2) φ_1(2) φ_1(1)          (2/5)(3/5)^2 balanced
(1,2,2) :  φ_1(1) φ_1(2) φ_1(2)          same product  (d_S)
```

So the merged mechanism is exactly "buy a unit of `AAA` with a unit of extra
length"; the same-length restriction charges one unit back, and symmetry makes
the trade break even. [mathematical proof + verified computation]

### 4.1 Length padding to length 6 does not escape

Write `S' = AAATT·z` for the appended letter `z ∈ {A,T}`.

- `z = A`: `S' = AAATTA`, spectrum `d_{S'} = (2,2,2) = d_D` — an exact tie.
- `z = T`: `S' = AAATTT`, spectrum `d_{S'} = (3,2,1)` and support
  `{AAA, AAT, TAA}`. Bridging fails the merged 3-read sample: `S'` has two
  maximal triple repeats, `A^3` and `T^3`; each copy of a length-`1` repeat is
  bridged by a read whose *middle* position is that copy, so `I_s` needs one
  distinct bridging read per copy, i.e. `n ≥ 6 = G`. [mathematical proof]

### 4.2 Bounded search for any support-preserving same-length lift

For `G ∈ {6, 7}`, all length-`G` words with window-class support exactly
`{AAA, AAT, TAA}`, every `I_s`-admissible read multiset (`n < G`), and every
same-length competitor: **zero** strict improvements (18 truths at `G = 6`, 28
at `G = 7`). A separate run over `G = 8` also returned zero. This is **bounded
search**, evidence rather than a proof of absence; it covers every literal
padding and many other support-preserving lifts. [verified computation, bounded]

### 4.3 Modeling caveat: integral vs. fractional flows

If §6.2 flows were allowed to be **fractional**, `t = (5/3,5/3,5/3)` itself
would be a same-length throughput and (were it in the flow polytope) would beat
`d_S` by Theorem 1. The obstruction in §3 therefore relies on the integral
reading of `d_i` as a *number of visits* (MB09 Observation 7), consistent with
the repository's treatment of the §6.2 object as an integer flow. Under the
fractional relaxation the same-length statement is a different, weaker question
and is not addressed here. [modeling choice / open]

---

## 5. The non-uniform escape: a same-length witness under the per-vertex lower bound

The symmetry of Corollary 2 is fragile. Once `x` is non-uniform, `t = N x / n`
selects a non-symmetric lattice point, and a same-length competitor can win.
The source's §6.2 lower bound is **per vertex** (`1` for each read molecule,
i.e. per *type*), not per occurrence, and under that reading the following
same-length instance is a strict counterexample.

```text
alphabet          {A, T},  reverse complement A ↔ T
truth             S = AAATAT             (G = 6)
competitor        D = AAAAAT             (|D| = 6 = N)
read length       L = 3
realized starts   (0, 0, 1, 3, 5)        (n = 5)
observed          x = { AAA:2, AAT:1, ATA:1, TAA:1 }
truth spectrum    d_S = { AAA:1, AAT:1, ATA:3, TAA:1 }
competitor spec   d_D = { AAA:3, AAT:1, ATA:1, TAA:1 }
```

Facts (all verified; reproduction script §C):

1. **`I_s` holds.** Coverage; the maximal triple repeat `A^3` is all-bridged by
   the reads at starts `0, 1`; the interleaved-repeat conjunct is satisfied.
   [verified computation]
2. **Both are source-faithful bidirected §6.2 circuits.** Each molecule is
   spelled by its cyclic length-`3` window walk; every window class lies in
   `supp(x)`; every observed molecule is visited at least once (per-vertex lower
   bound `1`). Consecutive windows overlap in `L−1 = 2` symbols, so the
   bidirected overlap edges exist for every `o_min ≤ 2`. [verified computation]
3. **`D` strictly wins.** `t = N x / n = (12/5, 6/5, 6/5, 6/5)`; its integral
   I-projection is `d_D = (3,1,1,1)`, and the truth `d_S = (1,1,3,1)` has the
   same mass but places the surplus on the *less observed* class `ATA`:
   `L_6.1(D)/L_6.1(S) = 5 > 1`. The exact fixed-length multinomial ratio is
   `3`. [mathematical proof + verified computation]

This witness is recorded on the unmerged branch
`analysis/se62-peroccurrence-slice-obstruction` (commit `d428506`,
`docs/section62-fixed-length-bidirected-counterexample.md`), which found 4608
fixed-length per-type counterexamples at `G = 6, L = 3`. The reproduction script
re-derives this single witness end to end and is **not** a re-run of that
bounded search.

**Crucially, the §5 witness is not a padding of `AAATT`.** It changes the read
multiset (adding the class `ATA`, changing `x_AAA` to `2`), which is exactly
what breaks the uniform-observation symmetry of §3. It also fails
**per-occurrence** feasibility: `d_S(AAA) = 1 < x_AAA = 2`. So it settles the
same-length statement only under the per-vertex reading, and leaves the
per-occurrence reading open.

---

## 6. The general rule

Putting Theorem 1 and its applications together:

> A variable-length §6.2 counterexample converts to a **same-length** one
> exactly when the observed multiset `x` (and external `N`) admit a same-length
> §6.2 throughput `d` with `ℓ(d) > ℓ(d_S)`. The best possible same-length
> throughput is the integral I-projection of `t = N x / n`. **Length padding
> alone cannot change `t` or the symmetry of the problem; only changing `x`
> (or relaxing the lower bound to the source's per-vertex reading) can.**

- The merged `AAATT` sample has uniform `x`, so its I-projection is symmetric
  and the truth is a lattice maximizer: obstructed (§3).
- A non-uniform sample of the same flavour loses the symmetry and admits a
  same-length winner (§5).
- The `n = N = G` "conservation" theorem is the special case in which the
  I-projection is forced onto `d = x`; here the obstruction is the more general
  *uniform-observation lattice maximum*.

This is the durable negative insight requested: the merged witness is a
length phenomenon only because extra length lets the candidate overshoot the
balanced point by one unit in every coordinate; the same-length restriction
removes exactly that freedom, and no re-padding of the word restores it.

---

## 7. Epistemic status

| Claim | Status |
|---|---|
| `log L_6.1` is `const − n Σ KL`, strictly concave; real maximizer `t = N x/n` | **mathematical proof** (Lemma 1, Theorem 1; standard calculus) |
| Uniform `x` ⇒ integral maximizers are the balanced partitions; merged `d_S` is balanced | **mathematical proof** (Corollary 2) |
| Merged `AAATT`: no same-length candidate (spelled or general integral flow) strictly beats the truth for fixed `(S,R,N)` | **mathematical proof + verified computation** |
| `AAATTA` padding ties; `AAATTT` padding forces `n ≥ G` by `I_s` triple-repeat bridging | **mathematical proof** |
| No support-preserving same-length lift for `G ∈ {6,7,8}` | **bounded search** (not a proof of absence) |
| `AAATAT → AAAAAT`: same-length, `I_s`, bidirected §6.2 circuits, §6.1 ratio `5` | **verified computation** (reproduces an unmerged branch witness `d428506`) |
| Same-length statement under the per-vertex bidirected reading | **false** (the §5 witness) |
| Same-length statement under the per-occurrence reading | **open** (bounded zero on the unmerged branch; §5 witness excluded) |
| Fractional-flow relaxation | **open / different question** |
| Uniform-observation obstruction for the exact merged parameters | **mathematical proof** |
| Which §6.1/§6.2 object and lower-bound reading the 2016 sentence intends | **source ambiguity, unchanged** |

---

## 8. Reproduce

```sh
python3 scripts/verify_same_length_lift.py
```

Checks: (A) the merged same-length obstruction over all support-positive
integral throughputs; (B) the bounded no-escape search for `G = 6, 7`; (C) the
`AAATAT → AAAAAT` same-length witness (`I_s`, bidirected circuit, ratios `5`
and `3`). Exact `fractions.Fraction`, deterministic, no third-party packages,
exits non-zero on any failed assertion.

---

## 9. Open questions

1. **Per-occurrence same length.** Does a same-length per-occurrence-feasible
   §6.2 counterexample exist? The §5 witness is per-type only; the merged
   witness is per-occurrence feasible but obstructed. Bounded zeros are not a
   proof of absence.
2. **Non-uniform general family.** Can the §5 mechanism be lifted to an infinite
   same-length family (analogous to the KKT family) with a closed-form ratio?
3. **Fractional flows.** If §6.2 admits fractional throughputs, the same-length
   obstruction of §3 disappears; whether the source permits them is a modeling
   question.
4. **Padding with longer gadgets.** §4.2 is bounded at `G ≤ 8`; a proof that no
   support-preserving padding ever escapes would strengthen the negative result.
