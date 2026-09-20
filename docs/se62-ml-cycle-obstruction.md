# The obstruction to "bridging forces fixed-`N` binomial optimality" is a profitable elementary cycle

_Status: structural determination for issue #36, 2026-09-20. Proposition-by-proposition
route rather than a search: it isolates the exact primitive that a counterexample needs
and proves that Shomorony bridging cannot remove it. All claims are labelled **source
fact**, **modeling choice**, **mathematical proof**, **verified computation**,
**kernel-checked**, or **open**._

_Reproduction:_ `python3 scripts/verify_se62_ml_cycle_obstruction.py` (deterministic,
exact `fractions.Fraction`, exits non-zero on any failed assertion).

_Scope._ This note works entirely inside the corrected Medvedev–Brudno §6.2 model fixed
by the issue-#36 reconciliation: read molecules as bidirected-graph vertices, proper
overlaps of length `≥ o_min`, Myers transitive reduction, vertex lower bound `1`, edge
lower bounds `0`, upper bounds `∞`, and the §6.1 **separable binomial** objective with
the external true genome length `N`. It is about the *closed-flow* (circuit/genome)
object. It does not decide which MB09 layer the 2016 Shomorony sentence denotes.

---

## 0. Verdict at a glance

The source-faithful implication

> **(P)** `I_s` holds **and** the truth-induced flow `d_S` is a feasible §6.2 closed
> flow ⇒ `d_S` maximises the §6.1 objective `L` over all feasible §6.2 closed flows

is **false**, and bridging is structurally incapable of making it true. The precise
reason is a separation of two pieces of data:

1. **Bridging is multiplicity-blind.** `I_s`, the read-type support `R`, and the truth
   flow `d_S` are determined by *which* reads were sampled (a set), never by the read
   multiplicities `x`. The objective `L` is determined by `x` and `n = Σ x` only.
   Therefore `I_s` cannot constrain the unconstrained maximiser
   `d*_w = N x_w / n` of the objective except through the support `R`.
   [mathematical proof; §4]
2. **The cost of a counterexample is one elementary cycle.** The §6.1 log-objective is
   separable and strictly concave, so any *additive* improvement of `d_S` decomposes
   into profitable elementary cycles of the overlap graph
   (`Δ(a+b) ≤ Δ(a)+Δ(b)`). The support-minimal primitive is a single profitable
   **self-loop** — an under-observed read whose molecule has a proper self-overlap.
   The `AAATT` instance attains exactly this primitive, with a kernel-checked strict
   ratio `9/8`. [mathematical proof + verified computation + kernel-checked; §2–§3]

The clean threshold for the self-loop primitive is `d_S,w + 1 ≤ N x_w / n`; the
kernel-checked `AAATT` witness straddles the real maximiser yet is still strictly
profitable (`ρ = 9/8`), so the exact one-step criterion, not the linear threshold, is
the correct primitive. [mathematical proof + verified computation; §2]

---

## 1. Setup and labelled assumptions

Fix the finite set `R` of observed read **molecules** (reverse-complement classes) and
the reduced bidirected overlap graph `G_R` of §6.2. Let

- `x : R → ℕ` be the observed read multiplicities, `n = Σ_w x_w`;
- `N` be the external true genome length (§6.1);
- `d : R → ℕ` be a candidate copy-count (vertex-throughput) vector, `0 ≤ d_w ≤ N`;
- `F` be the set of throughput vectors of **closed** §6.2 flows, i.e. integer sums of
  elementary cycles of `G_R`, intersected with the lower bound `d_w ≥ 1` on observed
  reads and the §6.1 domain `d_w ≤ N`;
- `d_S ∈ F` be the truth-induced flow (`d_S,w` = number of occurrences of read `w` in
  the true circular genome). [source fact + modeling choice]

The §6.1 objective is the product of binomial marginals

```text
L_x(d) = ∏_{w ∈ R} C(n, x_w) (d_w/N)^{x_w} (1 − d_w/N)^{n − x_w}.
```

Two source-faithful facts about the read/support link are used throughout:

- `supp(x) ⊆ supp(d_S)`: every sampled read is a window of the true genome.
  [source fact]
- `I_s` (coverage, all-bridged maximal triple repeats, bridged interleaved repeat
  pairs) is a predicate on the *set* of realized reads — their positions and types —
  and not on the multiplicities with which those reads were sampled. [modeling
  normalization + mathematical fact; §4]

Write, for fixed `X, n, N`,

```text
g_X(t) = (t/N)^X (1 − t/N)^{n−X},      h_X(t) = log g_X(t),
```

with `h_X'(t) = (X N − n t) / (t (N − t))` on `0 < t < N`. The multinomial
coefficient `C(n, x_w)` is `t`-independent and is dropped from every comparison.

---

## 2. Proposition 1 (strict log-concavity and the exact one-step criterion)

**(a) Strict log-concavity.** For fixed `X, n, N`,
`h_X''(t) = −[ X/t² + (n−X)/(N−t)² ] < 0` for `0 < t < N`. Hence `g_X` is strictly
log-concave, `h_X` is strictly concave, and the *discrete increments*
`Δ_X(m) := h_X(t+m) − h_X(t)` are non-increasing in `t`. [mathematical proof]

**(b) Unique real maximiser.** `h_X` is strictly increasing on `(0, N X / n)` and
strictly decreasing on `(N X / n, N)`, with `h_X' = 0` exactly at `d*_w := N X / n`.
[mathematical proof]

**(c) Sufficient one-step condition.** If `0 < t` and `t + 1 ≤ N X / n`, then
`g_X(t+1) > g_X(t)`. [mathematical proof]

_Proof._ `h_X(t+1) − h_X(t) = ∫_t^{t+1} h_X'(s) ds`. On `[t, t+1]` we have
`s ≤ t+1 ≤ N X / n`, so the numerator `X N − n s ≥ 0`; since `s (N−s) > 0`, the
integrand is `≥ 0` and is strictly positive on a set of positive measure (indeed
`h_X'` is strictly decreasing with `h_X'(s) > 0 = h_X'(t+1)` for `s < t+1`). ∎

**(d) Non-profit region.** If `n t ≥ N X` then `g_X(t+1) ≤ g_X(t)` (with strict
decrease whenever `h_X'(t) < 0`). [mathematical proof] _Proof mirror of (c): the
integrand is `≤ 0` on `[t, t+1]`. ∎_

**(e) Exact criterion.** `g_X(t+1) > g_X(t)` iff
`∫_t^{t+1} (X N − n s) / (s (N − s)) ds > 0`. The linear condition of (c) is
**sufficient but not necessary**, and condition `t < N X / n` is **necessary but not
sufficient**:

| `(X, n, N, t)` | `t < N X/n` | `t+1 ≤ N X/n` | `g_X(t+1)/g_X(t)` |
|---|---|---|---|
| `(1, 3, 5, 1)` (`AAATT` witness) | true | **false** (straddle) | `9/8 > 1` |
| `(1, 100, 101, 1)` | true | false | `≈ 0.7395 < 1` |
| `(1, 2, 5, 1)` | true | true | `3/2 > 1` |
| `(1, 3, 5, 2)` | false | false | `2/3 < 1` |

[mathematical proof + verified computation: script §B exhausts all `1 ≤ n,N ≤ 11`
and checks both implications]

The straddle row is why the obstruction cannot be reduced to a clean "under-observed"
support statement: at an integer coordinate strictly below the real maximiser the
one-step perturbation can still be strictly profitable, and that is precisely the
`AAATT` witness. [interpretation]

---

## 3. Proposition 2 (any profitable addition decomposes into profitable cycles)

Let `K ⊆ ℕ^R` be the **circulation monoid**: throughput vectors of non-negative
integral closed flows of `G_R`. By flow decomposition, `K` is generated by the
throughput vectors `c^{(1)}, …, c^{(r)}` of the elementary cycles of `G_R`:
`K = { Σ_i a_i c^{(i)} : a_i ∈ ℕ }`, and `F = K ∩ {d : 1 ≤ d_w ≤ N}` (up to the
support/lower-bound convention). [source fact + mathematical proof]

**(a) Subadditivity of increments.** For any `w` and `0 ≤ a, b` with
`d_w, d_w+a, d_w+b, d_w+a+b ≤ N`,

```text
Δ_{x_w}(a+b) ≤ Δ_{x_w}(a) + Δ_{x_w}(b).
```

[mathematical proof] _Proof._ For concave `h`, the increments of equal step size are
non-increasing in the base point, so
`h(t+a+b) − h(t+a) ≤ h(t+b) − h(t)`; adding `h(t+a) − h(t)` to both sides gives the
claim. Equivalently, in multiplicative form, `g(t+a+b) g(t) ≤ g(t+a) g(t+b)`. ∎
[verified computation: script §A checks 7987 inequalities exactly]

**(b) Profitable addition ⇒ profitable elementary cycle.** If `d_S ∈ F`, `v ∈ K`,
`d_S + v ∈ F`, and `L_x(d_S + v) > L_x(d_S)`, then some elementary cycle `c^{(j)}`
with `c^{(j)} ≤ v` satisfies `d_S + c^{(j)} ∈ F` and `L_x(d_S + c^{(j)}) > L_x(d_S)`.
[mathematical proof]

_Proof._ Write `v = Σ_j v^{(j)}` with each `v^{(j)}` a sum of copies of one
generator (so `v^{(j)}_w` counts the throughput of the `j`-th elementary cycle in a
flow decomposition of `v`; in particular `0 ≤ v^{(j)}_w ≤ v_w`). Then

```text
log L_x(d_S + v) − log L_x(d_S)
  = Σ_w Δ_{x_w}(v_w)
  ≤ Σ_w Σ_j Δ_{x_w}(v^{(j)}_w)          (subadditivity, (a))
  = Σ_j [ log L_x(d_S + v^{(j)}) − log L_x(d_S) ].
```

The left-hand side is positive, so some `j` has positive increment; rename its
throughput vector `c^{(j)}` (its support is one elementary cycle).
`d_S + c^{(j)}` is feasible because `c^{(j)} ≤ v` and `d_S + v ∈ F`. ∎

**(c) The upward cycle criterion.** `d_S` maximises `L_x` over `{d ∈ F : d ≥ d_S}`
if and only if **no** elementary cycle `c` with `d_S + c ≤ N` is profitable, i.e.
`L_x(d_S + c) ≤ L_x(d_S)`. [mathematical proof; `(b)` for necessity, immediate for
sufficiency]

**Remark (the subtractive gap).** Part (c) controls additions only. A feasible
`d ∈ F` with `d ∉ d_S + K` (a *subtractive* or mixed-sign move, e.g. dropping one
copy of an over-observed read) is not covered. In the `AAATT` instance the global
optimum found by exhaustive enumeration is additive, and every subtractive competitor
is strictly worse, so the determination does not depend on the gap. Whether bridging
constraints can ever force the *global* optimum to require a subtractive move while no
elementary cycle is profitable remains **open**; it is recorded here rather than
assumed away. [open]

---

## 4. Proposition 3 (the minimal obstruction is a profitable self-loop)

Let `w` be a read type carrying a proper self-overlap of length `≥ o_min`; then `G_R`
has a self-loop at `w` and `e_w ∈ K` (one extra traversal of the self-loop is a
closed flow). [source fact + mathematical proof]

**Self-loop obstruction.** If `d_S,w < N` and the exact one-step ratio satisfies
`g_{x_w}(d_S,w + 1) > g_{x_w}(d_S,w)` (e.g. if `d_S,w + 1 ≤ N x_w / n`), then
`d_S + e_w ∈ F` and `L_x(d_S + e_w) > L_x(d_S)`. Hence `d_S` is not optimal.
[mathematical proof]

**Minimality.** Every non-zero element of `ℕ^R` has support at least `1`, and the
only support-`1` directions are the unit vectors `e_w`. Hence a profitable elementary
cycle of support `1` is the support-minimal possible obstruction, and it exists
exactly when an observed read type has (i) a proper self-overlap and (ii) a profitable
unit increment. The `AAATT` witness is of this minimal kind: the only profitable
generator of its reduced circulation cone is `(1,0,0)`, the `AAA` self-loop.
[mathematical proof + verified computation; §5]

**Corollary (obstruction is not removed by bridging).** A self-overlap is a property
of the read word alone; `I_s` neither removes the self-loop from `G_R` nor constrains
`d_w` to `1`. A homopolymer run of length `≥ 2` gives rise to a read type `A^L` with a
proper self-overlap *and* a maximal triple repeat that `I_s` forces to be all-bridged.
The two facts coexist; bridging constrains the *spanning*/repeat structure and not the
self-loop multiplicity. [mathematical proof + the kernel-checked `AAATT` certificate]

---

## 5. The `AAATT` instance realizes the primitive

The finite witness already kernel-checked on this branch
(`AssemblyP1/Section62LowerBoundOneCounterexample.lean`) is exactly the self-loop
primitive:

```text
truth      S = AAATT   (N = 5),  L = 3,  reads starts (0,1,4)
observed   x = { AAA:1, AAT:1, TAA:1 },  n = 3
truth flow d_S = (1,2,2)   over (AAA, AAT, TAA)
reduced circulation cone generators: (1,0,0) [AAA self-loop], (0,1,1) [AAT↔TAA 2-cycle]
self-loop increment at d_S:  L((2,2,2))/L((1,2,2)) = 9/8 > 1
two-cycle increment at d_S:  L((1,3,3))/L((1,2,2)) = 4/9 < 1
exhaustive closed-flow optimum in 1 ≤ d_w ≤ 5:  (2,2,2)
```

[verified computation: script §C–§D; kernel-checked for the `9/8` strict inequality
and the `I_s` certificate in the cited Lean file]

The two-cycle direction is *not* profitable, so the obstruction is genuinely the
support-`1` self-loop and not an artefact of a larger cycle. The clean linear threshold
`d_S,AAA + 1 = 2 ≤ N x_AAA / n = 5/3` fails, yet the step is profitable (`ρ = 9/8`):
the witness is a boundary (straddle) case of Proposition 1(e).

A second multiplicity choice on the *same support* makes the linear threshold hold:
`x = (AAA:2, AAT:1, TAA:1)`, `n = 4` gives `d*_AAA = 5/2` and self-loop ratio `9/4`.
[verified computation; script §D]

---

## 6. Proposition 4 (bridging is multiplicity-blind — the structural reason)

Fix a realized read set `T` (a set of circular start positions of the true genome
`S`). Then:

1. the coverage and bridging conjuncts of `I_s` are functions of `T` alone;
2. the read-type support `R = { class(window at r) : r ∈ T }` is a function of `T`
   alone;
3. the truth flow `d_S`, being intrinsic to `S`, does not depend on `T` at all beyond
   `supp(d_S) ⊇ R`.

Multiplicities are extra data: any `x : R → ℕ_{>0}` with `Σ x_w = n` is realizable by
sampling the reads in `T` with those multiplicities, and leaves `T`, `I_s`, `R`, and
`d_S` unchanged. [modeling normalization + mathematical proof]

Consequently the implication `(P)` is equivalent to

> for every `x` on the fixed support `R`, `d_S` maximises `L_x` over `F`.

and this fails as soon as **one** compatible `x` and **one** feasible elementary cycle
makes the cycle profitable. No predicate that depends only on `T` (equivalently, only
on `I_s`) can force the `x`-dependent target `d*_w = N x_w / n` to equal `d_S,w`.

**Verified decoupling on the `AAATT` support.** With `R = {AAA, AAT, TAA}` and the same
`d_S = (1,2,2)`:

| `x` | `n` | target `d*` | ML optimum | truth optimal? |
|---|---|---|---|---|
| `(1,1,1)` | 3 | `(5/3, 5/3, 5/3)` | `(2,2,2)` | no (ratio `9/8`) |
| `(1,2,2)` | 5 | `(1, 2, 2)` | `(1,2,2)` | **yes** |

[verified computation: script §E]

The two rows have identical `I_s`, identical `R`, identical `d_S`; only the observed
multiplicities differ. Hence `I_s` cannot be the missing hypothesis. [mathematical
proof + verified computation]

**Positive boundary (for contrast).** If `supp(x) = supp(d_S)` and
`x_w / n = d_S,w / N` for every `w`, then `d*_w = d_S,w` and `d_S` is the coordinatewise
unconstrained maximiser; it is therefore optimal over every feasible set. This is the
"proportional observation" slice (`x ∝ d_S`), and it is not implied by `I_s`.
[mathematical proof]

---

## 7. What this settles, and what it does not

**Settles.** `I_s` + truth-flow feasibility does **not** force §6.1 fixed-`N` binomial
optimality. The structural reason is that bridging sees only the read *set*, while the
objective sees the multiplicities; and the support-minimal counterexample primitive is
a profitable self-loop — an under-observed read with a proper self-overlap. The
`AAATT` instance realizes the primitive with a kernel-checked `9/8`. The earlier
"under-observation obstruction" of
`docs/section62-bidirected-lowerbound1-determination.md` §3.2 is here sharpened into a
one-step criterion, a decomposition theorem, and a minimality statement.

**Does not settle.**

1. Which Medvedev–Brudno object the 2016 Shomorony sentence denotes. [open]
2. The subtractive gap of Proposition 2(c): whether a global counterexample can
   require a mixed-sign move with no profitable elementary cycle. [open]
3. The exact-multinomial (candidate-intrinsic `N(D)`) analogue of these propositions.
   [open]
4. Uniqueness/tie semantics, and the single-strand reading. [open]

---

## 8. Relation to existing artifacts

| Artifact | Relation |
|---|---|
| `docs/section62-bidirected-lowerbound1-determination.md` | its §3.2 "under-observation obstruction" is the additive special case; this note adds the exact one-step criterion (Prop. 1), the subadditivity/decomposition theorem (Prop. 2), minimality (Prop. 3), and the multiplicity decoupling (Prop. 4) |
| `docs/section62-aaatt-reduced-flow-cone-and-spectra.md` | supplies the reduced cone `{(a,k,k)}` with Hilbert basis `(1,0,0),(0,1,1)` used in §5; independently re-derived in the script |
| `docs/independent-se62-bidirected-model.md` | independently reproduces the same witness and the exhaustive closed-flow optimum |
| `AssemblyP1/Section62LowerBoundOneCounterexample.lean` | kernel-checks the `AAATT` `I_s` certificate, both `FeasibleType` claims, and `lik d_S < lik d_D` (`9/8`) |
| `docs/section62-feasibility-necessity-determination.md` | decides that §6.2 feasibility is not *necessary* for the published question; this note supplies the structural reason the §6.2-restricted implication fails |
| `docs/section62-kkt-and-bridging-family.md` (branch `analysis/se62-kkt-bridging-family-0920`) | its Theorem 1 is the definition of global optimality written with the gradient; its Theorem 2 is the *sufficient* single-cycle condition. This note adds the converse reduction within additions (Prop. 2b–c: any profitable additive displacement contains a profitable elementary cycle), the exact one-step criterion, the self-loop minimality, and the multiplicity decoupling (Prop. 4). Its infinite bridging-insufficiency family is **not** used here: the strict-bridging correction of `docs/section62-bidirected-lowerbound1-determination.md` §5 shows that family's `I_s` claim is false under the repository's accepted predicate, while the finite `AAATT` witness is unaffected |

**Note on the concurrent KKT packet.** The KKT/descent note independently reaches the
same negative answer and is a useful gradient picture. This note deliberately does not
rely on its infinite family, because the family's `I_s` certificate uses a wrap-around
"covers both flanks" test that is not the accepted strict predicate; the finite
kernel-checked witness is independent of that dispute. The genuinely new structural
content here is (i) the subadditivity/cycle-decomposition reduction, (ii) the
self-loop as the support-minimal obstruction, and (iii) the multiplicity-blindness of
`I_s`. [interpretation]

---

## 9. Epistemic status

| Claim | Status |
|---|---|
| §6.2 model (molecules, bidirected reduced graph, lower bound `1`, closed flows, §6.1 external-`N` binomial) | **source fact + modeling choice** (§1) |
| `g_X` strictly log-concave; real maximiser `N X / n` (Prop. 1a,b) | **mathematical proof** |
| Sufficient one-step condition `t+1 ≤ N X/n`; non-profit region `n t ≥ N X` (Prop. 1c,d) | **mathematical proof + verified computation** |
| Linear condition sufficient not necessary; `t < N X/n` necessary not sufficient (Prop. 1e) | **mathematical proof + verified computation** (`(1,3,5,1)`, `(1,100,101,1)`) |
| Subadditivity `Δ(a+b) ≤ Δ(a)+Δ(b)` (Prop. 2a) | **mathematical proof + verified computation** (7987 exact checks) |
| Profitable addition ⇒ profitable elementary cycle (Prop. 2b) | **mathematical proof** |
| Upward cycle criterion (Prop. 2c) | **mathematical proof** |
| Subtractive/mixed-sign global obstruction | **open** (Prop. 2 remark) |
| Self-loop is the support-minimal obstruction (Prop. 3) | **mathematical proof** |
| Bridging is multiplicity-blind (Prop. 4) | **modeling normalization + mathematical proof** |
| `AAATT` realization: `9/8` via `(1,0,0)`, two-cycle `4/9`, optimum `(2,2,2)` | **verified computation**; `9/8` and `I_s` **kernel-checked** |
| `x = (1,2,2)` makes the same-support truth optimal | **verified computation** |
| Implication `(P)` is false | follows |

---

## 10. Reproduce

```sh
python3 scripts/verify_se62_ml_cycle_obstruction.py
lake build AssemblyP1.Section62LowerBoundOneCounterexample
```

The script is self-contained (no repository imports), uses exact
`fractions.Fraction`/integer arithmetic, and exits non-zero on any failed assertion.
It checks §A–§E above: subadditivity, the one-step thresholds and boundary examples,
the reduced cone generators, the exact generator increments at `d_S`, the exhaustive
closed-flow optimum, and the multiplicity-decoupling pair.

Primary sources: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome Assembly*,
*J. Comput. Biol.* 16(8) (2009) 1101–1116, §6.1–6.2, DOI `10.1089/cmb.2009.0047`,
PMC3154397; Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*, *Bioinformatics*
32(17) (2016) i494–i502, Eq. (1); Guy Bresler, Ma’ayan Bresler, David Tse, *Optimal
assembly for high throughput shotgun sequencing*, *BMC Bioinformatics* 14(Suppl 5):S18
(2013).
