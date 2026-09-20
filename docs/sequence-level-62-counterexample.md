# A sequence-level §6.2 counterexample with a flow-feasible truth

_Status: mathematical proof + kernel-checkable finite exact-rational computation,
2026-09-20. All claims are classified as **source fact**, **source-supported
inference**, **mathematical argument**, **verified computation**, or **open**.
This note refutes a specific well-posed strengthening of the published
Shomorony et al. question; it does **not** settle the source-ambiguous published
sentence (which §6.1/§6.2 objective, candidate class, and tie semantics were
intended)._

_Reproduction:
`python3 scripts/verify_sequence_level_62_counterexample.py` (all assertions
pass; exact `fractions.Fraction`; deterministic) and
`lake build AssemblyP1.SequenceLevel62Counterexample` (kernel check)._

---

## 0. Answer at a glance

The repository's well-posed sequence-level question, recorded as open in
`docs/section-6-2-feasible-set-membership.md` §5 and
`docs/section62-bidirected-flow-feasibility.md` §6,

> Does `I_s` together with `S ∈ F_flow(R)` imply that `S` is a maximizer of the
> §6.2 (or §6.1) objective over sequence-level flow-feasible `D`?

is **false**. Explicit counterexample (single-strand reading, binary alphabet,
read length `L = 4`):

```
truth            S = AAAAAB                 (G = 6)
realized starts  = (0, 2, 3, 4, 5)          (n = 5 reads)
observed         x = {AAAA:1, AAAB:1, AABA:1, ABAA:1, BAAA:1}
competitor       D = AAABA                  (read-tiled: spec_4(D) = x)
```

- The source information-feasible hypothesis `I_s` holds for `(S, reads)`
  non-vacuously (coverage; six maximal all-bridged triple repeats; no
  interleaved repeat pair). **Mathematical proof + verified computation.**
- Both `S` and `D` are sequence-level §6.2 feasible in the Observation-7
  reading (`supp(spec_4(S)) = supp(x)`, `d_S ≥ x`; `spec_4(D) = x`).
  **Verified computation** (finite exact check).
- The competitor strictly beats the truth under both objectives:
  `L_exact(D)/L_exact(S) = 3888/3125 > 1` and the literal §6.1 binomial ratio is
  `625/512 > 1` (external `N = G = 6`), or `128/81 > 1` (external `N = n = 5`).
  **Mathematical proof + verified computation.**

The previous exhaustive search reported zero counterexamples only because it
fixed the number of reads `n` equal to the truth length `G`. With `n = G`, truth
feasibility `d_S ≥ x` plus `Σx = n = G = Σd_S` forces `x = d_S`, so no strictly
better read-tiled competitor can exist in that scope (§3).

This is a negative settlement of the *well-posed sequence-level schema*. It is
not a settlement of the 2016 sentence, because the source does not select the
objective, candidate class, or tie semantics
(`docs/source-notes/ml-objective-candidate-class-resolution.md`).

---

## 1. Exact predicates

Circular genome `S` of length `G`; read length `L`. The length-`L` window at
start `i` is `w_i = S[i..i+L-1]` (indices mod `G`); `spec_L(S)` is the multiset
of the `G` windows; `d_S(w)` its multiplicity. For a realized start multiset
`T`, the observed read multiset is `x(w) = #{t ∈ T : w_t = w}`.

**`I_s`** (Shomorony et al. 2016, Eq. (1), inherited from Bresler–Bresler–Tse
2013; transcription `docs/bridging-source-semantics.md`): coverage
(every position lies in some realized read), every maximal triple repeat
all-bridged, every interleaved repeat pair bridged. Maximal repeat pair / triple
repeat use the Bresler maximality conditions (preceding symbols differ and
following symbols differ, respectively not all equal over three copies).

**Sequence-level `F_flow(R)`** (`docs/section-6-2-feasible-set-membership.md`
§2; Observation-7 criterion): a circular molecule `D` is feasible iff

1. `supp(spec_L(D)) = supp(x)` (support equality, not just containment), and
2. `d_D(w) ≥ x_w` for every type `w` (per-occurrence lower bound).

---

## 2. The witness

`S = AAAAAB`, `G = 6`, `L = 4`, canonical starts `T = (0, 2, 3, 4, 5)`.

Windows of `S` (start: window): `0: AAAA`, `1: AAAA`, `2: AAAB`, `3: AABA`,
`4: ABAA`, `5: BAAA`, so

```
spec_4(S) = {AAAA:2, AAAB:1, AABA:1, ABAA:1, BAAA:1}.
```

Realized reads (`T`): `0: AAAA`, `2: AAAB`, `3: AABA`, `4: ABAA`, `5: BAAA`, so

```
x = {AAAA:1, AAAB:1, AABA:1, ABAA:1, BAAA:1},   n = 5.
```

### 2.1 `I_s` certificate (verified computation)

- **Coverage.** Reads at `0,2,3,4,5` cover position sets
  `{0,1,2,3}`, `{2,3,4,5}`, `{3,4,5,0}`, `{4,5,0,1}`, `{5,0,1,2}`; union all of
  `{0,…,5}`.
- **Triple repeats.** The maximal triple repeats are
  `(ℓ=1: {0,1,4}, {0,2,4}, {0,3,4})`, `(ℓ=2: {0,1,3}, {0,2,3})`, and
  `(ℓ=3: {0,1,2})`. Every selected copy at position `t` is bridged by a realized
  read: for the length-`1` triples a read covers `t−1` and `t+1`; for `ℓ=2`
  covers `t−1` and `t+2`; for `ℓ=3` covers `t−1` and `t+3`. The script checks
  each copy explicitly.
- **Interleaved pairs.** The maximal repeat pairs are
  `(ℓ=1: {0,4})`, `(ℓ=2: {0,3})`, `(ℓ=3: {0,2})`, `(ℓ=4: {0,1})`. They all share
  position `0`, so no two have four distinct alternating starts; there is no
  interleaved pair. This is independent of the cyclic-origin normalization and
  of whether maximality is read as "both sides differ" or the weaker
  "at least one side differs".

Hence `I_s` holds for `(S, T)`, and both the triple-repeat conjunct and the
length-`1`/`ℓ≥2` bridging conjuncts are genuinely exercised (not vacuous).

### 2.2 Both genomes are sequence-level §6.2 feasible

`spec_4(S)` has support `{AAAA,AAAB,AABA,ABAA,BAAA} = supp(x)` and
`d_S(AAAA) = 2 ≥ 1 = x(AAAA)`, `d_S(w) = 1 = x(w)` for the other four types.
So `S ∈ F_flow(R)`.

`D = AAABA` (length `5`) has windows `0:AAAB`, `1:AABA`, `2:ABAA`, `3:BAAA`,
`4:AAAA`, i.e. `spec_4(D) = x` exactly. So `D` is *read-tiled*, hence
`D ∈ F_flow(R)` and every read vertex is visited once (lower bound `1`
satisfied). Both `S` and `D` correspond to closed walks on the observed read
vertices with length-`(L−1)` overlaps, so both are legitimate spelled
molecules, not mere flow count vectors.

### 2.3 The competitor strictly beats the truth

Observation-only multinomial coefficients cancel in the exact ratio:

```
L_exact(D)/L_exact(S) = ∏_w (d_D(w)/|D|)^{x_w} / (d_S(w)/G)^{x_w}
                      = (1/5)^5 / ((2/6)·(1/6)^4)
                      = 3888/3125 > 1.
```

The literal §6.1 separable binomial ratio is

```
∏_w d_D(w)^{x_w}(N−d_D(w))^{n−x_w} / d_S(w)^{x_w}(N−d_S(w))^{n−x_w}
  = (625/512) > 1   for external N = G = 6,
  = (128/81)  > 1   for external N = n = 5.
```

The sign of the comparison is therefore robust to the exact-vs-binomial
objective fork.

### 2.4 Kernel check

`AssemblyP1/SequenceLevel62Counterexample.lean` kernel-checks the finite
instance, using only `decide`/`norm_num`:

| theorem | content |
|---|---|
| `truth_information_feasible` | coverage, all maximal triple repeats all-bridged, all interleaved pairs bridged (quantified over the finite instance) |
| `truth_section62_feasible` | `supp(spec_4(S)) = supp(x)` and `d_S ≥ x` |
| `competitor_read_tiled` | `spec_4(D) = x` |
| `competitor_beats_truth` | `likelihoodTruth < likelihoodCompetitor`; `likelihood_ratio` gives `3888/3125` |
| `sequence_level_section62_counterexample` | conjunction of the above |

Axiom audit (`#print axioms`) reports only `propext`, `Classical.choice`,
`Quot.sound`; no `sorry`, `admit`, or new axioms. The Lean `Interleaved`
predicate checks cyclic alternation of the two selected starts by sorting the
four positions and testing the label sequence, and `Bridged` uses the strict
one-base-each-side extension convention; these match the source transcription in
`docs/bridging-source-semantics.md`.

---

## 3. Why the earlier exhaustive search missed it

`docs/section62-bidirected-flow-feasibility.md` §5 reports 85 572 searched
instances and zero sequence-level counterexamples. Its
`search(G, L, σ, N, maxD, comp)` is always called with `N = G`, and it enumerates
start multisets of size exactly `N = G`
(`scripts/se62_bidirected_feasibility_search.py:329,243`).

With exactly `G` reads, truth feasibility is degenerate:

> `Σ_w x_w = n = G = Σ_w d_S(w)` and `x_w ≤ d_S(w)` coordinatewise force
> `x_w = d_S(w)` for every `w`.

Then the observed empirical distribution equals the truth's window
distribution, and the read-tiled competitor must satisfy `d_D ≥ x = d_S`; the
truth is a maximizer (ties are exactly the `k·d_S` class, by the AM–GM argument
of `docs/bridging-schemas-and-flow-feasibility-gaps.md` Prop. D). So the
`N = G` scope **cannot contain a counterexample by construction**, independent of
`I_s`. The witness has `n = 5 < G = 6` and lies outside the scope.

This also qualifies the claim in `docs/read-tiled-counterexample.md` §0.5 that
"when the observed spectrum is complete (`supp(x) = supp(S)`) the truth is a
maximizer among support-contained candidates in every tested range": the tested
ranges only reached `x = d_S`, so they did not test the complete-spectrum,
strictly-smaller-multiplicity case, which is exactly what fails here.

---

## 4. Why this is the general mechanism, not an accident

`docs/read-tiled-counterexample.md` Theorem 1 (read-tiled dominance) already
proves: if the observed histogram `x` is realizable as the spectrum of a
circular genome `D` (`|D| = n`, `d_D = x`), then `L_exact(D) = exp(n·D_KL(x/n ‖
d_S/G))·L_exact(S)`. Hence

> **Corollary.** If `(S, R)` satisfies `I_s`, `S ∈ F_flow(R)`, and `x` is
> Eulerian-realizable with `x/n ≠ d_S/G`, then `S` is **not** an exact
> multinomial maximizer over flow-feasible molecules.

The witness of §2 is the smallest binary instance of this corollary with
`n < G` (the bounded script recovers it and enumerates 38 such witnesses for
`G ≤ 7`). Realizability of `x` is exactly the Eulerian condition on the
de Bruijn multigraph of its `L`-mers (balanced degrees plus edge connectivity),
which the script checks.

The earlier repository note "Variant F is refuted ... the truth is not
flow-feasible there" (`docs/read-tiled-counterexample.md` §3.2) exhibited a
witness in which the truth was *infeasible*, so the negative conclusion was read
as not transferring to the well-posed schema. The present witness shows the
truth can be feasible simultaneously.

---

## 5. What this does and does not establish

| statement | status |
|---|---|
| `I_s` holds for the listed `(S, reads)` (coverage, non-vacuous all-bridged triples, no interleaved pair) | **mathematical proof + verified computation** |
| `S` and `D` are sequence-level §6.2 feasible (`supp`, `d ≥ x`) | **verified computation** (finite exact) |
| `L_exact(D) > L_exact(S)` and §6.1-binomial `L(D) > L(S)` | **mathematical proof + verified computation** |
| `I_s ∧ S ∈ F_flow ⇒ S is ML over `F_flow`` | **refuted** (this note) |
| the `N = G` search scope cannot contain such a counterexample | **mathematical argument** (`x = d_S`) |
| the published 2016 open sentence is settled | **no** — objective, candidate class, and tie semantics remain source-ambiguous |
| double-stranded / reverse-complement reading, general `o_min`, non-spellable flows | **not addressed here** |

### Epistemic status

| claim | class |
|---|---|
| `I_s` predicate transcription | source-supported (Bresler 2013 via Shomorony 2016; `docs/bridging-source-semantics.md`) |
| Observation-7 sequence-level `F_flow` criterion | mathematical argument (source note `docs/section-6-2-feasible-set-membership.md` §2) |
| the finite instance's predicates and ratios | verified computation (exact rationals) + kernel-checked (`AssemblyP1/SequenceLevel62Counterexample.lean`) |
| the general corollary | mathematical proof (repository Theorem 1) |
| published-problem settlement | open |

### Non-claims

This note does not decide which §6.1/§6.2 object the 2016 sentence intends; it
does not address the reverse-complement equivalence fork (which, for the
`A↔T` reading, can change which witnesses transfer,
`docs/section62-bidirected-flow-feasibility.md` §3.2); it does not claim the
source's algorithm would output `D` (only that `D` is admissible and more
likely); and it does not cover non-spellable flow count vectors.

Primary sources: Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C.
Tse, *Information-optimal genome assembly via sparse read-overlap graphs*,
Bioinformatics 32(17) (2016) i494–i502, Eq. (1); Paul Medvedev, Michael Brudno,
*Maximum Likelihood Genome Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116,
§6.1–6.2; Guy Bresler, Ma'ayan Bresler, David Tse, *Optimal assembly for high
throughput shotgun sequencing*, BMC Bioinformatics 14(Suppl 5):S18 (2013).

Cross-references: `docs/read-tiled-counterexample.md` (Theorem 1 and the
infeasible-truth witness); `docs/section-6-2-feasible-set-membership.md` (the
membership table and the open question); `docs/section62-bidirected-flow-feasibility.md`
(the `N = G` search); `docs/bridging-source-semantics.md` (predicate
transcription); `docs/ml-formalization-contract.md` (variant discipline).
