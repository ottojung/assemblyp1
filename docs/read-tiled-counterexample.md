# The fixed-length exact frontier under graded feasibility: a read-tiled counterexample

_Status: mathematical proof + kernel-checked finite counterexample + bounded
exhaustive computational evidence. 2026-09-19. Builds on the merged
fixed-length counterexample (`docs/fixed-length-exact-counterexample.md`,
`AssemblyP1/FixedLengthExactCounterexample.lean`) and on the schema/flow
corrections in `docs/bridging-schemas-and-flow-feasibility-gaps.md`. All claims
are classified by epistemic class; this note does not settle the source-ambiguous
Shomorony et al. open question._

---

## 0. Answer at a glance

1. The merged `AAABB → AAAAB` witness refutes the fixed-length exact
   multinomial target over **all** length-`G` candidates. Its strongest
   consequence is structural, not quantitative: the exact multinomial
   likelihood depends only on the candidate's `L`-mer spectrum, while the
   source `I_s` hypothesis constrains only the latent sampling realization; a
   candidate can therefore duplicate an overrepresented `L`-mer and win.

2. Adding a **feasibility** constraint on the candidate's spectrum is the only
   way to make the target non-trivially true. The relevant graded constraints
   are: support containment `supp(D) ⊆ supp(x)` (implied by every flow/assembly
   reading of Medvedev–Brudno §6.2), and the stronger **read-tiling** condition
   `d_D = x` (the per-occurrence reading: the candidate is exactly an assembly
   of the observed read multiset).

3. **Read-tiling does not rescue the target.** We prove a general dominance
   theorem (Theorem 1): if the observed read-type count vector `x` is realizable
   as the spectrum of a circular genome `D` of length `N`, then `D` is
   flow-feasible and its exact likelihood is at least the truth's, with equality
   iff `x/N = d_S/G`. And we kernel-check a concrete finite instance
   (`S = AAABCBC`, `G = 7`, `L = 3`) in which the full source `I_s` holds, the
   reads are exactly the spectrum of the read-tiled competitor `D = AAAAABC`,
   and `L(D)/L(S) = 27 > 1`. The truth is not flow-feasible there.

4. Consequently the repository's repeated claim that **Variant F (flow-feasible
   candidates) is "the only survivor" with no known counterexample is false**
   under either natural reading of §6.2. See §7 for the corrections.

5. What genuinely remains: when the observed spectrum is **complete**
   (`supp(x) = supp(S)`) the truth is a maximizer among support-contained
   candidates in every tested range (and provably so for repeat-free `S`), and
   the truth is read-tiled exactly when `x = d_S`, in which case all read-tiled
   candidates tie. So the only surviving positive content is the
   complete-spectrum, truth-feasible corner, which the i.i.d. sampling model
   reaches only in the no-oversampling regime.

---

## 1. The graded feasibility hierarchy

Fix read length `L`, a true circular genome `S` of length `G`, and a realized
read multiset `R` with `N` reads and observed type counts `x = (x_w)`.

**Variant E (fixed-length exact).** Candidates are all circular genomes `D` with
`|D| = G`; the objective is
`L_exact(D | x) ∝ ∏_w (d_D(w) / G)^{x_w}`.

**Support-contained (SC).** Add `supp(D) ⊆ supp(x)`. This is necessary for `D`
to be spelled by any walk in the read-overlap graph: the assembly can only use
read types that were observed.

**Per-occurrence / read-tiled (RT).** Add `d_D = x`. This is the condition that
`D`'s length-`L` window multiset is exactly the observed read multiset: each
observed read occurrence is used exactly once, and `|D| = N`.  A read-tiled
genome is spelled by the cyclic read order, hence flow-feasible in the
per-occurrence reading of Medvedev–Brudno §6.2.  In the per-*type* reading of
§6.2, the candidate set is exactly SC.

The inclusions are strict: RT ⊆ SC ⊆ E.

---

## 2. Theorem 1: read-tiled assemblies dominate (proof)

**Theorem 1 (read-tiled dominance).** Let `R` be a read sample with `N` reads and
type counts `x`, and suppose there is a circular genome `D` with `|D| = N` and
`d_D(w) = x_w` for every type `w`. Let `S` be any circular genome with
`d_S(w) > 0` whenever `x_w > 0`. Write `p_w = x_w / N` and
`q_w = d_S(w) / |S|`. Then

```
L_exact(D | x) / L_exact(S | x) = exp( N · D_KL(p ‖ q) )  ≥ 1,
```

with equality in the likelihoods iff `x_w / N = d_S(w) / |S|` for all `w`.

**Proof.** Both likelihoods share the observation-only multinomial coefficient
`N! / ∏_w x_w!`. Using the candidate's own length in the denominator,

```
L_exact(D|x) = (N!/∏x_w!) · ∏_w (x_w/N)^{x_w},
L_exact(S|x) = (N!/∏x_w!) · ∏_w (d_S(w)/|S|)^{x_w}.
```

The log-ratio is

```
Σ_w x_w log( (x_w/N) / (d_S(w)/|S|) )
  = N · Σ_w (x_w/N) log( (x_w/N) / q_w )
  = N · D_KL(p ‖ q) ≥ 0,
```

by Gibbs' inequality, with equality iff `p = q`. ∎

**Epistemic class: mathematical proof.**

**Consequence.** Whenever the sample's own type histogram happens to be
realizable as a genome, that genome is a flow-feasible competitor that is at
least as likely as the truth, and strictly more likely unless the empirical
distribution equals the truth's k-mer distribution. The source `I_s` hypothesis
does **not** imply `p = q`, so it does not force the truth to be the maximizer
over flow-feasible candidates.

**Corollary 1a (conditional positive).** If the truth itself is read-tiled
(`d_S = x`), then every read-tiled candidate has spectrum `x = d_S`, so all
read-tiled candidates have the same likelihood: the truth is a maximizer (ties
only), with no bridging content. Under the per-occurrence flow reading this is
the only situation in which the truth can be guaranteed optimal, and the
hypothesis forces `N = G` and no oversampling. Under the per-type reading the
truth is feasible whenever the observed spectrum is complete (`supp(x) =
supp(S)`), a strictly weaker condition.

---

## 3. The new finite counterexample

```
truth        S = A A A B C B C        (G = 7)
competitor   D = A A A A A B C        (G = 7)
read length  L = 3
latent starts  = (0, 0, 0, 1, 2, 5, 6)      (N = 7)
observed types = { AAA:3, AAB:1, ABC:1, BCA:1, CAA:1 } = x
```

### 3.1 Source hypothesis `I_s`

- **Coverage.** Reads at starts `0, 1, 2, 5, 6` cover positions
  `{0,1,2} ∪ {1,2,3} ∪ {2,3,4} ∪ {5,6,0} ∪ {6,0,1} = {0,…,6}`.
- **Triple repeat.** The `A` copies at positions `0, 1, 2` form the unique
  maximal length-`1` triple repeat: the preceding symbols are `C, A, A` (not
  all equal) and the following symbols are `A, A, B` (not all equal). There is
  no other maximal repeat with three selected copies (length-`2` windows
  `AA, AA, AB, BC, CB, BC, CA` contain no repeated triple).
- **All-bridged.** Copy `0` is bridged by the read at `6` (covers `6,0,1`),
  copy `1` by the read at `0` (covers `0,1,2`), copy `2` by the read at `1`
  (covers `1,2,3`).
- **Interleaved pairs.** None: the maximal repeat pairs are `A@(0,2)`,
  `AA@(0,1)`, and `BC@(3,5)`, and no two have four starts alternating on the
  circle (`A@(0,2)` and `BC@(3,5)` give cyclic labels `A,A,BC,BC`; `AA@(0,1)`
  shares a start with `A@(0,2)`).

Hence `R ∈ I_s`, non-vacuously.

### 3.2 The competitor is read-tiled and flow-feasible

Circular length-`3` windows of `D = AAAAABC` are
`AAA, AAA, AAA, AAB, ABC, BCA, CAA`, i.e. exactly `x`. So `d_D = x`, `|D| = N`,
and the cyclic read order is a valid overlap walk; `D` is flow-feasible.

The truth is **not** flow-feasible: its windows include `BCB` and `CBC`, which
are absent from `R`, so no closed walk in the read-overlap graph can spell `S`.
Thus `S ∉ F_flow(R)` even though `R ∈ I_s`.

The witness is single-strand. Passing to the bidirected/double-strand graph, or
to the transitive reduction, can only *enlarge* the admissible candidate set,
so this refutation is not an artifact of the single-strand normalization.

### 3.3 Exact likelihood

Length `G = N = 7` is common to truth and competitor, so the length factor
cancels. With `d_S(AAA) = 1` and `d_D(AAA) = 3`, and all other observed types
having `d_S = d_D = 1`,

```
L(D) / L(S) = (3/1)^3 = 27 > 1.
```

(`L(S) = 840/7^7`, `L(D) = 840·27/7^7`, matching Theorem 1's
`exp(7 · D_KL(p‖q))` with `D_KL = (3/7) log 3`.)

### 3.4 Kernel check

`AssemblyP1/ReadTiledCounterexample.lean` defines `ReadTiled` (the candidate
condition `d_D = x`), proves `ReadTiled competitor`,
`¬ ReadTiled truth`, `SourceHypotheses truth` (coverage plus the all-bridged
triple-repeat certificate), and the main theorem

```
read_tiled_counterexample :
  SourceHypotheses truth ∧ ReadTiled competitor ∧
    ¬ IsMaximumLikelihoodAmongReadTiled truth
```

using only `decide`/`norm_num`. Axiom audit reports only `propext`,
`Classical.choice`, `Quot.sound`; no `sorry`, `admit`, or new axioms.

**Epistemic class: kernel-checked finite theorem** (subject to the source/model
caveats in §6 of `docs/bridging-schemas-and-flow-feasibility-gaps.md` about
which §6.2 reading is intended).

---

## 4. Bounded exhaustive frontier survey

`scripts/support_feasibility_search.py` enumerates every truth genome, every
realized start multiset up to `N`, the full source `I_s`, and evaluates the
best competitor in each graded class with exact rational arithmetic. Counts
are exact; absence of witnesses is only within the stated finite ranges.

| `G` | `L` | `σ` | `N` | hypothesis | I_s instances | E cex | SC cex | RT/F* cex |
|----|----|----|----|-----------|---------------|-------|--------|-----------|
| 5 | 3 | 2 | 3 | I_s | 60 | 10 | 0 | 0 |
| 5 | 3 | 2 | 5 | I_s | 512 | 60 | 0 | 0 |
| 5 | 3 | 3 | 5 | I_s | 11 223 | 180 | 0 | 0 |
| 6 | 3 | 3 | 6 | I_s | 54 630 | 900 | 0 | 0 |
| 6 | 4 | 3 | 6 | I_s | 176 544 | 360 | 0 | 0 |
| 7 | 3 | 2 | 7 | I_s | 2 270 | 0 | 0 | 0 |
| 7 | 3 | 3 | 7 | I_s | 164 370 | 7 728 | **630** | **42** |
| 6 | 3 | 3 | 6 | coverage only | 244 944 | 12 348 | **1 800** | **216** |
| 6 | 3 | 3 | 6 | I_s, complete spectrum | 54 630 | 0 | 0 | 0 |
| 6 | 3 | 3 | 6 | coverage only, complete spectrum | 244 944 | 324 | 0 | 0 |
| 6 | 3 | 3 | 8 | I_s, complete spectrum | 208 467 | 0 | 0 | 0 |
| 7 | 3 | 3 | 7 | I_s, complete spectrum | 164 370 | 0 | 0 | 0 |

Observations, labelled as bounded computational evidence:

1. At `G ≤ 6` and every tested `(L, σ, N)`, **support containment eliminates all
   `I_s` counterexamples**, even though `E` has many with unbounded ratios
   (e.g. `AAABB → AAAAB`, ratio `2^{x_AAA}`). The first support-contained
   witness appears at `G = 7`, exactly the first length at which a self-loop
   `L`-mer can occur three times under Eulerian balance.
2. **Coverage alone is not enough**: with coverage but without the
   all-bridged-triple-repeat/interleaving conjuncts, SC and RT counterexamples
   already appear at `G = 6` (`1 800` and `216`). The bridging conjuncts, not
   coverage, are what block concentration at `G ≤ 6`.
3. **Complete observed spectrum is a sharp safe boundary.** In every tested
   range with `supp(x) = supp(S)`, the SC class has zero counterexamples, and
   under `I_s` even the unrestricted `E` class has zero. For repeat-free `S`
   this is immediate (`supp` containment plus complete spectrum forces
   `d_D = d_S`); the general repeated-spectrum case is covered by computation
   only.
4. The `G = 7` read-tiled witness is minimal in the tested ranges: the
   concentration `d_D(AAA) = 3` requires `G ≥ 7` under Eulerian balance.

---

## 5. The strongest consequence of the merged `AAABB` witness

The merged kernel-checked witness refutes fixed-length exact ML over all
length-`G` candidates. The sharpest general reading is:

> The exact multinomial objective depends on a candidate only through its
> `L`-mer spectrum `d_D`, and the source `I_s` hypothesis constrains only the
> latent realization `(S, R)`; `I_s` places no constraint on `d_D`. Since the
> unconstrained empirical-spectrum estimate `d_D ∝ x` is attainable whenever
> `x` is balanced, `I_s` cannot by itself force the truth to be optimal. The
> `AAABB` parametric family (`AAA^k, AAB, BAA`, ratio `2^k → ∞`) exhibits this
> without any large-`G` structure.

Adding feasibility that constrains `d_D` is therefore necessary. Theorem 1
shows that even the strongest spectrum constraint (`d_D = x`) does not by
itself restore the target, because `I_s` does not force `x = d_S`.

---

## 6. Reproducibility

```bash
python3 scripts/verify_flow_feasible_counterexample.py     # all checks PASS

# frontier survey (exact rational arithmetic)
python3 scripts/support_feasibility_search.py --G 7 --L 3 --alpha 3 --N 7 --detailed
python3 scripts/support_feasibility_search.py --G 6 --L 3 --alpha 3 --N 6 --hyp coverage
python3 scripts/support_feasibility_search.py --G 6 --L 3 --alpha 3 --N 6 --complete-only

# kernel check
lake build AssemblyP1.ReadTiledCounterexample
```

`scripts/support_feasibility_search.py` replaces the ad-hoc candidate filter of
`scripts/fixed_length_bridging_search_v2.py`; the read-tiled class at `N = G`
coincides with the per-occurrence class, which is why the `G = 7` F* witnesses
are exactly the read-tiled ones.

---

## 7. Corrections to existing repository claims

| Claim | Location | Status after this note |
|-------|----------|------------------------|
| Variant F (flow-feasible) has no known counterexample and is the sole survivor | `docs/bridging-consequences-lemmas.md` Thm 5; `docs/bridging-flow-feasibility-lemma.md` Thm 4/5; `docs/bridging-consequences-analysis.md` §d | **Corrected (false as stated)** — the read-tiled `AAABCBC → AAAAABC` instance is flow-feasible with ratio `27` under full `I_s`; `S ∉ F_flow(R)` there, and §6.2 ambiguity is recorded in `docs/bridging-schemas-and-flow-feasibility-gaps.md` |
| Flow-feasibility is a strict subset of Eulerian realizability and therefore "tighter" | `docs/eulerian-edge-count-formulation.md` §9.4 | Consistent, but tightness does not imply the target holds; Theorem 1 supplies a feasible dominating candidate |
| Fixed-length `I_s ⇒` truth maximizer | `docs/fixed-length-exact-counterexample.md` | Already refuted; unchanged |

---

## 8. Epistemic status

| Claim | Status |
|-------|--------|
| Theorem 1 (read-tiled dominance, `exp(N·D_KL)`) | **Proved** |
| Corollary 1a (truth read-tiled ⇒ all read-tiled candidates tie) | **Proved** |
| `AAABCBC → AAAAABC` satisfies full `I_s`, competitor read-tiled, ratio `27` | **Kernel-checked** (`AssemblyP1/ReadTiledCounterexample.lean`) + independent script |
| `S = AAABCBC` is not flow-feasible (uses unobserved `BCB`, `CBC`) | **Proved** (finite check) |
| Variant F refuted under per-occurrence and per-type readings | **Follows** from the kernel-checked witness + Theorem 1, conditional on the §6.2 reading |
| SC eliminates `I_s` counterexamples for `G ≤ 6` in tested ranges | **Bounded computational evidence** |
| Complete observed spectrum ⇒ truth is an SC maximizer | **Proved for repeat-free `S`**; **bounded computational evidence** for repeated spectra |
| Minimality of the `G = 7` read-tiled witness | **Bounded computational evidence** |

---

## 9. Non-claims

This note does not settle the Shomorony et al. open question; it does not decide
which §6.1/§6.2 object the published sentence intends; it does not address
reverse-complement equivalence, tie-breaking, or the accepted-text provenance
questions in `docs/source-notes/ml-objective-candidate-class-resolution.md`. The
read-tiled model is a named modeling decision used to prove a negative result;
it is not claimed to be the unique source-faithful reading of Medvedev–Brudno
§6.2.

Primary sources: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, J. Comput. Biol. 16(8) (2009) §6.1–6.2; Ilan Shomorony, Samuel H.
Kim, Thomas A. Courtade, David N. C. Tse, *Information-optimal genome assembly
via sparse read-overlap graphs*, Bioinformatics 32(17) (2016) i494–i502 Eq. (1);
Guy Bresler, Ma'ayan Bresler, David Tse, *Optimal assembly for high throughput
shotgun sequencing*, BMC Bioinformatics 14(Suppl 5):S18 (2013).
