# Fixed-length exact ML under per-occurrence flow feasibility: repeated truths

_Status: bounded exhaustive computational search with exact rational arithmetic. Not a Lean result. Does not settle the source-ambiguous Shomorony et al. open question. Reproducible via `python3 scripts/fixed_length_flow_feasible_repeat_search.py`._

## Purpose and relationship to existing work

`docs/bridging-schemas-and-flow-feasibility-gaps.md` proves **Proposition D**: for a *repeat-free* circular truth `S` whose read collection `R` satisfies `S ∈ F*(R)`, the truth is a fixed-length exact maximum-likelihood maximizer (not unique). That note leaves an explicit open question (its Open Question 1):

> Does Proposition D extend from repeat-free `S` to truths with bridged repeats, under `F*`?

This note answers that question in the negative direction — no counterexample was found, even against a *strictly larger* candidate universe than `F*` — for an exhaustively searched finite scope. It also isolates the role of the bridging hypothesis `I_s`: dropping `I_s` while keeping `S ∈ F*(R)` immediately produces counterexamples, so `I_s` is load-bearing rather than cosmetic.

This carries over the deliverable of the `AssemblyP1: fixed-length competitor search` packet. It does **not** duplicate the AAACC/AAAAB Section 6.2 flow-feasibility certificate (`docs/flow-feasibility-aaacc-witness.md`), which concerns the different **walk-spelled `F_flow`** reading; see §6 for why the two readings give opposite answers here.

## Model (exact)

Everything is finite and exact; all likelihood comparisons use `fractions.Fraction`.

- **Alphabet:** binary `{A,B}` in the primary scope; ternary `{A,B,C}` in the extended scope.
- **Truth:** circular genome `S` of length `G`, with length-`L` circular windows (`read types`) `w`.
- **Sequencing realization:** a multiplicity vector `m = (m_0,...,m_{G-1})` over the `G` circular start positions; `m_s` reads start at position `s` (so repeated starts are allowed and are what create read-type counts above one). Observed counts are
  `x_w = #{s : window(S,s,L) = w and m_s > 0 counted with multiplicity}`, and `n = Σ_w x_w`.
- **Hypothesis `I_s`** (Shomorony et al. 2016 Eq. (1); repeat semantics from Bresler et al. 2013 via `docs/bridging-source-semantics.md`):
  1. **Coverage:** the starts with `m_s > 0` cover every position of `S`.
  2. **All-bridged triple repeats:** every selected 3-copy maximal triple repeat has each copy strictly extended on both sides by some realized read.
  3. **Bridged interleaved pairs:** every pair of maximal repeat pairs whose four starts alternate cyclically has at least one constituent copy bridged.
  Maximality, strict two-sided extension, and cyclic interleaving are transcribed directly from `docs/bridging-source-semantics.md`; `committed` lengths `ℓ = G` are excluded.
- **Objective (fixed-length exact Variant E):**
  `L(D|x) = n!/(∏_w x_w!) · ∏_w (d_D(w)/G)^{x_w}`, where `d_D(w)` is the number of circular length-`L` windows of `D` equal to `w`. Since the candidate length is fixed at `G`, the multinomial coefficient cancels and ordering is by `∏_w d_D(w)^{x_w}`.
- **Genome equivalence:** cyclic shift (rotation classes only; no reverse complement).

## The feasibility ladder

For each `I_s`- and `S ∈ F*`-satisfying instance we test three candidate universes of length `G`:

| Universe | Candidate condition |
|----------|---------------------|
| `U0` | every circular candidate `D` with `|D| = G` |
| `U1` | additionally `supp(D) ⊆ supp(S)` |
| `U2` (`F*`) | additionally `d_D(w) ≥ x_w` for every observed type `w` |

`U2` is the per-occurrence reading of the Medvedev–Brudno §6.2 lower-bound-one-per-read-vertex constraint restricted to length `G`, i.e. the candidate set of Proposition D. `U0` is *strictly larger* and is the baseline fixed-length exact universe; a candidate with `supp(D) ⊉ supp(S)` scores `0` because some positive-count type is missing, so `U0` and `U1` differ only on zero-score candidates. The **truth-side assumption** is `S ∈ F*(R)`: `supp(R) = supp(S)` and `x_w ≤ d_S(w)` for every `w` (this also forces `n ≤ G`).

## Results

Primary scope: binary, `G = 4..8`, all `2 ≤ L < G`. Extended scope: binary `G = 9, L ≤ 4`; ternary `G = 5..6, L ≤ 3`. Every instance in these scopes with `I_s` and `S ∈ F*` was enumerated; results are in `results/fixed-length-flow-feasible-repeat-search.json`.

| Scope | Instances | with repeated truth | `U0` cex | `U1` cex | `U2` (`F*`) cex |
|-------|-----------|---------------------|----------|----------|------------------|
| Primary (binary `G ≤ 8`) | 753 | 602 | **0** | **0** | **0** |
| Extended (binary `G=9 L≤4`; ternary `G≤6`) | 462 | 323 | **0** | **0** | **0** |
| Control: `I_s` dropped, only `S ∈ F*` (binary `G=5..7`) | 651 | 582 | 100 | 94 | **94** |

The primary result is stronger than a mere persistence check: under `I_s` and `S ∈ F*`, the truth is a maximizer even against the unrestricted length-`G` universe `U0`, not just against `F*`. The control shows this is not an artifact of the `S ∈ F*` support restriction: once bridging is removed, `F*`-feasible same-length competitors appear immediately.

**Minimal control counterexamples** (`I_s` fails; not counterexamples to the stated hypothesis):

| `S` | `L` | observed `x` | `D` | truth score | candidate score |
|-----|-----|--------------|-----|-------------|-----------------|
| `AAAAB` | 2 | `AA:1, AB:1, BA:1` | `AABAB` | 3 | 4 |
| `AAAAAB` | 2 | `AA:1, AB:1, BA:1` | `AAABAB` | 4 | 8 |
| `AAAAAAB` | 3 | `AAA:1, AAB:1, ABA:1, BAA:1` | `AAABAAB` | 4 | 8 |

In each case the truth has an unbridged maximal triple repeat (e.g. the `A`-run triple repeat at read length 2), so `I_s` is false.

## Structural observation on the repeated truths

Among all `I_s`- and `S ∈ F*`-satisfying instances with a repeated read type, the multiplicity vector `d_S` always exhibited the following pattern: repeated types occur in tandem/periodic classes of equal multiplicity (e.g. `ABABABAB` has `d_S(ABAB) = d_S(BABA) = 4`; `AABBAABB` has four repeated types each of multiplicity `2`; homopolymers have one type of multiplicity `G`). This is consistent with `d_S` being the geometric-mean-optimal partition of `G` over `supp(S)`, and with the fact that on a circle an unbalanced mass distribution is constrained by the window-recurrence relations. No `I_s` instance was found where `d_S` is "concentrated" in the way that the control counterexamples require.

**Conjecture (extends Proposition D).** Let `S` be a circular genome of length `G`, `L` a read length, and `R` a read multiset with `S ∈ F*(R)` and `I_s(S,R)`. Then `S` is a fixed-length exact maximum-likelihood maximizer: `L(D|x) ≤ L(S|x)` for every circular `D` with `|D| = G`.

Uniqueness is *not* claimed: the tandem `k·d_S` tie class of Proposition D is present in the repeated-truth cases as well. The conjecture is computational evidence only; a proof would need to convert `I_s`'s repeat/bridging constraints into a bound on `d_D(w)^{x_w}` relative to `d_S(w)^{x_w}` for all same-length `D`.

## Why the two "flow" readings disagree

The repository now has two distinct candidate-set readings of Medvedev–Brudno §6.2, and they give opposite answers to the persistence question:

- **`F*` (per-occurrence, used here and in Proposition D):** every length-`L` window of the candidate must occur as an observed read (`supp(D) ⊆ supp(R)`), and `d_D(w) ≥ x_w`. Under this reading the known fixed-length exact witnesses are eliminated: `S = AAABB` with `R = {AAA,AAB,BAA}` is not even in `F*` (its windows `ABB`, `BBA` are unobserved), and the fixed-length interleaved witness `S = ABACABC` has only two observed types out of six.
- **`F_flow` (walk-spelled):** a candidate is accepted when it is spelled by a closed walk in the read overlap graph (loops allowed). `docs/flow-feasibility-aaacc-witness.md` shows the `AAACC/AAAAC` witness *is* `F_flow`-feasible, because the walk `AAA → AAA → AAC → CAA → AAA` spells `AAAAC` even though `D`'s window `ACA` is not an observed read.

So "do counterexamples persist under flow-related constraints?" has no single answer until the source selects one reading: **yes under `F_flow`, no under `F*` (with `I_s`)**. This is a modeling fork, not a mathematical contradiction; the source notes (`docs/source-notes/medvedev-brudno-candidate-class.md` §3) already warn that the §6.2 flow object is not definitionally the §6.1 circular-genome universe.

## Limits and epistemic status

- The result is an **exhaustive finite search**, not a proof of absence beyond the stated bounds. The conjecture above is not established.
- `I_s` is transcribed from `docs/bridging-source-semantics.md`; the exact publisher-hosted 2016 supplement was not recovered, so if it defines repeats/bridging differently the scope would move. The accepted paper's explicit attribution to Bresler et al. is the controlling source evidence used here.
- The single-strand, error-free, rotation-only conventions of the Shomorony exposition are used. Bidirected/reverse-complement flow semantics, `omin > 1`, and non-contiguous assemblies are out of scope and belong to `F_flow`.
- The control experiment shows the negative result depends on `I_s`; it does not show that `I_s` alone (without `S ∈ F*`) suffices.
- All arithmetic is exact rational; no randomness; the script asserts the expected pattern and exits nonzero otherwise.

## Reproduction

```sh
python3 scripts/fixed_length_flow_feasible_repeat_search.py
# writes results/fixed-length-flow-feasible-repeat-search.json
```

Runtime is about two minutes on the current development host. The script re-derives `I_s` structure per truth, enumerates all start-multiplicity vectors with `n ≤ G`, requires `supp(R) = supp(S)` and `x_w ≤ d_S(w)`, and checks all length-`G` rotation representatives for each of `U0`, `U1`, `U2`.

## Cross-references

| Fact | Repository anchor |
|------|-------------------|
| Proposition D (repeat-free `F*` maximizer) and its open question | `docs/bridging-schemas-and-flow-feasibility-gaps.md` §4 |
| Walk-spelled `F_flow` and the AAACC certificate | `docs/flow-feasibility-aaacc-witness.md` |
| Source semantics for repeats/bridging | `docs/bridging-source-semantics.md` |
| Fixed-length exact counterexample (`AAABB`) | `docs/fixed-length-exact-counterexample.md` |
| Interleaved-clause counterexample | `docs/fixed-length-interleaved-counterexample.md` |
| Candidate-universe discipline | `docs/ml-formalization-contract.md`; `docs/source-notes/medvedev-brudno-candidate-class.md` |
| Reproducible evidence | `scripts/fixed_length_flow_feasible_repeat_search.py`; `results/fixed-length-flow-feasible-repeat-search.json` |
