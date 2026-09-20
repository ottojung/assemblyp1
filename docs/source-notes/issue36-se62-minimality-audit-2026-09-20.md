# Issue #36: independent minimality audit of the integrated `AAATT → AAAATT` §6.2 witness

_Status: independent primary-source reconstruction + exact finite computation,
2026-09-20. This note does not import or run any existing repository verifier;
the companion `scripts/audit_se62_minimal_witness.py` is self-contained
(standard library only, exact `fractions.Fraction`). Claims are labelled
**source fact**, **mathematical proof**, **verified computation**, or **open**._

_Primary sources._

- Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome Assembly*,
  *J. Comput. Biol.* 16(8) (2009) 1101–1116, §3.1–3.4, §5.2, §6.1–6.2,
  [PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/).
- Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
  *Information-optimal genome assembly via sparse read-overlap graphs*,
  *Bioinformatics* 32(17) (2016) i494–i502, Eq. (1), attributed to
  Bresler–Bresler–Tse (2013).

_Reproduction:_ `python3 scripts/audit_se62_minimal_witness.py`.

_Subject of the audit:_ `docs/bridging-se62-flow-ml-counterexample.md` and
`docs/section62-mb09-bidirected-graph-audit.md` at `main` (`6256d46`).

---

## 0. Verdict

1. **The integrated witness is confirmed.** Reconstructing the §6.2 graph,
   the transitive reduction, the strict `I_s` predicate, and the §6.1
   objective from the source text reproduces the integrated certificate
   exactly: the `10`-edge graph on `{AAA, AAT, TAA}`, the two spelled
   bidirected circuits, the corrected `d_S = {AAA:1, AAT:2, TAA:2}`, and the
   ratio `9/8`. The Lean module
   `AssemblyP1.Section62BridgingCounterexample` builds and its main theorem
   depends only on `propext`, `Classical.choice`, `Quot.sound`.
   [mathematical proof + verified computation]

2. **The minimality claim is not valid as stated.** The main note says
   "the `G = 5` instance is the smallest with a clean integer ratio"
   (`docs/bridging-se62-flow-ml-counterexample.md` line 312) and restricts the
   search to the `n < N` regime (lines 327–330, 353–357). Under the
   source-faithful reading that the same note adopts — §6.2 lower bound is the
   **per-vertex** `1`, not the per-occurrence `x_w` — there are strictly
   smaller witnesses:

   | witness | `G` | `L` | `n` | competitor | ratio | `I_s` content |
   |---|---|---|---|---|---|---|
   | **A** | `4` | `2` | `3 < N` | `AAT` | `9/8` | coverage only |
   | **B** | `3` | `2` | `5 > N` | `AAAT` | `2` | coverage only |
   | **C** | `4` | `3` | `5 > N` | `AAAAT` | `32/27` | triple-repeat all-bridged |

   Witness A satisfies even the *stronger* per-occurrence support/lower-bound
   certificate (`SeqSupportLB`) with `n = 3 < N = 4`, so it is not an artifact
   of the per-vertex/per-occurrence dispute; only the unstated `L = 3`
   restriction excludes it. Witness C keeps `L = 3` and has non-vacuous
   bridging; only the unstated `n < N` restriction excludes it.
   [verified computation]

3. **Corrected scope.** `G = 5` is the smallest bidirected spelled-circuit
   witness only under the conjunction **`L = 3` and `n < N`** (and with a
   same-or-longer competitor). Outside that conjunction the minimum is `G = 3`
   (`L = 2`), or `G = 4` if `L = 3` is imposed but `n > N` is allowed.
   [verified computation, bounded but exhaustive over the stated finite boxes]

---

## 1. Independent reconstruction of the source objects

### 1.1 Graph (MB09 §3.1, §3.3, §3.4)

A read is a DNA molecule, an unordered reverse-complement pair; the vertex set
is the set of observed read molecule classes. Each molecule `x` has a positive
strand `p(x)` and negative strand `n(x) = rc(p(x))`. The four §3.3 strand
cases give a bidirected edge with incidences `(+,−)`, `(+,+)`, `(−,−)`,
`(−,+)` for `(p,p)`, `(p,n)`, `(n,p)`, `(n,n)` respectively; the length is the
underlying string-overlap length. Overlap means a nonempty suffix of the first
strand equals a prefix of the second (confirmed by the bidirected de Bruijn
construction, MB09 §4.1). Loops contribute `±2`/`0` per §3.2.

For `{AAA, AAT, TAA}` at `o_min = 2` this yields exactly the ten edges recorded
in `docs/section62-mb09-bidirected-graph-audit.md` §2, including the
twice-positive `AAT` loop and the twice-negative `TAA` loop. The truth `AAATT`
and competitor `AAAATT` window walks use only those edges, alternate
orientations at every interior vertex, and are closed. [verified computation]

### 1.2 Transitive reduction (MB09 §6.2, "spelled by two shorter overlaps")

Every edge a witness walk uses has the maximal proper overlap `L−1`. A direct
overlap of length `l` spelled through one intermediate read by proper overlaps
`l₁, l₂ < L` has `l = l₁ + l₂ − L` (Myers 2005 reading), which for
`l = L−1` forces `l₁ + l₂ = 2L−1 > 2(L−1)`, impossible. The literal "two
shorter overlaps" reading likewise needs `l₁ + l₂ = L + l` with
`l₁, l₂ ≤ l−1`, impossible for `l = L−1`. Hence the reduction removes no
employed edge, for every `L`. [mathematical proof]

### 1.3 `I_s` (Shomorony et al. 2016 Eq. (1); Bresler et al. 2013)

Coverage; every maximal **triple repeat** all-bridged (each copy strictly
extends on both sides); every **interleaved repeat pair** bridged (at least one
constituent copy bridged). Repeats use the maximality condition on both flanks;
a repeat is a selected pair of equal occurrences, not a word-multiplicity
count. For `AAATT` this gives: one maximal triple repeat `A@{0,1,2}`
(all three copies bridged by reads at `4, 0, 1`), maximal pairs
`A@{0,2}`, `AA@{0,1}`, `T@{3,4}` with no four-start cyclic alternation, and
coverage by starts `(0,1,4)`. [verified computation]

The integrated witness therefore survives the exact §6.2 graph/flow check and
the strict `I_s`. [verified computation]

---

## 2. Smaller witnesses

All three witnesses below are **spelled bidirected circuits**: the truth's
cyclic `L`-window walk and the competitor's cyclic `L`-window walk are closed
walks in the transitively reduced read-overlap graph, satisfy the vertex lower
bound `1`, edge lower bounds `0`, zero read-vertex balance, and use no
supersource/supersink edge. A spelled circuit is a special §6.2 flow, so
exhibiting one is sufficient to refute statement (P).

### 2.1 Witness A: `G = 4`, `L = 2`, `n = 3 < N` (per-occurrence feasible)

```text
truth        S = AATT          G = 4, L = 2, N = 4
read starts  (0, 1, 3)         n = 3
observed     x = { AA:1, AT:1, TA:1 }
truth spec   d_S = { AA:2, AT:1, TA:1 }
competitor   D = AAT           |D| = 3
competitor   d_D = { AA:1, AT:1, TA:1 }
ratio        L_{6.1}(D)/L_{6.1}(S) = 9/8 > 1
```

`I_s` is coverage only (`AATT` has maximal pairs `A@{0,1}`, `T@{2,3}` and no
triple or interleaved pair). The truth and competitor walks are
`AA→AT→AA→TA→AA` and `AA→AT→TA→AA`. `supp(d_S) = supp(d_D) = supp(x)` and
`d_S, d_D ≥ x` coordinatewise, so this instance satisfies the note's own
stronger `SeqSupportLB` certificate and its `n < N` regime; only `L = 2` rather
than `L = 3` excludes it. [verified computation]

### 2.2 Witness B: `G = 3`, `L = 2`, `n = 5 > N` (smallest `G`)

```text
truth        S = AAT           G = 3, L = 2, N = 3
read starts  (0, 0, 0, 1, 2)   n = 5
observed     x = { AA:3, AT:1, TA:1 }
truth spec   d_S = { AA:1, AT:1, TA:1 }
competitor   D = AAAT          |D| = 4
competitor   d_D = { AA:2, AT:1, TA:1 }
ratio        2 > 1
```

`I_s` is coverage only (`AAT` has the single maximal pair `A@{0,1}`, no triple,
no interleaved pair). `AA` and `TA` are palindromic molecules at `L = 2`; the
§3.3 construction still applies, since the positive/negative strand labelling
is arbitrary and §4.1 notes the choice of spelling strand does not affect the
edge orientation. The read multiset is exactly what independent uniform
sampling can produce. [verified computation]

This is the smallest non-degenerate `G`. `G = 2` is degenerate: the only
non-constant truth `AT` has `d_S = {AT:1, TA:1}` with `N = 2`, and no admissible
competitor exceeds it. [verified computation]

### 2.3 Witness C: `G = 4`, `L = 3`, `n = 5 > N` (non-vacuous bridging)

```text
truth        S = AAAT          G = 4, L = 3, N = 4
read starts  (0, 0, 1, 2, 3)   n = 5
observed     x = { AAA:2, AAT:1, ATA:1, TAA:1 }
truth spec   d_S = { AAA:1, AAT:1, ATA:1, TAA:1 }
competitor   D = AAAAT         |D| = 5
competitor   d_D = { AAA:2, AAT:1, ATA:1, TAA:1 }
ratio        32/27 > 1
```

`I_s` here is **non-vacuous**: `AAAT` has the maximal triple repeat
`A@{0,1,2}`, and each copy is strictly bridged (copy `0` by the read at `3`,
copy `1` by a read at `0`, copy `2` by the read at `1`). The maximal pairs
`A@{0,2}` and `AA@{0,1}` do not interleave. Thus the `L = 3` case has a
`G = 4` witness as soon as `n > N` is admitted. [verified computation]

---

## 3. Why the `n < N` restriction is not source-faithful

`docs/bridging-se62-flow-ml-counterexample.md` line 328 justifies the
`n < N` search box by "for a **per-occurrence** feasible truth one necessarily
has `Σ_w x_w = n ≤ Σ_w d_S(w) = G`". That implication is correct for the
stronger per-occurrence lower bound `d_i ≥ x_i`, but the same note's §1.3/§2
and the companion graph audit correctly insist that the **source** §6.2 lower
bound is the per-vertex `1`, not `x_w`. Under the per-vertex bound a truth flow
is feasible for any `n`; the observed count `x` does not lower-bound `d_S`.
Witnesses B and C exploit exactly this: `d_S` has a coordinate below `x` yet is
an admissible §6.2 flow.

The `n = N` slice collapse is real (the separable objective is coordinate-wise
maximized at `d = x` when `n = N`), but the source quantifies over all read
sets in `I_s`, so `n > N` cannot be excluded. The correct interior of the
"interesting" regime is `n ≠ N`, not `n < N`. [mathematical argument]

Independently, the `L = 3` restriction used by the search box is nowhere
justified by MB09 or by the 2016 paper; MB09's own experiments use `L = 25`,
`o_min ∈ {17,…,21}` (PMC3154397 §8.2), and the repository already uses `L = 2`
instances elsewhere (e.g. `docs/exact-variant-e-counterexample.md`).

---

## 4. Corrected minimality statement

| regime | smallest `G` | witness | ratio |
|---|---|---|---|
| any `L ≥ 2`, any `n`, spelled circuits | `3` | B (`S=AAT`, `L=2`, `n=5`) | `2` |
| `L = 3`, any `n`, spelled circuits | `4` | C (`S=AAAT`, `n=5`) | `32/27` |
| `L = 3`, `n < N`, spelled circuits | `5` | integrated (`S=AAATT`, `n=3`) | `9/8` |
| `L = 2`, `n < N`, per-occurrence certificate | `4` | A (`S=AATT`, `n=3`) | `9/8` |

The last two rows show that the integrated witness is minimal in its intended
box, but that the box must be stated: `L = 3` is a free modelling restriction,
and `n < N` is inherited from the stronger per-occurrence certificate rather
than from the source §6.2 lower bound.

---

## 5. Epistemic status and limits

| Claim | Status |
|---|---|
| §6.2 graph, signed incidences, transitive reduction, `I_s` definitions | **source fact** (MB09 §3.1–3.4, §6.2; Shomorony 2016 Eq. (1)) |
| Integrated `AAATT` witness survives the exact reconstruction; ratio `9/8` | **mathematical proof + verified computation** |
| Lean `AssemblyP1.Section62BridgingCounterexample` builds; only `propext`/`Classical.choice`/`Quot.sound` | **kernel-checked** |
| Witnesses A, B, C are admissible spelled §6.2 circuits satisfying strict `I_s` and beating the truth | **verified computation** (self-contained script) |
| Minimality table §4 | **verified computation** exhaustive over the stated finite boxes (`G ≤ 5`, `L ≤ G`, `n ≤ 6`, competitor length `≤ G+3`, spelled circuits) |
| Exhaustiveness beyond those boxes, or over genuinely non-spellable flows | **open**; the witnesses refute (P) regardless, since spelled circuits are admissible flows |
| Which MB object / strand / length / regime the 2016 sentence denotes | **open** (unchanged source ambiguity) |

The search is finite and bounded, so the minimality rows are evidence for the
stated boxes, not a global theorem. Existence of the smaller witnesses is a
proof of the corresponding negative statement regardless of the search's
completeness, because each is an explicit exact certificate.
