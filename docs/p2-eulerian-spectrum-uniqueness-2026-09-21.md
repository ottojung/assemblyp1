# Circular `P2` spectrum uniqueness via de Bruijn multigraph / Eulerian-circuit theory

_Status: independent mathematical note with exact-arithmetic computation,
2026-09-21. It attacks the equal-length uniqueness step of the
population/`P2` packet (issues [#45](https://github.com/ottojung/assemblyp1/issues/45)
and [#48](https://github.com/ottojung/assemblyp1/issues/48)) directly through
the de Bruijn multigraph, states the exact hypotheses, and reports a
counterexample search. It is written against `origin/main` at `f60ca5f` and is
independent of the concurrent source-fidelity branch artifacts
`docs/literature/circular-qgram-identifiability-and-Is-threshold-2026-09-21.md`
and `docs/issue48-p2-population-proportional-identification.md` (named, not
linked, because they are not on `main`)._

_Reproduction: `python3 scripts/p2_eulerian_attack.py` (definitions + moderate
scans), `scripts/p2_broad_scan.py`, `scripts/p2_euler_direct.py`,
`scripts/p2_obstruction_taxonomy.py`, `scripts/p2_no_primitivity_probe.py`,
`scripts/p2_raw_vs_maximal_probe.py`. Bounded searches are evidence only._

---

## 0. Direct answer

**`P2` excludes every alternate circular spelling, under the hypotheses of §1.**
No counterexample was found in any range searched. The implication

> `P2(S,L)` ⇒ the `L`-mer multiset determines `S` up to cyclic shift

is the `K = L−1` instance of Ukkonen's condition (Ukkonen 1992; Pevzner 1995;
Bresler–Bresler–Tse 2013, Theorem 3), read circularly; this note does **not**
re-prove that source theorem, but it (a) pins the exact correspondence with the
repository's `P2` predicate, (b) verifies it exhaustively over ranges wider than
previously recorded, and (c) isolates two exact-hypothesis corrections.

The two corrections matter and are the substance of the attack:

1. **The obstruction → ambiguity translation is false in one direction.**
   An unbridged *triple repeat* of length `≥ L−1` produces multiple Eulerian
   tours but can leave the spelled word unique. The smallest witness is
   `AAAAB` (`L = 3`, `n = 5`): a maximal triple repeat `AA` (length `2 = L−1`)
   yet the only same-spectrum word is `AAAAB` itself. So "triple repeat ⇒
   alternate spelling" is **refuted**; the triple clause is not individually an
   ambiguity generator.
2. **The *maximality* clause in `ILF` is load-bearing, not cosmetic.** Raw
   interleaving of two repeated `(L−1)`-mers (no maximality) is common —
   `28134` binary primitive words of length `≤ 18` are `P2` yet have raw
   interleaving — and is harmless. Only *maximal* interleaved pairs create
   ambiguity.

The asymmetry is sharpest in the joint taxonomy of §5: over binary primitive
words of length `≤ 18`, there are `18000` words whose only obstruction is a
triple repeat and which have no collision, `14425` whose only obstruction is an
interleaved pair and which do collide, and `0` words satisfying `P2` with a
collision.

---

## 1. Exact hypotheses

- `Σ` any finite alphabet; `S` a **circular** word of length `n ≥ 2`; indices
  cyclic. **(No primitivity is assumed** — see §5.4; the statement holds for
  periodic words too in the tested ranges, e.g. `AAA`, `ABAB`.)
- Read length `L` with `2 ≤ L ≤ n`; `K := L−1`.
- `L`-mer spectrum `d_S(w) = #{ i ∈ Z_n : S[i..i+L) = w }`, counted with
  multiplicity on the circle.
- Genome equivalence is **cyclic shift** (oriented single-strand panel).
- `P2(S,L) = TRF(S,L) ∧ ILF(S,L)` with the Bresler definitions of §2.
- Conclusion: every circular `T` with `d_T = d_S` is a cyclic shift of `S`.

Two hypotheses are **not** needed: same length (automatic, since
`Σ_w d_T(w) = |T| = |S|` for equal spectra) and primitivity. No read set,
bridging, coverage, or likelihood hypothesis enters this purely combinatorial
statement.

## 2. Bresler repeat vocabulary (as used)

Quoting the definitions the repository inherits from Bresler–Bresler–Tse 2013
(see `docs/bridging-source-semantics.md`):

- A **maximal repeat pair** of length `ℓ` is a pair `t₁ ≠ t₂` with
  `S[t₁..t₁+ℓ) = S[t₂..t₂+ℓ)`, `S[t₁−1] ≠ S[t₂−1]`, `S[t₁+ℓ] ≠ S[t₂+ℓ]`.
- A **triple repeat** of length `ℓ` is a triple of starts with equal `ℓ`-windows
  such that **neither** their preceding symbols are all equal **nor** their
  following symbols are all equal.
- A pair of maximal repeats `(t₁,t₃)`, `(t₂,t₄)` is **interleaved** if
  `t₁ < t₂ < t₃ < t₄` (cyclically); its length is the shorter constituent.
- `TRF(S,L)`: no triple repeat of length `≥ L−1`.
- `ILF(S,L)`: no interleaved pair of maximal repeats whose shorter constituent
  has length `≥ L−1`.

`P2` is exactly BBT's "no triple or interleaved repeats of length `≥ K`" at
`K = L−1`, because BBT define the length of an interleaved pair as the shorter
constituent. The exact (maximal) triple predicate agrees with the raw shortcut
"some `(L−1)`-mer occurs `≥ 3` times" on all primitive binary words of length
`≤ 16` (checked; `p2_eulerian_attack.check_definitions_agree`).

## 3. The de Bruijn / Eulerian translation

Build the de Bruijn multigraph `G(S,L)`:

- vertices: the distinct `(L−1)`-mers of `S`;
- one edge per **occurrence** of an `L`-mer, from its `(L−1)`-prefix to its
  `(L−1)`-suffix, labelled by the `L`-mer.

Then:

1. `S` itself is a cyclic Eulerian circuit of `G` (edge `i` is `S[i..i+L)`).
2. `d_T = d_S` iff `T` corresponds to a cyclic Eulerian circuit of the **same
   edge multiset** `G`. Since every circuit uses `n` edges, `|T| = n`. Distinct
   circular spellings up to rotation correspond to cyclic Eulerian circuits up
   to rotation, with **parallel edges bearing the same label collapsed** (they
   connect the same prefix/suffix and cannot change the spelling).
3. Vertex outdegree of `v` equals the multiplicity of the `(L−1)`-mer `v` in
   `S`. So `TRF` ⇔ every `(L−1)`-mer has multiplicity `≤ 2` (for primitive
   `S`; exactly BBT's triple condition in general), and under `P2` every vertex
   has outdegree ≤ 2 and the graph condenses to a `2`-in-`2`-out skeleton.
4. A **non-rotation** alternate spelling therefore requires a genuine *switch*
   between two branch vertices (repeated `(L−1)`-mers) whose occurrences can be
   exchanged without splitting the tour into two cycles. This is precisely a
   pair of **interleaved** branch structures; nested branch structures admit
   only tour choices that reproduce `S` up to rotation.

## 4. Obstruction vs. non-unique *word* (the exact asymmetry)

The task's phrasing "translate triple/interleaved obstructions into non-unique
Euler tours" needs two levels.

- **Tour level (true).** A triple repeat of length `≥ L−1` is a vertex of
  outdegree `≥ 3`, and an interleaved pair is a pair of branch vertices with
  crossing occurrence sets. Both make the number of edge-distinct Eulerian
  tours `> 1` (BEST count `> 1`), hence the raw de Bruijn graph is *not*
  uniquely Eulerian. This is why any statement of the form "`P2` ⇒ unique
  Eulerian cycle of the raw multigraph" is **false as stated** (already
  recorded for `AABAB`, where two parallel `ABA` edges give BEST count `2`).
- **Word level (false in general, true under `P2`).** Non-unique tours may all
  spell the same cyclic word. Witnesses:
  - `AAAAB` (`L = 3`): outdegree `3` at `AA`; the only spelled word is `AAAAB`.
  - `AABAB` (`L = 3`): two parallel `ABA` edges, BEST count `2`, one word.
  - `AABABB`/`AABBAB` (`L = 3`): an interleaved pair *does* produce two
    non-rotation spellings (`P2` fails).
  - The ROSALIND illustration `ACCTCCGCC` (`L = 3`, alphabet `{A,C,G,T}`) has
    the alternate spelling `ACCGCCTCC`, and indeed fails `P2` via the triple
    `CC` (`(L−1)`-mer `CC` occurs three times); it is not a counterexample.

So the correct translation is: *an alternate circular spelling exists exactly
when the obstruction survives as a maximal crossing switch; triple repeats and
non-maximal interleavings can collapse to the same word.*

## 5. Independent computation

All predicates below are re-derived from the published definitions (not from
the repository code). Ground truth is obtained by grouping words by exact
spectrum; the Eulerian route is a second, independent enumeration of spelled
words. Exact integer arithmetic.

### 5.1 Collision search (`P2` word with a non-rotation partner) — **zero hits**

| Scan | Range | Result |
|---|---|---|
| binary, group-first | `n ≤ 22`, `L ≤ 6` | 0 |
| ternary, group-first | `n ≤ 15`, `L ≤ 4` | 0 |
| 4 letters, group-first | `n ≤ 11`, `L ≤ 3` | 0 |
| 4 letters, group-first | `n ≤ 10`, `L ≤ 4` | 0 |
| 5 letters, group-first | `n ≤ 9`, `L ≤ 3` | 0 |
| 5 letters, group-first | `n ≤ 8`, `L ≤ 4` | 0 |
| all binary words (periodic included), no primitivity filter | `n ≤ 16`, `L ≤ n` | 0 |
| random primitive `P2`, `q ∈ [2,6]`, `n ∈ [6,26]`, `L ∈ [2,8]` | 1489 words, direct Eulerian route | 0 |

The random direct route enumerates the spelled words of the de Bruijn graph of
the sampled `S` (not other words), so it is not limited by alphabet size and
reaches lengths where full grouping is infeasible.

### 5.2 Obstruction taxonomy (binary primitive, `n ≤ 18`)

`T` = maximal triple of length `≥K`; `I` = interleaved maximal pair (shorter
`≥K`); `C` = a non-rotation same-spectrum partner exists:

| `(T,I,C)` | count | reading |
|---|---|---|
| `(F,F,F)` | 348 395 | no obstruction, unique |
| `(T,T,T)` | 111 122 | both obstructions, collides |
| `(T,F,F)` | 18 000 | triple only, **does not** collide |
| `(F,T,T)` | 14 425 | interleaved only, collides |
| `(T,T,F)` | 148 | both obstructions, still unique |

In particular `(F,F,T)` is **absent**: no `P2` word collides. The table also
shows the two exact-hypothesis points of §0: triple-only obstructions never
collided, and even a coexisting triple+interleaved obstruction can leave the
word unique.

### 5.3 `ILF` maximality is essential

Over binary primitive `n ≤ 18`, `28 134` `P2` words have two distinct repeated
`(L−1)`-mers whose **raw** occurrences interleave; all are collision-free
(`scripts/p2_raw_vs_maximal_probe.py`). A "raw interleaving" predicate would
therefore be gratuitously strong; the maximal-repeat form in `ILF` is the right
one.

### 5.4 Primitivity is not needed

Grouping **all** binary words (periodic included) by spectrum, `n ≤ 16`, found
`20 618` (`n ≤ 14`) and `85 041` (`n ≤ 16`) `P2` words and zero collision
members (`scripts/p2_no_primitivity_probe.py`). This supports the one-sided
claim that `P2(S)` alone suffices, with no primitivity hypothesis.

## 6. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| `P2(S,L)` ⇔ BBT "no triple or interleaved repeats of length `≥ K=L−1`" | **Analysis** (definitional identity) | §2, §3 |
| Same `L`-spectrum ⇒ same de Bruijn edge multiset / same length | **Proven** | §3.1–3.2 |
| Triple or interleaved obstruction ⇒ non-unique Eulerian **tour** | **Proven** | outdegree `≥3` / crossing switch |
| Triple obstruction ⇒ non-unique **word** | **Refuted** | `AAAAB`, `L=3` |
| Raw (non-maximal) `(L−1)`-mer interleaving ⇒ ambiguity | **Refuted** | 28 134 collision-free `P2` witnesses |
| `P2(S,L)` ⇒ `L`-spectrum determines `S` up to rotation | **Source theorem** (Ukkonen/Pevzner/BBT Thm 3, circular reading) + independent bounded verification; **no counterexample** | §0, §5 |
| Necessity (`P2` is required) | **Refuted** | `AAAAB` (and `(T,T,F)` cases) |
| Primitivity required | **Not required** (bounded) | §5.4 |

This note therefore **reclassifies** the standing caveat in
`reconcile/issue46-unlock-48-45-0921:180` ("P2 same-length `c=1`
open/conditional") as a **source-theorem instance** under the circular reading,
with the residual obligation that the circular reading of BBT Theorem 3 is a
reading of the accepted source and not an independently kernel-checked
statement. The finite evidence here is not a substitute for that theorem, but
it removes the possibility of a small counterexample and fixes the exact
predicate.

## 7. What a self-contained proof would need

The only unproved step is the contrapositive of the source theorem:

> if the de Bruijn multigraph of `S` has two cyclic Eulerian circuits spelling
> non-rotation words, then `S` has a maximal triple repeat of length `≥ L−1` or
> an interleaved pair of maximal repeats of length `≥ L−1` (shorter
> constituent).

Equivalently (Pevzner's criterion, Waterman Thm 7.5): non-uniqueness of the
Eulerian circuit is witnessed by a cycle in the intersection graph of simple
cycles of the condensed `2`-in-`2`-out graph; each such cycle is a pair of
simple cycles sharing two vertices, and the two interleaved paths between the
shared vertices are exactly a maximal interleaved repeat pair of length `≥ L−1`.
The bookkeeping step is that the shared vertices are `(L−1)`-mers occurring
twice, and the straightness of the remaining degree-1 paths is what makes the
repeat maximal. This is a plausible bounded graph-theoretic target; it is not
formalized here and the note does not claim it as proved.

## 8. Reproduction

```text
python3 scripts/p2_eulerian_attack.py        # definitions + moderate scans
python3 scripts/p2_broad_scan.py             # 4/5-letter group-first scans
python3 scripts/p2_euler_direct.py           # direct Eulerian spelled-word route
python3 scripts/p2_obstruction_taxonomy.py   # (T,I,C) table
python3 scripts/p2_no_primitivity_probe.py   # drop primitivity
python3 scripts/p2_raw_vs_maximal_probe.py   # raw vs maximal interleaving
```

## 9. Anchors and sources

- `docs/open-problem.md` — the published model and cyclic-shift equivalence.
- `docs/bridging-source-semantics.md` — Bresler repeat/maximality vocabulary.
- `docs/ml-formalization-contract.md` — likelihood depends on candidate only
  through length and `L`-mer spectrum (so spectrum uniqueness is the exact
  identifiability question at fixed length).
- `mathematics/bridging-and-spectrum-uniqueness.md` §5 — Conjecture 4 and the
  unproved "ambiguous circuit pair ⇒ unbridged structure" step.
- E. Ukkonen, *Theoret. Comput. Sci.* 92(1):191–211, 1992; P. A. Pevzner,
  *Algorithmica* 13(1–2):77–105, 1995; G. Bresler, M. Bresler, D. Tse,
  *BMC Bioinformatics* 14(Suppl 5):S18, 2013, Theorem 3.
