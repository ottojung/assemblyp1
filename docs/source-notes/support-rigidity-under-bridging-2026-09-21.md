# Support rigidity under bridging: the oriented single-strand MB09 §6.2 same-length residue is closed

_Status: mathematical proof, 2026-09-21. This note proves the conjecture stated
as "Conjecture C" in
[`oriented-single-strand-se62-same-length-2026-09-20.md`](oriented-single-strand-se62-same-length-2026-09-20.md)
§4, in the stronger and more useful form needed by the same-length §6.2
reduction. Every claim is labelled **source fact**, **mathematical proof**,
**verified computation**, or **open**._

_Reproduce: `python3 scripts/verify_support_rigidity_bridging.py` (exact integer
arithmetic, deterministic, exits non-zero on any failed assertion)._

_Scope. This settles the candidate-identity half (same length, same read-type
support, different read-type spectrum) of the strict oriented single-strand
Medvedev–Brudno §6.2 residue. It does **not** select which MB09 layer the 2016
sentence denotes, and it does not touch tie/equivalence semantics; it removes a
genuine algorithmic obstruction to a positive derivation at the §6.2
support-equality layer._

---

## 0. Result at a glance

Fix a circular word `S` over any alphabet, length `G`, read length `2 ≤ L ≤ G`.
Let `spec_L(S)` be the **oriented** length-`L` window spectrum and
`supp(spec_L(S))` its support.

**Main theorem (mathematical proof).** If `S` is `I_s`-admissible, then `S` is
**support-rigid**: every circular word `D` of length `G` with
`supp(spec_L(D)) = supp(spec_L(S))` satisfies `spec_L(D) = spec_L(S)`.

Consequently, by the proven reduction of
[`oriented-single-strand-se62-same-length-2026-09-20.md`](oriented-single-strand-se62-same-length-2026-09-20.md)
§3, **no strict same-length oriented single-strand §6.2 counterexample exists
for any `G, L, Σ`** (mathematical proof). The residue left open there is closed
negatively.

The two ingredients are:

1. **Theorem C (support rigidity criterion; mathematical proof).** If `S` is
   support-non-rigid, then some length-`(L−1)` substring of `S` occurs at least
   **three times**. This is the result conjectured as Conjecture C of the earlier
   note, strengthened from "triple repeat" to "(L−1)-mer multiplicity ≥ 3".
2. **Bridging excludes the criterion (mathematical proof).** `I_s`-admissibility
   forces every `(L−1)`-mer to occur at most twice (primitive `S`) or forces the
   de Bruijn support graph to be a single directed cycle (non-primitive `S`); in
   both cases rigidity follows from Theorem C or directly.

---

## 1. Definitions

**Circular word.** `S ∈ Σ^G`, indices mod `G`.

**Window spectrum.** `spec_L(S)(w) = #{i ∈ Z_G : S[i..i+L) = w}` for oriented
length-`L` words `w`; this is an integer vector with `Σ_w spec_L(S)(w) = G`.
Its support is `E(S) := {w : spec_L(S)(w) > 0}`.

**Read-type support graph** `Γ(S)` (the de Bruijn support graph). Vertices are
the `(L−1)`-mers occurring in `E(S)`; edges are the words `w ∈ E(S)`, with
`w = w_1…w_L` an edge from `u = w_1…w_{L−1}` to `v = w_2…w_L`. Multiplicities are
`d_S(w) := spec_L(S)(w) ≥ 1`; each vertex `u` has
`out_S(u) := Σ_{w: prefix w = u} d_S(w) = in_S(u) := Σ_{w: suffix w = u} d_S(w)`,
the number of occurrences of the `(L−1)`-mer `u` in `S`. The underlying
undirected graph of `Γ(S)` is connected, because `S` is a single closed walk
using every edge.

**Support-non-rigid.** `S` is support-non-rigid if some circular word `D` of
length `G` has `supp(spec_L(D)) = E(S)` and `spec_L(D) ≠ spec_L(S)`. Equivalently
(writing `d_D` for `spec_L(D)`, `d' := d_D`) there is a positive integer edge
weighting `d'` on `Γ(S)`, balanced at every vertex, with `Σ_w d'(w) = G`, and
`d' ≠ d_S`. This is exactly the MB09 §6.2 spelled-circuit support condition.

**`I_s`-admissible** (full-read reduction; source fact, Shomorony et al. 2016
Eq. (1) via Bresler et al. 2013; see
[`mathematical bridging-and-spectrum-uniqueness.md`](../../mathematics/bridging-and-spectrum-uniqueness.md)
§1): `S` admits a read collection `R ∈ I_s` iff

- every triple repeat of `S` has length `≤ L−2`, and
- every interleaved maximal-repeat pair has a constituent of length `≤ L−2`.

---

## 2. Theorem C: non-rigidity forces an `(L−1)`-mer of multiplicity ≥ 3

**Theorem C.** If `S` is support-non-rigid, then some length-`(L−1)` substring of
`S` occurs at least three times. Equivalently: if every `(L−1)`-mer of `S` occurs
at most twice, then `S` is support-rigid.

**Proof.** Suppose every `(L−1)`-mer occurs at most twice, and suppose for
contradiction that `d' ≠ d_S` is a positive integer balanced weighting on
`Γ(S)` with `Σ d' = Σ d_S = G`. Put `z := d' − d_S`. Then `z` is a nonzero
integer circulation on `Γ(S)` (`Bz = 0` for the vertex-incidence matrix `B`) with
`Σ_w z(w) = 0`, and `z(w) ≥ 1 − d_S(w)`.

Because `Σ z = 0` and `z ≠ 0`, there is an edge `e` with `z(e) < 0`. Then
`d'(e) ≥ 1` gives `d_S(e) ≥ 2`. Let `u := prefix(e)`. By the multiplicity
hypothesis, `out_S(u) ≤ 2`; but `out_S(u) ≥ d_S(e) ≥ 2`, so `out_S(u) = 2`,
`d_S(e) = 2`, and `e` is the **unique** edge of `Γ(S)` leaving `u`.

Now use balance for `d'` at `u`. Since `e` is the unique out-edge,
`d'(e) = Σ_{g: suffix g = u} d'(g)`. Every in-edge `g` of `u` lies in `E(S)`, so
`d'(g) ≥ 1`. Since `d'(e) = d_S(e) + z(e) ≤ 2 − 1 = 1`, the sum has exactly one
term: there is a unique in-edge `g₀` of `u`, and `d'(g₀) = d'(e) = 1`. Also
`out_S(u) = in_S(u) = 2` and `g₀` is the only in-edge, so `d_S(g₀) = 2` and
`z(g₀) = −1 < 0`.

So from any edge with negative `z` we have produced a unique predecessor
`pred(e) :=` (the unique in-edge of `prefix(e)`), again with negative `z`. The
map `pred` is deterministic and `E(S)` is finite, so the backward iterates of
`e` eventually repeat, yielding a directed cycle `O ⊆ E(S)`, every edge of which
has `z < 0`.

Every vertex touched by an edge of `O` has exactly one in-edge and one out-edge
in `Γ(S)`, both in `O` (uniqueness was established at `u = prefix(e)` for the
out-edge and at `u` for the in-edge; the property is intrinsic to an edge with
`z < 0` and the multiplicity hypothesis). Hence `O` is a union of connected
components of the underlying undirected graph of `Γ(S)`. That graph is
connected, so `O = E(S)`. Therefore `z(w) < 0` for every `w ∈ E(S)`, whence
`Σ_w z(w) < 0`, contradicting `Σ z = 0`. ∎

_Epistemic class: mathematical proof. The finite checks in
`scripts/verify_support_rigidity_bridging.py` assert the theorem (as
"`C`-violations = 0") over every word in the listed scopes, including the
non-primitive ones. [verified computation]_

**Remark.** Theorem C is stronger than the earlier Conjecture C: it identifies a
necessary condition (`(L−1)`-mer multiplicity ≥ 3) that does not mention
Bresler maximality, which makes it composable with the bridging hypothesis.

---

## 3. Bridging excludes the criterion

### 3.1 Primitive truth

**Lemma 1.** If `S` is primitive and some `(L−1)`-mer `u` occurs at least three
times, then `S` has a triple repeat of length `≥ L−1`. Hence such `S` is not
`I_s`-admissible.

**Proof.** Let `s₀, s₁, s₂` be three distinct start positions of `u`. Let `r` be
the largest integer such that the windows `S[sᵢ..sᵢ+r)` are equal for `i = 0,1,2`
(so `r ≥ L−1`), and let `a` be the largest integer such that the windows
`S[sᵢ−a..sᵢ)` are equal for `i = 0,1,2`. Since `S` is primitive, neither common
extension can wrap the whole circle; hence at distance `r` the following symbols
are not all equal and at distance `a` the preceding symbols are not all equal.
The equal window `S[sᵢ−a..sᵢ+r)` has length `a + r ≥ L−1` and satisfies Bresler's
maximality on both sides: it is a triple repeat of length `≥ L−1`. ∎

**Corollary.** A primitive `I_s`-admissible `S` has every `(L−1)`-mer occurring
at most twice, and therefore is support-rigid by Theorem C. ∎

### 3.2 Non-primitive truth

**Lemma 2.** Let `p` be the minimal period of `S`, so `S = C^k` with `C`
primitive, `k = G/p ≥ 2`. If `S` is `I_s`-admissible, then the `p` words
`(S[i..i+L−1))_{0 ≤ i < p}` are pairwise distinct.

**Proof.** Suppose `i ≠ j` in `[0, p)` have the same `(L−1)`-mer `u`. Since
`k ≥ 2`, the three starts `i`, `i+p`, `j` all carry `u` in `S`. If the preceding
symbols or the following symbols of the occurrences at `i` and `j` differ, then
maximising the common extension exactly as in Lemma 1 produces a triple repeat
of length `≥ L−1`, contradicting `I_s`-admissibility. If both neighbouring
symbols agree, then the length-`(L+1)` windows at `i−1` and `j−1` are equal;
shifting one step to the right, the `(L−1)`-mer at `i+1` equals that at `j+1`
and their neighbouring symbols again agree, so by induction `S` has period
`d := |i−j|` with `0 < d < p`, contradicting minimality of `p`. ∎

**Corollary.** If `S = C^k` is `I_s`-admissible, then `Γ(S)` is a single
directed cycle: the `p` pairwise distinct `(L−1)`-mers are the vertices, the `p`
distinct length-`L` windows (distinct because their `(L−1)`-prefixes are) are the
edges, and each vertex has in-degree and out-degree one. A positive balanced
weighting on a directed cycle is constant, and its total is `G = kp`, so it must
be the constant `k`; hence `d' = d_S`. In particular `S` is support-rigid. ∎

### 3.3 Main theorem

**Main theorem.** If `S` is `I_s`-admissible, then `S` is support-rigid.

**Proof.** If `S` is primitive, Corollary §3.1 applies. If `S` is
non-primitive, Corollary §3.2 applies. ∎

_Epistemic class: mathematical proof, resting on Theorem C and the two
elementary lemmas._

---

## 4. Consequence for the same-length §6.2 residue

The reduction proved in
[`oriented-single-strand-se62-same-length-2026-09-20.md`](oriented-single-strand-se62-same-length-2026-09-20.md)
§3 states:

> a strict same-length S62 counterexample exists iff there is a circular `S`
> such that (A) `I_s` is realizable on `S`, and (B) `spec_L(S)` is non-rigid on
> its support.

The Main theorem says (A) implies **not** (B). Hence:

**Corollary (closure of the residue; mathematical proof).** Under the strict
oriented single-strand reading with MB09 §6.2 support-equality (spelled-circuit)
admissibility, and for any fixed candidate length equal to the true length,
there is **no** strict counterexample to "the bridging hypothesis forces the
truth to be maximum-likelihood" at the level of read-type spectra: the only
`(L−1)`-mer-support-respecting, same-length candidate spectrum is the truth's
own. Equivalently, for every §6.2 spelled candidate `D` of length `G` with
`supp(spec_L(D)) = supp(x)` for an observed `x` with `supp(x) = E(S)`, the
likelihood ratio `E(d_D)/E(d_S)` equals `1` under the §6.1 same-length exact
objective, and under the fixed-`N` binomial objective with `N = G` as well (both
objectives factor through the spectrum).

_What this does and does not settle._ It closes exactly the algorithmic residue
recorded as Conjecture C. It does not by itself produce a single sequence-level
maximizer: two distinct sequences can share the truth's spectrum (the
`spectrum → sequence` fibre; repository Conjecture 4, which the
substring-spectrum literature places within the classical Ukkonen–Pevzner
characterization). It also does not fix tie/equivalence semantics. Those remain
the separate, already-documented choices ([`equivalence-and-tie-wellposedness.md`](equivalence-and-tie-wellposedness.md),
[`conclusion-semantics-determination.md`](conclusion-semantics-determination.md)).

---

## 5. Relation to the rest of the frontier

- **Supersedes the conjecture status of Conjecture C.**
  [`oriented-single-strand-se62-same-length-2026-09-20.md`](oriented-single-strand-se62-same-length-2026-09-20.md)
  §4 conjectures "non-rigid ⇒ triple repeat of length `≥ L−1`". Theorem C proves
  the sharper multiplicity statement, and §3 combines it with `I_s` to give the
  Main theorem. The exhaustive zeros tabulated there (`binary G ≤ 18`,
  `ternary G ≤ 12`, `four-letter G ≤ 10`) are the finite shadow of the proof.
- **Independent of the likelihood layer.** The argument is purely about
  `D ↦ spec_L(D)`; no sample `x` and no likelihood enters. It therefore applies
  to the §6.1 exact multinomial, the fixed-`N` binomial, and any objective that
  is a function of `(d_D, x)`.
- **Compatible with the population repair.** The note
  [`infinite-data-positive-analogue-reconnaissance-2026-09-20.md`](infinite-data-positive-analogue-reconnaissance-2026-09-20.md)
  identifies population concentration (unconditional) plus spectrum uniqueness
  (combinatorial) as the repaired positive statement. The present result supplies
  the support-level part of the combinatorial half at the `(L−1)` boundary,
  unconditionally in the §6.2 same-length setting.
- **Does not touch the Sequence (SEQ) layer.** The #32 witness `AAACC → AAAAC`
  lives at the sequence layer with candidates whose supports differ from
  `supp(x)`; it is untouched. The two facts are consistent.
- **Non-primitive handling.** The population/spectrum notes generally assume a
  primitive truth (`D10`). The present proof removes that assumption for support
  rigidity: §3.2 handles perfect powers directly.

---

## 6. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| Theorem C: support-non-rigid ⇒ some `(L−1)`-mer occurs ≥ 3 times | **mathematical proof** | §2 circulation/uniqueness argument |
| Lemma 1: primitive + `(L−1)`-mer ≥ 3 times ⇒ triple repeat length ≥ `L−1` | **mathematical proof** | maximal common-extension |
| Lemma 2: `I_s`-admissible perfect power ⇒ period `(L−1)`-mers pairwise distinct | **mathematical proof** | triple repeat or shorter period |
| Non-primitive `I_s`-admissible ⇒ `Γ(S)` is a single directed cycle ⇒ rigid | **mathematical proof** | §3.2 |
| Main theorem: `I_s`-admissible ⇒ support-rigid (all `S`) | **mathematical proof** | §3.1 + §3.2 |
| No strict same-length oriented single-strand §6.2 counterexample | **mathematical proof** | reduction of the cited note + Main theorem |
| Finite checks (C-violations = 0; admissible non-rigid = 0) | **verified computation** | `scripts/verify_support_rigidity_bridging.py` |
| Which MB09 layer the 2016 sentence denotes; sequence fibre; tie semantics | **open** | source gaps, unchanged |

---

## 7. Reproduction

```sh
python3 scripts/verify_support_rigidity_bridging.py
```

The script is self-contained (it re-implements spectra, exact support
non-rigidity by complete enumeration of balanced weightings, repeats,
interleaving and `I_s`), uses exact integers, and asserts, for every word in the
listed scopes (including non-primitive words) and for perfect powers:

- **Theorems C**: every support-non-rigid word has an `(L−1)`-mer of
  multiplicity `≥ 3`;
- **Main theorem**: every `I_s`-admissible word is support-rigid.

Primary sources for the hypothesis semantics: Ilan Shomorony, Samuel H. Kim,
Thomas A. Courtade, David N. C. Tse, *Information-optimal genome assembly via
sparse read-overlap graphs*, *Bioinformatics* 32(17) (2016) i494–i502, §2, §5,
Eq. (1); Guy Bresler, Ma'ayan Bresler, David Tse, *Optimal assembly for high
throughput shotgun sequencing*, *BMC Bioinformatics* 14(Suppl 5):S18 (2013);
Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome Assembly*, *J. Comput.
Biol.* 16(8) (2009) 1101–1116, §6.1–6.2.
