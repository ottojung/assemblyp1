# The strict oriented single-strand Section 6.2 zero: a rigidity theorem, and its same-length boundary

_Status: independent re-derivation + proof audit + exact computation, 2026-09-20.
Written against `origin/main` (`8b2f0fc`) and the PR #47 evidence. Every claim is
labelled **source fact**, **mathematical proof**, **verified computation
(exhaustive in scope)**, **conjecture**, or **open**. This note does not select
which Medvedev–Brudno (2009) likelihood layer the Shomorony et al. (2016)
sentence intends, and does not touch tie/equivalence semantics. It resolves one
precisely delimited question: **strict oriented single-strand read types plus the
MB09 §6.2 spelled-circuit, same-length candidate class.**_

_Reproduce: `python3 scripts/oriented_se62_rigidity_audit.py` (quick, ~30 s) and
`python3 scripts/oriented_se62_rigidity_audit.py --full` (wider scopes, several
minutes). Self-contained, exact `fractions.Fraction`, deterministic, exits
non-zero on any failed assertion._

_Independent provenance. The same rigidity theorem is proved, independently and
earlier, on the unmerged branch `research/uniform-oriented-strand-2026-09-20`
(`docs/source-notes/uniform-oriented-rigidity-obstruction.md`, commit `e354d94`,
not in `main`, no PR). The present note re-derives the proof, adversarially checks
its hypotheses against the two distinctions the task flags, extends the
exhaustive scopes to previously unsearched non-vacuous cells, and records a
**strict oriented variable-length counterexample** that the same-length zero does
not touch._

---

## 0. Answer at a glance

The PR #47 / unmerged-oriented bounded searches found zero same-length strict
oriented single-strand §6.2 counterexamples. That zero is **not** a finite-scope
artifact: it is a theorem.

1. **The mathematical reason (rigidity).** If a circular truth `S` admits a
   Shomorony `I_s` realization, then `spec_L(S)` is the **unique positive integer
   circulation of total `G = |S|`** on its own length-`L` window-support graph.
   Consequently every same-length §6.2 spelled candidate has the truth's
   spectrum, every likelihood ratio is exactly `1`, and no strict same-length
   counterexample exists for any `G`, `L`, or alphabet. The proof only needs that
   `S` has no Bresler triple repeat of length `≥ L-1`, which `I_s` implies.
   [mathematical proof; exhaustive consistency checks]

2. **Necessary support equality vs full feasibility.** Support equality
   `supp(spec_L(D)) = supp(x)` is only *necessary* for §6.2 spelled-circuit
   feasibility. The rigidity theorem is proved on the *larger* set of all
   positive circulations (not only fully reduced-graph-feasible ones), so it
   covers the smaller fully feasible set a fortiori. The direction of the
   over-approximation is what makes the zero robust. [mathematical proof]

3. **Exact multinomial vs fixed-`N` §6.1.** Whenever two candidates have equal
   spectrum, both objectives give ratio exactly `1`, so the same-length zero is
   objective-independent. The two objectives separate only for **different
   candidate lengths**. [mathematical proof]

4. **Beyond the searched scope: a strict oriented variable-length
   counterexample.** `S = AAATT`, `D = AAAATT`, `L = 3`, with the observed
   support equal to the truth support (one extra observed `AAA` read) is an
   `I_s`, support-equal, spelled-circuit instance in which `D` strictly beats
   `S` under **both** the exact multinomial (`15625/11664 > 1`) and the literal
   fixed-`N` §6.1 product (`81/64 > 1`). It is outside the same-length theorem and
   outside the PR #47 search scope (`n > N`, and it deliberately violates the
   per-occurrence strengthening `d_D ≥ x`, which is not the source lower bound).
   [verified computation]

The three distinctions are exactly the ones the task asks for: the rigidity is
about same-length positive circulations (not support membership alone), and it
does not extend to different candidate lengths, where the exact and fixed-`N`
objectives can both be beaten.

---

## 1. The convention, stated exactly

- **Read type.** The oriented length-`L` window `W_t = S_t S_{t+1} … S_{t+L-1}`
  of the circular truth, no reverse-complement collapse. [source fact:
  Shomorony et al. 2016 §2; reverse complements are experimental preprocessing in
  §4.1]
- **Spectrum.** `spec_L(S)(w) = #{t : W_t = w}`, total `G = |S|`; support `V`.
- **§6.2 spelled-circuit candidate.** A circular word `D` with
  `supp(spec_L(D)) = supp(x)` (the per-vertex lower bound `1`, Observation 7)
  whose consecutive windows are the read vertices. [source fact + source-supported
  inference]
- **Bridging.** Shomorony `I_s` (Eq. (1)): coverage, every Bresler triple repeat
  all-bridged, every interleaved pair bridged. A length-`L` read bridges a copy of
  a repeat of length `ℓ` only if `ℓ ≤ L-2`. [source fact]
- **Objectives.** The exact MB09 §6.1 multinomial with candidate-intrinsic
  `N(D) = |D|`, and the §6.1 fixed-`N` product of binomial marginals with
  external known `N`. [source fact]

The task's phrase "maximum-likelihood" is a source ambiguity
(`docs/source-notes/candidate-genome-class-resolution.md`); the theorem below is
stated for **any** objective that is a function of `(spec_L(D), x)` and is
constant on equal spectra.

---

## 2. The window-support graph `X_S`

Given a circular word `S`, build the directed multigraph `X_S`:

- **nodes**: distinct length-`(L-1)` circular windows occurring in `S`;
- **edges**: distinct length-`L` windows `w ∈ V`, edge `w` from
  `prefix_{L-1}(w)` to `suffix_{L-1}(w)`, with multiplicity `A(w) = spec_L(S)(w)`.

**Fact 1.** `A` is a positive integer circulation: at every node the incoming
multiplicity equals the outgoing multiplicity (both equal the number of
occurrences of that `(L-1)`-mer).

**Fact 2.** `X_S` is strongly connected: its edges are the edges of the single
closed walk `t ↦ W_t` on the circle.

A **positive circulation of total `G`** is `f : V → ℤ_{>0}` with Fact 1's balance
and `Σ_w f(w) = G`. The truth `A` is one. Every positive circulation on the
strongly connected `X_S` is realizable as the `L`-spectrum of a circular word of
length `G` (take an Eulerian circuit of the weighted multigraph). Conversely the
spectrum of any length-`G` circular word with support `V` is such a circulation.
So:

> same-length §6.2 spelled candidates with support `V`
> ⟺ positive circulations of total `G` on `X_S` that are single Eulerian
> circuits.

The rigidity theorem will prove there is only one circulation, so the
"single Eulerian circuit" restriction is immaterial.

---

## 3. Rigidity theorem

**Theorem A (rigidity under short `(L-1)`-repeats).** If every length-`(L-1)`
window of `S` occurs **at most twice**, then `A = spec_L(S)` is the unique
positive circulation of total `G` on `X_S`.

*Proof.* Let `B` be any positive circulation with `ΣB = G` and set `δ = B - A`;
then `Bδ = 0` and `Σδ = 0`. Since `A(w) ≤` (occurrences of `prefix_{L-1}(w)`)
`≤ 2` and `B(w) ≥ 1`, every `δ(w) ≥ 1 - A(w) ≥ -1`. Suppose `δ ≠ 0` and let
`N = {w : δ(w) < 0} ≠ ∅`. For `w ∈ N`, `δ(w) = -1`, `A(w) = 2`, `B(w) = 1`.

Let `v` be the tail of such a `w`. Because `A(w) = 2` and the total out-flow
`out_A(v) =` (occurrences of `v`) `≤ 2`, the edge `w` is the only outgoing edge
at `v`; hence `out_δ(v) = δ(w) = -1`, and balance gives `in_δ(v) = -1`. Every
incoming edge `e` has `δ(e) ≥ -1`, and the incoming edges have `A`-values summing
to `in_A(v) = out_A(v) = 2`: if `v` had two incoming edges, each would have
`A = 1`, hence `δ ≥ 0`, giving `in_δ(v) ≥ 0`, a contradiction. So `v` has a
single incoming edge `e`, with `A(e) = 2` and `δ(e) = -1`, i.e. `e ∈ N`. Thus
every edge incident to the tail of an `N`-edge lies in `N`; symmetrically the
same holds at the head (use `A(w) = 2` at the suffix node). Hence the edges of
`N` form a union of connected components of `X_S` with no edge to `V \ N`.

By Fact 2, `X_S` is strongly connected, so either `N = ∅` or `N = V`. If
`N = V` then `Σδ = -|V| < 0`, contradicting `Σδ = 0`. Hence `N = ∅`, so
`δ ≥ 0`; a nonnegative circulation with `Σδ = 0` is zero, so `B = A`. ∎

**Lemma B (primitive long triple repeat).** Let `S` be primitive and suppose a
length-`(L-1)` window occurs at least three times. Then `S` has a Bresler triple
repeat of length `≥ L-1`.

*Proof.* Take three starts carrying the same `(L-1)`-window and extend the three
copies in both directions while all three are equal. The process stays below
length `G`: three equal length-`G` windows would make `S` invariant under the
nonzero shift between two starts, contradicting primitivity. At termination one
cannot extend on either flank, i.e. the preceding symbols are not all equal and
the following symbols are not all equal. The length is `≥ L-1`. ∎

**Lemma C (periodic long triple repeat).** Let `S = P^k` with minimal period
`p < G`, and suppose some factor of `P` of length `≥ L-1` occurs at least twice
in circular `P`. Then `S` has a Bresler triple repeat of length `≥ L-1`.

*Proof.* Let `f` occur at residues `r₁ ≠ r₂ (mod p)`. Then `S` contains the two
translated families `r_i + jp`. Extend both families maximally in both
directions; by `p`-periodicity the extension is uniform within each family. It
cannot reach length `G`: that would make `r₂ - r₁` a period of `S`, hence
`gcd(r₂ - r₁, p) < p` a period of `P`, contradicting minimality. At termination
the two families differ on at least one flank; continuing on a still-equal flank
until length `G` is impossible, so both flanks differ. Choosing three
occurrences meeting both families then witnesses a Bresler triple repeat of
length `≥ L-1`. ∎

**Fact D.** If `S` admits `R ∈ I_s`, then `S` has no Bresler triple repeat of
length `≥ L-1` (a copy of such a repeat cannot be bridged by a length-`L` read).

**Main theorem.** If `S` admits a read realization `R ∈ I_s`, then `A = spec_L(S)`
is the unique positive circulation of total `G` on `X_S`.

*Proof.* **Primitive case.** By Fact D there is no Bresler triple repeat of
length `≥ L-1`; by Lemma B every `(L-1)`-window occurs at most twice; Theorem A
applies. **Periodic case** `S = P^k`: by Fact D and Lemma C every factor of `P`
of length `≥ L-1` occurs at most once, so the `p` length-`(L-1)` and length-`L`
windows of `P` are distinct and `X_S` is a single directed `p`-cycle with
`A(w) = k` on every edge. A positive circulation on a directed cycle is constant
along it, and total `G = kp` forces the value `k`; so `B = A`. ∎

The theorem's hypothesis is weaker than `I_s`: it uses only the triple-repeat
clause. The interleaved clause is not needed.

---

## 4. Corollary: the same-length zero is a theorem

Let `x` have `supp(x) = V = supp(spec_L(S))` (otherwise the truth is not a §6.2
candidate), and let `D` be any same-length §6.2 spelled candidate. Its spectrum
is a positive circulation of total `G` on `X_S`, hence by the main theorem
`spec_L(D) = spec_L(S)`. Therefore, for **every** objective that depends only on
`(spec_L(D), x)`:

```text
L(D | x) / L(S | x) = 1 .
```

There is no strict same-length counterexample for any `G`, `L`, or alphabet. This
single argument explains all of: the PR #47 §3.2 zeros, the
`oriented-single-strand-se62-same-length-2026-09-20.md` reduction's unsatisfiable
condition (B), and the `support_feasibility_search.py` `supp_cex = 0` count.
[mathematical proof; verified computation agrees]

The `main` same-length §6.2 witness `AAATAT → AAAAAT` is untouched: it is a
**molecule (reverse-complement-collapsed)** witness, and under strict oriented
types the observed `TAT` is absent from `AAAAAT` (competitor likelihood `0`).
[verified computation]

---

## 5. Distinction 1: support equality vs full §6.2 graph/transitive-reduction feasibility

The task asks to separate the **necessary** support condition from genuine
reduced-overlap-graph feasibility. The logical content is an over-approximation,
in the direction that protects the zero:

- A spelled §6.2 circuit visits every observed read vertex (lower bound `1`), so
  `supp(spec_L(D)) = supp(x)`: **support equality is necessary.**
- The theorem does not assume the overlap edges survive transitive reduction. It
  proves uniqueness on the set of *all* positive circulations of `X_S`. Any
  fully feasible spelled circuit is a spelled walk of `X_S`, hence one of those
  circulations. Therefore

  ```text
  full §6.2 feasible spelled candidates
    ⊆ support-equal spelled candidates
    = positive circulations of total G on X_S
    = {spec_L(S)} .
  ```

  A zero on the larger support-feasible set is a zero on the smaller fully
  feasible set.
- The edge-lower-bound reading (`0`) and the per-vertex lower bound (`1`) are the
  source's; the per-occurrence strengthening `d_D(w) ≥ x_w` is strictly stronger
  and is *not* used here. In particular the variable-length witness of §7 is
  excluded by that strengthening, which is exactly why PR #47's per-occurrence
  searches were vacuous for it.

[mathematical proof]

---

## 6. Distinction 2: exact multinomial vs fixed-`N` §6.1

Two candidates with the **same spectrum** receive:

- exact multinomial ratio `∏_w (d_D(w)/N(D))^{x_w} / (d_S(w)/N(S))^{x_w} = 1`
  when `N(D) = N(S)` and `d_D = d_S`;
- literal fixed-`N` product ratio `1` because every per-type binomial factor is
  identical.

So the same-length zero of §4 holds for **both** objectives; it is
objective-independent. The two objectives separate only when candidate lengths
(and hence spectra totals) differ. The §1 reduction of the unmerged oriented note
used the same-length exact multinomial; PR #47 used the fixed-`N` §6.1 product.
Both are covered because equal spectra make the distinction vacuous.

At different lengths the source's fixed-`N` §6.1 product does not constrain
candidate length at all (`N` is external), while the exact multinomial carries
`N(D) = |D|`. Both can be strictly beaten by a support-equal longer competitor
(§7); the same mechanism (a per-vertex support-equal candidate whose
multiplicity is reallocated onto an over-observed type) works for both, because
`p_D(w₀) > p_S(w₀)` for some observed `w₀` makes the ratio diverge after
amplification.

---

## 7. Beyond the searched scope: a strict oriented variable-length counterexample

The same-length theorem does not extend to different lengths. Minimal strict
oriented single-strand instance:

```text
truth            S = AAATT                     (G = 5)
read length      L = 3
observed         x = { AAA:2, AAT:1, ATT:1, TTA:1, TAA:1 }   (n = 6)
competitor       D = AAAATT                    (|D| = 6)
spec_3(S)        = { AAA:1, AAT:1, ATT:1, TTA:1, TAA:1 }
spec_3(D)        = { AAA:2, AAT:1, ATT:1, TTA:1, TAA:1 }
support equality : supp(spec_3 S) = supp(spec_3 D) = supp(x) = V   (yes)
exact multinomial        L(D)/L(S) = (5/3)^2 (5/6)^4 = 15625/11664 > 1
fixed-N 6.1 (N=5)        L(D)/L(S) = 81/64 > 1
```

- **`I_s` holds.** `x` is realized by reads at starts `0 (twice), 1, 2, 3, 4`
  (coverage); `S`'s only maximal triple repeat is the length-`1` `A` at
  `{0,1,2}` and it is all-bridged by reads at `4, 0, 1`; there is no interleaved
  pair. The copy length `1 = L-2` is bridgeable. [verified computation]
- **Both are §6.2 spelled circuits.** Each is its own cyclic length-`3` window
  walk; consecutive windows overlap in `L-1 = 2` symbols, the maximal proper
  overlap, and every observed read vertex is visited (per-vertex lower bound
  `1`); the circulations are balanced. [verified computation]
- **The same-length theorem is not violated.** `|D| = 6 ≠ 5`, so `D` is not a
  positive circulation of total `G = 5` on `X_S`. The theorem says nothing here.
- **The witness violates the per-occurrence strengthening.** `d_S(AAA) = 1 <
  x_AAA = 2`. The source §6.2 lower bound is per read *vertex* and equals `1`, so
  this is admissible; the strengthening `d_D ≥ x` (a different reading) excludes
  it. This is precisely why the earlier `n < N` per-occurrence searches did not
  see it.

A one-parameter family works by the same argument: for `S = AAATT`,
`D = AAAATT` and `x = d_S + M · e_{AAA}`, both ratios equal
`(5/3)^{1+M} (5/6)^4 · (1)` (exact) and grow without bound. Setting `M = 0`
reproduces the `n = N = G` slice in which the truth wins (exact `3125/3888`,
fixed-`N` `81/128`), so the boundary is exactly `n > N`. [verified computation]

**Relation to prior art.** The `AAATT → AAAATT` pair already appears on `main`
as a **bidirected / reverse-complement** variable-length witness
(`docs/bridging-se62-flow-ml-counterexample.md`, kernel-checked in
`AssemblyP1/Section62BridgingCounterexample.lean`). There the observed support is
`{AAA, AAT, TAA}` and the feasibility uses the collapse `ATT ~ AAT`, `TTA ~
TAA`; under strict oriented types that truth is **not** support-admissible
(`supp(x) ⊊ V`). The instance above fixes the orientation by observing every
truth type (plus an extra `AAA`), so `supp(x) = V`, and then the same pair is a
strict oriented counterexample. The mechanism is therefore **observed
multiplicity skew**, not reverse-complement collapse; the claim in
`bridging-se62-flow-ml-counterexample.md` §4 that "the mechanism needs the
reverse-complement collapse" is accurate only under the stronger
per-occurrence/n<N reading used there. [verified computation; correction]

---

## 8. Exhaustive consistency checks

`scripts/oriented_se62_rigidity_audit.py` re-derives the spectra, repeats, `I_s`,
support grouping and non-rigidity from scratch (no import of any repository
search). It groups all `σ^G` words by window support and counts (a) non-rigid
supports, (b) non-rigid words whose `(L-1)`-windows all occur `≤ 2`, (c) non-rigid
`I_s`-realizable words. The theorem predicts (b) = (c) = 0. Independent quick
scopes and, in `--full`, previously unsearched non-vacuous cells:

| alphabet | `L` | `G` | non-rigid supports | non-rigid ∧ `(L-1)`≤2 | non-rigid ∧ `I_s` |
|---|---|---|---|---|---|
| binary | 3 | 5–8 | 8 | 0 | 0 |
| binary | 4 | 12,14,16 | 333 | 0 | 0 |
| binary | 5 | 17,18 | 955 | 0 | 0 |
| ternary | 3 | 10,12,13 | 8001 | 0 | 0 |
| four-letter | 3 | 9,10,11 | 8478 | 0 | 0 |

The binary `G = 17,18` (`L = 5`), ternary `G = 13`, and four-letter `G = 11`
rows are non-vacuous and were not in the PR #47 / oriented-note scopes
(`G ≤ 16`, `G ≤ 12`, `G ≤ 10` respectively). All zeros. This is evidence and a
sanity check; the proof of §3 makes it unnecessary for correctness.
[verified computation, exhaustive in scope]

---

## 9. What this settles and what it does not

**Does.** It proves that the strict oriented single-strand, same-length,
per-vertex §6.2 spelled-circuit implication is **true with a margin**: the truth
ties every candidate (ratio `1`), for any `G, L, Σ`, under both the exact and
fixed-`N` objectives. The bounded zeros are subsumed.

**Does not.** It does not extend to different candidate lengths (§7), does not
cover the molecule / reverse-complement convention (where same-length
counterexamples exist — `AAATAT → AAAAAT`, kernel-checked), does not cover the
per-occurrence strengthening, and does not select which MB09 layer the 2016
sentence intends or the tie/equivalence semantics.

---

## 10. Epistemic classification

| Claim | Status |
|---|---|
| Shomorony oriented single-strand read types; reverse complement is preprocessing | source fact |
| A §6.2 spelled candidate has `supp(spec_L(D)) = supp(x)` (per-vertex lower bound `1`) | source fact + source-supported inference |
| `I_s` ⇒ no Bresler triple repeat of length `≥ L-1` | source fact + proof |
| Theorem A: all `(L-1)`-windows `≤ 2` ⇒ unique positive circulation of total `G` | mathematical proof |
| Lemmas B, C: primitive/periodic long triple repeats | mathematical proof |
| Main theorem: `I_s` ⇒ unique positive circulation of total `G` | mathematical proof |
| Same-length strict oriented §6.2 has no strict counterexample, any `G,L,Σ`, both objectives | mathematical proof |
| Support equality necessary; theorem holds on the circulation superset, hence covers full reduced-graph feasibility | mathematical proof |
| `S = AAATT`, `D = AAAATT`, extra observed `AAA`: strict oriented, support-equal, `I_s` variable-length counterexample, ratios `15625/11664` (exact) and `81/64` (fixed-`N`) | verified computation |
| The pair needs reverse-complement collapse under the per-occurrence/n<N reading but not under strict oriented per-vertex with `supp(x)=V` | verified computation; correction of a prior note |
| Exhaustive scans to `G = 18` (binary `L=5`), ternary `G=13`, four-letter `G=11` all zero | verified computation, exhaustive in scope |
| Which MB09 layer; tie/equivalence semantics | open |

---

## 11. Reproduce and cross-references

```sh
python3 scripts/oriented_se62_rigidity_audit.py          # quick (~30 s)
python3 scripts/oriented_se62_rigidity_audit.py --full   # wider scopes
```

Primary sources. Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C.
Tse, *Information-optimal genome assembly via sparse read-overlap graphs*,
*Bioinformatics* 32(17) (2016) i494–i502, §2–§5, DOI
`10.1093/bioinformatics/btw450`. Paul Medvedev, Michael Brudno, *Maximum
Likelihood Genome Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116, §6.1–6.2,
Observation 7, PMC3154397. Guy Bresler, Ma'ayan Bresler, David Tse, *Optimal
assembly for high throughput shotgun sequencing*, *BMC Bioinformatics*
14(Suppl 5):S18 (2013), PMC3706340.

Cross-references on `main`:
[`../bridging-se62-flow-ml-counterexample.md`](../bridging-se62-flow-ml-counterexample.md),
[`../section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md),
[`uniform-strand-convention-search-2026-09-20.md`](uniform-strand-convention-search-2026-09-20.md)
(branch artifact), [`../bridging-source-semantics.md`](../bridging-source-semantics.md).
Unmerged branch artifact with the same theorem:
`research/uniform-oriented-strand-2026-09-20`
(`docs/source-notes/uniform-oriented-rigidity-obstruction.md`).
