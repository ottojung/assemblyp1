# Strict oriented single-strand Section 6.2: a rigidity theorem, and why the length restriction is essential

_Status: independent mathematical proof + exact computation, 2026-09-20, written
for the residual left open on `main` by the unmerged oriented note
`oriented-single-strand-se62-same-length-2026-09-20.md` §4 (there called
Conjecture C) and by the issue-#36 flow-structure frontier. Every
claim is labelled **source fact**, **mathematical proof**, **verified
computation**, **modeling choice**, or **open**. It does not select which
Medvedev–Brudno (2009) likelihood layer the Shomorony et al. (2016) sentence
intends, and it does not touch tie/equivalence semantics._

_Reproduce: `python3 scripts/verify_oriented_se62_rigidity.py` (quick) and
`python3 scripts/verify_oriented_se62_rigidity.py --full` (wider exhaustive
scopes). Self-contained, exact `fractions.Fraction`, deterministic, exits
non-zero on any failed assertion._

_Independence. The same theorem is proved, independently and earlier, on the
unmerged branches `research/oriented-se62-rigidity-audit`
(`docs/source-notes/oriented-se62-rigidity-audit-2026-09-20.md`, branch tip
`f8f2e41`) and `research/uniform-oriented-strand-2026-09-20`
(`docs/source-notes/uniform-oriented-rigidity-obstruction.md`, branch tip
`7c2bb9f`), neither of which is on `main`. This note re-derives the statement and
proof from scratch, sharpens it to the exact hypothesis (only the triple-repeat
clause is used), and records the two boundaries (equal vs. different candidate
length; and the minimal obstruction showing the hypothesis is necessary)._

---

## 0. Answer at a glance

Work under the **strict oriented single-strand** convention: read types are the
oriented length-`L` windows of the circular truth `S` with no reverse-complement
collapse, and a Section 6.2 *spelled candidate* is a circular word `D` of length
`G` whose length-`L` window support equals the observed support.

1. **Same length is rigid.** If some read realization `R` of `S` lies in
   Shomorony's `I_s`, then `spec_L(S)` is the **unique positive integer
   circulation of total `G = |S|`** on its own length-`L` window-support graph
   `X_S`. Consequently every same-length Section 6.2 spelled candidate has the
   truth's spectrum, every likelihood ratio is exactly `1`, and **no strict
   same-length counterexample exists for any `G`, `L`, or alphabet**, under the
   exact multinomial and the fixed-`N` §6.1 binomial alike. [mathematical proof]

2. **Only the triple-repeat clause is used.** The hypothesis needed is weaker
   than `I_s`: the theorem only uses "no Bresler triple repeat of length
   `>= L-1`". The interleaved-repeat clause is not used. [mathematical proof]

3. **The equal-length restriction is essential and sharp.** For different
   candidate lengths the statement is false, with the strict oriented boundary
   witness `S = AAATT`, `D = AAAATT`, `L = 3`: `I_s` holds, the supports agree,
   and `D` strictly beats `S` once the observed multiplicity is skewed (`n > G`).
   [verified computation]

4. **The hypothesis is necessary.** Non-rigidity (`A` not unique) is exactly the
   same-length obstruction, and it forces a long Bresler triple repeat. The
   minimum same-length non-rigid pair is `S = AAAAB`, `D = AABAB` (`G = 5`,
   `L = 2`); with a skewed observation the truth is beaten. [mathematical proof +
   verified computation]

This is a genuine obstruction, not a finite search: it explains all previously
reported bounded single-strand zeros with one argument and closes the issue-#36
"oriented same-length Section 6.2" residue.

---

## 1. The convention, stated exactly

- **Read type.** The oriented length-`L` circular window
  `W_t = S_t S_{t+1} ... S_{t+L-1}` of the circular truth `S`, indices mod
  `  G = |S|`, with no reverse-complement collapse. [source fact: Shomorony et al.
  2016, §2; the double-strand-to-single-strand reduction is their own convention,
  recorded in the unmerged branch note `reverse-complement-strand-convention.md`]
- **Spectrum.** `spec_L(S)(w) = #{ t : W_t = w }`, total `G`; support
  `V = supp(spec_L(S))`.
- **Section 6.2 spelled candidate.** The observation has support `V_x = supp(x)`.
  A graph vertex is a read, with per-vertex lower bound `1`; Observation 7
  identifies vertex flow with submolecule multiplicity. Hence a spelled candidate
  `D` must satisfy `supp(spec_L(D)) = V_x` (see
  [`../section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md)
  §1.1 and the unmerged audit `mb09-se61-se62-candidate-semantics-audit-2026-09-20.md`
  §5.2). We treat this as **source fact + source-supported inference**.
- **Bridging.** Shomorony `I_s` (Eq. (1), inherited from Bresler et al. 2013):
  coverage, every Bresler triple repeat all-bridged, every interleaved pair
  bridged. A length-`L` read bridges a copy of a repeat of length `ell` only if
  `ell <= L-2` (strict extension on both sides:
  `ell < L-1`). [source fact; [`../bridging-source-semantics.md`](../bridging-source-semantics.md)]

  The three-copy Bresler maximality is used verbatim: three starts carrying an
  equal length-`ell` window whose **preceding symbols are not all equal** and
  whose **following symbols are not all equal**. [source fact]
- **Objectives.** The exact MB09 §6.1 multinomial with candidate-intrinsic
  `N(D) = |D|`, and the §6.1 fixed-`N` product of binomial marginals with external
  known `N`. Both are functions of `(spec_L(D), x)`. [source fact]

---

## 2. The window-support graph `X_S` and the reduction

Given a circular word `S`, build the directed multigraph `X_S`:

- **nodes** are the distinct length-`(L-1)` circular windows occurring in `S`;
- **edges** are the distinct length-`L` windows `w in V`; edge `w` runs from
  `prefix_{L-1}(w)` to `suffix_{L-1}(w)`, carrying multiplicity `A(w) = spec_L(S)(w)`.

**Fact 1 (the truth is a circulation).** `A` is balanced: at each node the total
incoming multiplicity equals the total outgoing multiplicity; both equal the
number of occurrences of that `(L-1)`-mer as a window of `S`. [mathematical proof]

**Fact 2 (support is strongly connected).** The edges are the edges of the single
closed walk `t -> W_t`, so `X_S` is strongly connected. [mathematical proof]

A **positive circulation of total `G`** is a map `f : V -> Z_{>0}` that is
balanced at every node and has `sum_w f(w) = G`. The truth `A` is one.

**Reduction R.** Same-length Section 6.2 spelled candidates with observed support
`V` are exactly the positive circulations of total `G` on `X_S`.

_Proof._ A circular word `D` of length `G` has a balanced positive spectrum of
total `G`; if `supp(spec_L(D)) = V` it is such a circulation. Conversely a
positive circulation `f` on the strongly connected balanced multigraph makes it
Eulerian, so an Eulerian circuit exists and spells a circular word `D` of length
`G` with `spec_L(D) = f`. (The "single Eulerian circuit" requirement is an extra
restriction on candidates, but the rigidity theorem proves uniqueness on the
larger circulation set, so it covers it a fortiori.) [mathematical proof]

Two candidates with the same spectrum tie under every `(spec_L, x)`-objective; in
particular equal spectra make the exact/fixed-`N` distinction vacuous. So on the
same-length slice the only route to a strict improvement is a different positive
circulation `B != A`.

---

## 3. The rigidity theorem

**Theorem A (short-repeat rigidity).** If every length-`(L-1)` window of `S`
occurs **at most twice**, then `A = spec_L(S)` is the unique positive circulation
of total `G` on `X_S`.

_Proof._ Let `B` be a positive circulation of total `G` and put `delta = B - A`.
Then `delta` is a circulation with `sum_w delta(w) = 0`. Since `A(w) <=`
(occurrences of `prefix_{L-1}(w)`) `<= 2` and `B(w) >= 1`, every
`delta(w) >= 1 - A(w) >= -1`; in particular `A(w) <= 2` on every edge.

Suppose `delta != 0`; then `N = { w : delta(w) < 0 }` is nonempty (because
`sum delta = 0`), and for `w in N` we have `delta(w) = -1`, `A(w) = 2`,
`B(w) = 1`.

Take `w in N` with tail `v`. Since `A(w) = 2` and the node bound
`out_A(v) =` (occurrences of `v`) `<= 2`, the edge `w` is the **only** outgoing
edge at `v`; hence `out_delta(v) = delta(w) = -1`, and balance gives
`in_delta(v) = -1`. Every incoming edge `e` has `delta(e) >= -1`, and the incoming
edges have `A`-values summing to `in_A(v) = out_A(v) = 2`. If `v` had two incoming
edges, each would have `A = 1`, hence `delta >= 0`, giving `in_delta(v) >= 0`, a
contradiction. So `v` has exactly one incoming edge `e`, with `A(e) = 2` and
`delta(e) = -1`, i.e. `e in N`. Symmetrically at the head of `w` (which has
`in_A = 2`, so one incoming edge `w` and one outgoing edge `f`, with `f in N`).
Thus every edge incident to a node touched by `N` lies in `N`: the edges of `N`
form a union of connected components of `X_S` with no edge to `V \ N`.

By Fact 2, `X_S` is strongly connected, so `N = empty` or `N = V`. If `N = V`
then `sum delta = -|V| < 0`, contradicting `sum delta = 0`. Hence `N = empty`, so
`delta >= 0`; a nonnegative circulation with `sum delta = 0` is zero, hence
`B = A`. ∎

**Lemma B (primitive extension).** Let `S` be primitive (minimal period `G`) and
suppose some length-`(L-1)` window occurs at least three times. Then `S` has a
Bresler triple repeat of length `>= L-1`.

_Proof._ Choose three distinct starts carrying the same length-`(L-1)` window.
Extend the three copies in both directions as long as all three remain equal: if
the three preceding symbols are all equal, prepend that symbol; if the three
following symbols are all equal, append it. The process cannot reach total length
`G`, because three equal length-`G` windows would make `S` invariant under the
nonzero shift between two starts, contradicting primitivity. At termination the
three preceding symbols are not all equal and the three following symbols are not
all equal, which is exactly Bresler's three-copy maximality; the length is
`>= L-1`. ∎

**Lemma C (periodic extension).** Let `S = P^k` with minimal period `p < G`, so
`k = G/p >= 2`, and suppose some factor of `P` of length `>= L-1` occurs at least
twice in the circular word `P`. Then `S` has a Bresler triple repeat of length
`>= L-1`.

_Proof._ Write such a factor as `f`, occurring at residues `r1 != r2 (mod p)`.
Then `f` occurs in `S` at `r1 + jp` and `r2 + jp` for `j = 0,...,k-1`, at least
four occurrences. Extend the two families maximally in both directions; by
`p`-periodicity the extension is uniform over `j`, and it cannot reach length `G`
because that would make `r2 - r1` a period of `S`, hence `gcd(r2-r1, p) < p` a
period of `P`, contradicting minimality. At termination neither flank extends:
the preceding symbols are not all equal and the following symbols are not all
equal (otherwise we would extend). The two families are translation-identical, so
the only possible symbol differences on each flank are between the families; any
three occurrences meeting both families therefore witness a Bresler triple repeat
of length `>= L-1`. ∎

**Fact D (bridging forbids long triple repeats).** A length-`L` read bridges a
copy of a repeat of length `ell` only if `ell <= L-2`. Hence if `R in I_s`, then
`S` has **no** Bresler triple repeat of length `>= L-1`. [source fact +
mathematical proof]

**Main theorem (rigidity under `I_s`).** If `S` admits a read realization
`R in I_s`, then `A = spec_L(S)` is the unique positive circulation of total `G`
on `X_S`.

_Proof._ If `S` is primitive: by Fact D there is no Bresler triple repeat of
length `>= L-1`; by Lemma B no length-`(L-1)` window occurs three times, hence
every one occurs at most twice and Theorem A applies. If `S = P^k` with minimal
period `p < G`: by Fact D and Lemma C, every factor of `P` of length `>= L-1`
occurs at most once. Hence the `p` length-`L` windows and the `p` length-`(L-1)`
windows of `P` are pairwise distinct, so `X_S` is a single directed `p`-cycle
with `A(w) = k` on every edge. A positive circulation on a directed cycle is
constant along it by balance, and total `G = kp` forces the value `k`, so
`B = A`. ∎

**Corollary (same-length zero is a theorem).** Suppose `R in I_s` and the truth
is Section 6.2-admissible, so `supp(x) = V = supp(spec_L(S))`. Then every
same-length Section 6.2 spelled candidate `D` satisfies `spec_L(D) = spec_L(S)`,
and for every objective that is a function of `(spec_L(D), x)`,

```text
L(D | x) / L(S | x) = 1 .
```

There is no strict same-length counterexample for any `G`, `L`, or alphabet.
[mathematical proof]

---

## 4. When can the truth-induced circuit be beaten?

The theorem above isolates the exact obstruction on the same-length slice.

**Theorem (same-length beatability criterion).** Fix `S`, `L`, and an observation
`x` with `supp(x) = V = supp(spec_L(S))`, and let `A = spec_L(S)`.

1. If `A` is the unique positive circulation of total `G` on `X_S`, then every
   same-length Section 6.2 spelled candidate has `spec_L(D) = A`, so the truth
   ties every candidate under any `(spec_L, x)`-objective.
2. If `B != A` is another positive circulation of total `G`, choose any `w0` with
   `B(w0) > A(w0)` and put `x_M = x + M * e_{w0}`. Then
   `ratio_M = ratio_0 * (B(w0)/A(w0))^M`, which exceeds `1` for all sufficiently
   large `M`, under the exact multinomial (same length, so length factors cancel)
   and the fixed-`N` §6.1 binomial, whose finite domain is respected because
   `B(w0) < G = N` whenever `B` is positive and non-constant. [mathematical proof]

So **non-rigidity is exactly the same-length obstruction**, and by the Main
theorem `I_s` (indeed just its triple-repeat clause) removes it. The minimum
non-rigid pair is recorded in §5.

**Boundary: different candidate lengths.** The same-length restriction is
essential. On the next slice, where `|D| > G` is allowed, the truth need not be
optimal even under `I_s`. The minimal strict oriented instance is
`S = AAATT`, `D = AAAATT`, `L = 3`; see §5. [verified computation]

**Boundary: other strand conventions.** The `main`-integrated same-length witness
`AAATAT -> AAAAAT` is a *molecule* (reverse-complement-collapsed) witness, not a
strict oriented one; under strict oriented types the observed `TAT` is absent from
`AAAAAT` (competitor likelihood `0`). It is therefore not evidence about the
oriented convention. [verified computation; repository fact]

---

## 5. Minimal obstructions

### 5.1 The hypothesis is necessary (same length, no `I_s`)

Minimum same-length non-rigid pair (searched over `sigma in {2,3,4}`,
`L in {2,3,4}`; smallest overall, then smallest with `L >= 3`):

| scope | `S` | `D` | `G` | `L` | `spec_L(S)` | `spec_L(D)` |
|---|---|---|---|---|---|---|
| overall min | `AAAAB` | `AABAB` | 5 | 2 | `AA:3, AB:1, BA:1` | `AA:1, AB:2, BA:2` |
| min with `L >= 3` | `AAAAAAB` | `AAABAAB` | 7 | 3 | `AAA:4, AAB:1, ABA:1, BAA:1` | `AAA:1, AAB:2, ABA:2, BAA:2` |

Both truths carry a long Bresler triple repeat (`ell = 1 = L-1` for `L = 2`,
`ell = 2 = L-1` for `L = 3`), so neither is `I_s`-admissible; skirting the
triple-repeat clause of `I_s` is exactly what permits the reallocation. With
`x = spec_L(S) + M * e_{w0}` (`w0 = AB`, resp. `AAB`) the competitor `D` strictly
beats the truth for large `M` (`16384/27`, resp. `128`, at `M = 12`).
[verified computation]

### 5.2 The length restriction is essential (variable length, with `I_s`)

A strict oriented Section 6.2 boundary witness:

```text
truth         S = AAATT          (G = 5)
read length   L = 3
competitor    D = AAAATT         (|D| = 6)
spec_3(S)     = { AAA:1, AAT:1, ATT:1, TTA:1, TAA:1 }
spec_3(D)     = { AAA:2, AAT:1, ATT:1, TTA:1, TAA:1 }
support       supp(spec_3 S) = supp(spec_3 D) = supp(x) = V   (yes)
```

`I_s` holds (coverage; the only maximal triple repeat is the length-`1` `A`,
bridgeable since `1 = L-2`; no interleaved pair). With
`x = spec_3(S) + M * e_AAA`:

| `M` (`n = 5+M`) | exact multinomial | fixed-`N` §6.1 (`N = 5`) |
|---|---|---|
| 0 | `3125/3888` (does not beat) | `81/128` (does not beat) |
| 1 | `15625/11664 > 1` | `81/64 > 1` |
| 2 | `78125/34992 > 1` | `81/32 > 1` |
| 3 | `390625/104976 > 1` | `81/16 > 1` |

The boundary is exactly `n > G`: at `n = G` the truth wins, and one extra sample
of an over-represented type overturns it. [verified computation]

This `AAATT -> AAAATT` pair already appears on `main` as a *bidirected /
reverse-complement* variable-length witness
([`../bridging-se62-flow-ml-counterexample.md`](../bridging-se62-flow-ml-counterexample.md),
kernel-checked in `AssemblyP1/Section62BridgingCounterexample.lean`). Here the
orientation is fixed by observing every truth type (plus an extra `AAA`), so
`supp(x) = V`, and the mechanism is **observed-multiplicity skew**, not
reverse-complement collapse.

---

## 6. Relation to issue #36 and the integrated witnesses

| prior claim / artifact | status after this note |
|---|---|
| Conjecture C: "non-rigid `spec_L(S)` requires a long triple repeat" (unmerged oriented note §4) | **proved** as the Main theorem + its exact hypothesis; the "no same-length strict counterexample under `I_s`" corollary follows |
| `oriented-single-strand-se62-same-length` reduction condition (B) | **shown unsatisfiable** under `I_s` |
| bounded single-strand / oriented Section 6.2 zeros | **explained** by the Main theorem, no longer merely evidence |
| `main` same-length witness `AAATAT -> AAAAAT` | unchanged; **molecule-only**, needs `TAT ~ ATA`, no strict oriented analogue |
| sequence-level `AAACC -> AAAAC` / `AAABB -> AAAAB` same-length witnesses | unchanged; they are not Section 6.2 (support differs), so they do not contradict the rigidity theorem |
| variable-length `AAATT -> AAAATT` | unchanged; now a strict oriented boundary witness |

The distinction is exactly the one issue #36 asks to keep explicit: the negative
result survives strict oriented read types at the **sequence level** (existing
witnesses) and is **impossible** at the same-length Section 6.2 spelled-circuit
level; it reappears at different candidate lengths.

---

## 7. Exhaustive evidence

`scripts/verify_oriented_se62_rigidity.py` re-implements spectra, support
grouping, Bresler triple repeats and the witnesses from scratch (no import of any
repository search). The main exhaustive assertion is:

> every word carrying a same-support same-length different-spectrum competitor
> has a Bresler triple repeat of length `>= L-1`; equivalently, no `I_s`-admissible
> word is non-rigid; and no word with all `(L-1)`-windows `<= 2` is non-rigid.

`--full` scopes (all `sigma^G` words enumerated; no sampling): binary `L = 3`
(`G <= 14`), `L = 4` (`G <= 13`), `L = 5` (`G <= 12`); ternary `L = 3`
(`G <= 10`); four-letter `L = 3` (`G <= 8`); 719 non-rigid supports scanned, all
zero violate the theorem. Periodic Lemma C is checked directly over primitive
periods `p <= 9` (`L = 3`), `p <= 8` (`L = 4`), `p <= 6` (ternary `L = 3`). The
exhaustive zeros are a sanity check; the proof makes them unnecessary for
correctness. [verified computation, exhaustive in scope]

---

## 8. Epistemic classification

| claim | status |
|---|---|
| Shomorony oriented single-strand read types; reverse complement is preprocessing | source fact |
| Section 6.2 spelled candidate has `supp(spec_L(D)) = supp(x)` | source fact + source-supported inference |
| `I_s` implies no Bresler triple repeat of length `>= L-1` | source fact + mathematical proof |
| Theorem A: all `(L-1)`-windows `<= 2` implies unique positive circulation of total `G` | mathematical proof |
| Lemmas B, C: primitive/periodic repetition implies a long Bresler triple repeat | mathematical proof |
| Main theorem: `I_s` implies unique positive circulation of total `G` | mathematical proof |
| Corollary: no strict same-length oriented Section 6.2 counterexample, any `G, L, Sigma`, both objectives | mathematical proof |
| Same-length beatability criterion; non-rigidity is exactly the obstruction | mathematical proof |
| Minimum non-rigid pairs `AAAAB`/`AABAB` (`L=2`) and `AAAAAAB`/`AAABAAB` (`L=3`, min with `L>=3`) | verified computation, exhaustive in searched scope |
| Variable-length boundary `AAATT -> AAAATT` | verified computation |
| Which MB09 layer the 2016 sentence intends; tie/equivalence semantics | open |

---

## 9. Sources

Primary. Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
*Bioinformatics* 32(17) (2016) i494–i502, §2–§5, DOI
`10.1093/bioinformatics/btw450`. Paul Medvedev, Michael Brudno, *Maximum
Likelihood Genome Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116, §6.1–6.2,
Observation 7, PMC3154397. Guy Bresler, Ma'ayan Bresler, David Tse, *Optimal
assembly for high throughput shotgun sequencing*, *BMC Bioinformatics*
14(Suppl 5):S18 (2013), DOI `10.1186/1471-2105-14-S5-S18`, PMC3706340.

Repository cross-references (on `main` unless noted):
[`../open-problem.md`](../open-problem.md),
[`../bridging-source-semantics.md`](../bridging-source-semantics.md),
[`mb09-se61-index-orientation-resolution.md`](mb09-se61-index-orientation-resolution.md),
[`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md),
[`conclusion-semantics-determination.md`](conclusion-semantics-determination.md),
[`../section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md),
[`../bridging-se62-flow-ml-counterexample.md`](../bridging-se62-flow-ml-counterexample.md),
[`../ml-formalization-contract.md`](../ml-formalization-contract.md).
Unmerged branch artifacts: `oriented-single-strand-se62-same-length-2026-09-20.md`,
`oriented-se62-rigidity-audit-2026-09-20.md`,
`uniform-oriented-rigidity-obstruction.md`.
