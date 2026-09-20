# Uniform single-strand/oriented read types: the surviving sequence-level negative result and the Section 6.2 rigidity obstruction

_Status: independent from-scratch mathematical proof + exact computation, 2026-09-20,
written against `origin/main` (`8b2f0fc`). Every claim is labelled **source fact**,
**mathematical proof**, **verified computation (exact, exhaustive in scope)**,
**bounded computation**, **repository fact**, or **open**. This note does not
select which Medvedev–Brudno (2009) likelihood layer the Shomorony et al. (2016)
sentence intends, and does not touch tie/uniqueness semantics. It resolves one
precisely delimited strand convention: **uniform single-strand / oriented read
types**._

_Reproduce: `python3 scripts/verify_uniform_oriented_rigidity.py` (quick, about
half a minute) and `... --full` (wider exhaustive scopes, several minutes). The
script is self-contained, exact (`fractions.Fraction`), deterministic, and exits
non-zero on any failed assertion._

---

## 0. Answer at a glance

The task asks whether the repository's negative result — “the bridging hypothesis
does **not** force the truth to be maximum-likelihood” — survives the strongest
plausible **uniform single-strand / oriented** strand convention, where read types
are oriented length-`L` windows and no reverse complement is ever collapsed. The
answer splits along the candidate class, and the two halves have opposite answers.

1. **Sequence objective (no Section 6.2 constraint): the negative result
   survives, and is already kernel-checked.** With oriented single-strand types,
   `S = AAATT`, `D = AAAAT`, `G = 5`, `L = 3`, realized starts `(0,1,4)`, the
   `I_s` certificate holds and the same-length exact ratio is exactly `2`
   (fixed-`N` Section 6.1 binomial ratio `1125/512 > 1`). This is the
   kernel-checked `AAABB → AAAAB` instance of
   `AssemblyP1/FixedLengthExactCounterexample.lean` under the alphabet rename
   `B ↦ T`; no reverse complement occurs on either side. [mathematical proof of
   transfer + verified computation; kernel check is repository fact]

2. **Section 6.2 spelled-circuit candidates, same length: the negative result
   does *not* survive, for every `G`, `L`, and alphabet.** The main theorem below
   proves that if `R ∈ I_s` then `spec_L(S)` is the **unique positive Eulerian
   circulation of total `G`** on its window support. Consequently every
   same-length Section 6.2 spelled candidate has the truth's length-`L` spectrum,
   the likelihood ratio against the truth is exactly `1`, and no strict
   same-length counterexample exists. This is a rigorous obstruction, not a
   finite search. It also explains, with a single argument, the bounded
   single-strand zeros recorded on the unmerged branch artifact
   `uniform-strand-convention-search-2026-09-20.md` §3.2. [mathematical proof;
   exhaustive computation in scope]

The integrated same-length Section 6.2 witness on `main`, `AAATAT → AAAAAT`, is a
**molecule-only** witness: it needs the reverse-complement collapse `TAT ~ ATA`.
Under the strict oriented reading it inverts (the observed oriented type `TAT` is
absent from `AAAAAT`, so that candidate has likelihood `0`). It is therefore not
evidence about the uniform single-strand convention at all. [verified computation;
repository fact]

---

## 1. The convention, stated exactly

**Read types (source fact).** Shomorony, Kim, Courtade & Tse (2016), §2, work
with a circular sequence `s` of length `G` and reads drawn from its length-`L`
substrings. The paper’s theory is single-stranded and identifies the
reconstruction target only up to **cyclic shift**; reverse complements appear only
as experimental preprocessing in §4.1 (“include each read and its reverse
complement”), which *adds* orientation nodes rather than identifying a read with
its reverse complement. [source fact]

**Uniform oriented convention used here.**

- Read type of a position `t`: the oriented word `W_t = s_t s_{t+1} … s_{t+L-1}`
  (indices mod `G`). No reverse-complement collapse.
- `spec_L(S)(w) = #{ t : W_t = w }`; its support is `V = supp(spec_L(S))`.
- Candidate: a circular word `D` of length `G`; it is scored through
  `spec_L(D)`.
- Genome equivalence: cyclic shift (not needed below).
- Bridging hypothesis: Shomorony’s `I_s` (Eq. (1)) — coverage, every Bresler
  triple repeat all-bridged, every interleaved repeat pair bridged. The Bresler
  (2013) repeat definitions, including the three-copy maximality condition, are
  the ones recorded in [`../bridging-source-semantics.md`](../bridging-source-semantics.md).
  [source fact]

**Section 6.2 spelled-circuit admissibility (source-supported inference).** In
MB09 §6.2 the graph vertices *are the reads*, each represented once, with a
per-vertex lower bound `1`; Observation 7 identifies a vertex flow with the
number of times the read is a submolecule of the spelled molecule. Hence a spelled
candidate `D` contains exactly the observed read types, i.e.
`supp(spec_L(D)) = supp(x)`, and its window multiplicities form a nonnegative
integer flow with total `= |D|`. This is the support-equality criterion used by
`main`’s Section 6.2 witness. [source fact + source-supported inference; see
[`../section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md)
§1.1]

**Objective.** Both the exact Medvedev–Brudno read-count multinomial with
candidate-intrinsic length and its Section 6.1 fixed-`N` product of binomial
marginals are functions of `(spec_L(·), x)`. For two candidates with the **same
length and the same spectrum**, the ratio is exactly `1` under either objective.

---

## 2. The sequence-level negative result survives (oriented, kernel-checked)

The kernel-checked module `AssemblyP1/FixedLengthExactCounterexample.lean` uses
`truth = AAABB`, `competitor = AAAAB`, `(G, L) = (5, 3)`, realized starts
`0, 1, 4`, observed reads `{AAA, AAB, BAA}`. Nothing in that file
takes a reverse complement; its read-type space is the oriented length-`3`
alphabet, and its `SourceHypotheses` is coverage plus the concrete all-bridged
maximal length-`1` triple repeat. Relabeling `B ↦ T` gives the real-DNA instance

```text
truth S = AAATT,  G = 5,  L = 3,  starts (0,1,4)
observed x = {AAA:1, AAT:1, TAA:1}
d_S = { AAA:1, AAT:1, ATT:1, TTA:1, TAA:1 }
D   = AAAAT,  d_D = { AAA:2, AAT:1, ATA:1, TAA:1 }
exact same-length ratio = 2
fixed-N Section 6.1 binomial ratio = 1125/512 > 1
```

`I_s` holds: the starts cover `{0,1,2,3,4}`, the maximal length-`1` triple repeat
`A@{0,1,2}` is all-bridged by the reads at starts `4,0,1`, and there is no
interleaved repeat pair. This is a genuine uniform oriented counterexample to the
**sequence-level** implication: `D` has the same length as `S`, both satisfy the
oriented model, and `D` is strictly more likely. [mathematical proof of the
relabeling transfer + verified computation; the base instance is kernel-checked]

The transfer is purely an alphabet renaming and preserves every repeat, bridge and
window relation; the script re-derives the spectra and the ratio from scratch.

---

## 3. The Section 6.2-oriented statement and its reduction

Fix `2 ≤ L ≤ G`, an alphabet `Σ`, and a circular truth `S` with an observed
oriented read multiset `x`. Suppose `R ∈ I_s` and the truth-induced flow is
Section 6.2-admissible, so `supp(x) = V = supp(spec_L(S))`.

**(P_fix_orient).** Every same-length Section 6.2 spelled candidate `D` (a
circular word of length `G` with `supp(spec_L(D)) = V` whose window multiplicities
form a positive integer vertex flow of total `G`) has
`spec_L(D) = spec_L(S)`; hence the truth maximizes the Section 6.1 objective and
the exact multinomial, and no strict same-length counterexample exists.

The reduction is immediate from the theorem of §5:

- a Section 6.2 spelled candidate of length `G` is exactly a positive integer
  Eulerian circulation `B` on the window-support graph with total `G`;
- the truth’s own spectrum `A = spec_L(S)` is such a circulation;
- the main theorem says `A` is the only one whenever `I_s` holds;
- equal spectra give likelihood ratio `1` under every `(d,x)`-objective.

This is exactly condition (B) of the reduction on the unmerged branch artifact
`oriented-single-strand-se62-same-length-2026-09-20.md`, now shown to be
unsatisfiable rather than merely unobserved.

---

## 4. The window-support graph

Given a circular word `S`, build the directed multigraph `X_S`:

- **nodes** are the distinct length-`(L-1)` circular windows occurring in `S`;
- **edges** are the distinct length-`L` windows `w ∈ V`; the edge `w` runs from
  `prefix_{L-1}(w)` to `suffix_{L-1}(w)`, with multiplicity `A(w) = spec_L(S)(w)`.

Two elementary facts.

**Fact 1 (truth is a circulation).** `A` is balanced: at each node the total
multiplicity of incoming edges equals the total multiplicity of outgoing edges.
Indeed both equal the number of occurrences of that `(L-1)`-mer as a window of
`S` (the shift `t ↦ t+1` pairs each occurrence’s prefix with the next suffix).
[mathematical proof]

**Fact 2 (support is strongly connected).** The edges `V` are the edge set of the
single closed walk `t ↦ W_t`, so `X_S` is strongly connected on `V`.
[mathematical proof]

A **positive circulation of total `G`** is a map `f : V → ℤ_{>0}` with the
balance of Fact 1 and `Σ_w f(w) = G`. The truth `A` is one. Non-rigidity means
some other one exists. A positive circulation on the strongly connected `X_S` is
realizable as the length-`L` spectrum of a circular word of length `G` (take an
Eulerian circuit of the weighted multigraph).

---

## 5. Rigidity theorem and two extension lemmas

**Theorem A (rigidity under short repeats).** Let `S` be a circular word in which
every length-`(L-1)` window occurs **at most twice**. Then `A = spec_L(S)` is the
unique positive circulation of total `G` on `X_S`.

*Proof.* Let `B` be any positive circulation of total `G`, and put `δ = B − A`.
Then `δ` is a circulation with `Σ_w δ(w) = 0`. Since `A(w) ≤` (occurrences of
`prefix_{L-1}(w)`) `≤ 2` and `B(w) ≥ 1`, we have `δ(w) ≥ 1 − A(w) ≥ −1`; in
particular `A(w) ≤ 2` for every edge. Suppose `δ ≠ 0` and let
`N = { w : δ(w) < 0 }`, which is nonempty because `Σδ = 0`. For `w ∈ N` we have
`δ(w) = −1`, `A(w) = 2`, `B(w) = 1`.

Take `w ∈ N` with tail node `v`. From `A(w) = 2` and the node bound
`out_A(v) =` (occurrences of `v`) `≤ 2`, the edge `w` is the *only* outgoing edge
at `v`, so `out_δ(v) = δ(w) = −1`. Balance of `δ` gives `in_δ(v) = −1`. Since
every incoming edge `e` has `δ(e) ≥ −1`, and the incoming edges have `A`-values
summing to `in_A(v) = out_A(v) = 2`: if `v` had two incoming edges they would each
have `A = 1`, hence `δ ≥ 0` and `in_δ(v) ≥ 0`, a contradiction. So `v` has exactly
one incoming edge `e`, with `A(e) = 2` and `δ(e) = −1`, i.e. `e ∈ N`. Thus `v` has
all its incident edges in `N`; every node incident to `N` is incident to no edge
outside `N`. So the edges of `N` form a union of connected components of `X_S`
with no edges to `V \ N`.

By Fact 2, `X_S` is strongly connected. Hence either `N = ∅` or `N = V`. If
`N = V`, then `Σδ = −|N| < 0`, contradicting `Σδ = 0`. Therefore `N = ∅`, so
`δ ≥ 0`; and a nonnegative circulation with `Σδ = 0` is identically zero, hence
`B = A`. ∎

**Lemma B (primitive extension).** Let `S` be primitive (minimal period `G`) and
suppose some length-`(L-1)` window occurs at least three times in `S`. Then `S`
has a Bresler triple repeat of length `≥ L − 1`.

*Proof.* Choose three distinct starts `t₁,t₂,t₃` carrying the same
`(L-1)`-window. Extend the three copies in both directions as long as all three
remain equal: if the three preceding symbols are all equal, prepend that symbol;
if the three following symbols are all equal, append that symbol. The process
cannot reach total length `G`, because three equal length-`G` windows would make
`S` invariant under the nonzero shift `t₂ − t₁`, contradicting primitivity. At
termination the three preceding symbols are not all equal and the three following
symbols are not all equal, giving a Bresler triple repeat of length `≥ L − 1`. ∎

**Lemma C (periodic extension).** Let `S = Pᵏ` with minimal period `p < G`, so
`k = G/p ≥ 2`, and suppose some factor of `P` of length `≥ L − 1` occurs at least
twice in the circular word `P`. Then `S` has a Bresler triple repeat of length
`≥ L − 1`.

*Proof.* Write such a factor as `f`, occurring at residues `r₁ ≠ r₂` mod `p`.
Then `f` occurs in `S` at `r₁ + jp` and `r₂ + jp` for `j = 0,…,k−1`, at least
four occurrences. Extend the two families maximally in both directions; by
`p`-periodicity the extension is uniform over `j`, and it cannot reach length `G`
because that would make `r₂ − r₁` a period of `S`, hence
`gcd(r₂ − r₁, p) < p` a period of `P`, contradicting minimality of `p`. At
termination the preceding symbols are not all equal and the following symbols are
not all equal (otherwise extend on the equal side). Since the two families are
translation-identical, the only possible symbol differences on each flank are
between the two families, so any three occurrences meeting both families witness
a Bresler triple repeat of length `≥ L − 1`. ∎

**Fact D (bridging forbids long triple repeats).** A length-`L` read can bridge a
copy of a repeat of length `ℓ` only if `ℓ + 2 ≤ L`, i.e. `ℓ ≤ L − 2`. Hence if
`R ∈ I_s`, then `S` has **no** Bresler triple repeat of length `≥ L − 1`.
[source fact + mathematical proof]

**Main theorem.** If `S` admits a read realization `R ∈ I_s`, then `A = spec_L(S)`
is the unique positive circulation of total `G` on `X_S`.

*Proof.* Suppose first `S` is primitive. By Fact D, `S` has no Bresler triple
repeat of length `≥ L − 1`. If some `(L-1)`-window occurred three times, Lemma B
would produce one, a contradiction. Hence every `(L-1)`-window occurs at most
twice, and Theorem A applies.

Suppose `S = Pᵏ` with minimal period `p < G`, `k ≥ 2`. By Fact D and Lemma C,
every factor of `P` of length `≥ L − 1` occurs at most once. In particular the `p`
length-`L` windows and the `p` length-`(L-1)` windows of `P` are pairwise
distinct, so `X_S` is a single directed `p`-cycle and `A(w) = k` on every edge.
Any positive circulation `B` on a directed cycle is constant along the cycle by
balance, and `ΣB = G = kp` forces `B = k = A`. Rigid. ∎

**Corollary.** Under uniform oriented single-strand read types with Section 6.2
spelled-circuit admissibility and `R ∈ I_s`, `(P_fix_orient)` holds: every
same-length candidate has the truth’s spectrum and ties it; there is no strict
same-length counterexample, for any `G`, `L`, or alphabet. The negative result
does **not** survive this convention. ∎

---

## 6. Exhaustive verification

`python3 scripts/verify_uniform_oriented_rigidity.py` re-derives, from scratch and
independently of the reviewed searches:

| check | result |
|---|---|
| `AAATT → AAAAT` oriented exact ratio `2`, Section 6.1 ratio `1125/512`, non-vacuous `I_s` | pass |
| Theorem A: non-rigid supports with all `(L-1)`-mers `≤ 2` | `0` in every scope |
| Lemma B: primitive, some `(L-1)`-mer `≥ 3`, no long triple repeat | `0` in every scope |
| Lemma C: periodic order-`≥2` with a repeated long period factor, no long triple repeat | `0` in every scope |
| Main theorem: `I_s`-realizable **and** non-rigid (the oriented S62 witnesses) | `0` in every scope |

Quick scopes (about half a minute): binary `(G,L) ∈ {(12,3),(14,3),(12,4)}`,
ternary `(10,3)`. `--full` adds binary up to `G = 18`, ternary up to `G = 12`,
four-letter up to `G = 10`. The scans are exhaustive over all `σ^G` circular
words; the non-rigidity test groups words by window support and detects supports
carrying more than one spectrum (equivalent to carrying a same-length
same-support different-spectrum competitor). [verified computation, exact and
exhaustive in scope]

The exhaustive zeros are evidence and a sanity check; the theorem of §5 makes
them unnecessary for correctness.

---

## 7. Relation to the integrated witnesses and earlier notes

| claim / artifact | status after this note |
|---|---|
| `main`’s `AAATAT → AAAAAT` Section 6.2 same-length witness needs `TAT ~ ATA`; oriented ratio is `0` | unchanged; it is molecule-only and does not bear on the uniform oriented convention (**verified computation**) |
| `AAABB → AAAAB` / `AAATT → AAAAT` exact sequence witness | unchanged; it **is** the uniform oriented sequence-level negative result and does not need Section 6.2 (**kernel-checked**) |
| unmerged `oriented-single-strand-se62-same-length-2026-09-20.md` Conjecture C (“non-rigid ⇒ an `(L-1)`-mer repeats `≥3`”) | proved here as a special case; its stronger “no string witness for any `(d,x)`-objective under `I_s`” now follows from the main theorem (**mathematical proof**) |
| unmerged `uniform-strand-convention-search-2026-09-20.md` §3.2 single-strand S62 zeros | now explained by the main theorem rather than left as bounded evidence |
| molecule convention same-length witnesses at `(6,3)` and `(8,3)` | unchanged; the mechanism is reverse-complement collapse plus the per-vertex lower bound, both absent from the oriented convention |

The distinction is sharp and source-relevant: the negative result is robust under
oriented single-strand read types **only at the sequence level**, and is impossible
under the Section 6.2 spelled-circuit restriction. The integrated molecule
same-length witness is a cross-source panel (Shomorony’s placement-based `I_s`
plus MB09’s reverse-complement molecule read types), exactly as recorded in
[`../section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md)
§1.1 and in the unmerged `reverse-complement-strand-convention.md`.

**Boundary not addressed here.** If the candidate class is enlarged to all
circular words of length `G` (no Section 6.2 spelled-circuit restriction), the
sequence-level witness of §2 applies and the negative result survives. If
different-length candidates are allowed under Section 6.2, the present theorem
does not constrain them; the separated-length behavior is recorded elsewhere.

---

## 8. Epistemic classification

| claim | status |
|---|---|
| Shomorony (2016) theory is single-strand oriented, cyclic-shift only; reverse complement is preprocessing | **source fact** |
| MB09 §6.2 reads are molecule vertices, per-vertex lower bound `1`; a spelled candidate has support equality with the observation | **source fact + source-supported inference** |
| `AAATT → AAAAT` is a uniform oriented same-length sequence witness, exact ratio `2` | **verified computation**; base instance **kernel-checked** |
| Theorem A: every `(L-1)`-mer `≤ 2` ⇒ unique positive circulation of total `G` | **mathematical proof** |
| Lemma B, Lemma C: long triple repeats from primitive/periodic repetition | **mathematical proof** |
| Main theorem: `I_s` ⇒ unique positive circulation of total `G` | **mathematical proof** |
| Corollary: no same-length oriented Section 6.2 counterexample, any `G, L, Σ` | **mathematical proof** |
| Bounded exhaustive scans agree with all of the above | **verified computation (exact, exhaustive in scope)** |
| Which MB09 likelihood layer the 2016 sentence intends | **open** |
| Tie/uniqueness semantics and genome-equivalence choice | **open** (unchanged) |

---

## 9. Reproduce

```sh
python3 scripts/verify_uniform_oriented_rigidity.py          # quick
python3 scripts/verify_uniform_oriented_rigidity.py --full   # wider scopes
lake build AssemblyP1.FixedLengthExactCounterexample
```

Primary sources. Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C.
Tse, *Information-optimal genome assembly via sparse read-overlap graphs*,
*Bioinformatics* 32(17) (2016) i494–i502, §2–§5, DOI
`10.1093/bioinformatics/btw450`. Paul Medvedev, Michael Brudno, *Maximum
Likelihood Genome Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116, §3.1,
§4.1, §6.1–§6.2, Observation 7, PMC3154397. Guy Bresler, Ma’ayan Bresler, David
Tse, *Optimal assembly for high throughput shotgun sequencing*, *BMC
Bioinformatics* 14(Suppl 5):S18 (2013), DOI `10.1186/1471-2105-14-S5-S18`,
PMC3706340 (repeat/bridging definitions).

Cross-references (on `main` unless noted):
[`../bridging-source-semantics.md`](../bridging-source-semantics.md),
[`../section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md),
[`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md),
[`mb09-se61-index-orientation-resolution.md`](mb09-se61-index-orientation-resolution.md),
[`../fixed-length-exact-counterexample.md`](../fixed-length-exact-counterexample.md).
Unmerged branch artifacts referenced: `oriented-single-strand-se62-same-length-2026-09-20.md`,
`uniform-strand-convention-search-2026-09-20.md`, `reverse-complement-strand-convention.md`.
