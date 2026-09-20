# Adversarial audit: the Medvedev–Brudno likelihood index set (§6.1 `4^k` vs §6.2 DNA-molecule vertices) and the `AAATAT → AAAAAT` witness

_Status: independent primary-text + exact-computation audit, 2026-09-20, written
for issue #36. Every claim is labelled **source fact** (quoted or paraphrased
from the primary text), **source-supported inference**, **mathematical fact**,
**verified computation**, **repository fact**, or **open**._

_Scope. This note examines only the tension recorded in
[`../section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md):
§6.1 literally writes `4^k` variables / oriented `k`-mers, while §6.2 uses
DNA-molecule (reverse-complement-class) vertices. It determines which indexing
the objective actually optimizes and re-checks the `AAATAT → AAAAAT` witness
under the most faithful combined reading. It does **not** work on the
per-occurrence (`d ≥ x`) strengthening, does not select the 2016 referent, and
does not settle tie/equivalence semantics._

_Reproduce:
`python3 scripts/verify_mb09_likelihood_index.py` (self-contained, exact
`Fraction`/integer arithmetic, deterministic, exits non-zero on any failed
assertion)._

---

## 0. Verdict at a glance

1. **The optimized §6.2 objective is indexed by observed DNA-molecule classes,
   not by independent oriented `k`-mers.** §6.2 identifies §6.1's `d_i` with
   "the value of the flow through vertex `i`", and its vertices "are the reads,
   which are DNA molecules" (each read/molecule one vertex). A flow variable per
   molecule vertex cannot carry two independent per-orientation values, and
   there are at most `n` observed read vertices — never `4^k`. [source fact +
   source-supported inference]

2. **§6.1's literal "There are `4^k` such variables" is a genuine
   source-internal inconsistency.** The count of `k`-molecule classes is
   `(4^k + p_k)/2` (`p_k = 4^{k/2}` for even `k`, `0` for odd `k`): `32`, not
   `64`, for `k = 3`. The paper's own vocabulary is molecule-first (§3.1
   defines `k`-molecule and distinguishes it from `k`-mer; §4.1 "each
   `k`-molecule is represented only once"; §1.1 "Each read is represented by a
   single node"). The `4^k` sentence and the `M27`/`M28` formula indices are the
   inconsistent half. [source fact + mathematical fact, verified]

3. **The two halves cannot both be read literally.** If the §6.2 graph vertices
   are molecules and `d_i` is the flow through vertex `i`, the §6.1 index set is
   forced to the vertex set. The coherent resolutions are (i) molecule-class
   indexing with a `4^k` counting slip, or (ii) an oriented graph — which
   contradicts §1.1, §3.1, §4.1, and §6.2's own definition of the vertices. The
   source vocabulary and the actually-optimized object select (i). [source
   fact + source-supported inference]

4. **The `AAATAT → AAAAAT` witness remains valid under the most faithful
   combined reading** (molecule-class vertices + §6.1 separable binomial +
   per-vertex lower bound `1`): class support equality holds for both the truth
   and the competitor, and the objective ratios are exactly `5` (binomial) and
   `3` (same-length exact multinomial). [verified computation; matches the
   kernel-checked certificate on `main`]

5. **Under a strictly oriented reading the witness does not merely fail, it
   inverts.** The truth has `d_S(TAT) = 1`, so the truth can explain the
   observed `TAT` read; the competitor `AAAAAT` has no `TAT` window at all, so
   its oriented likelihood is `0`. [verified computation]

6. **Correction to a prior unmerged decision note.** The note
   `docs/source-notes/se62-revcomp-index-decision.md` on branch
   `analysis/se62-revcomp-index-decision-0920` (commit `7bb1f3a`) reaches the
   same conclusion, but two of its supporting claims should not be relied on:
   its "oriented and aggregated objectives agree on double-stranded candidates"
   argument is not the operative reason and is false under the paper's
   one-strand length convention; and its statement that independent oriented
   variables "must enforce `d_w = d_{rc(w)}`" is not correct (independent
   oriented variables satisfy `d_w + d_{rc(w)} = d_class` and need not be
   symmetric). The load-bearing reason is the vertex/index identification of
   §6.2 alone. See §7. [mathematical fact]

---

## 1. Primary artifacts and precise citations

Primary source: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* **16**(8) (2009) 1101–1116,
DOI [10.1089/cmb.2009.0047](https://doi.org/10.1089/cmb.2009.0047),
[PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/).

| Artifact read for this audit | Locator | SHA-256 |
|---|---|---|
| Published article PDF (typeset, `pdftotext -layout`) | cached `jcb09.pdf` | `bfeaec37de55e87c35438108c33a8052f0fd6eb56f2903bb1d50d2793d8a5aa3` |
| PMC HTML body (re-read this run) | `PMC3154397` | HTML body + display equations `M26`–`M33` |

The PDF hash is byte-identical to the artifact independently used in the
unmerged branch artifact `docs/source-notes/mb09-se62-relations-independent-audit-2026-09-20.md`
§1 (branch `audit/mb09-se62-relations-2026-09-20`). Citations below give
section and, where useful, the equation image labels `M26`–`M33` used by the
PMC HTML. [verified computation]

### 1.1 The two source facts that are in tension

**(§6.1, molecule vocabulary and outcome, source fact.)**

> "Let `D` be a circular genome of length `N(D)`, and let `d_i` denote the
> number of times the `k`-molecule `i` appears in `D`. Probabilistically, the
> dataset of `n` reads corresponds to a set of outcomes from `n` independent
> trials. In each trial, a position is uniformly sampled from `D` and **the
> outcome of the trial is the `k`-molecule beginning at that position**. For a
> given `i`, the probability that the outcome of a single trial is `i` is
> simply `d_i/N(D)`. Let the random variable `X_i` denote the number of trials
> whose outcome is `i`. **There are `4^k` such variables**, and when considered
> independently of each other, they each follow the binomial distribution."

The displayed joint distribution (`M27`) and likelihood (`M28`) index the
variables literally from `1` to `4^k`:

```text
P[X_1 = x_1, X_2 = x_2, ... , and X_{4^k} = x_{4^k}] = (n! / ∏ x_i!) ∏_i (d_i/N(D))^{x_i}
L[d_1, ..., d_{4^k} | x_1, ..., x_{4^k}]          = (n! / ∏ x_i!) ∏_i (d_i/N(D))^{x_i}
```

**(§6.2, molecular vertices and the `d_i ↔` vertex-flow identification, source
fact.)**

> "The first step is to build a bidirected overlap graph from the set of reads,
> **which are DNA molecules. The vertices of this graph are the reads** … Each
> vertex has a lower bound of `1` since it represents a read that must be
> present in the genome at least once. … By **Observation 7**, **the `d_i`'s
> described above actually correspond to the value of the flow through vertex
> `i`**, and we let `c_i` be the convex cost functions for the vertices."

**(§3.1, what a molecule is, source fact.)**

> "A **DNA molecule** is an unordered pair of strings (also called strands) that
> are reverse complements of each other. … A **`k`-molecule** is a DNA molecule
> whose corresponding strings have length `k`. The **`k`-molecule-spectrum** of
> a DNA molecule is the set of all `k`-molecules that are its submolecules."

**(§4.1, one vertex per molecule, source fact.)**

> "we show how to construct a bidirected de Bruijn graph, where **each
> `k`-molecule is represented only once**."

**(§1.1, one node per read molecule, source fact.)**

> "Each read is represented by a single node, and each overlap (edge) has an
> orientation at both endpoints."

**(§8.2, vertices are read types, source fact.)**

> "we compared the flow going through every vertex in the overlap graph to the
> number of times that **the corresponding read** appears in the original
> genome."

---

## 2. The literal reading has a counting defect

Let `Σ` be the DNA alphabet (`|Σ| = 4`) and `rc` the reverse-complement
involution on `Σ^k`. The `k`-molecule types are the orbits of `rc`, which have
size `1` (palindromic, `w = rc(w)`) or `2`. The number of palindromic `k`-mers
is `p_k = 4^{k/2}` for even `k` and `p_k = 0` for odd `k` (no base equals its
own complement). Hence

```text
#k-molecule classes = (4^k + p_k)/2,   p_k = 4^{k/2} (k even), 0 (k odd).
```

For `k = 3`: `(64 + 0)/2 = 32`, not `64`. For `k = 4`: `(256 + 16)/2 = 136`,
not `256`. So "There are `4^k` such variables" is not the number of distinct
`k`-**molecule** trial outcomes; `4^k` is the size of the ambient oriented
`k`-mer alphabet. [mathematical fact, verified for `k ≤ 6`]

Since §6.1 twice uses the phrase "the `k`-molecule" for the outcome and the
`d_i`, and the paper separates `k`-mer from `k`-molecule throughout §3.1, the
counting sentence and the `1..4^k` formula indices are the inconsistent half.
[source fact + source-supported inference]

---

## 3. Adversarial case for the oriented `4^k` indexing (steelman)

The strongest argument for taking `4^k` at face value is textual and should be
stated before it is rejected:

1. **It is repeated, not a one-off typo.** The number appears in the prose and
   the displayed multinomial (`M27`) and likelihood (`M28`) run `X_1, …,
   X_{4^k}` and `d_1, …, d_{4^k}`. A careless slip would be less systematic.
2. **It makes the binomial independence sentence literal.** "when considered
   independently of each other, they each follow the binomial distribution" is
   naturally read as one binomial per oriented `k`-mer.
3. **The separable cost `c_i(d_i) = −x_i log d_i − (n − x_i) log(N − d_i)`
   (§6.1, `M33`) is indexed by `i`.** If `i` is a molecule class, the
   approximation's per-variable bookkeeping is over classes; if oriented, over
   `4^k`.
4. **`4^k` is exact and natural; a molecule-class count is not.** A careful
   paper might prefer the exact `4^k`.

An advocate of this reading would conclude that the §6.1 objective is over
oriented `k`-mers and that "`k`-molecule" in §6.1 is loose wording.

---

## 4. Why the oriented reading does not survive §6.2

The steelman fails at the point where §6.1 is wired to §6.2:

- §6.1's `d_i` are declared identical to "the value of the flow through vertex
  `i`" (§6.2). [source fact]
- §6.2's vertices "are the reads, which are DNA molecules" and are built "from
  the **set** of reads", with each read a single node (§1.1) and each
  `k`-molecule represented once (§4.1). [source fact]
- Therefore the index set that §6.2 actually sums over is the set of observed
  read **molecules** — at most `n` of them, and in practice many fewer once
  reverse-complement and duplicate reads are collapsed. It is not `4^k`, and it
  is not the oriented `k`-mer alphabet. [source-supported inference]

If one insists on oriented `k`-mer types, then the vertices of a `4^k`-variable
graph would be oriented `k`-mers, not reads/molecules; two sampled reads that
are reverse complements would be distinct vertices, contradicting §1.1
("impossible to know from which of the two strands the sequence is read"), §4.1
("each `k`-molecule is represented only once"), and §6.2's construction from
the read set. [source fact + source-supported inference]

There is no third option in which the `4^k` objective and the molecular graph
are simultaneously literal: the `d_i` are the vertex flows, so the objective's
index set is exactly the vertex set. Either the index set is the observed
molecule classes (and `4^k` is a slip), or the graph is oriented (and §1.1,
§3.1, §4.1, §6.2 are contradicted). The model vocabulary, the reason the paper
exists (double-strandedness), and the object actually optimized all select the
first. [source-supported inference]

**Separate axis, recorded for completeness.** Even under the molecule reading,
§6.2 restricts the candidate spectrum to the observed read vertices (unobserved
molecule classes have no vertex, hence `d_i = 0`), whereas §6.1's all-types sum
allows any circular `D`. That is the candidate-class restriction (reading 3 in
[`ml-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md)),
not the index-set fork. It is not needed for the conclusion here.

---

## 5. The `AAATAT → AAAAAT` witness under the faithful combined reading

Independent recomputation (`scripts/verify_mb09_likelihood_index.py`), exact
`Fraction` arithmetic, sharing no code with the repository searches:

```text
alphabet {A, T};  rc: A <-> T;  L = 3;  N = |S| = 6;  n = 5
read starts (0, 0, 1, 3, 5) on circular S = AAATAT
oriented windows S  : AAA, AAT, ATA, TAT, ATA, TAA
oriented windows D  : AAA, AAA, AAA, AAT, ATA, TAA
observed reads      : AAA, AAA, AAT, TAT, TAA
molecule classes    : cls(w) = min(w, rc(w)), so TAT <-> ATA

truth  class spectrum d_S = { AAA:1, AAT:1, ATA:3, TAA:1 }   (sum 6)
comp.  class spectrum d_D = { AAA:3, AAT:1, ATA:1, TAA:1 }   (sum 6)
observed class counts x   = { AAA:2, AAT:1, ATA:1, TAA:1 }   (sum 5)
```

- **Class support equality holds for both**: `supp(x) = supp(d_S) = supp(d_D)
  = {AAA, AAT, ATA, TAA}`. Under the per-vertex lower bound `1`, both spelled
  molecules are §6.2-admissible candidates. [verified computation]
- **Oriented support fails for both**: the truth and competitor spectra contain
  `ATA`, which is unobserved (`x_ATA = 0`); the observed oriented read is
  `TAT`. `supp(d_S) \ supp(x) = supp(d_D) \ supp(x) = {ATA}`. [verified
  computation]
- **Objective ratios** (candidate-dependent parts; `D` is the competitor):
  the §6.1 fixed-`N` product of binomials gives `L(D)/L(S) = 5`; the
  same-length exact multinomial gives `L(D)/L(S) = 3`. Both strictly exceed
  `1`. [verified computation; matches
  `../section62-same-length-bidirected-counterexample.md` §0 and the
  kernel-checked `SameLengthSection62Counterexample`]

### 5.1 The strict-oriented reading inverts the witness

Under a strictly oriented index set the competitor `AAAAAT` has no `TAT`
window (`d_D(TAT) = 0`) while the observation includes one `TAT` read
(`x_TAT = 1`), so its oriented likelihood factor is `(0/N)^1 = 0`. The truth
`AAATAT` does have `d_S(TAT) = 1`. Hence the strict oriented reading not only
removes the witness, it makes the truth beat the competitor for this
observation. [verified computation]

### 5.2 Why this does not save the oriented reading

The inversion does not show that MB09 intends oriented types; it only shows
that the two readings are genuinely different on this instance. The reading
that §6.2 forces (§4) is the molecule one, and under it the witness stands.

---

## 6. Residual ambiguity

The following remain open and are not decided here:

1. **Whether the 2016 sentence denotes §6.2 at all.** Shomorony et al. (2016)
   are single-strand and cyclic-shift-only, and name Medvedev–Brudno only by
   bibliography; the referent could be the §6.1 exact multinomial rather than
   the §6.2 flow. That is a separate cross-source question
   (`mb-formulation-referent-reconciliation.md`,
   `shomorony-mb-formulation-provenance.md`). [open]
2. **Per-occurrence strengthening** (`d ≥ x`), explicitly out of scope here.
   [open]
3. **Tie/equivalence semantics** and the publisher supplement. [open]

The index-set question itself — *given §6.2 as the object, what does the
objective sum over* — is resolved to the molecule classes.

---

## 7. Correction to the prior decision note

The unmerged note `docs/source-notes/se62-revcomp-index-decision.md` (branch
`analysis/se62-revcomp-index-decision-0920`, commit `7bb1f3a`) reaches the same
decision and states the correct conclusion ("For the Section 6.2 objective,
aggregate reverse-complement classes"). Two supporting claims in it are
imprecise and should be replaced by §4 above. [repository fact + mathematical
fact]

1. **Its §3 "agreement on double-stranded genomes" is not the operative
   bridge, and its symmetry premise is false under the source's length
   convention.** It claims a genuinely double-stranded candidate has
   orientation-symmetric oriented counts `d_w = d_{rc(w)}`, so the oriented and
   aggregated objectives agree. But §6.1's constraint `N(D) = Σ_i d_i` (`M30`)
   and §4.1's length `k + l` count occurrences on **one** strand; a generic
   double-stranded candidate's one-strand oriented counts are not symmetric.
   On this witness `d_S(ATA) = 2` and `d_S(TAT) = 1`, while the class count is
   `d_S(ATA-class) = 3`. The correct relation is `d_w + d_{rc(w)} = d_class`,
   with no symmetry required. [mathematical fact, verified]
2. **Its §4 claim that independent oriented variables "must enforce
   `d_w = d_{rc(w)}`" is not correct.** Independent oriented variables are
   simply not representable by §6.2: the `d_i` *are* the vertex flows, and the
   vertices are molecules. The obstruction is the vertex/index identification,
   not an orientation-symmetry requirement. [source fact + mathematical fact]

Consequently, the "oriented" column of that note's witness table should be
read as an **oriented-vertex model** (an unfaithful variant that contradicts
§1.1/§3.1/§4.1/§6.2), not as "the `4^k` objective applied to the MB09 graph."
Under an oriented objective on molecular vertices the combined model is
underdetermined (the class flow does not determine `d_w` and `d_{rc(w)}`
separately), so there is no coherent "oriented objective + faithful graph"
alternative to test. [source-supported inference]

These corrections do not change that note's decision or its witness table's
bottom line; they change *why* the decision holds.

---

## 8. Epistemic classification

| Claim | Status |
|---|---|
| §6.1 outcome and `d_i` are `k`-molecules; §6.1 writes "There are `4^k` such variables"; `M27`/`M28` index `1..4^k` | **source fact** |
| §3.1/§4.1/§1.1: reads are DNA molecules, one node per read, each molecule once | **source fact** |
| §6.2 vertices are the reads (molecules); `d_i` = vertex flow; per-vertex lower bound `1`; observation 7 | **source fact** |
| `(4^k + p_k)/2` molecule classes; `32` at `k = 3`, `136` at `k = 4` | **mathematical fact**, verified |
| §6.2's objective index set equals its vertex set = observed molecule classes | **source-supported inference** (forced) |
| §6.1 `4^k` and §6.2 molecular vertices cannot both be literal | **source-supported inference** |
| Witness: class support equality for S and D | **verified computation** |
| Witness: oriented support fails on `ATA` for S and D | **verified computation** |
| Witness ratios: binomial `5`, same-length exact `3` | **verified computation**, matches kernel-checked `main` certificate |
| Strict oriented reading inverts the witness (competitor likelihood `0`) | **verified computation** |
| Prior note's symmetry/`d_w=d_{rc(w)}` reasoning is not the operative bridge | **mathematical fact** |
| 2016 referent, per-occurrence strengthening, tie semantics | **open** |

---

## 9. Reproduce

```sh
python3 scripts/verify_mb09_likelihood_index.py
```

The script counts molecule classes against `(4^k + p_k)/2` for `k ≤ 6`,
recomputes the witness windows, class and oriented spectra, observed counts,
class-support equality, and the two exact objective ratios, and exhibits the
non-symmetry `d_S(ATA) = 2`, `d_S(TAT) = 1`. It shares no code with the
repository's searches.

Primary source: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* **16**(8) (2009) 1101–1116, §1.1, §3.1, §3.4,
§4.1, §6.1–§6.2, §8.2, PMC3154397.

Cross-references (on `main` unless noted):
[`../section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md),
[`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md),
[`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md).
Unmerged branch artifacts referenced:
`docs/source-notes/se62-revcomp-index-decision.md`
(branch `analysis/se62-revcomp-index-decision-0920`, commit `7bb1f3a`),
`docs/source-notes/reverse-complement-strand-convention.md`
(branch `audit/mb09-se62-relations-2026-09-20`),
`docs/source-notes/mb09-se62-relations-independent-audit-2026-09-20.md`
(branch `audit/mb09-se62-relations-2026-09-20`).
