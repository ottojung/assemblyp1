# MB09 §6.1 index set: is the literal `4^k` objective oriented, and does the PR #43 same-length witness survive?

_Status: independent primary-text + exact-computation resolution, 2026-09-20, for
issue #36. Written to resolve the orientation / reverse-complement indexing fork
recorded in [`section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md)
(PR #43) §1.1. Every claim is labelled **source fact**, **source-supported
inference**, **mathematical fact**, **verified computation**, **repository
fact**, or **open**. It does not select which MB09 layer the Shomorony et al.
(2016) sentence denotes, and does not touch the per-occurrence strengthening or
tie/equivalence semantics._

_Reproduce: `python3 scripts/verify_mb09_se61_index_orientation.py`
(self-contained, exact integer/`Fraction` arithmetic, deterministic, exits
non-zero on any failed assertion)._

---

## 0. Answer at a glance

1. **The literal `4^k` count is an oriented-`k`-mer count.** `4^k` is the size
   of the oriented length-`k` alphabet. The displayed multinomial (`M27`) and
   likelihood (`M28`) literally index the variables `X_1,…,X_{4^k}` and
   `d_1,…,d_{4^k}`. So the *only* way for the §6.1 formula to be internally
   consistent is for the indexed objects to be oriented `k`-mers, **not**
   `k`-molecules. [source fact + mathematical fact]

2. **The paper's model and its own §6.2 wiring are molecular, so the operative
   objective is indexed by observed DNA-molecule (reverse-complement) classes.**
   §6.2 says the graph vertices "are the reads, which are DNA molecules", one
   node per read, and that "the `d_i`'s described above actually correspond to
   the value of the flow through vertex `i`". A per-molecule vertex flow cannot
   carry two independent per-orientation values. The `4^k` count and the
   molecular vertices cannot both be literal; the model vocabulary, the paper's
   purpose, and the object actually optimized all select the molecule reading.
   [source fact + source-supported inference]

3. **Reverse-complement classes enter through the model definition, not through
   an extra quotient.** §1.1 (a read is a molecule, its strand is unknown),
   §3.1 (`k`-molecule = unordered reverse-complement pair), §4.1 ("each
   `k`-molecule is represented only once"), and decisively §6.2 (vertices are
   the reads as molecules; `d_i` = vertex flow) are the source of the collapse.
   No separate "identify `w` with `rc(w)`" step needs to be assumed. [source
   fact]

4. **The PR #43 same-length witness survives the source-faithful §6.2
   objective and inverts under the strict oriented objective.** Under molecule
   classes, `AAATAT → AAAAAT` has class support equality on both sides and
   strictly improves both objectives (`5` binomial, `3` same-length exact);
   under strict oriented indexing the competitor `AAAAAT` has no `TAT` window,
   so its oriented likelihood factor is `0` against an observed `TAT` read.
   [verified computation]

5. **What remains open is a different axis:** whether Shomorony et al. (2016)
   intend the §6.2 flow object at all. The index-set question *given §6.2* is
   resolved to molecule classes. [open, out of scope]

---

## 1. Primary source facts

Primary source: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* **16**(8) (2009) 1101–1116, DOI
[10.1089/cmb.2009.0047](https://doi.org/10.1089/cmb.2009.0047),
[PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/). The PDF
below is the published typeset article; its SHA-256 is recorded so the reading
is reproducible.

| Artifact | Locator | SHA-256 |
|---|---|---|
| Published article PDF (`pdftotext -layout` extraction used here) | cached `jcb09.pdf` | `bfeaec37de55e87c35438108c33a8052f0fd6eb56f2903bb1d50d2793d8a5aa3` |
| PMC HTML body (re-read independently this run) | `PMC3154397` | display equations `M26`–`M33` |

### 1.1 The model is double-stranded and molecular (source facts)

§1.1:

> "A read, on the other hand, is actually a DNA molecule—it consists of two
> strands that are reverse complements of each other. … [I]t is impossible to
> know from which of the two strands the sequence is read." … "Each read is
> represented by a single node, and each overlap (edge) has an orientation at
> both endpoints."

§3.1:

> "A **DNA molecule** is an unordered pair of strings (also called strands) that
> are reverse complements of each other. … A **`k`-molecule** is a DNA molecule
> whose corresponding strings have length `k`. The **`k`-molecule-spectrum** of
> a DNA molecule is the set of all `k`-molecules that are its submolecules."

§4.1:

> "Pevzner et al. (2001) attempt to do this by **including both of the `k`-mers
> associated with every `k`-molecule** in the de Bruijn graph. They then search
> for two 'complementary' walks … Instead, we show how to construct a bidirected
> de Bruijn graph, where **each `k`-molecule is represented only once**."

§6.2:

> "The first step is to build a bidirected overlap graph from the set of reads,
> **which are DNA molecules. The vertices of this graph are the reads** … Each
> vertex has a lower bound of `1` since it represents a read that must be
> present in the genome at least once. … By Observation 7, **the `d_i`'s
> described above actually correspond to the value of the flow through vertex
> `i`**, and we let `c_i` be the convex cost functions for the vertices."

§8.2:

> "[W]e compared the flow going through every vertex in the overlap graph to the
> number of times that **the corresponding read** appears in the original
> genome."

### 1.2 The §6.1 counting sentence in tension (source fact)

§6.1:

> "Let `D` be a circular genome of length `N(D)`, and let `d_i` denote the number
> of times the **`k`-molecule** `i` appears in `D`. … In each trial, a position
> is uniformly sampled from `D` and **the outcome of the trial is the
> `k`-molecule beginning at that position**. For a given `i`, the probability
> that the outcome of a single trial is `i` is simply `d_i/N(D)`. Let the random
> variable `X_i` denote the number of trials whose outcome is `i`. **There are
> `4^k` such variables** …"

The displayed equations (`M27`, `M28`; published PDF `p. 10`) index the
variables from `1` to `4^k`:

```text
P[X_1 = x_1, X_2 = x_2, … , and X_{4^k} = x_{4^k}]   (M27)
L[d_1, … , d_{4^k} | x_1, … , x_{4^k}]                (M28)
c_i(d_i) = −(x_i log d_i) − (n − x_i) log(N − d_i)     (M33)
```

Re-read directly from the published PDF this run: "There are 4 k such
variables"; `P[X1 ¼ x1, X2 ¼ x2, … , and X4k ¼ x4k ]`;
`L[d1, … , d4k jx1, … , x4k ]`. The `4^k` count is the **oriented** `k`-mer
alphabet size and is not the number of reverse-complement classes. [source fact]

---

## 2. The counting defect (mathematical fact)

Let `rc` be the reverse-complement involution on `Σ^k`, `|Σ| = 4`. The
`k`-molecule types are the orbits of `rc`; an orbit has size `1` for a
palindromic `k`-mer (`w = rc(w)`) and size `2` otherwise. The number of
palindromic `k`-mers is `p_k = 4^{k/2}` for even `k` and `p_k = 0` for odd `k`
(no base is its own complement). Hence

```text
#k-molecule classes = (4^k + p_k)/2,   p_k = 4^{k/2} (k even), 0 (k odd).
```

For `k = 1, 2, 3, 4, 5, 6` this is `2, 10, 32, 136, 512, 2080`, versus
`4, 16, 64, 256, 1024, 4096`. In particular the §6.1 sentence's `4^k` is
**not** the number of distinct `k`-**molecule** trial outcomes. [mathematical
fact, verified]

**Why the slip exists (source-supported inference).** §4.1 states that the
oriented-`k`-mer-doubling construction ("including both of the `k`-mers
associated with every `k`-molecule") is exactly the predecessor approach that
MB09 replaces with the bidirected, one-representative-per-molecule graph. The
`4^k` count is the natural count for that predecessor, single-strand/oriented
model. So the counting sentence is best read as a leftover from the oriented
formulation, while the paper's own model and §6.2 are molecular. This is a
reading, but it is supported by the paper's own contrast in §4.1.

---

## 3. Why the operative objective's index set is molecule classes

The chain is short and each link is a source fact:

1. §6.1 defines `d_i` as the count of `k`-molecule `i` in `D` and calls the
   trial outcome a `k`-molecule. [source fact]
2. §6.2 says the vertices of the optimized graph "are the reads, which are DNA
   molecules", one node per read (§1.1). [source fact]
3. §6.2 identifies "the `d_i`'s described above" with "the value of the flow
   through vertex `i`". [source fact]
4. Therefore the objective's index set is the graph's vertex set: observed read
   molecules, each represented once. Two sampled reads that are reverse
   complements are one vertex and one variable. [source-supported inference]

An oriented `4^k` index would require the vertices to be oriented `k`-mers, so
that a read and its reverse complement are two distinct vertices. That flatly
contradicts §1.1 ("impossible to know from which of the two strands the sequence
is read", "each read is represented by a single node"), §3.1 (a `k`-molecule is
a reverse-complement pair), §4.1 ("each `k`-molecule is represented only once"),
and §6.2's own vertex definition. There is no reading in which the `4^k` formula
and the molecular graph are simultaneously literal. [source fact +
mathematical fact]

**Consequence for candidate classes (separate axis, recorded for clarity).**
Because unobserved molecule classes have no vertex, a §6.2 flow assigns `d_i = 0`
there. This is consistent with §6.1's objective (the `x_i = 0` binomial terms
are minimized at `d_i = 0`) but it is the candidate-class restriction, not the
index-set fork. The witness below has class support equal to the observation
support on both sides, so it is unaffected. [source-supported inference]

---

## 4. The same-length witness `AAATAT → AAAAAT` under each reading

PR #43 witness data (`S = AAATAT`, `D = AAAAAT`, `L = 3`, `G = N = 6`, `n = 5`,
sampled starts `(0,0,1,3,5)`, `rc: A↔T`). Recomputed independently this run.

```text
S oriented windows : AAA, AAT, ATA, TAT, ATA, TAA
D oriented windows : AAA, AAA, AAA, AAT, ATA, TAA
observed reads     : AAA, AAA, AAT, TAT, TAA

class spectrum  d_S = { AAA:1, AAT:1, ATA:3, TAA:1 }   (sum 6)
class spectrum  d_D = { AAA:3, AAT:1, ATA:1, TAA:1 }   (sum 6)
observed counts x   = { AAA:2, AAT:1, ATA:1, TAA:1 }   (sum 5)
```

| reading | truth admissible? | competitor admissible? | objective ratio `L(D)/L(S)` |
|---|---|---|---|
| molecule classes + per-vertex lower bound `1` (§6.2-faithful) | yes (`TAT↦ATA`) | yes | §6.1 binomial `= 5`; same-length exact `= 3` |
| strict oriented `4^k` | no (`ATA` unobserved) | no (`TAT` unobserved) | competitor factor `0` (inverted) |

- Molecule reading: `supp(x) = supp(d_S) = supp(d_D) = {AAA, AAT, ATA, TAA}`.
  Both spelled molecules are §6.2-admissible (per-vertex lower bound `1`), and
  `D` strictly improves both objectives. The exact `§6.1` product of binomial
  marginals gives `5`; the same-length exact multinomial gives `3`. [verified
  computation; matches the kernel-checked `SameLengthSection62Counterexample`]
- Strict oriented reading: `S` has `d_S(TAT) = 1` while `D` has `d_D(TAT) = 0`,
  and the observation contains one `TAT` read; hence `D`'s oriented likelihood
  factor is `(0/N)^1 = 0`. The witness does not merely fail, it inverts.
  [verified computation]
- Non-symmetry of the one-strand oriented counts (why the two readings cannot be
  identified on this instance): `d_S(ATA) = 2`, `d_S(TAT) = 1`, while the class
  count is `d_S(ATA-class) = 3`. The correct relation is
  `d_w + d_{rc(w)} = d_class`; no symmetry is forced. [mathematical fact,
  verified]

**Determination.** Under the source-faithful §6.2 object — read-molecule
vertices, §6.1 separable binomial costs, per-vertex lower bound `1` — the PR #43
same-length witness survives and strictly beats the truth. It does not survive a
strict oriented `4^k` index, but that index contradicts §6.2's own graph. [source
fact + verified computation]

---

## 5. Relation to PR #43 and to unmerged branch notes

- PR #43 (`docs/section62-same-length-bidirected-counterexample.md` §1.1)
  already records the tension and explicitly calls the oriented reading "a
  separate, unresolved source fork"; its single-strand control row records the
  bounded zero. This note supplies the primary-text determination the PR left
  open: the fork is resolved in favour of the molecule-class index *given §6.2*,
  and the witness survives. [repository fact + source fact]
- Unmerged branch `analysis/se62-revcomp-index-decision-0920` (commit `7bb1f3a`)
  reaches the same decision. Its supporting arguments were corrected on
  `audit/mb09-likelihood-index-2026-09-20` (commit `7164db6`, §7): the
  symmetry premise `d_w = d_{rc(w)}` and the "must enforce `d_w = d_{rc(w)}`"
  step are not the operative bridge; the §6.2 **vertex/index identification** is.
  This note independently confirms that correction: `d_S(ATA) = 2`,
  `d_S(TAT) = 1` is a concrete counterexample to the symmetry premise, and the
  load-bearing fact is source link §6.2 `d_i` = vertex flow. [repository fact +
  mathematical fact]
- Nothing here contradicts the bounded-search rows of PR #43: the single-strand
  and per-occurrence controls remove the mechanism and find no beat; that is
  consistent with the mechanism being reverse-complement collapse plus the
  per-vertex (not per-occurrence) lower bound. [repository fact]

---

## 6. Epistemic classification

| Claim | Status |
|---|---|
| §6.1 trial outcome and `d_i` are `k`-molecules; "There are `4^k` such variables"; `M27`/`M28` index `1..4^k` | **source fact** |
| §1.1/§3.1/§4.1: reads are DNA molecules; one node per read; each `k`-molecule represented once; oriented doubling is the predecessor approach | **source fact** |
| §6.2: vertices are the reads (molecules); `d_i` = vertex flow; per-vertex lower bound `1`; Observation 7; §8.2 flow = read copy count | **source fact** |
| `(4^k + p_k)/2` `k`-molecule classes (`32` at `k=3`, `136` at `k=4`) | **mathematical fact**, verified |
| The literal `4^k` count is the oriented alphabet size, not the class count | **source fact + mathematical fact** |
| §6.1 `4^k` and §6.2 molecular vertices cannot both be literal | **source-supported inference** |
| Given §6.2, the objective index set is observed molecule (reverse-complement) classes | **source-supported inference** |
| Witness class support equality for `S` and `D`; ratios binomial `5`, same-length exact `3` | **verified computation**; matches kernel-checked certificate |
| Strict oriented reading inverts the witness (`D` oriented likelihood `0`) | **verified computation** |
| Prior symmetry premise `d_w = d_{rc(w)}` is false (`d_S(ATA)=2`, `d_S(TAT)=1`) | **mathematical fact**, verified |
| Which MB09 layer the 2016 sentence denotes; per-occurrence strengthening; tie semantics | **open** |

---

## 7. Reproduce

```sh
python3 scripts/verify_mb09_se61_index_orientation.py
```

The script counts `k`-molecule classes against `(4^k + p_k)/2` for `k ≤ 6`,
recomputes the `AAATAT → AAAAAT` windows, class and oriented spectra, observed
counts, class-support equality, the strict-oriented `TAT` failure, the
non-symmetry `d_S(ATA)=2, d_S(TAT)=1`, and the two exact objective ratios `5`
and `3`. It shares no code with the repository's searches.

Primary source: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* **16**(8) (2009) 1101–1116, §1.1, §3.1, §4.1,
§6.1–§6.2, §8.2, PMC3154397.

Cross-references (on `main` unless noted):
[`../section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md),
[`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md),
[`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md).
Unmerged branch artifacts referenced: `docs/source-notes/se62-revcomp-index-decision.md`
(`analysis/se62-revcomp-index-decision-0920`, `7bb1f3a`),
`docs/source-notes/mb09-se62-likelihood-index-adversarial-audit.md`
(`audit/mb09-likelihood-index-2026-09-20`, `7164db6`).
