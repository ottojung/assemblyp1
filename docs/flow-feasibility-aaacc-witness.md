# Section 6.2 flow feasibility of the AAACC/AAAAC fixed-length witness

_Status: reproducible finite certificate with exact-rational arithmetic and
exhaustive enumeration over the relevant flow space. This note resolves, for
the repository's Variant F, the explicit hedge in
`docs/fixed-length-binomial-counterexample.md` ("this note does **not** show
that `D` is feasible for the Section 6.2 ... flow problem"). It does not claim
settlement of the 2016 open question._

Primary source for the flow model:

- Paul Medvedev and Michael Brudno, "Maximum Likelihood Genome Assembly,"
  *Journal of Computational Biology* 16(8), 2009, 1101--1116.
  DOI: [10.1089/cmb.2009.0047](https://doi.org/10.1089/cmb.2009.0047);
  open full text: <https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/>,
  Sections 6.1--6.2.

Primary source for the truth/repeat/bridging hypotheses and the open question:

- Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, and David N. C. Tse,
  "Information-optimal genome assembly via sparse read-overlap graphs,"
  *Bioinformatics* 32(17), 2016, i494--i502.
  DOI: [10.1093/bioinformatics/btw450](https://doi.org/10.1093/bioinformatics/btw450).

Epistemic class: the finite flow calculations are a **computational
certificate** (exact rationals, reproducible by
`scripts/flow_feasibility_aaacc.py`); the supporting invariants below are a
**mathematical proof**.

## 1. Result

The fixed-length binomial counterexample **does transfer** to the
Medvedev--Brudno Section 6.2 overlap-graph flow candidate set:

- Truth `S = AAACC`, read length `L = 3`, realized starts `0, 1, 4`, observed
  reads `AAA, AAC, CAA` (each once). The hypothesis `I_s` holds.
- Competitor `D = AAAAC` (same length as the truth) is **flow-feasible**: its
  observed-read copy vector `(d_AAA, d_AAC, d_CAA) = (2, 1, 1)` is realized by
  the integer circulation
  `AAA --(overlap 2)--> AAA --(2)--> AAC --(1)--> CAA --(2)--> AAA`,
  which spells exactly `D`.
- Under the literal Section 6.2 vertex-cost objective (external length
  `N = 5`, observed counts `x = (1,1,1)`, `n = 3`) the competitor strictly
  beats the truth: ratio `9/8`.
- Under the full Section 6.1 product-of-binomials over all read types the
  competitor also strictly beats the truth: ratio `1125/512`.

The smallest same-length flow-feasible counterexample found is even smaller:
`S = AACC`, `L = 2`, starts `1, 3`, reads `AC, CA`, competitor `D = ACAC`,
with full-objective ratio `4096/729`. No same-length flow-feasible
counterexample exists at `G = 3` in the searched alphabet.

## 2. The Section 6.2 model used

Medvedev--Brudno Section 6.2:

> "The vertices of this graph are the reads, and the edges are all possible
> bidirected overlaps of length at least `omin` ... We then perform transitive
> edge reduction ... We define a convex min-cost biflow problem on this graph
> ... Each vertex has a lower bound of 1 since it represents a read that must
> be present in the genome at least once. All other lower bounds are 0 and all
> upper bounds are infinity ... Since any flow can be decomposed into a
> collection of walks, our flow represents a (non-contiguous) assembly of the
> genome, and the flow going through each vertex represents the number of time
> the read is present in the assembly."

The checks use this model with the following explicitly named decisions:

1. **Vertices are the distinct observed read types.** Duplicated reads collapse
   to one vertex with lower bound 1.
2. **Edges are all overlaps of length `1..L-1`** (i.e. `omin = 1`). The paper
   allows `omin` as a parameter. For the witness the threshold is
   load-bearing: with `omin = 2` the `AAC -> CAA` overlap of length 1 is
   dropped and **no** feasible circulation exists at all, so even the truth
   becomes flow-infeasible and the instance is ill-posed. `omin = 1` is
   therefore the only coherent threshold for this finite instance.
   **Self-overlaps (loops) are included**, because Section 3.2 of the paper
   explicitly allows loops in the multigraph. This is the decision that makes
   the witness work; see Section 5.
3. **Transitive reduction is not applied before the feasibility check.** The
   paper states that transitive reduction leaves the set of spelled molecules
   unchanged, so it cannot change copy-vector feasibility. The witness walk
   below uses only overlaps that survive it (see Section 3).
4. **`d_v` is the flow through vertex `v`** (inflow in a circulation).
5. **Objective.** Section 6.2 minimizes vertex costs `c_v(d_v)`. The Section
   6.1 binomial approximation gives, up to constants, the exact-rational
   likelihood `L_flow(d) = prod_v (d_v/N)^{x_v} (1 - d_v/N)^{n - x_v}` with
   external length `N`. The full product over all `k`-mers (including
   unobserved types) is checked separately.

## 3. The witness certificate

Truth windows of `S = AAACC` at the observed starts `0, 1, 4`:

- start `0` = `AAA`, start `1` = `AAC`, start `4` = `CAA`; coverage all five
  positions; the maximal length-1 `A` triple repeat at starts `0,1,2` is
  all-bridged (reads at `4,0,1`); there is no interleaved repeat pair.
  `satisfies_Is` returns true.

Overlap graph on `{AAA, AAC, CAA}` (loops included):

```text
AAA -> AAA (2)      AAA -> AAC (2)
AAC -> CAA (1)      CAA -> AAA (2)
```

plus additional overlaps of length 1 that the witness does not need.

Competitor `D = AAAAC` has circular 3-mer multiplicities
`AAA: 2, AAC: 1, ACA: 1, CAA: 1`. Projected onto the observed vertices this is
`d_D = (2, 1, 1)`. The circulation

```text
AAA --2--> AAA --2--> AAC --1--> CAA --2--> AAA
```

places reads at starts `0, 1, 2, 4` of `D`:

| read | start | window of `D` |
|------|-------|----------------|
| AAA  | 0     | `D[0..2]`      |
| AAA  | 1     | `D[1..3]`      |
| AAC  | 2     | `D[2..4]`      |
| CAA  | 4     | `D[4],D[0],D[1]` |

Every position is covered, consecutive reads overlap consistently, and the
closed walk spells exactly `D`. The observed read occurrences
`AAA: 2, AAC: 1, CAA: 1` equal the visit counts, so Observation 7 of the source
holds for the observed types.

Exact objective values:

| objective | truth | `D = AAAAC` | ratio |
|-----------|-------|-------------|-------|
| Section 6.2 vertex-cost `L_flow` | `4096/1953125` | `4608/1953125` | `9/8` |
| full Section 6.1 product of binomials | `16777216/30517578125` | `294912/244140625` | `1125/512` |

The relabelled repository instance `AAABB`/`AAAAB` gives identical ratios
(`9/8` and `1125/512`), confirming the certificate is invariant under the
symbol relabelling already used in `docs/fixed-length-binomial-counterexample.md`.

## 4. Smallest same-length flow-feasible counterexample

A bounded exhaustive search over circular truths `S` on a two-symbol alphabet
with `3 <= G <= 4`, all read lengths `2 <= L < G`, all covering start sets
satisfying `I_s`, all same-length circular competitors `D`, and all integer
flows with edge values at most 4, minimizing under the full Section 6.1
binomial objective, gives:

- `G = 3`: no same-length flow-feasible counterexample.
- `G = 4, L = 2`: truth `S = AACC` (starts `1, 3`, reads `AC, CA`), competitor
  `D = ACAC`. `D`'s copy vector `(d_AC, d_CA) = (2, 2)` is the doubled
  `AC -> CA -> AC` circulation. Full-objective ratio `4096/729`; vertex-only
  Section 6.2 ratio `16/9`.

The search is reproducible by `smallest_counterexample()` in the certificate
script and is not optimized for large `G`; it is completeness evidence only in
the stated finite range.

## 5. Modeling forks and limits of the result

These are the interpretation questions on which the result depends. They are
recorded here rather than silently resolved.

1. **Self-overlaps / loops.** The AAA self-loop is what makes `d_AAA = 2`
   compatible with conservation. If self-loops are excluded from the overlap
   graph, the circulation invariants become `d_AAC = d_CAA` and
   `d_AAA <= d_AAC`, so `D` is **not** flow-feasible. The source's Section 3.2
   explicitly permits loops, and the witness walk is consistent with
   Observation 7 (unlike a degenerate single-loop walk), so the loop-inclusive
   reading is the natural one. This is the single load-bearing modeling
   decision.
2. **Single-strand specialization.** The calculations use the error-free
   single-strand reads of the Shomorony exposition as the overlap-graph
   vertices. The literal 2009 graph is over double-stranded DNA molecules;
   Section 3.3 defines bidirected overlaps via the two strands, and Section 5.1
   monotonizes the bidirected flow. Whether the reverse-complement behaviour
   changes the copy-vector feasibility of `D` is **not** settled here; the
   reverse-complement strands form a structurally identical overlap family on
   the complementary alphabet, but the exact bidirected balance semantics
   remain a documented fork.
3. **Objective: vertices only vs all types.** The paper's graph has cost
   functions on the observed-read vertices, so Section 6.2 literally omits
   unobserved `k`-mers. The full Section 6.1 product includes them. The witness
   beats the truth under both, so the result is robust to this fork.
4. **Fixed external length `N`.** Both objectives use `N = G`, as the paper
   states for its experiments. The vertex-only Section 6.2 objective has no
   constraint `sum_v d_v = N`, so it also admits the tandem-doubled flow
   `(2,2,2)` with ratio `729/512`; the same read set is therefore an even
   stronger counterexample under the literal objective. The witness `D` itself
   is a genuine same-length genome, so the tandem remark is secondary.

## 6. Consequences for the repository

- The hedge in `docs/fixed-length-binomial-counterexample.md` is resolved in
  the direction of feasibility: the fixed-length binomial witness is not
  blocked by Section 6.2; the same `I_s`-satisfying instance already refutes
  the Section 6.2 flow objective.
- Variant F is therefore not an escape hatch from the repository's negative
  fixed-length results under the loop-inclusive reading. Under a no-loops
  reading, the specific competitor is blocked but the flow objective is still
  beaten by the tandem-doubled flow; either way the published
  "bridging implies ML" reading is not supported by these instances.
- The finite claim is arithmetic-only and could be kernel-checked by a small
  evaluator; the binding modelling choice (loops) should be fixed in any such
  formalization first, per the variant discipline in
  `docs/ml-formalization-contract.md`.

## 7. Reproduction

```sh
python3 scripts/flow_feasibility_aaacc.py
```

The script asserts every claim above and prints `ALL CHECKS PASSED`. It uses
`fractions.Fraction` throughout.
