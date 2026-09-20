# The AAACC / AAAAC witness under the actual Medvedev–Brudno §6.2 flow formulation

_Status: primary-source reading + exact-rational computation, 2026-09-19. Not a
Lean result. Every claim is classified as **source fact**, **source-supported
inference**, **verified computation**, or **open**. This note does not settle the
source-ambiguous Shomorony et al. open question; it resolves what the §6.2 object
does and does not contain for this specific witness._

_Reproduction: `python3 scripts/section62_aaacc_witness.py` (all assertions pass;
exact `Fraction` arithmetic)._

---

## 0. Answer at a glance

1. The witness is the issue #31 / #32 instance (DNA relabeled `B → C`):
   truth `S = AAACC` (`G = 5`), competitor `D = AAAAC` (length 5), read length
   `k = L = 3`, `n = 3` reads, realized starts `0, 1, 4`, so the observed
   read types are `{AAA:1, AAC:1, CAA:1}`; fixed external `N = 5`.

2. **The observed reads are trivially §6.2-feasible**: they are exactly the
   vertex set of the read-overlap graph. The count vector `(AAA:1, AAC:1, CAA:1)`
   is realizable by the single open walk `CAA → AAA → AAC`.

3. **The source I_s hypothesis holds** for the realized starts (coverage; the
   unique maximal triple repeat `A@(0,1,2)` is all-bridged; there is no
   interleaved pair), so this is a genuine bridging instance.

4. **Neither the truth genome `S` nor the competitor genome `D` is a §6.2
   spelled molecule.** `S` has unobserved 3-mers `ACC`, `CCA`; `D` has the
   unobserved 3-mer `ACA`. The §6.2 graph has vertices *only for observed
   reads*, and by Observation 7 a walk's read visits are exactly the
   submolecules of the spelled molecule, so a spelled genome must be
   support-contained in the observed read types. Both fail. Under a strict
   "single circular genome = circuit" reading the feasible set is empty here.

5. **The competitor's observable projection is §6.2-feasible, and it still
   beats the truth counts.** The count vector `(AAA:2, AAC:1, CAA:1)` — the
   projection of `AAAAC` onto the observed read vertices — is realized by the
   *single* open walk `CAA → AAA → AAA → AAC`. Under the §6.1 separable
   binomial cost that §6.2 uses, it strictly beats the truth-induced counts
   `(1,1,1)` by `9/8`. Using both the self-loop and the two non-revisitable
   reads, the unreconstrained per-type optimum is `(2,2,2)`, with ratio
   `(9/8)^3 = 729/512`. **The witness therefore changes (indeed refutes) the ML
   ordering under §6.2; §6.2 does not restore truth-optimality for this
   instance.**

6. **Correction to a repository search artifact.** The support-contained and
   per-occurrence columns of `scripts/support_feasibility_search.py` (and the
   frontier table in `docs/read-tiled-counterexample.md` §4) restrict candidates
   to *fixed-length `G` circular genomes*. That is not the §6.2 candidate
   object, which is a flow / non-contiguous assembly over read-vertex counts
   with vertices only at observed reads and no upper bounds. The statement "SC
   eliminates all I_s counterexamples at `G ≤ 6`" is therefore a statement
   about a stricter, fixed-length, circular candidate class, not about §6.2.
   The `AAACC` instance at `G = 5` is a §6.2 counterexample despite having
   `0` fixed-length support-contained counterexamples.

---

## 1. What the primary source actually says about §6.2

Primary source: Paul Medvedev and Michael Brudno, "Maximum Likelihood Genome
Assembly," *J. Comput. Biol.* 16(8) (2009) 1101–1116, doi:10.1089/cmb.2009.0047,
open text PMC3154397, §6.2 "Putting it all together."

**Source facts** (direct quotations):

- "The first step is to build a bidirected overlap graph from the set of reads,
  which are DNA molecules. **The vertices of this graph are the reads**, and the
  edges are all possible bidirected overlaps of length at least `o_min` … we
  refer to the resulting graph as the transitively reduced bidirected overlap
  graph."
- Observation 7: "Let `r` be a read and `W` a walk in the transitively reduced
  bidirected overlap graph. **The number of times `W` visits `r` is equal to the
  number of times `r` appears a submolecule of the molecule spelled by `W`.**"
- "In this graph, the original double-stranded genome corresponds to a circuit
  (assuming high enough coverage)."
- "Each vertex has a lower bound of 1 since it represents a read that must be
  present in the genome at least once. **All other lower bounds are 0 and all
  upper bounds are infinity.**"
- "By Observation 7, the `d_i`'s described above actually correspond to the
  value of the flow through vertex `i`, and we let `c_i` be the convex cost
  functions for the vertices."
- "Since any flow can be decomposed into a collection of walks, **our flow
  represents a (non-contiguous) assembly of the genome**, and the flow going
  through each vertex represents the number of time the read is present in the
  assembly."

The `c_i` are the §6.1 separable binomial costs
`c_i(d_i) = -(x_i log d_i) - (n - x_i) log(N - d_i)`, i.e. the objective is the
literal product of binomial marginals with fixed external `N` and includes the
`(1 - d_i/N)^{n - x_i}` zero-observation factors (see
`docs/audit-binomial-marginals-issue32.md`).

### 1.1 Source-supported inferences

- **(I1) Support containment.** Because the vertices are *only the observed
  reads*, and (by Observation 7) a walk's visits are exactly the read
  submolecules of the spelled molecule, any molecule spelled by a §6.2 flow has
  its `L`-molecule support contained in the set of observed read types.
  (Formally this is cleanest when overlaps have length `L − 1`; for this
  instance every nonzero overlap does, see §2.2.)
- **(I2) Vertex counts are not pinned to the sample counts.** The lower bound is
  `1` per read *vertex* (read type), not `x_i` per observed occurrence, and all
  upper bounds are infinite. Hence a flow may visit a read type more often than
  it was observed.
- **(I3) The candidate object is an assembly, not a genome.** The paper
  explicitly allows a non-contiguous assembly (a collection of contigs). A
  single circular genome is represented only through a circuit, which exists
  only at sufficiently high coverage.
- **(I4) Source/sink penalty.** A supersource/supersink is added with
  "prohibitively large costs … so that their usage is minimized," so count
  vectors requiring more open contigs are disfavored. The conclusion in §3 below
  is robust to this: the winning competitor uses a single open contig.

---

## 2. The witness

```
truth        S = A A A C C        (G = 5)
competitor   D = A A A A C        (|D| = 5)
read length  L = 3,  n = 3 reads
realized starts  0, 1, 4
observed types   { AAA:1, AAC:1, CAA:1 }
external N = 5
```

### 2.1 Spectra and observed support

```
spec(S) = { AAA:1, AAC:1, ACC:1, CCA:1, CAA:1 }
spec(D) = { AAA:2, AAC:1, ACA:1, CAA:1 }
supp(x) = { AAA, AAC, CAA }
```

### 2.2 Read-overlap graph (single strand, overlaps of length `L − 1 = 2`)

```
AAA → AAA   (self-loop)
AAA → AAC
CAA → AAA
CAA → AAC
```

`AAC` has no outgoing edge, `CAA` has no incoming edge, and no edge has an
overlap shorter than 2. Consequently:

- no nonempty circuit visits all three read types (the truth's genome circuit
  does not exist at this coverage);
- `CAA` is non-revisitable and `AAC` is terminal, so within one open contig
  `d_CAA = d_AAC = 1`, while the `AAA` self-loop makes `d_AAA` arbitrary.

### 2.3 Support containment

- `S` requires vertices `ACC`, `CCA`, which are not observed reads.
- `D` requires vertex `ACA`, which is not an observed read.

Hence, by (I1), neither `S` nor `D` is spellable by any §6.2 walk, i.e. neither
is flow-feasible as a molecule. Under the strict "single circular genome"
reading `F_flow(R) = ∅`, so the ML question is vacuous for this instance.

### 2.4 Flow-feasible count vectors

Explicit valid overlap walks (verified in the script):

| count vector | walk(s) | open contigs |
|---|---|---|
| `(AAA:1, AAC:1, CAA:1)` | `CAA → AAA → AAC` | 1 |
| `(AAA:2, AAC:1, CAA:1)` | `CAA → AAA → AAA → AAC` | 1 |
| `(AAA:2, AAC:2, CAA:2)` | `CAA → AAA → AAC` twice | 2 |

The middle row is exactly the observable projection of the competitor genome
`AAAAC`; it is feasible with the *minimum possible* number of open contigs
(one), so by (I4) it is not penalized relative to the truth.

The observed read multiset `{AAA, AAC, CAA}` is **not** Eulerian-realizable
(the `(L−1)`-mer balance has `AC` and `CA` nonzero), so there is no read-tiled
or per-occurrence circular genome at all for this sample.

---

## 3. The §6.2 objective and the ML ordering

§6.2 assigns each read vertex `w` the §6.1 binomial cost with observed count
`x_w` and fixed external `N`. Unobserved types have no vertex (`d = 0`, factor
`1`). For this witness `x_w = 1`, `n = 3`, `N = 5`, so the per-vertex factor is
`3 · d · (5 − d)^2 / 5^3`, maximized at `d = 2` (`d = 0` or `5` gives factor 0).

Exact values (script):

```
L62(1,1,1) = 110592 / 1953125
L62(2,1,1) = 124416 / 1953125     ratio to truth = 9/8      = 1.125
L62(2,2,2) = 157464 / 1953125     ratio to truth = 729/512  ~= 1.4238
```

- If the source/sink penalty dominates, the best one-open-contig flow is
  `(2,1,1)`, and it beats the truth-induced counts by `9/8`.
- If the vertex costs dominate, each observed read independently maximizes at
  `d = 2`, giving `(2,2,2)` and ratio `729/512`.
- In both cases the truth-induced count vector `(1,1,1)` is **not** an ML
  maximizer, so the §6.2 ordering refutes the positive answer for this instance.

The genome-level orderings for the same witness (for comparison, from
`docs/audit-binomial-marginals-issue32.md`): literal binomial on genomes
`1125/512`; fixed-length exact multinomial `2`. All orderings agree that the
competitor beats the truth.

**Note on well-posedness.** The §6.2 candidate object is an assembly (I3), not a
circular genome, and the truth genome is not feasible at this coverage.
"Truth-is-ML" is therefore not literally well-posed here; the precise
refutation is that the truth's induced count vector is dominated by a feasible
§6.2 flow.

---

## 4. Correction to the repository's Variant F search

`scripts/support_feasibility_search.py` enumerates `genomes = product(..., repeat=G)`
and defines:

- **S / support-contained**: fixed-length-`G` genomes with
  `supp(spec(D)) ⊆ supp(x)`;
- **F\***: fixed-length-`G` genomes with `d_D(w) ≥ x_w`.

Both classes are therefore **fixed-length circular genomes**, not §6.2 flows.
The frontier table of `docs/read-tiled-counterexample.md` §4 inherits this
restriction. The AAACC instance at `G = 5, L = 3, σ = 2, N = 3` has `0`
support-contained counterexamples in that table, yet the §6.2 flow candidate
`(2,1,1)` violates truth-optimality by `9/8`. The correct reading is:

> Fixed-length support containment is strictly stronger than §6.2 flow
> feasibility. The §6.2 flow candidate set allows variable-length,
> non-contiguous assemblies and unbounded vertex multiplicities, so it does not
> inherit the fixed-length search's `G ≤ 6` "SC elimination" phenomenon.

This is consistent with (and sharpens) `docs/bridging-schemas-and-flow-feasibility-gaps.md`
§4/§5: the per-type §6.2 reading is support containment, and the per-occurrence
reading is the read-tiled class; neither is a fixed-length-genome class.

---

## 5. Epistemic status

| Claim | Status | Basis |
|-------|--------|-------|
| §6.2 vertices are observed reads; lower bound 1; no upper bounds; objective is §6.1 binomial cost; flow = non-contiguous assembly | **Source fact** | §6.2 direct quotation (PMC3154397) |
| A spelled molecule's `L`-support is contained in the observed read types | **Source-supported inference** | Observation 7 + vertex set |
| Observed reads are the vertex set; `(1,1,1)` is flow-feasible | **Verified** | explicit walk |
| `S` and `D` are not §6.2-spellable (need `ACC,CCA` / `ACA`) | **Verified** | support containment check |
| strict single-circular-genome reading gives `F_flow(R) = ∅` | **Verified** | no circuit through all reads |
| `(2,1,1)` and `(2,2,2)` are flow-feasible; `(2,1,1)` uses one open contig | **Verified** | explicit walks |
| §6.2 binomial ratio `(2,1,1)` vs truth `= 9/8`; `(2,2,2)` vs truth `= 729/512` | **Verified** | exact rationals |
| I_s holds for the realized starts | **Verified** (finite check) | coverage + all-bridged triple, no interleaved pair |
| No read-tiled / per-occurrence circular genome exists for the sample | **Proved** (Eulerian imbalance) | `AC`, `CA` unbalanced |
| The fixed-length SC/F\* search does not test the §6.2 candidate set | **Source-supported inference + code inspection** | `support_feasibility_search.py` |
| Shomorony et al. intended §6.2 (or any specific variant) | **Open** | bare-bibliography citation, not disambiguated |

---

## 6. What remains open

1. Which Medvedev–Brudno object the 2016 open question intends (exact
   multinomial, separable binomial, or the §6.2 flow). Unchanged by this note.
2. Whether §6.2 flow-feasibility can ever force the truth's count vector to be
   optimal for instances where the truth is actually feasible (high coverage,
   `S ∈ F_flow(R)`). The AAACC instance is outside that regime; it shows only
   that the witness's amplification mechanism survives §6.2.
3. Whether reverse-complement (double-strand) identification enlarges the
   spelled support enough to admit `ACA`'s molecule; it does not for this
   instance (`ACA/TGT` is not among the observed read molecules), and the
   bidirected graph can only add overlaps, not vertices.

---

## 7. Reproduction

```bash
python3 scripts/section62_aaacc_witness.py   # all assertions pass
```

The script prints the spectra, support containment, circuit check, explicit
walk realizations, the exact §6.2 objective values and ratios, the I_s check,
and the read-tiling (Eulerian) check.

Primary sources: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, J. Comput. Biol. 16(8) (2009) §6.1–6.2 (PMC3154397); Ilan Shomorony,
Samuel H. Kim, Thomas A. Courtade, David N. C. Tse, *Information-optimal genome
assembly via sparse read-overlap graphs*, Bioinformatics 32(17) (2016) i494–i502
Eq. (1).
