# Section 6.2 bidirected-flow feasibility of the kernel-checked fixed-length witnesses (issue #36)

_Status: primary-source reading + mathematical argument + bounded exhaustive
exact-rational computation. 2026-09-20. All claims are classified as **source
fact**, **source-supported inference**, **mathematical argument**, **verified
computation**, or **open**. This note resolves only what the Medvedev–Brudno
§6.2 object does and does not contain for the issue #31/#32 witnesses; it does
not settle the source-ambiguous Shomorony et al. open question._

_Reproduction: `python3 scripts/se62_bidirected_feasibility_search.py` (all
assertions pass; exact `fractions.Fraction`, deterministic, about four minutes
on the development host; `--quick` runs a small subset)._

---

## 0. Answer at a glance

1. **Section 6.2 searches a bidirected *flow*, not a sequence.** The vertices
   are the reads (DNA molecules), the edges are bidirected overlaps, every read
   vertex has lower bound `1`, and the objective is the §6.1 separable binomial
   cost on the vertex flow. A flow is explicitly "a (non-contiguous) assembly
   of the genome" (source fact, quoted in §1).

2. **The sequence-level feasible set is exactly support equality.** By
   Observation 7, a molecule `D` is spelled by a walk in the (transitively
   reduced) bidirected overlap graph iff every length-`L` submolecule of `D` is
   an observed read **and** every observed read is a submolecule of `D`;
   equivalently `supp(spec_L(D)) = supp(R)`, with `spec_L` taken on read
   *molecules* when reverse complements are identified. This is a mathematical
   argument (§2).

3. **Neither kernel-checked witness transfers at the sequence level.**
   - Single-strand reading: in both `AAABB → AAAAB` (#31) and
     `AAACC → AAAAC` (#32) neither the truth nor the competitor is spelled; the
     competitor carries an unobserved window (`ABA` resp. `ACA`), and the truth
     carries unobserved windows (`ABB, BBA` resp. `ACC, CCA`).
   - **Real double-stranded (revcomp `A↔T`) reading: the #31 *truth* `AAATT`
     becomes feasible while its competitor does not.** The windows `ATT`,
     `TTT`, `TTA` are the reverse complements of the observed reads `AAT`,
     `AAA`, `TAA`; the competitor's window `ATA` has molecule class
     `{ATA, TAT}`, which is unobserved. So under the biological reading the #31
     witness is not merely non-transferable, it is **inverted**: the truth is
     spellable and the competitor is not.
   - The #32 witness stays infeasible on both sides under real DNA (`C↔G`).
   - No reading gives a witness with **both** truth and competitor spelled.

4. **The witnesses transfer only as flow/copy-count statements.** The
   competitor's window spectrum projected onto the observed read vertices,
   `(AAA:2, AAC:1, CAA:1)`, *is* a feasible §6.2 flow (the open walk
   `CAA → AAA → AAA → AAC`), and its §6.2 vertex cost beats the truth-induced
   count vector `(1,1,1)` by `9/8`. But a non-contiguous assembly is not a
   sequence, so this does not compare the truth against a sequence-level §6.2
   competitor (§4).

5. **Bounded exhaustive search finds no sequence-level §6.2 counterexample.**
   Over 85 572 `I_s`- and truth-feasible instances (binary `G ≤ 8`, ternary
   `G ≤ 6`, read lengths `L = 3, 4`, candidate lengths up to `3G`, both the
   single-strand and revcomp readings), there is **no** spelled candidate `D`
   with `supp(spec_L(D)) = supp(R)`, `d_D ≥ x`, and strictly larger literal
   §6.1 binomial likelihood than the spelled truth. So no witness in which both
   the truth and a competitor are §6.2 molecules was found in that scope (§5).

6. **The genuine residue is the flow-level (non-spellable) gap.** The search
   covers candidates that are single molecules. Section 6.2's candidate object
   is any feasible flow, including count vectors not realizable by a single
   molecule. Whether a *spellable* truth can be beaten by such a non-spellable
   flow is not settled here and remains open (§6).

---

## 1. What §6.2 searches (source facts)

Primary source: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116, §6.2 "Putting it all
together", PMC3154397.

Direct quotations:

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
`c_i(d_i) = -(x_i log d_i) - (n - x_i) log(N - d_i)` with fixed external `N`;
the literal objective retains the zero-count factors
`(1 - d_i/N)^{n - x_i}` (see `docs/audit-binomial-marginals-issue32.md`).

Three consequences are worth isolating:

- **(S1) Vertices are read molecules.** Because a read is a DNA molecule
  (an unordered reverse-complement pair), two reads that are reverse
  complements *of the same sequence* are the same vertex.  Whether the final
  theorem should identify reverse complements is a **source ambiguity**
  recorded in `docs/ml-formalization-contract.md`; this note analyses both
  readings rather than choosing one.
- **(S2) Support containment is forced.** Vertices exist only for observed
  reads, so a spelled molecule's `L`-submolecules must all be observed.
- **(S3) The output need not be a sequence.** A flow may be a collection of
  walks, i.e. a non-contiguous assembly; only a circuit corresponds to a
  circular genome.

## 2. The sequence-level feasibility criterion

Throughout, `L` is the read length, `R` the observed read multiset with read
type counts `x`, and `spec_L(M)` the multiset of length-`L` submolecules of a
circular molecule `M`.

**Criterion.** A molecule `D` is *sequence-level §6.2-feasible* with respect to
`R` iff

1. `supp(spec_L(D)) = supp(R)` (over read *molecule classes* when reverse
   complements are identified); and
2. `d_D(w) ≥ x_w` for every observed type `w` (per-occurrence lower bound; the
   per-type reading uses `d_D(w) ≥ 1`).

**Proof (mathematical argument).**

- *Necessity.* If a walk `W` in the read-overlap graph spells `D`, then by
  Observation 7 each visit to a read `r` is a submolecule occurrence of `D`.
  Hence `spec_L(D)` is supported on the visited read vertices, giving
  `supp(spec_L(D)) ⊆ supp(R)`; the lower bound `1` on every read vertex gives
  `supp(R) ⊆ supp(spec_L(D))`, hence equality, and per-occurrence lower bounds
  give `d_D(w) ≥ x_w`.
- *Sufficiency.* List the `|D|` length-`L` windows of `D` in cyclic order. Any
  two consecutive windows overlap in `L − 1` symbols, so they form a walk in the
  overlap graph; the transitive reduction preserves the set of spelled
  molecules (source fact), so the walk survives it. Support equality makes every
  step a visited observed-read vertex, and the multiplicity condition uses each
  occurrence at least once. ∎

Thus the sequence-level feasible set is **support equality plus multiplicity
lower bounds**; support *containment* alone is the relaxation used in
`docs/section-6-2-feasible-set-membership.md`.

**Caution against conflating levels.** Criterion (1) is about a single
molecule; the flow optimum of §6.2 ranges over all count vectors realizable by
collections of walks and need not be the spectrum of any molecule. The two
levels can disagree (the `AAACC` copy vector of §4 is the example).

## 3. The kernel-checked witnesses are not sequence-level feasible

Witnesses (identical up to relabeling `B → C`):

```
#31  truth S = AAABB   competitor D = AAAAB   L = 3   starts {0,1,4}
#32  truth S = AAACC   competitor D = AAAAC   L = 3   starts {0,1,4}
```

Realized start multiplicities are all one, so per-occurrence and per-type
readings agree.

### 3.1 Single-strand reading

```
#31 observed support        {AAA, AAB, BAA}
    spec(D) support         {AAA, AAB, ABA, BAA}     unobserved: ABA
    spec(S) support         {AAA, AAB, ABB, BAA, BBA} unobserved: ABB, BBA
#32 observed support        {AAA, AAC, CAA}
    spec(D) support         {AAA, AAC, ACA, CAA}     unobserved: ACA
    spec(S) support         {AAA, AAC, ACC, CAA, CCA} unobserved: ACC, CCA
```

Neither `S` nor `D` satisfies criterion (1): both carry unobserved length-`3`
windows. The witness refutes the fixed-length exact / binomial objectives of
issues #31/#32 over the *sequence* universe, but not §6.2.

### 3.2 Real double-stranded reading: the #31 witness inverts

Take the real DNA complement `A↔T`, and write the witness symbol `B` as `T`.
Reads are molecules, so a read and its reverse complement are one vertex.

```
S = AAATT
windows of S         AAA, AAT, ATT, TTT, TTA
molecule classes     AAA, AAT, AAT, AAA, TAA          (ATT~AAT, TTT~AAA, TTA~TAA)
observed molecules   AAA, AAT, TAA                    (AAA, AAT, TAA)
d_S                  AAA:2, AAT:2, TAA:1
```

So `supp(spec_3(S)) = {AAA, AAT, TAA} = supp(R)` and `d_S ≥ x`. **The #31
truth is sequence-level §6.2-feasible under the biological reading.**

The competitor `D = AAAAT` has windows `AAA, AAT, AAT, ATA, TAA`. The molecule
class of `ATA` is `{ATA, TAT}`, which is not observed. Hence `D` is **not**
feasible. The witness does not transfer; it reverses.

For #32, `C ↔ G` is not the complement of `A`, and the unobserved windows
`ACC, CCA` (`D`: `ACA`) have molecule classes containing `G`, so no collapse
occurs: both sides remain infeasible.

The reading is parameter-dependent in exactly the source-ambiguous way flagged
in `docs/ml-formalization-contract.md:47`: with an *artificial* involution that
pairs the two symbols used by a witness (`A↔C` for #32), the #32 truth also
becomes feasible and the competitor still does not. In every reading tested, **no
witness has both the truth and the competitor spelled** (verified computation).

## 4. Flow-level transfer: the copy-vector statement

The molecule reading is not the only content of the witnesses. The competitor
`AAAAC`'s length-`3` spectrum is `{AAA:2, AAC:1, ACA:1, CAA:1}`; its projection
onto observed vertices is `(AAA:2, AAC:1, CAA:1)`. This count vector is
realizable by the open walk

```
CAA → AAA → AAA → AAC
```

with overlaps of length `L − 1 = 2`, i.e. a single non-contiguous contig. Under
the literal §6.1 binomial with `N = 5`, `n = 3`, `x = (1,1,1)`:

```
positive-type factor ratio = (2/5)(3/5)^2 / ((1/5)(4/5)^2) = 9/8 > 1
```

so the §6.2 vertex cost strictly prefers the competitor's count vector to the
truth-induced `(1,1,1)`. The same computation applies to #31.

This is a genuine §6.2 statement about a **non-contiguous assembly**, not about
the ML *sequence*. The source's own prose ("a (non-contiguous) assembly of the
genome") makes the gap explicit. The 2016 open question concerns a
maximum-likelihood *sequence*; a non-contiguous assembly is not one, so the
flow-level transfer does not settle the sequence-level statement. This is the
same distinction recorded in `docs/section-6-2-feasible-set-membership.md` §4
for the (corrected) `AAACC` flow claim.

## 5. Bounded exhaustive search for a sequence-level counterexample

A sequence-level counterexample must have **both** the truth and the winning
candidate spelled (support equality, multiplicity lower bounds), because
otherwise the truth is not an admissible §6.2 output and there is nothing to
refute.

**Method.** For each truth `S`, each read length `L`, and each realized start
multiset with `n = |S|` reads:

1. keep the instance only if the realized reads satisfy `I_s` and the truth is
   sequence-level feasible (`supp(spec_L(S)) = supp(R)` and `d_S ≥ x`);
2. enumerate every circular molecule `D` over the alphabet with `|D| ≤ maxD`
   whose window spectrum has the *same support* as `R` and satisfies
   `d_D ≥ x`; deduplicate by spectrum (the §6.1 binomial depends only on the
   spectrum);
3. compare the literal §6.1 binomial with fixed external `N = |S|`, requiring
   the binomial domain `d_i ≤ N`.

Run under both the single-strand reading (`comp=False`) and the reverse-complement
reading (`comp=True`, an involution on the alphabet).

**Result.** Zero counterexamples in every scope:

| reading | scope | instances | cex |
|---|---|---|---|
| single-strand | binary `4 ≤ G ≤ 8`, `L = 3, 4`, `|D| ≤ 3G` | 35 505 | 0 |
| single-strand | ternary `G = 5, 6`, `L = 3, 4`, `|D| ≤ 2G` | 6 057 | 0 |
| revcomp | binary `4 ≤ G ≤ 8`, `L = 3, 4`, `|D| ≤ 3G` | 43 995 | 0 |
| revcomp | ternary `G = 5, 6`, `L = 3, 4`, `|D| ≤ 2G` | 10 049 | 0 |

Total 85 572 instances, 0 counterexamples. The search is exhaustive over the
stated finite scope; it is computational evidence, not a proof of absence
beyond it.

**Relation to prior computations.** The fixed-length search
`docs/fixed-length-flow-feasible-repeat-search.md` (branch artifact) required
candidates to have length `G` and found zero `I_s` + `F*` counterexamples. The
present search additionally allows variable candidate length (up to `3G`) and the
reverse-complement reading, and requires the candidate to be a *single spelled
molecule* rather than an arbitrary count vector. The zero count is stable under
all three extensions in scope.

## 6. What this does and does not establish

| statement | status |
|---|---|
| §6.2 feasible objects are bidirected flows / non-contiguous assemblies; objective is §6.1 binomial on vertex flow | **source fact** |
| Sequence-level criterion `supp(spec_L(D)) = supp(R)` ∧ `d_D ≥ x` | **mathematical argument** (Observation 7 + consecutive-window walk + transitive reduction) |
| #31/#32 competitors are not sequence-level §6.2-feasible (single-strand) | **verified computation** |
| #31 truth becomes feasible under the real revcomp reading, competitor does not; witness inverts | **verified computation** |
| No reading gives a witness with both truth and competitor feasible | **verified computation** |
| Competitor copy vector is a feasible §6.2 flow and beats the truth count vector by `9/8` | **verified computation** (matches the corrected `AAACC` analysis) |
| No sequence-level §6.2 counterexample in the searched scope | **verified computation** (bounded, not a proof) |
| A *spellable* truth can be beaten by a §6.2 flow that is not any single molecule | **open** |
| Shomorony et al. intended §6.2 for the open question | **unresolved source ambiguity** |

## 7. Open questions

1. **Flow-level (non-spellable) candidates.** Section 6.2's optimum ranges over
   all feasible flows, not only molecule spectra. A bounded search that
   enumerates flow count vectors (and checks realizability in the bidirected
   overlap graph) is needed to close the gap between §5 and the literal §6.2
   algorithm.
2. **`o_min`.** The overlap threshold is a free parameter; `o_min = L − 1`
   (used above) is the densest graph. Smaller `o_min` can only add edges and
   thereby add feasible flows. The obstruction in §3 is support-theoretic and
   therefore independent of `o_min`; the search's zero count might not be.
3. **Reverse-complement equivalence.** The #31 inversion shows the choice
   materially changes which witness transfers. The final formalization must fix
   the genome-equivalence relation before any settled statement can be made.
4. **Per-occurrence vs per-type lower bound.** The source lower bound of `1` is
   per read *vertex*; whether duplicate reads are distinct vertices is
   unresolved. Both readings are implemented; the results do not depend on the
   choice for the witnesses (all realized multiplicities are one).

## 8. Reproduce

```sh
python3 scripts/se62_bidirected_feasibility_search.py          # full, ~4 min
python3 scripts/se62_bidirected_feasibility_search.py --quick  # small subset
```

The script asserts: no kernel witness has both truth and competitor
sequence-feasible; the competitor copy vector is feasible; and every recorded
search scope has zero counterexamples. It exits non-zero on any violation and
uses only exact `fractions.Fraction` arithmetic.

## 9. Epistemic status

| claim | status |
|---|---|
| §6.2 quotes and model | source fact (PMC3154397 §6.2, §3.3) |
| Observation-7 feasibility criterion | mathematical argument |
| Witness membership tables | verified computation (exact rationals) |
| Revcomp #31 inversion | mathematical argument + verified computation |
| Bounded search zero-counterexample result | verified computation, bounded |
| Flow-level gap | open |

Primary sources: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116, §3.3, §6.1–6.2, PMC3154397;
Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
Bioinformatics 32(17) (2016) i494–i502.

Cross-references: `docs/section-6-2-feasible-set-membership.md` (membership of
the witnesses in the support/sequence sets); `docs/read-tiled-counterexample.md`
(kernel-checked read-tiled witness); `docs/fixed-length-exact-counterexample.md`
and `docs/fixed-length-binomial-counterexample.md` (the #31/#32 witnesses);
`docs/source-notes/medvedev-brudno-candidate-class.md` (candidate-class
separation).

---

## 10. Addendum (2026-09-20): current canonical read-tiled witness

Sections 1–9 above analyse the #31 (`AAABB → AAAAB`) and #32 (`AAACC → AAAAC`)
witnesses.  The repository's **current canonical** fixed-length witness is the
read-tiled instance

```
truth S = AAABCBC   competitor D = AAAAABC   L = 3
observed x = {AAA:3, AAB:1, ABC:1, BCA:1, CAA:1}
```

kernel-checked in `AssemblyP1/ReadTiledCounterexample.lean` and documented in
`docs/read-tiled-counterexample.md`.  It is the strongest fixed-length witness
because the competitor is *read-tiled*, i.e. its length-`3` spectrum is exactly
the observed spectrum `x`.  This addendum records whether that witness transfers
to §6.2 and kernel-checks the answer in
`AssemblyP1/Section62FlowObstruction.lean`.

### 10.1 Reconstructed feasibility predicate

The §6.2 sequence-level criterion used here is the Observation-7 criterion of
§2, not re-derived: a circular molecule `D` is sequence-level §6.2 feasible iff

1. every length-`L` window of `D` is an observed read type
   (`WindowSupported`); and
2. every observed read occurrence is used, i.e. `d_D(w) ≥ x_w`
   (`LowerBounded`).

For the canonical instance the observed counts are `AAA:3` and
`AAB, ABC, BCA, CAA:1`.

### 10.2 Kernel-checked result

| theorem (`AssemblyP1.Section62FlowObstruction`) | content |
|---|---|
| `competitor_section62_feasible` | `AAAAABC` satisfies `WindowSupported ∧ LowerBounded` |
| `truth_not_section62_feasible` | `AAABCBC` does **not** satisfy it |
| `truth_unobserved_windows` | `occ truth BCB = 1`, `occ truth CBC = 1`, and neither is observed |
| `canonical_witness_section62_obstruction` | `Section62Feasible competitor ∧ ¬ Section62Feasible truth` |

All four are proved by `decide` over the fixed length-`7` instance; no `sorry`,
`axiom`, or `admit`.

### 10.3 Interpretation and preserved assumptions

- The **competitor is §6.2-feasible**: read-tiling makes it the cyclic read
  order, a legitimate walk in the read-overlap graph, and the flow vertex cost
  strictly prefers it to the truth count vector (`docs/read-tiled-counterexample.md`
  Theorem 1; §4 above).
- The **truth is not §6.2-feasible**: its windows `BCB` and `CBC` are
  unobserved, so no closed walk on read vertices spells `S`.  Hence the truth is
  not an admissible §6.2 *sequence* candidate at all.
- **Obstruction.** Because the truth is not a candidate, the canonical witness
  cannot refute the well-posed statement “`I_s` ∧ `S ∈ F_flow(R)` ⇒ `S` is ML
  over `F_flow(R)`.”  This matches the #31/#32 conclusion of §3–§4 and the
  membership table of `docs/section-6-2-feasible-set-membership.md` §3.
- **Assumptions preserved.** Fixed read length `L = 3`; single-strand reading;
  fixed candidate length `7`; per-occurrence lower bounds.  The
  reverse-complement reading (which inverts witness #31, §3.2), the
  non-spellable flow-level gap (§6), and the unresolved choice of §6.1 layer
  are untouched.

### 10.4 Epistemic status of the addendum

| claim | status |
|---|---|
| Reconstruction of the Observation-7 feasibility predicate | source fact + source-note (`docs/section-6-2-feasible-set-membership.md` §2); not re-derived here |
| `competitor` §6.2-feasible, `truth` not | **kernel-checked** (`Section62FlowObstruction.lean`) |
| Obstruction to transferring the canonical witness | **kernel-checked** |
| Positive sequence-level §6.2 statement | **open** |

Reproduce: `lake build AssemblyP1.Section62FlowObstruction`.

---

## 11. Addendum (2026-09-20): per-type reading admits fixed-length counterexamples

Sections 5 and 6 recorded zero sequence-level §6.2 counterexamples under the
**per-occurrence** lower bound (`d_D(w) ≥ x_w`) and `N = G`. That zero result
does not extend to the **per-type** lower bound (`d_D(w) ≥ 1` for every observed
molecule), which is the literal reading of the source's “set of reads … which
are DNA molecules”.

`scripts/se62_fixed_length_bidirected_search.py` fixes `|D| = G` and searches
both readings and both lower-bound readings. Under the bidirected (reverse
complement) reading with the per-type lower bound it finds 4608 fixed-length
likelihood-improving witnesses at `G = 6, L = 3` (over the rotation/complement
orbit of `AAATAT`; exact ratios `3`–`81`, every binomial ratio `> 1`). The
minimal member is

```
S = AAATAT   D = AAAAAT   L = 3   starts (0,0,1,3,5)
observed molecules x = { AAA:2, AAT:1, ATA:1, TAA:1 }
d_S = {AAA:1, AAT:1, ATA:3, TAA:1}     (TAT ~ ATA raises ATA to 3)
d_D = {AAA:3, AAT:1, ATA:1, TAA:1}
I_s holds; both spectra have support supp(x); L_exact(D)/L_exact(S) = 3.
```

For every other recorded scope — single-strand (either lower bound) and
bidirected per-occurrence — the counterexample count is zero. Full scope,
exact-rational reproduction, and the reading-dependence argument are in
`docs/section62-fixed-length-bidirected-counterexample.md`. This refutes the
fixed-length statement under the per-type bidirected reading and leaves the
per-occurrence statement open.

---

## 12. Addendum (2026-09-20): the non-spellable-flow gap (§6, §7.1)

Section 6 left open whether a *spellable* truth can be beaten by a §6.2 flow
that is not any single molecule. `scripts/se62_nonspellable_flow_search.py`
enumerates the full integer **cycle cone** of the read-overlap graph (so
non-spellable flows are included) rather than single spelled molecules.

- On the **full (unreduced)** overlap graph with `o_min = 1`, the answer is
  yes under the per-occurrence reading: `S = 01011`, `G = 5`, `L = 3`, starts
  `(0,1,2,3)`, non-spellable flow `d = x = {010:1,101:1,011:1,110:1}`, cycle
  `010 → 101 → 011 → 110 → 010` (step overlaps `2,2,2,1`), binomial ratio
  `32/27 > 1`.
- That witness uses the overlap-`1` edge `110 → 010`, which is transitively
  reducible (the read `101` spans the junction), so it does **not** survive the
  source's transitive reduction.
- On the **Myers-string-reduced** graph, exhaustive search finds **zero**
  per-occurrence counterexamples (spellable or not) for binary `G = 5,6,7`,
  `L = 3`, `o_min = 1,2`.

Hence the §6 residue is resolved in the negative for the source-faithful
reduced model in the bounded scope; the positive full-graph witness isolates
the phenomenon as an artifact of retaining transitively reducible edges. Details,
assumptions, and epistemic status: `docs/section62-nonspellable-flow-counterexample.md`.
