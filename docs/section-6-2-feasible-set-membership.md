# Do the bridging counterexamples live in the Medvedev–Brudno §6.2 feasible set?

_Status: source reading + mathematical argument + exact-rational computation,
2026-09-20. Not a Lean result. All claims are classified as **source fact**,
**source-supported inference**, **mathematical argument**, **verified
computation**, or **open**. This note reconciles three unmerged §6.2 analyses
and does not settle the source-ambiguous Shomorony et al. open question._

_Reproduction: `python3 scripts/se62_feasible_set_membership.py` (all
assertions pass; exact `fractions.Fraction` arithmetic)._

---

## 0. Answer at a glance

1. Medvedev–Brudno §6.2 searches a **convex min-cost flow on the read-overlap
   graph**, with a lower bound of `1` on every read vertex, objective equal to
   the §6.1 separable binomial approximation, and output that "represents a
   (non-contiguous) assembly of the genome." A flow is **not** a sequence.

2. The sequence-level sub-case — the one relevant to "the maximum-likelihood
   **sequence** is the true sequence" — is exactly: `D` is a circular genome
   every length-`L` window of which is an observed read type, with each observed
   read vertex used at least once. Equivalently `supp(spec(D)) = supp(x)` and
   (per-occurrence reading) `d_D(w) ≥ x_w`. This is the set on which
   Observation 7 of the source holds (walk visits = submolecules of the spelled
   molecule).

3. **Only two of the repository's counterexamples have a competitor in that
   sequence-level feasible set**: the read-tiled `AAABCBC → AAAAABC` and the
   smallest `AACC → ACAC`. In both, the **truth is not feasible**. Every other
   fixed-length/interleaved witness has a competitor with an **unobserved
   window**, so the competitor is not even support-contained, let alone
   flow-feasible.

4. **No current counterexample has both truth and competitor in the
   sequence-level §6.2 feasible set.** Therefore no current counterexample
   refutes the well-posed statement “`I_s` ∧ `S ∈ F_flow(R)` ⇒ the truth is an
   ML maximizer over `F_flow(R)`.” The negative results address the larger sets
   “all length-`G` genomes” (Variant E) or “all support-contained/read-tiled
   genomes” without requiring the truth to be a candidate.

5. **Correction to an unmerged certificate.** The claim (branch
   `agent/flow-model-0919b`, commit `f3cf5d0`) that the `AAACC` competitor
   `D = AAAAC` “is flow-feasible … which spells exactly `D`” is **false under
   the source's Observation 7**. The witness walk uses a length-`1` overlap
   `AAC → CAA`, which leaves `D`'s window `ACA` (unobserved) unvisited; the
   visit-count identity fails. Only the *copy vector* `(AAA:2, AAC:1, CAA:1)` is
   a feasible **flow** on the observed vertices, i.e. a non-contiguous assembly,
   not the sequence `D`. The independent audit `agent/flow-feasible-0919c`
   (commit `4c22516`) correctly proves the truth is not spellable, but shares
   the same error when it accepts `D` as spellable via the length-`1` edge.

---

## 1. What §6.2 actually searches

**Source facts** (Medvedev–Brudno §6.2, PMC3154397):

- "The vertices of this graph are the reads, and the edges are all possible
  bidirected overlaps of length at least `o_min`."
- "Each vertex has a lower bound of 1 since it represents a read that must be
  present in the genome at least once. All other lower bounds are 0 and all
  upper bounds are infinity."
- "By Observation 7, the `d_i`'s ... actually correspond to the value of the
  flow through vertex `i`, and we let `c_i` be the convex cost functions for
  the vertices."
- "Since any flow can be decomposed into a collection of walks, our flow
  represents a (non-contiguous) assembly of the genome, and the flow going
  through each vertex represents the number of time the read is present in the
  assembly."

Observation 7: "The number of times `W` visits `r` is equal to the number of
times `r` appears a submolecule of the molecule spelled by `W`."

Two candidate objects coexist in the source and are not the same:

| object | what it is | sequence? |
|---|---|---|
| integer circulation / flow | nonnegative integer values on read vertices, conservation, lower bound `1` | no (may be a collection of walks) |
| walk-spelled molecule | a single closed walk in the read-overlap graph | yes |

The §6.2 objective is the §6.1 **separable binomial approximation**
`∏_i C(n,x_i)(d_i/N)^{x_i}(1-d_i/N)^{n-x_i}` with external `N` and
`c_i(d_i)=-(x_i log d_i)-(n-x_i)log(N-d_i)`, not the exact multinomial. This is
a second, independent reason the repository's “Variant F = exact multinomial
over flow-feasible genomes” is a hybrid object, not the literal §6.2 problem.

## 2. Sequence-level feasibility criterion

Let `x` be the observed read-type count vector (a multiset of occurrences).

**Criterion (sequence-level `F_flow`).** A circular genome `D` is
sequence-level §6.2-feasible iff

1. every length-`L` window of `D` is an observed read type
   (`supp(spec(D)) ⊆ supp(x)`); and
2. every observed read is used at least once — per-**occurrence** reading:
   `d_D(w) ≥ x_w`; per-**type** reading (duplicate reads collapsed to one
   vertex): `d_D(w) ≥ 1` for every `w ∈ supp(x)`.

Because condition (1) already gives `supp(spec(D)) ⊆ supp(x)` and condition (2)
gives `supp(x) ⊆ supp(spec(D))`, **both** source readings force support
equality `supp(spec(D)) = supp(x)`; they differ only in the multiplicity lower
bound. Support containment alone (`SC`) is therefore a strict *relaxation* of
the source feasible set, retained below as a convenient outer bound.

**Why the criterion is exact (mathematical argument).** Condition (1) makes
every step of `D`'s own cyclic window sequence a visited observed-read vertex;
condition (2) makes each observed read visited. All occurrences of a given read
type have identical overlap neighbourhoods in the read-overlap graph, so the
type-level closed walk of `D` lifts to an occurrence-level closed walk using
each of the `x_w` occurrences at least once. Conversely any walk-spelled
molecule has windows among the vertices (Observation 7), so (1)–(2) are
necessary. Hence the walk-spelling set is exactly
`{D : supp(spec(D)) = supp(x) ∧ d_D ≥ x}` (per-occurrence) or its per-type
counterpart.

This is the same set called `F*(R)` in
`docs/bridging-schemas-and-flow-feasibility-gaps.md` §4, here given a
walk-spelling derivation from Observation 7.

**Observation-7 test for a proposed walk.** A placement of read occurrences on
`D` is Observation-7-admissible iff the induced window multiset equals the
**full** spectrum `spec(D)`. A walk that overlaps two reads by less than
`L − 1` can skip an intermediate window of `D`, and then Observation 7 fails.

## 3. Membership of the repository's counterexamples

`SC` = support containment `supp(spec(D)) ⊆ supp(x)` (a relaxation of the
source set, which forces equality); `F*` = `SC` plus `d_D(w) ≥ x_w` (the
per-occurrence condition). The first four competitors below fail even `SC`;
the last two satisfy the stronger `F*`. Reproduced by
`scripts/se62_feasible_set_membership.py`.

| witness | `D` feasible? | `S` feasible? | reason |
|---|---|---|---|
| `AAABB → AAAAB` (kernel-checked, exact) | no | no | `D` uses unobserved `ABA`; `S` uses `ABB`, `BBA` |
| `AAACC → AAAAC` (fixed-length binomial) | no | no | `D` uses unobserved `ACA`; `S` uses `ACC`, `CCA` |
| `AAABACC → AAAABAC` (interleaved, same word) | no | no | `D` uses `ABA`, `ACA`; `S` uses `ABA`, `ACC`, `CCA` |
| `ABACABC → ACABACB` (interleaved, distinct words) | no | no | `D` uses `ABA`, `ACA`, `ACB`, `CBA`; `S` uses four others |
| `AAABCBC → AAAAABC` (read-tiled) | **yes** | no | `d_D = x` exactly; `S` uses `BCB`, `CBC` |
| `AACC → ACAC` (smallest flow-feasible) | **yes** | no | `d_D(AC)=d_D(CA)=2 ≥ 1`; `S` uses `AA`, `CC` |

Two observations:

1. The competitor is feasible in only the two read-tiled-style witnesses; the
   four “unrestricted/fixed-length” witnesses have competitors outside even the
   support-containment relaxation. Those witnesses therefore say nothing about
   §6.2 and only refute the larger Variant E / fixed-length classes.
2. In **every** witness the realized spectrum is incomplete
   (`supp(x) ⊊ supp(S)`), so the **truth is never sequence-level feasible**.

Under the source §6.2 **binomial** objective, the two feasible competitors also
strictly beat the truth:

| witness | `L_62(D)/L_62(S)` |
|---|---|
| `AAABCBC → AAAAABC` | `16/3 > 1` |
| `AACC → ACAC` | `16/9 > 1` |

So the negative ordering is robust to the exact-vs-binomial objective fork.

## 4. Correction: the `AAACC` “transfer” certificate

`agent/flow-model-0919b` (commit `f3cf5d0`) asserts the `AAACC → AAAAC`
fixed-length binomial witness transfers to §6.2 because `D = AAAAC` is
flow-feasible via the circulation

```text
AAA --2--> AAA --2--> AAC --1--> CAA --2--> AAA.
```

The auditor branch `agent/flow-feasible-0919c` (commit `4c22516`) distinguishes
copy-vector feasibility from walk spelling and correctly proves that the truth
`S = AAACC` is not walk-spellable, but then accepts the same `D` as
walk-spellable.

**Both are wrong about `D`.** `spec(AAAAC) = {AAA:2, AAC:1, ACA:1, CAA:1}`
includes the unobserved window `ACA`, so `supp(spec(D)) ⊄ supp(x)` and `D` is
not sequence-level feasible. The proposed walk places reads at starts `0,1,2,4`
of the length-`5` circle; the induced visited windows are
`{AAA:2, AAC:1, CAA:1}`, which omits `ACA` (the window at start `3`). Its
`AAC → CAA` step has overlap length `1 < L − 1 = 2`, so the spelled molecule
contains a window that is not a visited read — Observation 7 fails.

What is true is weaker: the **copy vector** `(AAA:2, AAC:1, CAA:1)` projected
onto the observed vertices is a feasible flow (the open walk
`CAA → AAA → AAA → AAC`), i.e. a **non-contiguous assembly**, and the §6.2
vertex cost of that flow beats the truth's induced flow. But a non-contiguous
assembly is not a sequence, so this does not compare the truth against a
sequence-level §6.2 competitor. The strict sequence-level reading gives
`F_flow(R) = ∅` for this instance (as noted independently in
`docs/section62-aaacc-witness-feasibility.md`, branch `agent/section62-aaacc-witness`,
commit `3c3b5fb`).

**Consequence for the search claims.** The bounded search in `4c22516`
(“binary `G = 3..8`, with `I_s`: 17 596 truth-flow-feasible instances, 0
sequence-level counterexamples”) inherits the loose walk definition; its
completeness claim should be re-run with the Observation-7 criterion of §2
before it is relied on. The weaker conclusion it supports — that `I_s` plus
truth-feasibility may block the counterexamples, in contrast to the
coverage-only control (234 counterexamples) — is consistent with the exact
`F*` picture here and with Proposition D of
`docs/bridging-schemas-and-flow-feasibility-gaps.md`.

## 5. What the current counterexamples do and do not establish

| statement | status |
|---|---|
| Fixed-length exact/unrestricted Variant E is refuted | unchanged (kernel-checked witnesses); these competitors are not §6.2-feasible |
| “`I_s` ⇒ truth is ML over **all** length-`G` genomes” | refuted (truth not even a candidate-optimal there) |
| “`I_s` ⇒ truth is ML over the **sequence-level §6.2** set” | **not refuted by any current witness**: no witness has both `S` and `D` feasible |
| “`I_s` ⇒ truth is ML over **support-contained / read-tiled** fixed-length genomes” | refuted by `AAABCBC → AAAAABC` (competitor feasible, truth not) |
| The `AAACC` competitor is a sequence-level §6.2 solution | **false** (unobserved `ACA`; Observation 7 fails) |

The well-posed sequence-level question therefore remains open:

> Does `I_s` together with `S ∈ F_flow(R)` imply that `S` is a maximizer of the
> §6.2 (or §6.1) objective over sequence-level flow-feasible `D`?

Two partial results are already known in the repository:

- **Tandem invariance** (`docs/bridging-schemas-and-flow-feasibility-gaps.md`,
  Prop. A): `L_exact(D^k|x) = L_exact(D|x)`, and `S^k ∈ F_flow(R)` whenever
  `S ∈ F_flow(R)`. Hence `allMaximizersAreTruth` is false for any
  sequence-level flow class; only `truthIsML` can hold.
- **Repeat-free feasible truth** (ibid., Prop. D): if `S` is repeat-free and
  `S ∈ F*(R)`, then `S` is an exact maximizer (ties are the `k·d_S` class).

The repeated-truth, truth-feasible regime is the remaining gap.

## 6. Open questions

1. **Per-occurrence vs per-type lower bound.** The source says lower bound `1`
   on every read vertex but does not settle whether duplicate reads are distinct
   vertices. The two readings give `F*` and `SC`; the truth-feasibility
   obstruction and the two feasible competitors are unaffected, but a positive
   proof must name the reading.
2. **`o_min`.** For the `AAACC` flow the copy vector needs `o_min = 1`; with
   `o_min = 2` no feasible circulation exists. The source leaves `o_min` a
   parameter. Any claimed transfer must fix it.
3. **Transitive reduction and bidirectedness.** The strict sequence-level
   obstruction appears single-strand-robust (the truth's observed placements
   leave a cyclic gap larger than `L − 1`), but a fully explicit bidirected
   formulation is not written down. **Addressed for the #31/#32 witnesses in
   `docs/section62-bidirected-flow-feasibility.md`:** under the real
   double-stranded reading the #31 *truth* becomes feasible and its competitor
   does not, so that witness inverts rather than transfers.
4. **Re-run the `I_s` + truth-feasible search under the Observation-7
   criterion** to replace the loose-walk bounded evidence with an exact,
   durably verified boundary. **Done in
   `docs/section62-bidirected-flow-feasibility.md` §5** for single-molecule
   candidates (variable length up to `3G`, single-strand and revcomp readings):
   zero counterexamples over 85 572 instances.
5. **Which MB layer the 2016 sentence intends** (exact multinomial vs binomial
   approximation vs §6.2 flow) — unchanged.

## 7. Relationship to unmerged branches

| artifact | commit | disposition here |
|---|---|---|
| `docs/flow-feasibility-aaacc-witness.md` (`agent/flow-model-0919b`) | `f3cf5d0`, `849c061` | competitor transfer claim **corrected** (§4) |
| `docs/flow-feasibility-aaacc-witness-audit.md` (`agent/flow-feasible-0919c`) | `4c22516` | truth-infeasibility arguments **confirmed**; `D`-spellability and the loose-walk search **flagged** (§4) |
| `docs/section62-aaacc-witness-feasibility.md` (`agent/section62-aaacc-witness`) | `3c3b5fb` | conclusion that neither genome is spellable **confirmed** |
| `docs/read-tiled-counterexample.md` (this branch, working tree uncommitted) | — | “Variant F refuted” **qualified**: only when truth-candidate-membership is not required |
| `docs/bridging-schemas-and-flow-feasibility-gaps.md` (this branch) | `2af17e4` | `F*` characterization **re-derived** from Observation 7; consistent |

These branches are unmerged; the corrections are recorded here rather than
rewriting another worker's branch.

## 8. Epistemic status

| claim | status |
|---|---|
| §6.2 feasible objects are flows; output may be non-contiguous; objective is the §6.1 binomial | source fact |
| Sequence-level criterion `supp(D) ⊆ supp(x) ∧ d_D ≥ x` | mathematical argument from Observation 7 + vertex interchangeability |
| Membership table of §3 | verified computation (exact rationals) |
| `D = AAAAC` is not sequence-level feasible; claimed walk violates Observation 7 | mathematical proof + verified computation |
| `AAABCBC → AAAAABC` and `AACC → ACAC` competitors are sequence-level feasible and beat the truth under the binomial objective | verified computation (exact rationals) |
| No current counterexample has both truth and competitor sequence-level feasible | verified computation over the enumerated current witnesses |
| “`I_s` ∧ `S ∈ F_flow` ⇒ truth is ML” is open | open |

Primary sources: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116, §6.1–6.2, PMC3154397; Ilan
Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
Bioinformatics 32(17) (2016) i494–i502, Eq. (1); Guy Bresler, Ma'ayan Bresler,
David Tse, *Optimal assembly for high throughput shotgun sequencing*, BMC
Bioinformatics 14(Suppl 5):S18 (2013).
