# Audit: does the AAACC/AAAAC witness correspond to a Section 6.2 flow solution?

_Status: mathematical audit with an exact-rational, reproducible computational
check. Not a Lean result. Does not settle the source-ambiguous Shomorony et al.
open question._

_Reproduction: `python3 scripts/flow_feasibility_aaacc_audit.py` (asserts every
claim below, exits non-zero otherwise, exact `fractions.Fraction` arithmetic;
runtime about 50 s)._

This note audits the claim on the unmerged branch `agent/flow-model-0919b`
(`docs/flow-feasibility-aaacc-witness.md`) that the fixed-length binomial
witness `S = AAACC` / `D = AAAAC` "does transfer to the Medvedev–Brudno
Section 6.2 overlap-graph flow candidate set." It was produced independently of
that branch by re-deriving the objective, re-running the finite checks, and
testing a distinction the certificate does not separate: **copy-vector
feasibility versus walk spelling**.

Primary sources:

- Paul Medvedev and Michael Brudno, "Maximum Likelihood Genome Assembly,"
  *Journal of Computational Biology* 16(8), 2009, 1101–1116,
  DOI [10.1089/cmb.2009.0047](https://doi.org/10.1089/cmb.2009.0047),
  Sections 3.2, 5.2, 6.1–6.2, Observation 7.
- Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, and David N. C. Tse,
  "Information-optimal genome assembly via sparse read-overlap graphs,"
  *Bioinformatics* 32(17), 2016, i494–i502,
  DOI [10.1093/bioinformatics/btw450](https://doi.org/10.1093/bioinformatics/btw450).

## 1. What Section 6.2 actually searches

Medvedev–Brudno Section 6.2 builds a **bidirected overlap graph** on the
observed reads, performs transitive edge reduction, adds a supersource/supersink,
and defines a convex min-cost biflow with a lower bound of 1 on every read
vertex. It then writes (source fact):

> "Since any flow can be decomposed into a collection of walks, our flow
> represents a (non-contiguous) assembly of the genome, and the flow going
> through each vertex represents the number of time the read is present in the
> assembly."

Two different candidate objects therefore coexist in the source:

- a **flow**, i.e. an integer circulation with vertex lower bounds, which may
  decompose into several walks (a non-contiguous assembly); and
- a **sequence**, i.e. a single circular genome, which is realized only when a
  single closed walk in the (transitively reduced) overlap graph *spells* it.
  Observation 7 is stated for a walk `W`: the number of times `W` visits a read
  equals the number of times it occurs as a submolecule of the spelled molecule.

The 2016 open question is about "the maximum-likelihood **sequence** is the true
sequence." The sequence-level reading of Section 6.2 is the walk-spelling one;
a non-contiguous flow does not name a sequence. Accordingly this audit
distinguishes:

| reading | candidate `D` is accepted when |
|---------|-------------------------------|
| **weak** (copy vector) | its observed-read copy vector `d_D` is a feasible integer circulation copy vector |
| **strong** (walk spelling, the repository's `F_flow`) | some closed walk in the read overlap graph spells `D` |

## 2. Source-objective verification (source fact / arithmetic)

The certificate's exact objective is the literal Section 6.1 binomial
approximation. The published equations (retrieved from the primary text) are

```text
L[d_1,...,d_{4^k} | x_1,...,x_{4^k}] ≈ ∏ P[X_i = x_i]
    = ∏ C(n, x_i) (d_i / N)^{x_i} (1 - d_i / N)^{n - x_i},

c_i(d_i) = -(x_i log d_i) - (n - x_i) log(N - d_i).
```

The audit reproduces the certificate's two ratios exactly:

| objective | truth | `D = AAAAC` | ratio |
|-----------|-------|-------------|-------|
| Section 6.2 vertex cost | `4096/1953125` | `4608/1953125` | `9/8` |
| full product over all types | `16777216/30517578125` | `294912/244140625` | `1125/512` |

So the arithmetic of the certificate is correct, and the exponent is `n - x_i`
(not `N - x_i`), matching the source.

_Epistemic class: source fact (equations) plus exact arithmetic._

## 3. The witness under the strong reading (mathematical proof)

Truth `S = AAACC`, read length `L = 3`, observed starts `{0, 1, 4}`, observed
read types `{AAA, AAC, CAA}` with counts `x = (1, 1, 1)`. `I_s` holds
(computed), and the truth's copy vector `d_S = (1, 1, 1)` is a feasible
circulation copy vector. But:

**Proposition (the truth is not walk-spellable).** No closed walk in the
overlap graph on `{AAA, AAC, CAA}` spells `S = AAACC`.

**Proof.** In `S`, the window `AAA` occurs only at start `0`, the window `AAC`
only at start `1`, and the window `CAA` only at start `4`; the windows at starts
`2` and `3` are `ACC` and `CCA`, which are not observed read types. A closed walk
that spells `S` must place each visited read at an occurrence of that read type
in `S`. The observed overlaps give `AAC` exactly one outgoing edge, `AAC → CAA`
of length `1`, i.e. shift `L - 1 = 2`. Hence a walk through the mandatory `AAC`
at position `1` must place `CAA` at position `1 + 2 = 3`. But `S`'s window at
position `3` is `CCA`, and its only `CAA` window is at position `4`; the forced
placement contradicts `S`. ∎

The competitor `D = AAAAC` **is** walk-spellable: the closed walk

```text
AAA --2--> AAA --2--> AAC --1--> CAA --2--> AAA
```

has edge shifts `1, 1, 2, 1` (sum `5 = |D|`), places the reads at starts
`0, 1, 2, 4` of `D`, and spells `D` exactly. So the competitor corresponds to a
genuine Section 6.2 flow solution even in the strong reading, while the truth
does not.

The same defect holds for the relabelled `AAABB / AAAAB` witness and for the
smallest fixed-length instance `S = AACC`, `D = ACAC` (reads `AC, CA`, `L = 2`):
the truth is not spellable, the competitor is. In each case the certificate's
`d_truth feasible: True` is a statement about a feasible **copy vector**, not
about the existence of a flow that spells the truth. For the witness, the
feasible cycle realizing `d_S = (1, 1, 1)` is `AAA → AAC → CAA → AAA` with all
overlaps `1`; it spells a length-6 genome, not `S`.

_Epistemic class: mathematical proof (Proposition) plus exact finite
verification (walk enumeration)._

## 4. Consequence for the certificate

- The competitor is flow-feasible under both readings, so the fixed-length
  binomial counterexample is not blocked by Section 6.2.
- The truth is flow-feasible only under the **weak** reading. Under the
  **strong** reading used elsewhere in the repository to call this `F_flow`
  ("a candidate is accepted when it is spelled by a closed walk"), the truth is
  not in the candidate set at all. In that case the comparison "the competitor
  beats the truth" compares a feasible sequence against an infeasible one, and
  the instance is ill-posed for the published bridging-to-ML question.
- The certificate's phrase "a flow realizes a circular assembly `D` exactly
  when its copy vector equals `d_D`" is therefore too strong: a flow with copy
  vector `d_D` realizes a *non-contiguous* assembly whose per-type counts match
  `d_D`; a single spelled sequence requires a closed walk.

## 5. Bounded search for a source-faithful sequence-level counterexample

To see whether the obstruction is specific to this witness, the audit searches
finite instances where the truth **is** a sequence-level Section 6.2 solution
(`S` walk-spellable) and asks for a same-length competitor `D` that is also
walk-spellable and strictly beats the truth under the literal Section 6.2
vertex cost `∏_v (d_v/N)^{x_v}(1-d_v/N)^{n-x_v}` with `N = |S|`.

| scope | truth-flow-feasible instances | sequence-level counterexamples |
|-------|------------------------------|-------------------------------|
| binary, `G = 3..8`, with `I_s` | 17596 | **0** |
| ternary, `G = 3..5`, with `I_s` | 1232 | **0** |
| control: coverage only (repeat-bridging clauses of `I_s` dropped), binary `G = 3..7` | 8328 | **234** |

The control's smallest counterexample is `G = 5`, `L = 2`, truth `AAAAC`
(starts `{1, 3, 4}`), competitor `AACAC`, observed `x = (1, 1, 1)`,
vertex-cost ratio `27/16`. It does not satisfy `I_s` (the `A`-run triple repeat
is not all-bridged; verified in the script). Thus the bridging hypothesis is
load-bearing under the sequence-level flow reading too, mirroring the
per-occurrence `F*` result on branch `agent/fixed-length-flow-repeat`.

_Epistemic class: bounded exhaustive computational evidence. The absence of a
counterexample is not a proof beyond the stated finite scope; the conjecture
that `I_s` plus `S ∈ F_flow` implies the truth is a maximizer is not established._

## 6. Modeling forks recorded, not resolved

1. **Weak versus strong Section 6.2 reading.** This is the fork that determines
   the answer. The audit does not select one by fiat; it reports the answer
   under each (weak: the witness is a counterexample at the flow level; strong:
   the truth is not even feasible).
2. **Bidirected / reverse-complement semantics.** Section 6.2's graph is
   double-stranded. The walk enumeration above uses the single-strand
   specialization shared with the Shomorony exposition and with the certificate.
   The obstruction in Section 3 is nevertheless stranding-orthogonal: the truth's
   observed placements are at starts `{0, 1, 4}` of the 5-cycle, so, whatever
   the orientation convention, some cyclic gap between consecutive observed
   placements has length `3`. Consecutive reads of a closed walk have shift
   `L - overlap <= L - 1 = 2`, so the walk cannot step across that gap; it would
   need a placed read at position `2` or `3`, whose truth molecule
   (`{ACC, GGT}` or `{CCA, TGG}` under the DNA complement `A<->T`, `C<->G`) is
   not an observed vertex. Reverse-complement overlaps can add edges (for
   example `n(AAC)=GTT` overlaps `n(AAA)=TTT` with length 2), but they connect
   the observed vertices to one another and do not supply the missing
   intermediate molecule. A fully explicit bidirected formulation remains a
   documented fork and should be formalized before any infeasibility claim is
   treated as final.
3. **`omin`.** The witness requires `omin = 1`; with `omin = 2` the read graph
   has no feasible circulation at all (neither the truth nor the competitor copy
   vector), so the instance is ill-posed there. Medvedev–Brudno leave `omin` as
   a free parameter, so this is a parameter choice, not a source contradiction.
4. **Transitive reduction.** The certificate defers transitive reduction. Since
   the strong reading is defined by walk spelling, and transitive reduction
   preserves the set of spelled molecules in the source's claim, this does not
   affect Section 3; the explicit walk for `D` is given in unreduced form.

## 7. Cross-references

| Fact | Repository anchor |
|------|-------------------|
| Certificate under audit (copy-vector reading) | `docs/flow-feasibility-aaacc-witness.md`, branch `agent/flow-model-0919b`, unmerged |
| Source objective and candidate-class distinction | `docs/source-notes/medvedev-brudno-candidate-class.md`; `docs/ml-formalization-contract.md` (Variant F) |
| Per-occurrence `F*` reading and its `I_s` search | `docs/fixed-length-flow-feasible-repeat-search.md`, branch `agent/fixed-length-flow-repeat`, unmerged |
| Section 6.2 flow/non-contiguous interpretation | this note, Section 1; Medvedev–Brudno Section 6.2 |
| Reproducible evidence | `scripts/flow_feasibility_aaacc_audit.py` |
