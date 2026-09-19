# Candidate-genome-class semantics across the ML formulations: reconciliation and mismatch register

_Status: source reconciliation note, 2026-09-19. It fixes what the primary
sources say about the **competitor universe** in each maximum-likelihood layer
under discussion, states which axes are live modeling forks, and records the
conflicts among current repository notes. It is not a new counterexample, it
does not re-derive or kernel-check the binomial objective (issue #32), and it
does not select which Medvedev–Brudno layer the Shomorony et al. (2016) sentence
intends._

Scope boundary: the binomial arithmetic is deliberately **not** reproduced here.
For that, see [`fixed-length-binomial-counterexample.md`](fixed-length-binomial-counterexample.md)
and the audit branches referenced in §4. This note only adjudicates what class of
objects each formulation quantifies over.

## 1. Primary sources re-read for this note

- Paul Medvedev and Michael Brudno, “Maximum Likelihood Genome Assembly,”
  *Journal of Computational Biology* 16(8), 2009, 1101–1116,
  DOI <https://doi.org/10.1089/cmb.2009.0047>, full text
  [PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/), re-read
  2026-09-19 in this packet.
- Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, and David N. C. Tse,
  “Information-optimal genome assembly via sparse read-overlap graphs,”
  *Bioinformatics* 32(17), 2016, i494–i502,
  DOI <https://doi.org/10.1093/bioinformatics/btw450>. The open-question
  sentence and its scoping to `I_s` are treated as established by the locked
  ground truth [`literature-status.md`](literature-status.md) and are not
  re-quoted beyond the candidate-class point.
- Guy Bresler, Ma'ayan Bresler, and David Tse, “Optimal assembly for high
  throughput shotgun sequencing,” *BMC Bioinformatics* 14(Suppl 5):S18, 2013,
  DOI <https://doi.org/10.1186/1471-2105-14-S5-S18>, for the same-length
  equal-likelihood obstruction.

## 2. Candidate class by formulation

Medvedev–Brudno §6.1 introduces the candidate directly (source fact):

> “Let `D` be a circular genome of length `N(D)`, and let `d_i` denote the
> number of times the `k`-molecule `i` appears in `D`. … In each trial, a
> position is uniformly sampled from `D` and the outcome of the trial is the
> `k`-molecule beginning at that position. For a given `i`, the probability
> that the outcome of a single trial is `i` is simply `d_i/N(D)`.”

with the displayed multinomial constraint `N(D) = Σ_i d_i`.

| Axis | Variant E — exact §6.1 multinomial | Variant A — literal §6.1 product-of-binomial-marginals | Variant F — §6.2 biflow |
|---|---|---|---|
| Shape of a competitor | Circular genome (`D` a circular genome) | Circular genome realizing a copy-count vector; the scored object is `(d_i)` | A biflow on the transitively reduced bidirected overlap graph built from the reads |
| Length | Intrinsic `N(D) = Σ_i d_i`; no external constraint | Not stated. Denominator is fixed external `N`; whether competitors are restricted to `|D| = N` is **MM1** below | Implicit in the flow/overlap graph; not an external parameter |
| Read-type space | `4^k` k-mers (source says “there are `4^k` such variables”); see **MM4** | Same `4^k` index set | Vertices are the observed reads, not k-mer types |
| Realizability constraint | A candidate must be a genome realizing `(d_i)`; §6.1 does not spell out the realizable set | A candidate must be a genome realizing `(d_i)` and satisfy `d_i ≤ N` for every `i` | Flow conservation, balances, edge/vertex bounds |
| Read-support / flow constraint | None beyond realizability | None beyond realizability | **Yes**: graph is read-derived; every read vertex has lower bound `1` |
| Genome identity | Cyclic shift required by the 2016 circular model; reverse-complement unresolved | Cyclic shift; reverse-complement unresolved | Bidirected graph inherits the double-strand convention; a flow may be a non-contiguous assembly |
| Source basis | §6.1 body + displayed `M26/M27/M30` | §6.1 second half + displayed `M31/M33` | §6.2 |

**Source fact (2016 model fixes the truth, not competitors).** Shomorony et al.
§2 fix the true circular sequence `s` to length `G` and sample `N` length-`L`
reads uniformly from its `G` circular start positions. Neither the 2016 main text
nor the cited Medvedev–Brudno passage states that maximum-likelihood competitors
must have length `G`. Transferring `|D| = G` (or `|D| = N`) to the competitor
universe is an **additional model restriction**, not a default. This agrees with
[`ml-formalization-contract.md`](ml-formalization-contract.md) §“Candidate-universe
discipline” and [`literature-status.md`](literature-status.md) §12.2.

## 3. Axes that could invalidate or strengthen a current counterexample

### 3.1 Circular versus linear competitors

The §6.1 objective is defined on a **circular** genome. The normalization
`N(D) = Σ_i d_i` holds precisely because a circular genome has exactly `N(D)`
length-`k` start positions. A **linear** candidate of length `M` has `M − k + 1`
windows (for `M ≥ k`), not `M`, so `d_i/N(D)` is not its sampling probability
and `Σ_i d_i = N(D)` fails. Admitting linear competitors therefore changes the
objective, not merely the candidate set, and requires a separately named model.

Consequence for the current witnesses: all repository competitors are circular,
so none is invalidated by this axis. Conversely, a reader who silently allows
linear competitors would be extending the source model and could introduce
competitors of a different length budget; that possibility should be handled as
a named variant, not folded into Variant E.

### 3.2 Read-type space: `4^k` k-mers versus reverse-complement classes (MM4)

§6.1 says the candidate is built from `k`-molecule types and that “there are
`4^k` such variables,” and the displayed formula (`M27`) indexes `i` over `4^k`
types. But §3.1 defines “A DNA molecule” as “an unordered pair of strings … that
are reverse complements of each other.” Taken literally, the molecule type space
is smaller than `4^k` (roughly half, up to reverse-complement palindromes), so
the “`4^k`” statement and the molecule definition are in tension. This is a
**source-internal** ambiguity, not a repository invention.

The literal formula and the current kernel-checked witnesses use the `4^k`
k-mer indexing. If a later source reading quotients the type space by reverse
complement, the occurrence counts `d_i` change and the likelihood comparison must
be redone. The effect is not cosmetic:

- **Fixed-length exact `AAABB`/`AAAAB` witness
  ([`fixed-length-exact-counterexample.md`](fixed-length-exact-counterexample.md)).**
  The observed types `AAA, AAB, BAA` have pairwise distinct reverse-complement
  classes, and the extra `AAA` occurrence in `AAAAB` stays in its own class, so
  the ratio `2` is unchanged under reverse-complement class counting.
- **Unrestricted-length exact `ACGT`/`ACACGT` witness
  ([`exact-variant-e-counterexample.md`](exact-variant-e-counterexample.md)).**
  Under `4^k` k-mer indexing the exact likelihoods are `3/64` and `1/18`, giving
  the strict difference `5/576 > 0`. Under reverse-complement class counting the
  two sides tie exactly: the observed reads `AC, AC, GT` all fall in the class
  `{AC, GT}`, the truth `ACGT` has class count `2` of `4`, and `ACACGT` has class
  count `3` of `6`, so both likelihoods equal `(1/2)^3 = 1/8`. The witness still
  refutes the **uniqueness** schema (the two genomes are non-equivalent and of
  different lengths), but it would no longer refute the **truth-is-a-maximizer**
  schema. This is a genuine scoping condition on the existing negative result.
- **Binomial `AAACC`/`AAAAC` witness
  ([`fixed-length-binomial-counterexample.md`](fixed-length-binomial-counterexample.md)).**
  As in the fixed-length exact case, the observed classes are distinct and the
  repeated `AAA` stays in its own class, so the `1125/512` ratio is unchanged.

Epistemic status: the `4^k` reading is the literal displayed formula and is what
the kernel-checked Lean modules implement. The tie computation above is an
algebraic scoping observation, **not** kernel-checked. The correct durable
conclusion is: the exact `ACGT`/`ACACGT` refutation of the maximizer schema is
conditional on the `4^k` k-mer type space, and that condition should be visible
in any correspondence claim that leans on it.

### 3.3 Fixed versus variable candidate length (MM1)

Variant E uses the candidate’s own length; Variant A replaces `N(D)` by an
external `N`. These are different probability models. Whether Variant A
*additionally restricts competitors to `|D| = N`* is not stated in the source and
is the live repository mismatch MM1 (§4).

For the current witnesses this axis is benign: every existing competitor pair is
**same-length** (`|S| = |D| = G = N`), so each counterexample lies inside the
intersection of the two readings and its conclusion is robust to MM1. The
unrestricted-length `ACGT`/`ACACGT` witness is not affected by MM1 because it
targets Variant E, where intrinsic length is a source fact.

### 3.4 Read support / flow feasibility (Variant F)

Variant F is the only layer whose competitor class is constrained by the
observed reads: the graph vertices are the reads, the graph is transitively
reduced, and every read vertex has lower bound `1`. §6.2 states this directly:

> “Each vertex has a lower bound of 1 since it represents a read that must be
> present in the genome at least once. All other lower bounds are 0 and all
> upper bounds are infinity.”

and

> “Since any flow can be decomposed into a collection of walks, our flow
> represents a (non-contiguous) assembly of the genome, and the flow going
> through each vertex represents the number of time the read is present in the
> assembly.”

So Variant F competitors are read-supported flows and need not be contiguous,
circular genomes. A theorem over Variant F must not be presented as a theorem
over Variant E’s candidate universe without a correspondence argument. This
fork is already recorded in
[`ml-formalization-contract.md`](ml-formalization-contract.md) (Variant F) and
[`source-notes/medvedev-brudno-candidate-class.md`](source-notes/medvedev-brudno-candidate-class.md)
§3. Feasibility of the `AAACC` witness for the §6.2 flow problem is treated on a
separate branch and is out of scope here.

## 4. Mismatch register (durable)

These are current repository statements that conflict or that extend the source.
They are recorded, not silently resolved where the source does not decide.

### MM1 — Variant A competitor universe

- **Reading A1 (external `N` is a denominator only):** the approximation scores
  free copy-count vectors `(d_i)` subject to `0 ≤ d_i ≤ N`; it does not impose
  `Σ_i d_i = N` and does not fix candidate length. Sources:
  `agent/candidate-class-0919b:docs/source-notes/candidate-class-resolution.md`
  §2; `analysis/fixed-length-binomial-source-fidelity:docs/source-notes/fixed-length-binomial-source-fidelity.md`
  §3; `agent/candidate-length-source-note:docs/source-notes/candidate-length-semantics.md`
  §1/§4; `agent/ml-layer-source-verification:docs/source-notes/ml-objective-candidate-class-resolution.md`
  §6.
- **Reading A2 (approximation restricts to length `N`):** replacing `N(D)` by
  the known true `N` restricts competitors to `Σ_i d_i = N`; candidates of
  length `≠ N` are not source-supported. Source:
  `audit/issue32-end-to-end:docs/audit-issue32-end-to-end.md` §3.
- **Assessment.** The source passage changes the **denominator**, not the
  candidate universe; it explicitly calls the result an approximation and never
  states a competitor-length constraint. A2 reads a derivation-based domain
  restriction into the displayed product. Because both readings contain every
  same-length witness, the existing `AAACC`/`AAAAC` result is unaffected; but
  any statement that Variant A is refuted at *arbitrary* competitor length must
  carry the A1 restriction as a named hypothesis until the source is stronger.
- **Citation defect.** `audit-issue32-end-to-end.md` §3 attributes the A1 claim
  to `docs/source-notes/candidate-genome-class-resolution.md` §2.2. No branch
  contains a file with that exact name; the file is
  `docs/source-notes/candidate-class-resolution.md` (branch
  `agent/candidate-class-0919b`). Future reconciliations should use the actual
  path.

### MM2 — Does fixed-length Variant A coincide with fixed-length Variant E?

`agent/fixed-length-expanded-search:docs/candidate-length-freedom-characterization.md`
§3.4 and §6 state that “for fixed-length candidates, Variant A reduces to the
same objective as Variant E.” This is **false as stated**: fix `N` and compare

- Variant E: `∝ N^{-n} ∏_i d_i^{x_i}`;
- Variant A: `∝ ∏_i d_i^{x_i} (N-d_i)^{n-x_i}`.

The extra `(N-d_i)^{n-x_i}` factors are candidate-dependent whenever some
`n - x_i > 0`, so the two objectives order competitors differently. The
`AAACC`/`AAAAC` instance exhibits this numerically: ratio `2` under fixed-length
exact E versus `1125/512` under the literal binomial objective. The source
displayed equations `M31`/`M33` and
`audit/issue32-end-to-end.md` §2 support the non-equivalence. The
characterization note should be corrected to use the binomial objective’s
actual cost, or to state the reduction it relies on (for example, dropping
zero-count factors is a further, separately named simplification).

### MM3 — Linear versus circular

No live conflict: `literature-status.md` §12 and the §6.1 text make the
competitor circular. Recorded here because a linear reading is a recurrent
temptation and is not equivalent (§3.1).

### MM4 — `4^k` k-mer types versus reverse-complement classes

Source-internal tension in Medvedev–Brudno §3.1 versus §6.1; see §3.2. The
repository’s kernel-checked modules use `4^k`; the alternative reading changes
the exact `ACGT`/`ACACGT` witness from a strict inequality to a tie.

### MM5 — Naming: “fixed-length binomial” versus “fixed-external-`N` binomial”

Several notes and file names call Variant A the “fixed-length” objective. That
name fuses the denominator substitution (source fact) with a candidate-length
restriction (not stated). Recommended durable name: **fixed-external-`N`
binomial approximation**, with any `|D| = N` restriction carried as a separate
named hypothesis. This is a wording correction only; it does not change any
arithmetic or the kernel-check boundary for issue #32.

### MM6 — Accepted 2016 supplement not independently recovered

Carried forward from
[`source-notes/shomorony-ml-reference.md`](source-notes/shomorony-ml-reference.md)
and [`ml-formalization-contract.md`](ml-formalization-contract.md): the accepted
main text has been re-verified, but the publisher supplement
(`bioinformatics_32_17_i494_s1.zip`) has not been independently inspected.
Nothing in this note depends on it.

## 5. Impact summary for current counterexamples

| Witness | Variant / universe | Length reading | `4^k` vs RC classes | Survives? |
|---|---|---|---|---|
| `ACGT` vs `ACACGT` ([`exact-variant-e-counterexample.md`](exact-variant-e-counterexample.md)) | Exact E, unrestricted length, kernel-checked | Intrinsic (E) — robust | Refutes maximizer + uniqueness under `4^k`; tie under RC classes (refutes uniqueness only) | Conditional on `4^k` for the maximizer claim |
| `AAABB` vs `AAAAB` ([`fixed-length-exact-counterexample.md`](fixed-length-exact-counterexample.md)) | Exact E, `\|D\| = G` restriction, kernel-checked | Same-length — robust to MM1 | Distinct classes; ratio `2` unchanged | Robust |
| `AAACC` vs `AAAAC` ([`fixed-length-binomial-counterexample.md`](fixed-length-binomial-counterexample.md)) | Literal Variant A, same-length competitor | Same-length — robust to MM1/A1 vs A2 | Distinct classes; ratio `1125/512` unchanged | Robust (within its named objective) |

The common structural reason the bridging hypothesis does **not** constrain the
Variant E/A competitor pool is that bridging constrains the true realization
(coverage and repeat copies of `s`), whereas a Variant E/A competitor enters only
through its own occurrence vector `(d_i)`, with no requirement that the observed
reads be supported by it. Variant F is the only layer where the observed-read
overlap graph restricts competitors; this is why the frontier has moved to it.

## 6. Epistemic classification

| Claim | Class | Basis |
|---|---|---|
| §6.1 candidate is a circular genome with intrinsic `N(D) = Σ_i d_i` | Source fact | §6.1 body + `M26/M27/M30` |
| §6.1 index set is `4^k` types | Source fact | §6.1 body (“`4^k` such variables”) |
| “DNA molecule” is an unordered reverse-complement pair | Source fact | §3.1 |
| `4^k` versus reverse-complement molecule classes is internally unresolved | Source-internal tension | §3.1 vs §6.1 |
| §6.1 imposes no fixed competitor length | Source reading (well-supported) | No restriction appears; length is candidate-internal |
| Variant A replaces `N(D)` by external `N` | Source fact | §6.1 second half |
| Variant A does or does not restrict `|D| = N` | **Unresolved (MM1)** | No source statement |
| Fixed-length A and fixed-length E coincide | **False (MM2)** | `M31/M33` zero-count factors; `1125/512` vs `2` |
| Linear competitors are outside §6.1 | Source reading | `N(D) = Σ_i d_i` requires circular windows |
| §6.2 competitors are read-supported biflows, possibly non-contiguous | Source fact | §6.2 |
| Reverse-complement quotient turns `ACGT`/`ACACGT` into a tie | Computation (not kernel-checked) | §3.2 |
| Which 2009 layer the 2016 sentence intends | Unresolved | [`source-notes/shomorony-ml-reference.md`](source-notes/shomorony-ml-reference.md) |

## 7. Handoff

- When naming or formalizing Variant A, use “fixed-external-`N` binomial
  approximation”; expose any fixed-length restriction in the theorem type.
- Keep `4^k` k-mer indexing explicit in any statement that rests on the exact
  strict-inequality witnesses, and record the reverse-complement alternative as
  a fork rather than silently adopting one.
- Reconcile MM1 and correct MM2 on the affected branches before any of those
  notes are treated as source-locked.
- Do not upgrade any scoped Variant E/A result into a settlement of the 2016
  question; the layer choice remains unresolved.
