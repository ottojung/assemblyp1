# Candidate length versus the likelihood's external `N`: resolution from Medvedev–Brudno and Shomorony

_Status: focused primary-source resolution, 2026-09-20. Resolves, on the
Medvedev–Brudno (2009) side, whether maximum-likelihood candidates are
constrained to the known true genome length `N` or merely scored with an
external `N`. Every claim is labelled **source fact**, **source-supported
inference**, **interpretation**, **mathematical fact**, or **open**._

_Companions: [`medvedev-brudno-candidate-class.md`](medvedev-brudno-candidate-class.md)
(`N(D)` vs approximation vs §6.2), [`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md)
§8.2, [`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md) §6,
and [`../bridging-se62-flow-ml-counterexample.md`](../bridging-se62-flow-ml-counterexample.md) §0.
This note isolates one axis those documents leave partly entangled: a fixed
value in the objective versus a restriction on the candidate set._

---

## 0. Question and verdict

Three readings of the Medvedev–Brudno maximum-likelihood object:

1. **Candidate-length constraint.** Competitors are restricted to genomes of
   length `N` (the known/true length).
2. **External likelihood parameter.** Candidates may have any length; `N`
   appears only as a fixed constant inside the likelihood.
3. **Flow-feasible class.** Candidates are integer bidirected flows of MB09
   §6.2; `N` appears only in the vertex cost.

**Verdict.** On the Medvedev–Brudno side, readings 2 and 3 hold and reading 1
does not. No MB09 layer imposes `|D| = N`. The exact multinomial uses the
candidate's intrinsic `N(D)`; the separable/binomial approximation explicitly
replaces the *constant* `N(D)` by an external `N` and drops (rather than adds)
the multinomial coupling; and the §6.2 search space is a flow polytope whose only
length-like bounds are the per-vertex lower bound `1` and the per-type domain
`d_i < N`. [source fact + source-supported inference; §1–§3]

**Consequence.** The length change in the merged `AAATT (|S| = 5) → AAAATT
(|D| = 6)` witness, scored with external `N = 5`, violates no MB09 length
constraint. It is admissible under readings 2 and 3. Excluding it requires an
*added* restriction `|D| = N` that MB09 never states. [mathematical fact given
§1–§3]

**Scope.** This note resolves only the candidate-length axis. Which MB09 layer
the 2016 sentence intends, and the strand/tie/equivalence conventions, remain
open.

---

## 1. MB09 §6.1, exact multinomial: candidate-intrinsic `N(D)`

Primary source: Paul Medvedev and Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116, §6.1,
[PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/).

Verbatim:

> “Let `D` be a circular genome of length `N(D)`, and let `d_i` denote the
> number of times the `k`-molecule `i` appears in `D`. … In each trial, a
> position is uniformly sampled from `D` and the outcome of the trial is the
> `k`-molecule beginning at that position. For a given `i`, the probability that
> the outcome of a single trial is `i` is simply `d_i/N(D)`.”

The likelihood is the multinomial

```text
L_exact(D | x) = n! / (∏ᵢ xᵢ!) · ∏ᵢ (dᵢ / N(D))^{xᵢ},
```

and MB state that the multinomial “has the constraint that `N(D) = Σ_i d_i`”
(this exact wording is in the 2010 dissertation, Ch. 4; the paper’s equation is
an image). [source fact]

**Reading.** `N(D)` is an intrinsic property of the candidate `D`, introduced as
“a circular genome of length `N(D)`”. The coupling `Σ_i d_i = N(D)` ties a
candidate’s count vector to *its own* length; it is **not** a constraint that
`N(D) = N`. Nothing in §6.1 restricts candidates to the true length. [source fact
+ source-supported inference]

---

## 2. MB09 §6.1, separable/binomial approximation: external `N`

Verbatim:

> “Because in the binomial approximation the length of the genome `N(D)` is a
> constant that is independent of each `d_i`, we can replace it by `N`, which is
> the length of the actual genome from which the reads were sampled. … **For our
> experiments, we assume that the genome size is known.**”

The approximate objective (dissertation form) is separable:

```text
−log L ≈ K + Σᵢ cᵢ(dᵢ),   cᵢ(dᵢ) = −xᵢ log dᵢ − (n − xᵢ) log(N − dᵢ),
```

with `N` the externally supplied constant. [source fact]

**Why this is reading 2, not reading 1.**

- The sentence is about replacing a *value inside the objective*, not about
  restricting the candidate set. MB never write “candidates have length `N`”.
  [source fact]
- In the exact multinomial `N(D) = Σ_i d_i`, so `N(D)` is *not* independent of
  the `d_i`. Declaring it “a constant that is independent of each `d_i`” is
  precisely the step that removes the simplex coupling and makes the cost
  separable. The approximation can therefore only *relax* the length coupling;
  it cannot introduce `|D| = N`. [source-supported inference]
- The binomial factors require `d_i > 0` and `N − d_i > 0`, i.e. the per-type
  domain `0 < d_i < N`. This is a per-type cap (a probability denominator), not
  a total-length constraint. The total `Σ_i d_i` is unconstrained and may exceed
  `N`. [source-supported inference; cf. reconciliation note §2.2, §6]

---

## 3. MB09 §6.2, the actual optimization: no length variable

Verbatim §6.2:

> “The vertices of this graph are the reads … Each vertex has a lower bound of 1
> since it represents a read that must be present in the genome at least once.
> **All other lower bounds are 0 and all upper bounds are infinity.** … By
> Observation 7, the `d_i`’s described above actually correspond to the value of
> the flow through vertex `i`, and we let `c_i` be the convex cost functions for
> the vertices.”

**Trace of the variables.** The decision variables are the edge/vertex flows.
The only bounds enumerated are `l(vertex)=1` on read vertices, `l=0` elsewhere,
and `u=∞`; the supersource/sink edges carry prohibitively large costs and are
minimized, not bounded by a length. There is no aggregate constraint on total
flow and no constraint tying the spelled molecule’s length to `N`. `N` enters
only through the vertex costs `c_i(d_i) = −x_i log d_i − (n−x_i) log(N−d_i)`.
[source fact + source-supported inference]

The output is explicitly “a (non-contiguous) assembly of the genome”, not
necessarily a single sequence of any prescribed length. [source fact]

**Reading.** In the layer MB actually calls its algorithm, the candidate class
is a flow polytope; candidate length is not among its constraints. [source-
supported inference]

---

## 4. Implementation evidence that `N` is a soft parameter

Verbatim §8.2:

> “Our algorithm relies on having an estimate on the length of the genome, and
> we tested to what extent the accuracy is affected when the length is
> mis-estimated. Running our algorithm using a length that was 10% shorter on
> the 75× 3k dataset, we made 84 off-by-one errors (a 2.3-fold increase)… For a
> length that was 10% longer, we made 351 off-by-one errors, a 9.5-fold
> increase… As expected, when the length estimate was made shorter, most of the
> errors were under-estimations of the actual counts, while the opposite
> occurred when the length was made longer.”

[source fact]

**Reading.** If `N` were a hard candidate-length constraint, mis-estimating it
would redefine the candidate space; the reported behaviour is instead a graded,
monotone shift of predicted copy counts (shorter `N` biases counts down, longer
`N` biases them up) while the algorithm still runs and remains useful. That is
exactly the behaviour of `N` as a cost-function parameter. §6.1 likewise calls
the approximate length something to be “ascertained … or through an
Expectation-Maximization type approach”, i.e. an estimable parameter, not a
structural identity of the candidate. [source-supported inference]

---

## 5. The Shomorony (2016) side

- The accepted 2016 text contains no likelihood formula, no occurrence of
  “multinomial”/“binomial”, no mention of the §6.2 flow, and no statement about
  competitor length. It names Medvedev–Brudno only by bibliography and the
  phrase “maximum-likelihood formulation of the AP”. [source fact; recorded in
  [`shomorony-ml-reference.md`](shomorony-ml-reference.md) and
  [`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md)
  §2.1]
- Section 2 of Shomorony et al. fixes the *true* circular genome to length `G`
  for the data-generating model. It says nothing about ML competitors. [source
  fact]
- The only same-length likelihood statement in the Shomorony author-hosted
  version/supplement is attributed to **Bresler, Bresler & Tse (2013)**:
  “there is another sequence `s'` **of the same length** under which the
  likelihood of observing the reads is the same” (Shomorony supplement,
  Theorem 2; Bresler et al. 2013, Theorem 1). [source fact]

**Interpretation.** Bresler’s same-length result is a property of the
fixed-`G` feasibility/data-generating model, and the open-question sentence
cites MB09, not Bresler. It therefore does not transfer a fixed-length
constraint onto the MB09 referent. Conversely, if the sentence were read as the
paper’s own Bresler-style likelihood, competitors would be same-length; but that
substitutes a different cited object for the one named. Either way the
candidate-length axis is not settled in favour of MB09 reading 1.

---

## 6. Consequences for repository state

1. **The merged §6.2 witness stands on its length axis.** `AAATT → AAAATT`
   (`|D| = 6`, external `N = 5`) does not violate any MB09 length constraint; it
   is admissible under readings 2 and 3, as already recorded in
   [`../bridging-se62-flow-ml-counterexample.md`](../bridging-se62-flow-ml-counterexample.md) §0
   and [`../section62-mb09-bidirected-graph-audit.md`](../section62-mb09-bidirected-graph-audit.md).
   [mathematical fact given §1–§3]
2. **`|D| = N` is an added restriction.** Any statement proved or refuted only
   over length-`N` competitors must name that restriction; it does not follow
   from MB09. This matches
   [`../ml-formalization-contract.md`](../ml-formalization-contract.md) §“Candidate-universe
   discipline” and §“Variant E”. [source-supported inference]
3. **Correction to an unmerged note.** The unmerged branch note
   `docs/source-notes/candidate-length-semantics.md` (branch
   `agent/candidate-length-source-note`) states in its §4: “The binomial
   approximation fixes competitor length to a constant.” That sentence conflates
   a fixed *objective parameter* with a candidate-set constraint and should not
   be merged as written; its other statements (exact multinomial admits
   arbitrary nonempty length; the open question does not select a convention)
   are consistent with this note. [mathematical/source-supported correction]
4. **`ml-formalization-contract.md` “whether competitors must have length `G`”.**
   This remains open as a question about which variant the 2016 sentence
   intends, or whether an independent restriction is added. It should not be
   read as a live ambiguity in MB09’s own equations, which admit arbitrary
   candidate length in every layer. [interpretation]

---

## 7. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| MB09 §6.1 exact multinomial uses candidate-intrinsic `N(D)` and imposes `Σ_i d_i = N(D)`, not `N(D) = N` | source fact | MB09 §6.1; 2010 thesis Ch. 4 |
| MB09 §6.1 approximation replaces the constant `N(D)` by external `N` and assumes the genome size is known | source fact | MB09 §6.1 |
| Declaring `N(D)` independent of the `d_i` removes the multinomial coupling rather than adding `|D| = N` | source-supported inference | MB09 §6.1 |
| Approximation domain is per-type `0 < d_i < N`; total `Σ d_i` is unconstrained | source-supported inference | objective form; reconciliation §2.2, §6 |
| MB09 §6.2 bounds are per-vertex (`l = 1` on reads, `0` else, `u = ∞`) with no aggregate length constraint | source fact | MB09 §6.2 |
| MB09 §8.2 tests `N` mis-estimation with graded, monotone count shifts | source fact | MB09 §8.2 |
| `N` is a soft cost parameter, not a hard candidate-length constraint | source-supported inference | §6.1, §8.2 |
| The 2016 accepted text states no likelihood formula or candidate-length restriction | source fact | Shomorony et al. 2016 §2, §5; repo notes |
| The only same-length likelihood result in the Shomorony version/supplement is Bresler’s, not MB09’s | source fact | Shomorony supplement Thm. 2; Bresler et al. 2013 Thm. 1 |
| The merged `AAATT → AAAATT` witness violates no MB09 length constraint | mathematical fact given the source readings | this note §1–§3; graph audit |
| Which MB09 layer the 2016 sentence denotes; strand/tie/equivalence conventions | **open** | provenance/reconciliation notes |

---

## 8. Sources

- Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome Assembly*,
  *J. Comput. Biol.* 16(8) (2009) 1101–1116, §6.1–§6.2, §8.2,
  [PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/), DOI
  [10.1089/cmb.2009.0047](https://doi.org/10.1089/cmb.2009.0047).
- Paul Medvedev, *Genome Graphs*, PhD thesis, University of Toronto, 2010,
  Ch. 4 (dissertation version of the above),
  `https://hdl.handle.net/1807/26297`.
- Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
  *Information-optimal genome assembly via sparse read-overlap graphs*,
  *Bioinformatics* 32(17) (2016) i494–i502, §2 and §5,
  DOI [10.1093/bioinformatics/btw450](https://doi.org/10.1093/bioinformatics/btw450);
  author-hosted version `https://web.stanford.edu/~gkamath/nsgIlan.pdf`.
- Guy Bresler, Ma’ayan Bresler, David Tse, *Optimal assembly for high
  throughput shotgun sequencing*, *BMC Bioinformatics* 14(Suppl 5):S18 (2013),
  Theorem 1, [PMC3706340](https://pmc.ncbi.nlm.nih.gov/articles/PMC3706340/).
