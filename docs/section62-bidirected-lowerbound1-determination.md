# Determination under the corrected MB09 §6.2 model: bridging does not force ML-optimality (lower bound 1, bidirected flows)

_Status: source reading + structural reduction + rigorous finite counterexample +
kernel check, 2026-09-20. Independent of the unmerged §6.2 search packets; it
reads them adversarially rather than summarizing them. All claims are labelled
**source fact**, **modeling choice**, **mathematical proof**, **verified
computation**, **kernel-checked**, or **open**._

_Reproduction:_

```sh
python3 scripts/verify_se62_lb1_bidirected_determination.py
lake build AssemblyP1.Section62LowerBoundOneCounterexample
```

## 0. Verdict at a glance

Fix the Medvedev–Brudno §6.2 object as **corrected** in the issue-#36
reconciliation: vertices are read DNA molecules, every read vertex has lower
bound `1` (not `d_i ≥ x_i`), the graph is bidirected and transitively reduced,
the candidate is a flow, and the objective is the §6.1 separable binomial with
the external true genome length `N`. Then the source-faithful implication

> **(P)** `I_s` holds **and** the truth-induced flow `d_S` is an admissible §6.2
> candidate ⇒ `d_S` is a §6.2 maximum-likelihood optimum

is **false**. There is a rigourous counterexample

```text
alphabet   {A, T},  reverse complement A <-> T
truth      S = AAATT    (00011)      G = 5,  L = 3,  N = 5
reads      starts (0, 1, 4)          n = 3
observed   x = { AAA:1, AAT:1, TAA:1 }
truth flow d_S = { AAA:1, AAT:2, TAA:2 }      (x ≤ d_S, and d_S ≥ 1)
competitor D = AAAATT   (000011)     d_D = { AAA:2, AAT:2, TAA:2 }
```

`I_s` holds under the strict bridging predicate; both `S` and `D` are spelled
molecules, hence admissible §6.2 flows (Observation 7); and the literal §6.1
product-of-binomial-marginals ratio with `N = 5`, `n = 3` is

```text
L_{6.1}(D) / L_{6.1}(S) = 9/8 > 1.
```

[mathematical proof + verified computation + kernel-checked]

The structural reason is independent of the witness: the §6.2 objective is
**separable in the vertex throughputs** and is maximised near `d*_w = N x_w / n`,
whereas `I_s` constrains only the *support/ repeat-bridging* structure of the
reads. Bridging can force `d_w ≥ 1`; it cannot force `d_w` to equal `d*_w`.
[mathematical proof; §3]

Two boundary corrections are recorded:

1. **The unmerged "infinite bridging-insufficiency family" is invalid under
   strict bridging.** The family `S = 0^(G-1)1`, `D = 0^(G-2)1`, `L = G-2` has a
   maximal triple repeat of length `G-3`, and no length-`(G-2)` read can strictly
   bridge a `(G-3)`-copy: that needs a read of length `≥ (G-3) + 2 = G-1 > L`.
   Its certificate used a wrap-around "covers both flanks" test, which is not the
   accepted predicate. The **finite** witness above is unaffected. [mathematical
   proof + verified computation; §5]
2. **The corrected lower bound genuinely matters.** The second witness
   `AAATAT → AAATA` has `d_S(AAA) = 1 < x(AAA) = 2`, so it is *excluded* by the
   older per-occurrence reading but *admitted* by the source’s lower bound `1`.
   The first witness satisfies both readings, so the negative answer is robust to
   the per-type/per-occurrence ambiguity. [verified computation; §4]

The note does **not** settle which Medvedev–Brudno layer the 2016 Shomorony
sentence denotes (exact multinomial, separable binomial, or the §6.2 flow
optimisation); it decides the §6.2-restricted implication that the issue-#36
comments identify as the remaining source-faithful residue. [open]

---

## 1. The model, with every assumption named

### 1.1 Source facts

Primary source: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116, §6.1–6.2,
DOI [10.1089/cmb.2009.0047](https://doi.org/10.1089/cmb.2009.0047),
[PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/). Quotations are
as transcribed in the independent source audit
`docs/section62-bidirected-flow-source-fidelity-audit.md` (branch artifact) and
the issue-#36 status comment of 2026-09-20:

- "The vertices of this graph are the reads, and the edges are all possible
  bidirected overlaps of length at least `o_min` … we refer to the resulting
  graph as the transitively reduced bidirected overlap graph."
- "Each vertex has a lower bound of 1 since it represents a read that must be
  present in the genome at least once. All other lower bounds are 0 and all
  upper bounds are infinity."
- **Observation 7.** "The number of times `W` visits `r` is equal to the number
  of times `r` appears a submolecule of the molecule spelled by `W`."
- "Since any flow can be decomposed into a collection of walks, our flow
  represents a (non-contiguous) assembly of the genome."
- §6.1: the objective is the product of per-type binomials
  `∏_w C(n,x_w) (d_w/N)^{x_w}(1-d_w/N)^{n-x_w}`, with `N` the **external** true
  genome length ("we assume that the genome size is known"); the exact
  multinomial’s candidate-intrinsic `N(D)` is replaced by `N`.

Bridging `I_s` is from Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David
N. C. Tse, *Information-optimal genome assembly via sparse read-overlap graphs*,
*Bioinformatics* 32(17) (2016) i494–i502, Eq. (1), attributed to Bresler,
Bresler & Tse (2013): coverage, every triple repeat all-bridged, every
interleaved repeat pair bridged. The strict extension normalization used here is
the repository’s accepted transcription (`docs/bridging-source-semantics.md`):
a read interval `[r, r+L)` on an integer lift bridges the copy `[t, t+ℓ)` iff
`r < t` and `t + ℓ < r + L`. [source fact + modeling normalization]

### 1.2 Assumptions used (explicit)

- **A1.** A read is a DNA molecule = unordered reverse-complement pair; on the
  binary alphabet the involution is `0 ↔ 1`, and a read *type* is the class
  `min(w, rc(w))`. [source fact §3.1 + modeling]
- **A2.** Every read vertex has lower bound `1`; edge lower bounds `0`; upper
  bounds `∞`. The observed multiplicity `x_w` is **not** a lower bound on the
  candidate copy count `d_w`. [source fact §6.2; issue-#36 correction]
- **A3.** Candidate objects are integer flows on the transitively reduced
  bidirected overlap graph; a single molecule is a special case (a circuit).
  [source fact]
- **A4.** The objective is the §6.1 separable binomial with external `N = |S|`
  and `0 ≤ d_w ≤ N`. [source fact]
- **A5.** The genome is circular; starts and windows are cyclic. [source fact]
- **A6.** `o_min` is a free parameter; we use `o_min ≤ L-1`, so consecutive
  length-`L` windows of a molecule overlap by `L-1 ≥ o_min`. The source’s own
  experiments use `o_min < L-1`. [source fact §8.2]
- **A7.** `I_s` uses the strict bridging predicate of §1.1. [modeling
  normalization; see §5 for why the alternative is not the accepted one]
- **A8.** The §6.2 flow optimum minimises the contig-count penalty first; our
  witnesses are single circuits, so they incur no source/sink cost and this
  choice does not affect the determination. [source fact + modeling]

---

## 2. Flow objects are not spellable sequences

The §6.2 candidate is a **flow**, which is explicitly a possibly
**non-contiguous** assembly; it is not, in general, a genome. The bridge between
the two is Observation 7:

> **Lemma 1 (spellable molecule ⇒ feasible flow).** Let `D` be a circular
> molecule spelled by a closed walk `W` in the (transitively reduced) read
> overlap graph. Then its induced vertex-throughput vector
> `d_D(w) :=` number of occurrences of read type `w` in `D` is realised by the
> flow whose edge multiplicities are those of `W`. In particular `d_D` is
> intrinsic to `D` and independent of the choice of walk.

_Proof._ The walk’s edge multiplicities are a nonnegative integral circulation,
so they are a feasible flow; Observation 7 identifies the vertex throughput with
the occurrence counts. Transitive reduction preserves the set of spelled
molecules, so any `D` spelled before reduction is spelled after it, and the
occurrence-count vector is unchanged. ∎ [source fact + mathematical proof]

Consequently, for the single-molecule sub-case the §6.2 feasibility of `D`
reduces to a spelling condition on `D` alone. For the general `o_min < L-1`
criterion (support containment plus `(L-o_min)`-density of observed windows) see
`docs/section62-feasibility-independent-reconstruction.md`; the witnesses below
additionally have **all** windows observed, so they satisfy the strongest
(`o_min = L-1`) form, support equality. [mathematical proof]

This is the distinction the task requires us to keep: `d_S` and `d_D` are flow
objects (vertex throughputs); `S` and `D` are spellable sequences that induce
them.

---

## 3. Structural reduction: separability vs bridging

### 3.1 The objective is separable

Write `n = Σ_w x_w`. The §6.1 log-objective is

```text
log L(d) = Σ_w [ x_w log(d_w/N) + (n − x_w) log(1 − d_w/N) ] + const.
```

It is a sum of one-variable concave functions `g_w(d) = (d/N)^{x_w}(1-d/N)^{n-x_w}`,
each maximised at the real value `d*_w = N x_w / n` (with endpoint cases
`x_w = 0 ⇒ d_w = 0`, `x_w = n ⇒ d_w = N`). Therefore the optimum over any
feasible set depends on the candidate only through the vector `d`, and the
unconstrained target is `d*`. [mathematical proof; standard Bernoulli calculus]

### 3.2 The exact obstruction

**Proposition 1 (under-observation obstruction).** Let `d_S ∈ F` be the
truth-induced §6.2 flow and let `w` be an observed type such that
`d_S + e_w ∈ F`. If

```text
g_w(d_S,w + 1) / g_w(d_S,w)
  = ((d_S,w + 1)/d_S,w)^{x_w} · ((N − d_S,w − 1)/(N − d_S,w))^{n − x_w}
  > 1,
```

then `d_S` is not a §6.2 maximum-likelihood optimum.

_Proof._ All coordinates other than `w` are unchanged, so the likelihood ratio
equals the displayed one-variable ratio; and `d_S + e_w` is feasible. ∎
[mathematical proof]

When `d_S,w < d*_w = N x_w/n` the derivative `∂_w log L ∝ N x_w − n d_S,w` is
positive, so raising `d_w` toward `d*_w` improves; the integer step is exactly
the displayed ratio. In particular:

- **Self-loop corollary.** If the reduced overlap graph has a self-loop at `w`
  (the read molecule `w` has a proper self-overlap of length `≥ o_min`), then
  `e_w` is in the cycle cone and `d_S + e_w ∈ F`; so any under-observed `w` with
  `d_S,w < N` and `g_w(d_S,w+1) > g_w(d_S,w)` defeats the truth.
- More generally, a spelled molecule `D` realising `d_S + e_w` gives the same
  conclusion without appealing to reduction conventions (Lemma 1).

`I_s` is a *lower-bound/spanning* hypothesis: it forces support/coverage and
repeat bridging, both of which are consistent with `d_w = 1`. It does not force
`d_w = d*_w`. Since `n = Σx` can be smaller than `N` (partial coverage in the
statistical sense), `d*_w > 1` for small `x_w`, and the truth’s `d_S,w = 1` is
below target. This is the structural reason bridging cannot force optimality, and
it is independent of the specific numeric witness. [mathematical proof]

### 3.3 Why this does not contradict a positive theorem

A §6.2 optimum is forced only under additional conditions, e.g. `d_S = d*`
(the `n = N` read-tiled slice), a rigid flow set `F = {d_S}`, or a normal-cone
condition over every cycle of the overlap graph. None of these follows from
`I_s`. [mathematical proof; see the KKT packet for the full characterization]

---

## 4. The counterexample, verified

### 4.1 Witness 1: `AAATT → AAAATT`

```text
S = 00011  (AAATT),  L = 3,  starts (0, 1, 4),  N = 5,  n = 3
```

Circular read-molecule classes and spectra (A↦0, T↦1; class = min(w, rc(w))):

| window start | word | class |
|---|---|---|
| 0 | `000` | `000` |
| 1 | `001` | `001` |
| 2 | `011` | `001` (rc of `001`) |
| 3 | `110` | `100` (rc of `100`) |
| 4 | `100` | `100` |

Hence `d_S = {000:1, 001:2, 100:2}` and, for the realised starts,
`x = {000:1, 001:1, 100:1}`. [verified computation]

**`I_s` holds (strict predicate).** Coverage: `[0,3) ∪ [1,4) ∪ [4,7) =
[0,7)` covers `{0,1,2,3,4}`. The only **triple** repeat is the length-`1` run of
`A` at starts `{0,1,2}`, a maximal triple repeat (left flank `T,A` differ; right
flank `A,T` differ). Its copies are bridged by reads at starts `4` (contains
`4,0,1`, strictly containing copy `0` at `-1,0,1` on the lift), `0` (contains
`0,1,2`, copy `1` at `1` strictly inside), and `1` (contains `1,2,3`, copy `2`
strictly inside). The length-`2` repeats (`00` at `{0,1}`, `11` at `{3,4}`) are
ordinary pairs; the four starts `0,1,3,4` do not cyclically alternate between
the two pairs, so the interleaving conjunct is vacuous. No other triple repeat
exists. [mathematical proof + verified computation + kernel-checked]

**Truth and competitor are feasible.** `S` is spelled by its cyclic window
walk; `D = 000011` is spelled by its cyclic window walk
`000,000,001,001,100,100`; all consecutive overlaps are `L-1 = 2 ≥ o_min` for
every `o_min ∈ {1,2}`, and every window is an observed read type. Both satisfy
`x ≤ d` and the lower bound `1`. By Lemma 1 both induce feasible §6.2 flows.
[mathematical proof + verified computation + kernel-checked]

**The competitor strictly wins.** The only coordinate that differs is `000`:
`d_S(000) = 1`, `d_D(000) = 2`, with `x_000 = 1`, `n = 3`, `N = 5`. The
`000` factor ratio is

```text
[(2/5)^1 (3/5)^2] / [(1/5)^1 (4/5)^2]
  = (2·9) / (1·16) = 18/16 = 9/8 > 1,
```

and the other two factors are unchanged. So `L_{6.1}(D)/L_{6.1}(S) = 9/8 > 1`.
[mathematical proof + verified computation + kernel-checked]

### 4.2 Witness 2: `AAATAT → AAATA` (the lower bound matters)

```text
S = 000101 (AAATAT),  L = 3,  starts (0,0,1,3,5),  N = 6,  n = 5
observed x      = { 000:2, 001:1, 010:1, 100:1 }
truth flow d_S  = { 000:1, 001:1, 010:3, 100:1 }
competitor D    = 00010,  d_D = { 000:2, 001:1, 010:1, 100:1 }
```

`I_s` holds strictly (checked); `d_S(000) = 1 < x(000) = 2`, so this truth is
**not** per-occurrence feasible but **is** §6.2-lower-bound-1 feasible. The
`000` and `010` factors give

```text
L_{6.1}(D)/L_{6.1}(S)
  = [(2/6)^2 (4/6)^3 / ((1/6)^2 (5/6)^3)] · [(1/6)(5/6)^4 / ((3/6)(3/6)^4)]
  = (256/125) · (625/243) = 1280/243 ≈ 5.2675 > 1.
```

This is the same instance as the `analysis/se62-actual-flow-feasibility` packet,
independently re-derived and re-certified here under the strict bridging
predicate. [verified computation]

### 4.3 Kernel check

`AssemblyP1/Section62LowerBoundOneCounterexample.lean` kernel-checks Witness 1:
the finite `I_s` certificate, the source-faithful per-type predicate
`FeasibleType` (support equality plus `d_w ≥ 1` on observed vertices) for both
`S` and `D`, and the strict likelihood inequality `lik obs dS < lik obs dD`. The
main theorem

```text
AssemblyP1.Section62LowerBoundOneCounterexample.se62_lower_bound_one_counterexample
  : SourceCertificate ∧ FeasibleType dS obs ∧ FeasibleType dD obs ∧
      lik obs dS < lik obs dD
```

depends only on the three standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`). The file contains no `sorry`, `axiom`, `admit`, or
`native_decide`. [kernel-checked]

---

## 5. Adversarial correction: the unmerged “infinite family” is invalid

An unmerged packet (`analysis/issue36-se62-source-semantics-verify-0920`,
`docs/section62-kkt-and-bridging-family.md`, Theorem 3) claims that for every
`G ≥ 6` the family

```text
truth S = 0^(G-1) 1,  competitor D = 0^(G-2) 1,  L = G−2,
reads = the windows of D placed in S at starts {0} ∪ {2,…,G−1}
```

satisfies `I_s`, with both `S` and `D` admissible and a likelihood ratio
`(1/2)((G-1)/(G-2))^(G-2) > 1`. The ratio computation is correct. The **`I_s`
claim is false** under the repository’s strict bridging predicate.

**Reason (mathematical proof).** `S = 0^(G-1)1` has a maximal triple repeat of
length `ℓ = G-3`: the copies `{0, m, G-1-ℓ}` with `0 < m < G-1-ℓ` satisfy the
three-copy maximality condition (left flanks `1,0,0`; right flanks `0,0,1`).
Strictly bridging an `ℓ`-copy requires a read of length at least `ℓ + 2 = G−1`,
because the read must contain the copy and extend at least one base on **each**
side. But `L = G−2 < G−1`, so **no** length-`L` read can bridge such a copy.
Hence `I_s` fails; in fact the copy at `t = G-1-ℓ = 2` is unbridged for the
read set `{0} ∪ {2,…,G−1}` for every `G ≥ 6`. [mathematical proof + verified
computation]

**Where the branch proof goes wrong.** It asserts “a read bridges a copy at `t`
when it contains both `t−1` and `t+ℓ`.” On a circle that is not equivalent to
bridging: a read can cover both flanking positions by wrapping the **other way**
around without containing the copy. For `G = 6`, `ℓ = 2`, the copy at `t = 2`
(positions `2,3`) has flanks `1` and `4`; the read at start `4` covers
`4,5,0,1` and so contains both flanks but not the copy. The branch’s
case analysis accepts it, and `I_s` is wrongly declared to hold. The repository
has already fixed the strict normalization in `docs/bridging-source-semantics.md`
(`r < t` and `t+ℓ < r+L`), under which the copy is not bridged.
[mathematical proof + verified computation]

**Consequence.** The infinite-family negative result is **not established**.
The finite Witness 1 is unaffected (it has no long triple repeat: its only
triple repeat has length `1`, and `ℓ + 2 = 3 = L` is bridgeable). A correct
infinite family remains **open**; the finite witness already refutes (P), so
this does not change the determination. [open]

---

## 6. Relation to existing artifacts

| Artifact | Claim | Status after this note |
|---|---|---|
| `docs/bridging-se62-flow-ml-counterexample.md` (branch) | `AAATT`, `9/8`, per-occurrence predicate | witness valid; relabelled to the source-faithful lower bound `1` and kernel-checked as `FeasibleType`; §2’s per-occurrence *criterion* is not the §6.2 rule (the witness satisfies both anyway) |
| `docs/section62-actual-flow-feasibility.md` (branch) | `AAATAT`, per-type, flow optimum `AAATA` | independently reproduced; strict `I_s` re-certified; ratio `1280/243` |
| `docs/section62-kkt-and-bridging-family.md` Theorem 3 (branch) | infinite family satisfying `I_s` | **refuted under strict bridging**; ratio identity itself correct |
| `docs/section62-nonspellable-flow-counterexample.md` (branch) | per-occurrence string-graph zero | consistent: it uses per-occurrence truth feasibility, which excludes Witness 2; does not bear on the corrected lower bound `1` |
| `docs/section62-bidirected-flow-source-fidelity-audit.md` (branch) | no source-faithful bidirected model exists | this note is a determination at the sequence/circuit level via Observation 7, which is reduction- and orientation-robust |
| `docs/section62-aaatt-reduced-flow-cone-and-spectra.md` (this branch) | exact §6.2 copy-count cone of Witness 1's reads | **extends** the witness check: with Myers transitive reduction every closed §6.2 flow on `{AAA, AAT, TAA}` has `d_AAT = d_TAA`, so the feasible cone is `{(a,k,k)}`, `(1,2,2)` and `(2,2,2)` are real, and `(2,2,1)` is **not** a closed flow; also isolates that the finite `FeasibleType` predicate does not encode conservation |

The last row matters for the scope of the kernel-checked witness: `FeasibleType`
(support equality plus `d_w ≥ 1`) admits `(2,2,1)`, so it is a sufficient
finite certificate, not §6.2 feasibility. The witness itself is unaffected — its
`d_S = (1,2,2)` and `d_D = (2,2,2)` are genuine circuits — but the phrase
"admissible §6.2 flow" must be justified by the graph/flow certificate (or by
Lemma 3 of the new note), not by `FeasibleType`.

---

## 7. Epistemic status

| Claim | Status |
|---|---|
| §6.2 vertices are read molecules; lower bound `1`; edges bidirected, `≥ o_min`; transitive reduction; objective = §6.1 separable binomial with external `N` | **source fact** (MB09 §6.1–6.2, PMC3154397) |
| Strict bridging predicate `r < t ∧ t+ℓ < r+L` | **modeling normalization** (`docs/bridging-source-semantics.md`) |
| A spelled molecule induces a feasible flow with `d =` occurrence counts (Lemma 1) | **mathematical proof** from Observation 7 |
| §6.2 objective separable, target `d*_w = N x_w/n` | **mathematical proof** |
| Proposition 1 (under-observation obstruction) | **mathematical proof** |
| Witness 1 `AAATT → AAAATT`: strict `I_s`, both feasible, ratio `9/8` | **mathematical proof + verified computation + kernel-checked** |
| Witness 2 `AAATAT → AAATA`: strict `I_s`, truth per-type feasible, ratio `1280/243` | **mathematical proof + verified computation** |
| Implication (P) is false under the corrected §6.2 model | follows |
| Unmerged infinite family satisfies `I_s` | **false** under strict bridging (this note) |
| Correct infinite family satisfying strict `I_s` | **open** |
| Which MB09 layer / tie semantics the 2016 sentence denotes | **open** (source ambiguity, unchanged) |

---

## 8. What this does and does not settle

**Does.** It decides the §6.2-restricted residue under the corrected
lower-bound-`1` bidirected reading: `I_s` does not imply that the truth-induced
flow is §6.2 ML-optimal, with a rigorous finite counterexample that is
kernel-checked. It isolates the structural reason (separability versus a
support/bridging hypothesis) and corrects an invalid infinite-family proof.

**Does not.** It does not decide which Medvedev–Brudno object the Shomorony
sentence denotes, nor the tie/maximizer-versus-uniqueness conclusion, nor the
single-strand reading (the witnesses use reverse-complement classes), nor
whether a valid infinite family exists.

---

## 9. Reproduce

```sh
python3 scripts/verify_se62_lb1_bidirected_determination.py
lake build AssemblyP1.Section62LowerBoundOneCounterexample
```

The Python script re-derives `x`, `d_S`, `d_D`, the strict `I_s` predicate, both
sequence-level feasibility claims, the exact ratios, and the failure of the
unmerged infinite family, using only exact `fractions.Fraction` arithmetic; it
exits non-zero on any failed assertion. The Lean module kernel-checks the finite
`I_s` certificate, the two `FeasibleType` claims, and the strict likelihood
inequality.

Primary sources: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116, §6.1–6.2, PMC3154397;
Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
*Bioinformatics* 32(17) (2016) i494–i502, Eq. (1); Guy Bresler, Ma’ayan Bresler,
David Tse, *Optimal assembly for high throughput shotgun sequencing*,
*BMC Bioinformatics* 14(Suppl 5):S18 (2013).
