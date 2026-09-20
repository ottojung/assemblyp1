# Claim boundary of the `AAATT → AAAATT` Medvedev–Brudno §6.2 witness

_Status: source reading + claim-boundary determination for issue #36, 2026-09-20.
Written after PR #40 (`6256d46`) was merged into `main`. It records exactly what
the merged §6.2 witness proves, which source/model choices the conclusion rests
on, and which remaining assumption could change the answer. Claims are labelled
**source fact**, **mathematical fact**, **verified computation**,
**kernel-checked**, **interpretation**, or **open**. It does not select a
referent for the 2016 phrase by fiat._

_Companion artifacts on `main`: `docs/bridging-se62-flow-ml-counterexample.md`
(the witness note), `docs/section62-mb09-bidirected-graph-audit.md` (the
graph/flow construction), `AssemblyP1/Section62BridgingCounterexample.lean`
(the kernel check)._

## 0. Bottom line

The `AAATT → AAAATT` witness **does not settle the published Shomorony et al.
(2016) open question**. It settles one named interpretation, and only that one:

> **(W)** Under the MB09 §6.2 reading in which
> (i) graph vertices are read DNA molecules (reverse-complement classes),
> (ii) the candidate is a single spelled molecule inducing an admissible §6.2
> bidirected circuit, (iii) the source lower bound `1` is read per read vertex,
> (iv) candidate length is unconstrained, and
> (v) likelihood is the literal §6.1 product-of-binomial-marginals with the
> external known `N`,
>
> the bridging hypothesis `I_s` does **not** force the truth-induced candidate
> to be maximum-likelihood.

The reason this is not a settlement is that no primary source selects the
referent of “the maximum-likelihood formulation of the AP (Medvedev and Brudno,
2009)”, the 2016 sentence is phrased about a *sequence* and names no section or
formula, and (W) is a conjunction of five convention choices each of which can
flip the answer. The single load-bearing remaining assumption is the
**probability-model/referent choice**; the strand, length, sample-size-regime,
and tie conventions are additional independent forks.

## 1. Source facts

### 1.1 Shomorony, Kim, Courtade & Tse (2016)

Accepted article, §5 Discussion (printed p. i501), verbatim:

> “The maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009), on
> the contrary, seems to be robust to these issues, and thus a good candidate
> for the ‘correct’ formulation. Understanding whether bridging conditions can
> be used to guarantee that the maximum-likelihood sequence is the true sequence
> is currently an open question.”

Supporting source facts (see `shomorony-mb-formulation-provenance.md` and
`mb-formulation-referent-reconciliation.md` for the page/hash ledger):

- The sentence carries **no subsection, equation, figure, or page pointer** into
  Medvedev–Brudno; a full-text scan finds no `multinomial`/`binomial`, no
  likelihood formula, and no candidate-length/tie discussion in the passage.
- The paper's “AP” is the *Assembly Problem*, and its own optimization
  formulations are single-sequence (generalized Hamiltonian path). The sentence
  therefore contrasts *objectives over a sequence*, not flows.
- §2 fixes a circular single strand `s` of length `G`; reads are uniform
  length-`L` substrings.
- `I_s` (Eq. (1), p. i497) requires coverage, all triple repeats all-bridged,
  and one constituent of every interleaved repeat pair bridged.
- The theory's reconstruction target is `s` **up to cyclic shift**; reverse
  complements enter only as §4.1 experimental preprocessing. [source fact]

### 1.2 Medvedev & Brudno (2009)

Direct reading of `PMC3154397` confirms **four** distinct objects, only some of
which are sequence-valued:

| Object | Output | Sequence? | Source role |
|---|---|---|---|
| exact global read-count multinomial, candidate-intrinsic `N(D)` | circular genome `D` | yes | named target; explicitly not separable |
| §6.1 product of binomial marginals, external `N` | circular genome `D` scored by `d_i` | yes | the approximation actually used |
| §6.2 convex min-cost bidirected flow | a flow / “(non-contiguous) assembly” | **no** | the algorithm |
| “maximum likelihood framework” | — | n/a | umbrella term |

Verbatim §6.1 (source fact):

> “Let `D` be a circular genome of length `N(D)`, and let `d_i` denote the number
> of times the `k`-molecule `i` appears in `D`. … There are `4^k` such variables
> … their joint distribution is exactly the multinomial distribution …”

> “Since in the binomial approximation the length of the genome `N(D)` is a
> constant that is independent of each `d_i`, we can replace it by `N`, which is
> the length of the actual genome from which the reads were sampled. … **For our
> experiments, we assume that the genome size is known.**”

Verbatim §6.2 (source fact):

> “The first step is to build a bidirected overlap graph from the set of reads,
> which are DNA molecules. **The vertices of this graph are the reads** … **Each
> vertex has a lower bound of 1** since it represents a read that must be present
> in the genome at least once. **All other lower bounds are 0 and all upper
> bounds are infinity.** … Since any flow can be decomposed into a collection of
> walks, our flow represents a **(non-contiguous) assembly** of the genome …”

MB09 §7 turns the flow into contigs with a heuristic, and §8.2 states “Our
algorithm relies on having an estimate on the length of the genome.” MB09 states
no maximizer, uniqueness, cyclic-shift, or reverse-complement equivalence claim
for the maximum. [source fact]

## 2. What the merged PR #40 artifact actually establishes

Kernel-checked in `AssemblyP1.Section62BridgingCounterexample` (no `sorry`,
`axiom`, `admit`, or `native_decide`; standard axioms only), for

```text
truth            S = AAATT            (G = 5)
read length      L = 3, starts (0,1,4), n = 3, external N = 5
observed         x = { AAA:1, AAT:1, TAA:1 }        (molecule classes)
truth spectrum   d_S = { AAA:1, AAT:2, TAA:2 }
competitor       D = AAAATT           (|D| = 6), d_D = { AAA:2, AAT:2, TAA:2 }
```

the theorem
`se62_bridging_flow_counterexample` proves
`SourceCertificate ∧ SeqSupportLB dS obs ∧ SeqSupportLB dD obs ∧ lik obs dS < lik obs dD`,
i.e. the instance `I_s` certificate, the sequence-level support/lower-bound
certificate for both `S` and `D`, and the literal §6.1 ratio
`L_{6.1}(D)/L_{6.1}(S) = 9/8 > 1`. [kernel-checked + mathematical fact]

Two epistemic boundaries internal to PR #40 itself:

1. `SeqSupportLB` (support equality plus `x ≤ d`) is **not** MB09 §6.2
   feasibility; it is a stronger finite sufficient certificate that happens to
   hold here. [source fact; repository]
2. The exact §6.2 graph construction — transitive reduction, bidirected
   incidence, balance, supersource/sink, and that both `S` and `D` are
   admissible bidirected circuits with per-vertex lower bound `1` — is verified
   only computationally in `scripts/verify_se62_mb09_bidirected_graph.py`, **not
   kernel-checked**. [verified computation]

So the kernel-checked content is the *sequence-level* claim; the *§6.2-flow*
content is a verified finite computation.

## 3. The convention panel the witness sits on, and what flips the answer

| Axis | Value used by PR #40 | Source status | If flipped |
|---|---|---|---|
| Read type / strand | reverse-complement molecule classes | MB09 molecule model, but Shomorony is single-strand | single-strand bounded search found no witness (`G ≤ 6, L = 3`) — evidence, **not** a proof of absence |
| Candidate length | unconstrained (`|D| = 6 ≠ N = 5`) | §6.1 imposes no fixed competitor length, but MB assume a known genome size | the fixed-length `|D| = N` sub-case is untouched here; same-length witnesses handle it for the sequence objectives |
| Objective | literal §6.1 external-`N` product of binomial marginals | MB09 call this an *approximation*; the exact multinomial is the named ideal | the exact candidate-intrinsic-`N(D)` multinomial is a different objective |
| Lower bound | per read vertex `1` | literal §6.2 wording | per-occurrence `d_D(w) ≥ x_w` is strictly stronger and is what some repository witnesses use |
| Sample-size regime | finite realized read set (per-instance) | the sentence has no coverage qualifier | under fixed-length high coverage the truth is asymptotically the unique maximizer (conditional on the spectrum-uniqueness bridge) |
| Candidate universe | spelled single molecule inducing a §6.2 circuit | §6.2 returns flows, but the sentence says “sequence” | genuinely non-spellable feasible flows are not addressed |
| Conclusion | strict inequality: truth is not *the* maximizer | tie semantics not specified | “truth is *a* maximizer” vs “every maximizer is the truth up to genome equivalence” is a separate fork |

## 4. Remaining assumption(s) that could change the answer

Ranked by how much would change:

1. **Referent / probability model (load-bearing).** Exact multinomial with
   candidate-intrinsic `N(D)` versus the §6.1 external-`N` binomial versus the
   §6.2 flow. The accepted text selects none. The witness uses the external-`N`
   binomial; a different objective can have a different truth-maximizer status.
2. **Strand / read-type convention.** Shomorony's theory is single-strand and
   cyclic-shift-only; MB09's §6.2 is reverse-complement molecular. The witness
   needs the reverse-complement collapse (`ATT ~ AAT`, `TTA ~ TAA`), which no
   single primary source forces for *Shomorony's* question.
3. **Candidate-length convention.** “Known genome size” is a likelihood
   parameter in §6.1, not a stated competitor-length constraint; whether the
   published question compares same-length or arbitrary-length candidates is
   unresolved.
4. **Sample-size quantifier.** The literal sentence is per-instance over
   `R ∈ I_s`; under high coverage the fixed-length answer is opposite. The
   witness is a finite-sample phenomenon only.
5. **Tie / conclusion semantics.** Maximizer versus unique-up-to-equivalence.
6. **The publisher supplement (sections A–G)**, still HTTP 403, is the one
   unexamined accepted artifact that could name a §6.2/likelihood object.

## 5. Exact defensible claim boundary

**May be claimed:** Under panel (W) — bidirected read-molecule §6.2, literal
per-vertex lower bound `1`, unrestricted candidate length, external-`N` §6.1
binomial — the bridging hypothesis `I_s` does not force ML-optimality, and in
particular the §6.2-flow escape does not preserve the implication for the
spelled-circuit sub-case. This is kernel-checked at the sequence level and
verified computationally at the §6.2 graph/flow level.

**Must not be claimed:** A negative answer to the published Shomorony et al.
(2016) open question; any statement about the single-strand reading, the
fixed-length `|D| = N` reading, the exact candidate-intrinsic multinomial as
applied to *this* witness, the high-coverage regime, or genuinely non-spellable
flows; or that the 2016 phrase denotes §6.2.

**Relationship to the other witnesses.** The kernel-checked same-length
witnesses (`AAABB → AAAAB` exact; `AAACC → AAAAC` binomial) already refute the
two *sequence-level* determinate readings under the per-instance regime by
candidate-set inclusion. PR #40 is complementary and narrower in scope but
stronger in one respect: it removes the hypothesis that §6.2 flow feasibility
could rescue the implication under the bidirected reading. It is therefore a
robustness result about a specific panel, not the settlement of the published
question.

## 6. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| 2016 sentence names no MB09 section/equation/formula; is sequence-valued | source fact | accepted text §5, p. i501 |
| MB09 has four objects; §6.2 output is a non-contiguous flow | source fact | MB09 §6.1–6.2, §7 |
| PR #40 witness satisfies `I_s`; `lik(D) > lik(S)`; ratio `9/8` | kernel-checked + mathematical fact | `AssemblyP1.Section62BridgingCounterexample` |
| Both `S`, `D` are admissible §6.2 bidirected circuits | verified computation, **not** kernel-checked | `scripts/verify_se62_mb09_bidirected_graph.py`; `docs/section62-mb09-bidirected-graph-audit.md` |
| `SeqSupportLB` is not the §6.2 source definition | source fact / repository | Lean docstring; witness note §2 |
| Witness refutes (P) for the bidirected spelled-circuit sub-case | follows | §2 |
| Witness settles the published question | **no** | §3–§5 |
| Referent, strand, length, regime, tie remain open | source gap | §4 |

## 7. Relation to existing repository notes

- `docs/bridging-se62-flow-ml-counterexample.md` (PR #40) already states in §8
  that the witness does not settle which MB object is intended nor the
  single-strand/fixed-length sub-cases. This note makes that boundary explicit
  and ranks the residual assumptions; it adds no new mathematical claim.
- `shomorony-mb-formulation-provenance.md` and
  `mb-formulation-referent-reconciliation.md` establish the referent ambiguity.
- `medvedev-brudno-candidate-class.md` and
  `same-length-witnesses-candidate-set-inclusion.md` establish the candidate-set
  transfer for the sequence-level witnesses.
- `docs/literature/ml-tie-semantics.md` records the tie fork.

## 8. Locators

- I. Shomorony, S. H. Kim, T. A. Courtade, D. N. C. Tse, “Information-optimal
  genome assembly via sparse read-overlap graphs,” *Bioinformatics* 32(17)
  (2016) i494–i502, DOI `10.1093/bioinformatics/btw450`; Eq. (1)/Theorem 1
  p. i497; open question p. i501.
- P. Medvedev, M. Brudno, “Maximum Likelihood Genome Assembly,” *J. Comput.
  Biol.* 16(8) (2009) 1101–1116, §6.1–6.2, §7, §8.2, PMC3154397.
- Merge commit `6256d46` (PR #40), files
  `docs/bridging-se62-flow-ml-counterexample.md`,
  `docs/section62-mb09-bidirected-graph-audit.md`,
  `AssemblyP1/Section62BridgingCounterexample.lean`,
  `scripts/verify_se62_mb09_bidirected_graph.py`.
- Reproduce: `python3 scripts/verify_se62_mb09_bidirected_graph.py`;
  `lake build AssemblyP1.Section62BridgingCounterexample`.
