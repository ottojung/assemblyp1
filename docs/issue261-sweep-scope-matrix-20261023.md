# Issue #261: exact scope of the bounded spelled/flow sweep

This note audits the finite search reported in the preceding
unmerged handoff document `issue261-audit-spelled-flow-sweep.md` (commit
`faf41aaf4ebe2c47b5bc9a2276736473f8f6f7f2`) against the source definitions recorded in
[`section62-mb09-bidirected-graph-audit.md`](section62-mb09-bidirected-graph-audit.md)
and `AssemblyP1/Section62BidirectedFlow.lean`. It records what follows from
that search and what remains open; it is not a new maximality theorem.

## Scope matrix

| Axis | What the sweep actually checks | What source-faithful §6.2 needs | Transfer/status |
|---|---|---|---|
| Graph/overlap range | No graph is constructed; binary circular words over lengths `L..8`, read lengths `L=2,3` | `overlapEdges` on observed RC molecule vertices with every proper overlap `o_min ≤ len < L`, including arbitrary `o_min ≤ L-1` | No candidate-set inclusion from graph flows to weak compositions, or reverse. Graph-specific axis OPEN. |
| Reduction | No overlap edges or reduction predicate are checked | MB09 §6.2 removes an edge when its overlap is spelled through two shorter overlaps; source-faithful reduction must preserve spelling and signed endpoints | Sweep says nothing about reduction invariance. Literal implementation caveat is separately noted in `issue261-general-bidirected-flow-ml.md` §“Source-faithfulness…”; do not assume either current surrogate predicate is the source rule. |
| Vertex lower bound | Spelled candidates are circular binary strings; arbitrary count vectors have no observed-graph vertex set | Every observed graph vertex has throughput at least 1 (`Admissible` in `Section62BidirectedFlow.lean`) | The weak-composition superset need not satisfy this bound; the spelled-string subset is not linked to a particular reduced graph. |
| Incidence, orientation, RC classes | Spectrum uses reverse-complement molecule classes; no signed graph incidences are generated | Source graph has oriented strands and signed ends; flows satisfy the bidirected incidence balance, with RC quotient conventions requiring an explicit adapter | Quotienting spectrum coordinates does not establish signed-flow feasibility. No inclusion proved. |
| Candidate object | (i) binary circular genomes for bounded spelled-maximality; (ii) all weak compositions for score search | Distinguish feasible integer flows, spelled bidirected circuits, and circular genomes. A flow need not be one circuit or spell any single genome | Search does not enumerate flows or prove that a score-vector candidate has a flow/genome representative. In particular it cannot test the source flow converse. |
| Integrality | Count entries are integers, but unconstrained compositions are not integral graph flows | §6.2 integer feasible flows; separately the half-integral LP relaxation | Integer coordinate values alone do not instantiate graph conservation. Relaxation comparison is outside this sweep. |
| Objective / length | Candidate-intrinsic exact multinomial score `∏(d_c/N)^{x_c}`; candidate lengths and composition totals bounded by 8 | For the §6.2 convex-flow algorithm, the relevant source objective is the §6.1 fixed-external-`N` product-binomial approximation, including `(1-d_i/N)^{n-x_i}`; exact §6.1 likelihood is a distinct question | Different objective and length parameter. Neither positive nor negative maximality conclusions transfer across this mismatch. |
| Sample/truth | Complete spectrum sample generated from each truth; bounded binary truth lengths; 1,012 truth cases total, with no separating surrogate count vector | Specify fixed observed support, truth admission, candidate graph built from that support, and the intended read-sampling likelihood | The sweep establishes no claim for other alphabets, supports, sample multiplicities, lengths, or graph constructions. Truth is a candidate in the bounded genome search by construction, not established as a feasible source flow for a specified graph. |

## Exact bounded conclusion and transfer rule

The checkable result remains exactly the one stated in the parent audit: for
the enumerated binary truths and bounded word/count-vector universes, the
bounded spelled-genome test found 1,012 spelled-maximal truth instances and
no *weak-composition* strict defeater under its exact variable-length
multinomial score. It is a finite surrogate census, not a proof of global
spelled maximality and not a flow-domain census.

The relevant transfer fact is one-way: a strict defeater in a subclass
transfers to a superclass only after proving candidate-set inclusion and
using the same truth, observation/sample, score, normalization, and length
parameter. A positive maximality result over the smaller spelled class does
not imply maximality over a larger flow class. Here the broad composition
universe is not a source-flow superset under a common objective/length
interpretation, and the searched spelled class is not established as the
source truth class. Thus neither direction yields a §6.2 conclusion.

## Smallest next bridge

The smallest bridge needed before this finite search can be source-faithful is
not an all-length maximality theorem. It is a **single-instance, explicit
graph-to-score adapter**: fix one observed RC molecule support, `L`, `o_min`,
the source-faithful reduced signed overlap graph, terminal convention, and
external `N`; then define its feasible integer-flow set and prove that the
throughput map sends exactly those feasible flows to the score vectors being
compared, with the truth's candidate status stated. Score both sides with the
same fixed-`N` binomial objective. This requires, at minimum, reduction and
signed-incidence feasibility to be explicit; a claimed flow-to-genome
transfer additionally needs a circuit/spelling theorem and cannot be assumed
for disconnected or non-Eulerian flows.

Once that adapter exists, the smallest falsification target is finite:
search one fixed instance for a truth that is maximal among its declared
spelled candidates but has a strictly better feasible integer-flow
throughput. The active literal graph-feasibility enumeration and verifier
repair are separate live lanes; this note does not duplicate either.

## Anchors and validation

* `AssemblyP1/Section62BidirectedFlow.lean`: `overlapEdges` (source graph),
  `isReducibleB` / alternatives (reduction hypotheses), `Admissible`
  (edge bounds, vertex lower bound and signed balance), and `throughput`.
* `docs/issue261-general-bidirected-flow-ml.md`, especially the source-fidelity
  blockers on reduction, spelling alignment, signed throughput, terminal
  modeling, probability bounds, and fixed observed support.
* Prior handoff `docs/issue261-audit-spelled-flow-sweep.md` at commit
  `faf41aaf4ebe2c47b5bc9a2276736473f8f6f7f2`: finite run and objective/domain
  audit; the two independent surrogate verifiers passed at the cited commit.
* MB09 §6.1–§6.2 source: <https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/>.

This is a documentation-only scope reconciliation. Validation: `git diff
--check`; `python3 scripts/check-research-docs.py`.
