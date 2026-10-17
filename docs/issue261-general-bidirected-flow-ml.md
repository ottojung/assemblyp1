# Issue #261: ML maximality in general bidirected flow domains

Child of #255; extends #260 from full overlap to genuine MB09 §6.2 bidirected
overlap graphs at arbitrary `o_min ≤ L − 1`.

## Source audit

Primary source: Medvedev & Brudno, *Maximum Likelihood Genome Assembly*,
J. Comput. Biol. 16(8) (2009) 1101–1116 (PMC3154397), §3.1–§3.4, §5.2, §6.1–§6.2,
as quoted in `docs/section62-mb09-bidirected-graph-audit.md` and read directly
from the PMC full text on 2026-10-10.

A project implementation of parts of the §6.2 feasibility object (Variant F
of `docs/ml-formalization-contract.md`) is provided in
`AssemblyP1/Section62BidirectedFlow.lean`. **It is not yet an established
source-faithful equivalence**, owing to the reduction, throughput, terminal and
spelling-flow adapter gaps detailed below. In the intended historical model,
vertices are observed read
molecule classes (§3.1, §4.1), edges are all proper bidirected overlaps of length
`≥ o_min` (§3.3, §6.2), transitive edge reduction removes overlaps spelled by two
shorter overlaps (§6.2), each vertex has lower bound 1 (§6.2), edge lower bounds
are 0 and upper bounds infinite (§6.2), and the signed-incidence balance
`pos(f)(v) − neg(f)(v) = 0` holds after the supersource/supersink conversion
(§3.4, §6.2).

**The §6.1 objective has two displays (primary-source correction).** §6.1 first
writes the exact *global read-count multinomial* in the candidate's own length
`N(D)` with the constraint `∑ᵢ dᵢ = N(D)`, then states that this is not separable
and approximates it by the *product of per-class binomials* with the **external**
genome size `N` (known from experiment). §6.2's convex-flow algorithm optimizes
the **binomial approximation**, not the exact multinomial. Keeping these two
objectives distinct is part of correctness; the earlier draft conflated them.

## The new phenomenon at arbitrary overlap

At full overlap (`o_min = L − 1`) every edge overlap is exactly `L − 1`, so a
flow that visits `k` reads spells a genome of length exactly `k`: the length is
fixed by the throughput. At arbitrary `o_min ≤ L − 1` an edge may carry any
overlap length in `[o_min, L − 1]`, so a flow that visits `k` reads with overlap
lengths `o_1, …, o_k` spells a genome of length `∑ (L − o_j)`, which is **not**
determined by the throughput. For the *exact multinomial* objective the candidate
length `N` is therefore a variable and the comparison acquires a length factor.

## Candidate classes and maximality conditions

### Class 1: Variable-length exact multinomial (the §6.1 first display)

- **Candidates**: count vectors `d` with variable length `N` (flows, not
  necessarily spelled circuits or circular genomes). The §6.1 exact multinomial
  additionally requires `∑ᵢ dᵢ = N`; `varLengthCriterion` is stated without that
  constraint, so it is a criterion at the count-vector layer.
- **Truth**: admitted.
- **Likelihood**: exact multinomial `∏ᵢ (dᵢ/N)^(xᵢ)` (the §6.1 first display).
- **Length universe**: variable `N`.
- **Maximality condition** (`varLengthCriterion`): the truth is sample-uniformly
  maximal for this objective **iff** `∀ i ∈ supp A : Bᵢ·G ≤ Aᵢ·N` (the density
  bound). This is necessary and sufficient for the stated objective. At `N = G` it
  reduces to coordinatewise dominance (`fixedLengthRecovery`), recovering #260's
  Proposition 3.2. Under the genome constraint `∑ᵢ dᵢ = N`, summing the density
  bound forces equality, i.e. `B = (N/G)·A` (the rescaling class of Class 5).
- **Source status**: **project-defined objective**. This is the §6.1 *exact*
  multinomial, which §6.2 does **not** optimize. It is a well-defined and
  kernel-checked mathematical result, but it is not by itself a claim about the
  §6.2 algorithm's optimum.
- **Witnesses**: `stretch_beats` (AATATT beats AATT on `e_{AT}`), `dilution_witness`.

### Class 2: Fixed-external-`N` multinomial product (NOT the §6.1 binomial)

- **Candidates**: throughput vectors `B` (count vectors), external `N = G` fixed.
- **Truth**: admitted.
- **Likelihood**: the exact multinomial with a *common external* length `N = G`
  substituted for candidate and truth; after cancelling the candidate-independent
  `n!/∏xᵢ!` and the common `N⁻ⁿ` the comparison is `∏ᵢ Bᵢ^xⁱ ≤ ∏ᵢ Aᵢ^xⁱ`.
- **Length universe**: fixed `N = G`.
- **Maximality condition** (`flow_dominance_criterion`): the truth is
  sample-uniformly maximal for this product objective over a class of throughput
  vectors **iff** no candidate `B` in the class has `Bᵢ > Aᵢ` for some
  `i ∈ supp A` (coordinatewise dominance). Necessary and sufficient **for this
  product objective**.
- **Source status**: **project-defined, correctly labelled.** This product is
  **not** the §6.1 separable binomial: the binomial retains a per-class
  `(1 − dᵢ/N)^(n−xᵢ)` factor that does not cancel.
- **Refutation of the §6.1 binomial as coordinatewise** (kernel-checked):
  `binomial_not_coordinatewise` exhibits truth `A = (1, 2)`, candidate `B = (1, 1)`,
  external `N = 3`, sample `x = (2, 1)`, where `B ≤ A` coordinatewise yet the
  separable-binomial core `binomCore` satisfies `binomCore B x 3 = 8 > 4 =
  binomCore A x 3`. So coordinatewise dominance is **not sufficient** for the
  §6.1 binomial, and `flow_dominance_criterion` must not be cited as its criterion.

### Class 2′: Genuine §6.1 product-binomial likelihood (count-vector theorem derived; flow-level OPEN)

- **Source model**: The §6.1 approximation is the product of binomials over all
  read-molecule classes (including classes with observed count zero). Its
  *external* denominator `N=G` is fixed from the true genome. This does
  **not** impose candidate genome length `G`, nor does it bound an otherwise
  unbounded flow's throughput by itself.
- **Probability domain**: for each candidate throughput `d_j`, require
  `0 ≤ d_j ≤ N` before assigning a binomial probability. §6.2 graph edge
  capacities are infinite; the reconciliation of that graph domain with the
  binomial probability domain (restriction or extended cost) remains **OPEN**.
- **Exact factorization** (kernel-checked in
  `AssemblyP1.Section62BinomialCriterion.binomCoreNat_eq_prod_qFac`):
  for the full class universe `T`, let `n=∑_{j∈T}x_j` and
  `K(d;x)=∏_{j∈T} d_j^{x_j}(N-d_j)^{n-x_j}`.
  For each `i∈T`, define
  `q_i(d)=d_i·∏_{j∈T,j≠i}(N-d_j)`.
  Then **`K(d;x)=∏_{i∈T}q_i(d)^{x_i}`** exactly, including
  integer endpoints with `0^0=1`. The omitted binomial coefficients and
  the common `N` powers do not depend on `d`.
- **Exactly fixed read count `n), observed support fixed**:
  take the set `I={i:x_i>0}` to be the *same* set of observed read types
  for all samples compared, put `m=|I|` and assume `n≥m≥1`.
  A supported observation has `x_i≥1` for each `i∈I`,
  `x_j=0` outside `I`, and total `n`.
  Let `P_A=∏_{i∈I}q_i(A)`, `P_B=∏_{i∈I}q_i(B)` and `t=n-m`.
  If the true spectrum has `q_i(A)>0` on `I`, **B never strictly beats A
  for any such observation iff**
  `∀i∈I: P_B·q_i(B)^t ≤ P_A·q_i(A)^t`.
  Proof: distribute one count to every `i∈I`, then concentrate the remaining
  `t` observations at the type with greatest `q_i(B)/q_i(A)`.
  If any candidate `q_i(B)=0`, its likelihood is zero for every
  positive-full-support observation, and these inequalities still hold.
  This is an exact `m`-check equivalence for a **fixed candidate B**;
  quantifying over a source-faithful feasible-flow universe is a further step.
- **Uniformly over every `n≥m`** (kernel-checked in
  `AssemblyP1.Section62BinomialCriterion.binomial_uniform_criterion`):
  for a fixed candidate B, with `I` the observed support and the truth an
  *interior* truth (`q_i(A)>0` for all `i∈I`), non-defeat over **all** samples
  supported exactly on `I` is equivalent to `P_B=0` **or**
  `∀i∈I: q_i(B)≤q_i(A)`. Unlike the interior-only version,
  this correctly handles zero-likelihood candidate boundaries. The fixed-`n`
  (non-uniform) extreme-sample iff is stated separately above and is
  numerically audited by `scripts/verify_261_binomial_extreme_samples.py`; its
  Lean formalization remains **OPEN**.
- **Neither direction of coordinatewise dominance on the original `d_i`
  is valid as a general binomial criterion**:
  `binomial_not_coordinatewise` shows it is **not sufficient**
  (`A=(1,2)`, `B=(1,1)`, `N=3`, `x=(2,1)`, core 8 versus 4).
  It is **not necessary** even for genuine circular spellings of different
  lengths: `S=ACA` has length 3 and molecule counts `A=(1,1,1)`
  on `{AA,AC,CA}` at read length 2; `D=ACAACA` has
  `B=(2,2,2)`. Under the fixed external `N=3`, the candidate/truth
  product-binomial ratio is `2^(−n)<1` for every nonempty observation
  on those classes, although every candidate throughput is greater.
  This is a **pairwise** counterexample, not a theorem that S globally
  maximizes likelihood over all admissible flows. A source-model Lean
  adapter for this example remains open.
- **Flow-level structural characterization (program, not yet a proof)**:
  For the *actual* source-faithful finite integer-flow fiber, the fixed-n
  criterion reduces sample-uniform ML to the `m` extreme observations.
  On a correctly bounded split-vertex flow representation, the negative
  log-binomial cost for each extreme is separable convex. Standard Graver
  optimality theory would then give a finite structural certificate via
  absence of a feasible improving Graver augmentation. The **bidirected
  flow-to-matrix**, transitive reduction, terminal treatment, probability
  boundaries and valid throughput adapter are **not formalized here**.
  Pure likelihood maximization must also be distinguished from the
  terminal-penalized algorithm's optimization problem.
- **Counterexample already formalized**: the `AAATT` instance at
  `o_min=1` has nonspelled optimizing flows that beat truth by `256/81`
  under the project's existing flow predicate; see Class 4. Its fidelity
  to every detail of the original reduced graph remains to be audited.

### Class 3: Integer flows vs half-integral relaxation

- **Candidates**: integer §6.2 flows vs half-integral (LP relaxation) flows.
- **Truth**: admitted.
- **Likelihood**: §6.1 separable binomial, fixed `N = G`.
- **Length universe**: fixed `N = G`.
- **Status**: **RESOLVED at the flow level** by `AssemblyP1.Section62NonSpelledFlow`
  (`half_integral_strictly_better`, kernel-checked): the integer flow constraint is
  binding. The new module contributes the exact arithmetic of the `AAA` factor:
  `d²(5−d)²` is `36` at `d = 2, 3` but `625/16` at `d = 5/2`, giving the ratio
  `625/576` (`half_integral_gap`, `half_integral_beats_integral`). This arithmetic
  alone is **not** a feasibility proof; the flow-level feasibility is the cited
  kernel-checked result.

### Class 4: Flows that do NOT spell one circular genome

- **Candidates**: §6.2 feasible flows that are not necessarily spelled by a
  single circular genome (non-spelled flows).
- **Truth**: admitted.
- **Likelihood**: §6.1 separable binomial, fixed `N = G`.
- **Length universe**: fixed `N = G`.
- **Maximality condition**: no tractable structural criterion is known. The
  `AAATT` instance at `o_min = 1` exhibits non-spelling flow maximizers that beat
  the truth (ratio `256/81`). `AssemblyP1.Section62NonSpelledFlow` kernel-checks
  the literal §6.2 feasibility of the truth and the competitors and that the
  maximizer set `{(2,1,1), (3,1,1)}` consists of non-sequence spectra.
- **Status**: **OPEN** at the level of a general criterion; the finite obstruction
  is kernel-checked. No necessary-and-sufficient condition is known.

### Class 5: Rescaling ties at variable length

- **Candidates**: count vectors with variable length.
- **Truth**: admitted.
- **Likelihood**: exact multinomial.
- **Length universe**: variable.
- **Maximality condition**: uniqueness of the normalized spectrum is
  **impossible** at variable length. The `k`-fold cover `S^k` has spectrum `k·A`
  and length `k·G`, so its normalized spectrum equals the truth's and it ties on
  every sample (`rescaling_tie`). No full-overlap analogue.

## Adjudication (2026-10-16): unobserved molecule types and the count-vector criterion

An open review objection on #261 (research-assistant, 2026-10-14) observed that
MB09 §6.1's fixed-`N` separable product-binomial is a product over **all**
`4^k` molecule types, *including* types with observed count `x_i = 0`, so a
candidate that leaves an unobserved type at count `0` might avoid the
`(1 - d_i/N)^n < 1` penalty that a spelled genome with a positive count there
must pay, while the §6.2 overlap graph carries only *observed* read vertices.
The adjudication below is kernel-checked in
`AssemblyP1/Section62BinomialSupportAdjudication.lean`.

**Verdict.**

1. **Which `c_i(d_i)` terms the criterion includes.** At the count-vector layer
   the criterion is *already* full-support. Write `n = ∑ x`, `T` for the whole
   class universe, and `I` for the observed support. The literal §6.1 core is
   `K(d;x) = ∏_{j∈T} d_j^{x_j}(N-d_j)^{n-x_j}`. `binomCoreNat_support_split`
   proves the exact split
   `K(d;x) = (∏_{j∈T∖I}(N-d_j))^n · ∏_{i∈I} d_i^{x_i}(N-d_i)^{n-x_i}`, so each
   **unobserved** class contributes the full factor `(N-d_j)^n` and is *not*
   dropped. Equivalently, by `binomCoreNat_eq_prod_qFac` and
   `criterion_is_full_support`, the score is `∏_{i∈I} q_i(d)^{x_i}` with
   `q_i(d) = d_i ∏_{j∈T, j≠i}(N-d_j)`, and `qFac_split` exhibits the unobserved
   factors `(N-d_j)` inside every effective weight `q_i`.
2. **Unobserved coordinates are neither forced to zero nor immaterial.** The
   count-vector theorem places no restriction on the unobserved coordinates.
   `unobserved_coord_matters` exhibits `wd = (2,1,0)` and `wd' = (2,1,1)` on
   `I = {0,1}` with `x = (1,1,0)`, `N = 5`: they agree on `I` but score
   `600 ≠ 384`. Worse, the naive **observed-only** shortcut
   `q^I_i(d) = d_i ∏_{j∈I, j≠i}(N-d_j)` is a *wrong* criterion:
   `observedOnly_insufficient` gives `oA = (2,1,4)` (truth carrying mass `4` on
   the unobserved class `2`), `oB = (2,1,0)` (candidate leaving it at `0`), with
   `x = (1,1,0)`, `N = 5`; the observed-only weights dominate (`q^I(oB) =
   q^I(oA) = (8,3)`) yet the candidate strictly beats the truth (`24 < 600`).
   `full_criterion_detects` confirms the full-support criterion detects the
   defeat, and `exists_defeating_sample` recovers a defeating sample through the
   kernel-checked `binomial_uniform_criterion`. Hence the full-support terms are
   indispensable and the criterion is **not** a function of observed
   coordinates alone.
3. **The flow-level §6.2 obligation is genuinely different and stays OPEN.** A
   §6.2 feasible flow's throughput is supported on the observed read vertices,
   so it does not by itself specify the unobserved coordinates.  This is exactly
   where the spelled half of the adapter stops: `Section62SpelledFlowAdapter`
   proves `throughput (sp.flow) edges v = sp.visits v`, i.e. a spelled circuit's
   count vector is its **observed-vertex visit vector**, not its genome's
   *complete* molecule spectrum.  `flow_genome_gap` quantifies the residual
   discrepancy exactly: if a flow `d` agrees with a genome `d'` on `I` and is
   `0` off `I`, then on any sample supported on `I`,
   `K(d;x)·(∏_{j∉I}(N-d'_j))^n = K(d';x)·(∏_{j∉I} N)^n`, i.e. the flow is
   larger by `∏_{j∉I}(N/(N-d'_j))^n ≥ 1`. A flow does **not** pay for the
   genome's unobserved mass. Deciding the unobserved-coordinate convention (and
   the throughput-image characterization) remains OPEN.

**Well-defined class covered by the theorem.** Candidates are count vectors
`d : T → ℕ` over the *full* molecule-type universe with the observed support `I`
and the unobserved coordinates *explicitly specified* — not §6.2 flows, not
spelled circuits, not circular genomes. The truth is admitted (any full count
vector `A` with `q_i(A) > 0` on `I`). The likelihood is the MB09 §6.1
fixed-external-`N` separable product-binomial; the length universe is fixed
external `N`.

**Independent audit.** `scripts/verify_261_support_adjudication.py` re-derives
the q-factorization, the support split, the qFac split, the unobserved witness,
the observed-only refutation, and the ratio identity in exact integer
arithmetic.

**Remaining OPEN subclaims (unchanged by this adjudication).**

- OPEN-1: **throughput-image characterization** of the §6.2 feasible set
  (incidence/Graver); the spelled *inclusion* half is resolved by
  `Section62SpelledFlowAdapter.spelling_flow_feasible`, but the converse and the
  image remain OPEN.
- OPEN-2: **spelled-circuit → genome spectrum** alignment (`d = Spelling.visits`
  vs the genome's complete spectrum), equivalently the unobserved-coordinate
  convention (flow default `0` vs spelled-genome spectrum). The `AAATA` witness
  is a spelled circuit whose observed throughput omits a positive unobserved
  type; the discrepancy is exactly `∏_{j∉I}(N/(N-d'_j))^n` (`flow_genome_gap`).
- OPEN-3: general **non-spelled-flow** maximality criterion.
- OPEN-4: **transitive reduction** interaction with ML.
- OPEN-5: **orientation/RC class** interaction.  The *representation* defect
  (palindrome orientations collapsing under word-equality signs) is repaired and
  kernel-checked in `AssemblyP1/Section62OrientedStrandFlow` (2026-10-16); what
  remains OPEN is the interaction of the corrected incidence signs with the
  transitive reduction and the RC-quotient of candidate genomes.  See
  `docs/issue261-oriented-strand-source-model.md`.
- OPEN-6: **sample realizability** at arbitrary `o_min`.
- OPEN-7: **fixed-`n` (non-uniform) extreme-sample iff** in Lean — **RESOLVED
  on the full-count-vector side** (2026-10-16, `AssemblyP1.Section62FiniteNExtremeSamples.binomial_fixed_n_extreme_iff`,
  kernel-checked, PR #279): for fixed `n = |I| + t`, full observed support `I`,
  and positive truth effective `q`-weights over the whole molecule-type
  universe, the candidate never beats the truth on any full-coverage sample
  iff `P_B·q_B(k)^t ≤ P_A·q_A(k)^t` for every `k ∈ I`, where
  `P_C = ∏_{i∈I} q_i(C)`; ties, `t = 0`, and zero candidate weights are
  covered. Count-vector scope only: it does not settle the §6.2 flow-level
  classification, flow realizability, or the unobserved-coordinate convention.
  `scripts/verify_261_binomial_extreme_samples.py` remains as an independent
  numerical regression.

## Remaining-open matrix

See `docs/issue261-axis-matrix-20261014.md` for the independently audited matrix
(current at `origin/main` `e024af2`), including the flow-to-count-vector adapter
half added by `AssemblyP1.Section62FlowCountVectorAdapter`.

| Axis | Status |
|---|---|
| Variable-length exact-multinomial criterion (§6.1 exact display) | **RESOLVED** (`varLengthCriterion`), project-defined objective |
| Fixed-external-`N` multinomial-product criterion | **RESOLVED** (`flow_dominance_criterion`), correctly labelled |
| Genuine §6.1 separable-binomial count-vector criterion | **RESOLVED at the count-vector layer** (`AssemblyP1.Section62BinomialCriterion.binomial_uniform_criterion`, kernel-checked): exact q-factorization `K(d;x)=∏ᵢqᵢ(d)^{xᵢ}` and the all-`n` interior-truth iff `∏ᵢqᵢ(B)=0 ∨ ∀i∈I, qᵢ(B)≤qᵢ(A)`. **Adjudicated 2026-10-16** (`AssemblyP1.Section62BinomialSupportAdjudication`): the criterion is full-support (unobserved terms appear as `(N-d_j)^n`); unobserved coordinates are not forced to zero and matter; the observed-only shortcut is refuted. **Fixed-`n` full-coverage extreme-sample iff RESOLVED 2026-10-16** (`AssemblyP1.Section62FiniteNExtremeSamples.binomial_fixed_n_extreme_iff`, kernel-checked, PR #279): `P_B·q_B(k)^t ≤ P_A·q_A(k)^t` for every `k∈I` at `n=|I|+t`; count-vector scope only |
| §6.1 binomial over the §6.2 feasible flow set | **PARTIAL** — spelled half RESOLVED (`Section62SpelledFlowAdapter.spelling_flow_feasible`, 2026-10-15); the image identity `Θ(F)=spelledVisitSet` is **REFUTED** (2026-10-15, `Section62SpelledFlowImageRefutation`); general image characterization still OPEN |
| Half-integral relaxation gap | **RESOLVED** (flow level: `Section62NonSpelledFlow`; arithmetic: `half_integral_gap`) |
| Rescaling ties at variable length | **RESOLVED** (`rescaling_tie`) |
| Non-spelled-flow maximality criterion | **OPEN** (finite obstruction kernel-checked) |
| Transitive reduction interaction with ML | **OPEN** |
| Orientation/RC class interaction | **PARTIAL** — the palindrome representation defect is repaired and kernel-checked (`Section62OrientedStrandFlow`: bit-derived incidences, palindrome and non-palindrome graph/throughput/balance/feasibility, 2026-10-16); the ML classification in the corrected domain reduces exactly to the corrected throughput image (`Section62OrientedMLClassification`), with the image identity still OPEN; transitive-reduction interaction remains OPEN |
| Sample realizability at arbitrary overlap | **OPEN** |

## Source-faithfulness and remaining proof blockers (explicit)

The existing abstract count-vector theorems are useful and kernel-checked, but
**they do not, by themselves, solve the full MB09 §6.2 flow classification**.

1. **Transitive reduction.** `isReducibleB` requires both two-leg proper
   overlap lengths to be smaller than the direct overlap `l<L`, while imposing
   `l1+l2-L=l`; these inequalities cannot hold simultaneously. Hence the
   literal predicate cannot delete any proper overlap. The alternative
   `isReducibleLongerB` only checks that each leg is longer; it does *not*
   require equal spelled sequence, signed-endpoint compatibility, or even
   that both legs survive the overlap threshold. With `L=4`,
   `AAAC→ACCA→CAAA` using overlaps 2 and 2 spells `AAACCAAA`,
   whereas direct `AAAC→CAAA` at overlap 1 spells `AAACAAA`.
   Blindly reducing the latter edge changes the language of spelled molecules.
   Myers (2005) and the MB09 §6.2 citation require spelling-preserving
   transitive reduction, not either current approximation.
2. **Flow attached to spelling.** The project predicate `SpelledFeasible62`
   checks a spelling alongside an explicitly handed-in feasible flow `f`, and does
   not itself prove `f = Spelling.flow sp` or `d = Spelling.visits sp`; the flow
   admissibility conjunct is checked against the unreduced edge graph even when the
   spelling checks a reduced graph. The **general alignment theorem** is now
   kernel-checked: `Section62SpelledFlowAdapter.spelling_flow_feasible` proves
   that the walk flow `Spelling.flow` is `Feasible62` with
   `d = Spelling.visits` on any `Nodup` graph containing its steps (given the
   visits-observed hypothesis). What remains is the source-faithful reconciliation
   of `SpelledFeasible62`'s unreduced-graph admissibility conjunct with the
   reduced graph, and the interaction with transitive reduction.
3. **Signed bidirected throughput.** The current `throughput` counts
   departures using the stored `sx` end of edges. A general bidirected
   traversal may use the reversed orientation; show its equality to the
   split-vertex visit count under all allowed traversals, or explicitly
   restrict the candidate domain.
4. **Terminal modeling.** The zero-terminal `Feasible62` circuit subdomain
   is not all augmented flows: MB09 uses expensive supersource/sink arcs
   rather than forbidding them. The *pure binomial ML* objective and the
   *binomial-plus-terminal-penalty* solver objective are different.
5. **Probability feasibility.** Original §6.2 edge upper bounds are
   infinite, but the §6.1 binomial is probabilistic only when `0≤d_i≤N`.
   An explicit restriction or extended-cost convention is required.
6. **Fixed observed support vs missing types.** The fixed-n extremal theorem
   varies read multiplicities while holding the set `I` of *observed types*
   and hence the constructed overlap graph fixed. Omitting a true-positive
   molecule changes that graph and may remove the truth's flow. It needs
   separate classification.
7. **Integer optimization adapter.** A useful future endpoint is a
   precise integer matrix for the faithfully reduced signed bidirected
   graph, explicit throughput and terminal variables, then a verified
   Graver augmentation optimality theorem for each fixed-support extreme
   sample. Any constraints requiring candidates to be spelled by a
   *single primitive genome* must be treated separately from all flows.

Source reading: [Medvedev–Brudno 2009, §§6.1–6.2](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/);
[Myers 2005 string-graph reduction](https://pubmed.ncbi.nlm.nih.gov/16204131/).

## Artifacts

- `AssemblyP1/GeneralBidirectedFlowML.lean`: kernel-checked abstract theorems,
  including the §6.1-binomial counterexample `binomial_not_coordinatewise`.
- `AssemblyP1/Section62BinomialCriterion.lean`: kernel-checked genuine §6.1
  separable-binomial **count-vector** criterion at a fixed external `N`: the
  q-factorization `binomCoreNat_eq_prod_qFac`, the concentrated-sample score
  `binomCoreNat_concentrated`, and the all-`n` interior-truth iff
  `binomial_uniform_criterion`; plus the `A=(1,2)`, `B=(1,1)`, `N=3` witness.
  Its axioms are `[propext, Classical.choice, Quot.sound]`. It does **not**
  provide the §6.2 flow adapter, so the flow-level rows stay OPEN.
- `AssemblyP1/Section62BinomialSupportAdjudication.lean`: kernel-checked
  adjudication of the unobserved-molecule-type objection: the exact support
  split `binomCoreNat_support_split`, the effective-weight split `qFac_split`,
  the full-support restatement `criterion_is_full_support`, the unobserved
  witness `Witness.unobserved_coord_matters` (600 vs 384), the observed-only
  refutation `ObservedOnly.observedOnly_insufficient` (24 vs 600), and the
  flow-vs-genome bound `flow_genome_gap`. Axioms
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
- `AssemblyP1/Section62FiniteNExtremeSamples.lean`: kernel-checked exact
  fixed-`n` full-coverage extreme-sample iff for §6.1 count vectors — the
  general nonnegative-product extremal lemmas (`product_le_extreme`,
  `rational_extreme_iff`, `weighted_extreme_iff`), the surplus decompositions
  (`surplus_sum_of_fullcoverage`, `binomCoreNat_factor_surplus`), and
  `binomial_fixed_n_extreme_iff`; plus nonvacuity regressions at `N=3`
  (`fixed_two_reads_never_beat`, `fixed_three_reads_can_beat`,
  `zero_candidate_weight_never_beats`). Count-vector scope only; no
  flow-realizability claim. Axioms `[propext, Classical.choice, Quot.sound]`.
- `scripts/verify_261_support_adjudication.py`: independent exact-integer audit
  of the adjudication identities and witnesses.
- `scripts/verify_issue261_general_bidirected_flow_ml.py`: independent exact
  recomputation (all checks pass), including the binomial counterexample.
- `scratch261/Audit.lean`: axiom audit (only propext, Classical.choice, Quot.sound).
- `AssemblyP1/Section62FlowCountVectorAdapter.lean`: the flow-to-count-vector
  adapter half — `maximal_of_subset` / `not_maximal_of_subset` (candidate-set
  inclusion transfers failures, not positive statements) and `throughputVec_congr`
  / `maximal_image_iff` (ML maximality over a flow set equals maximality over its
  throughput image). It does **not** characterize the throughput image, so the
  §6.1-binomial-over-§6.2-flow row stays OPEN.
- `AssemblyP1/Section62SpelledFlowAdapter.lean`: the spelled-circuit →
  feasible-flow half of the §6.2 adapter (2026-10-15). `spelling_flow_feasible`
  proves the cyclic walk flow of a bidirected-circuit spelling is a zero-terminal
  §6.2 feasible flow with `d = Spelling.visits`, on any `Nodup` graph containing
  its steps; `throughput_eq_visits` and `balCore_eq_zero` are the two
  computational halves, `weighted_dedup` the de-duplication core, and
  `visits_mem_throughput_image` places spelled visit vectors in the feasible
  throughput image. Axioms: `[propext, Classical.choice, Quot.sound]`
  (`AssemblyP1/Section62SpelledFlowAdapterAudit.lean`). It does **not**
  characterize the image (the `AAATT` obstruction keeps that OPEN) and does not
  touch the transitive-reduction axis.
- `AssemblyP1/Section62SpelledFlowMaximality.lean`: the spelled sub-class
  maximality transfer and length universe (2026-10-15). `sum_visits_eq_n` /
  `sum_throughput_eq_n` fix the total mass of a spelled candidate to its number of
  read positions `n`; `spelledVisitSet_subset_image` places the spelled count
  vectors inside the feasible throughput image; `spelled_maximal_of_flow_maximal`
  restricts flow-level maximality to the spelled sub-class and
  `flow_not_maximal_of_spelled_witness` (plus its spelled-truth form) transfers a
  spelled dominator upward to the full feasible-flow set. Axioms:
  `[propext, Classical.choice, Quot.sound]`
  (`AssemblyP1/Section62SpelledFlowMaximalityAudit.lean`). It is a **necessary,
  not sufficient** criterion: the spelled sub-class is a strict sub-class (the
  `AAATT` non-spelled throughput), so the full image characterization and the
  spelled-maximal-but-not-flow-maximal question stay OPEN. The spelled sub-class
  is also limited to candidates whose every window is an observed graph vertex.
  `flow_maximal_iff_spelled_maximal_of_image_eq` reduces sufficiency exactly to the
  open identity `Θ(feasibleFlowSet) = spelledVisitSet`.
- `AssemblyP1/Section62SpelledFlowImageRefutation.lean` (+ `.Audit.lean`): the
  **refutation** of that identity (2026-10-15). It proves two general structural
  obstructions and exhibits two genuine MB09 §6.2 `overlapEdges` instances at
  `o_min = 1`, `readLen = 3`:
  * `visits_eq_zero_of_no_arriving_maxEdge` — no spelled circuit visits a class
    `v` unless some maximal edge (`len = readLen − 1`) *arrives* at `v`, because
    every visited position is the arrival strand of the maximal step `pred i`;
  * `spelledVisitSet_eq_empty_of_no_maxEdge` — a graph with no maximal edge has
    no spelled circuit at all.
  Instance A (`AAC`, `CCA`) has no maximal edge, so `spelledVisitSet = ∅`, while a
  zero-terminal feasible flow exists (`image_ne_spelledVisitSet`).  Instance B
  (`AAA`, `ACA`) *does* contain maximal edges, but none arrives at the class `ACA`;
  a feasible flow routes through `ACA` on a length-`1` overlap, so its throughput
  is not spelled (`image_ne_spelledVisitSet_of_maxEdge_instance`).  Axioms:
  `[propext, Classical.choice, Quot.sound]`
  (`AssemblyP1/Section62SpelledFlowImageRefutationAudit.lean`), all `decide`-checked
  against the literal `overlapEdges` construction.

  **Source-fidelity qualification.** These are counterexamples to
  `Θ(feasibleFlowSet) = spelledVisitSet` for the *project's narrow*
  `Spelling.step` model (each edge has overlap length `L-1`) on the
  **complete** overlap graph. They do **not** refute MB09 Observation 7,
  which speaks about occurrences along walks of the *transitively reduced*
  graph, including potentially shorter-than-maximal overlaps. To address
  Observation 7 requires a separate no-skipped-observed-windows theorem,
  relating all positions of a circular spelling to its read-vertex anchors.

  **Consequence for the sufficiency axis.**  The hypothesis `hEq` of
  `flow_maximal_iff_spelled_maximal_of_image_eq` is *not* universally satisfiable:
  the identity is false, so the spelled test cannot be a sufficient condition for
  flow-level maximality in general.  The precise obstruction is that a §6.2
  feasible flow may be supported on proper overlaps strictly shorter than
  `readLen − 1`, while `Spelling.step` is always the maximal overlap; the graph
  need not even contain a maximal edge.  The identity restricted to graphs whose
  *every* edge is maximal (so the obstruction above cannot occur) remains OPEN;
  there the spelled sub-class and the feasible set can still differ by
  connectivity and strand-consistency.
- `AssemblyP1/Section62OrientedStrandFlow.lean` +
  `AssemblyP1/Section62OrientedMLClassification.lean` (+
  `Section62OrientedStrandFlowAudit.lean`): the **corrected oriented-strand
  source model and its ML classification** (2026-10-16).  The historical
  `strandsOf rc verts = verts ++ verts.map rc` + word-equality signs collapse a
  palindrome's two physical orientations to one edge value and one sign pair;
  the corrected model keeps an explicit orientation bit (`OStrand W = W × Bool`)
  separate from the nucleotide word, derives the signed incidences from the bit
  (`sgnRep_oRep`, `sgnTgt_oRep`), and reuses the historical `overlapEdges`/
  `Feasible62`/`throughput`/`balance` at the tagged strand type.  Palindrome
  semantics, non-palindrome agreement, balancing and throughput are
  kernel-checked (`corrected_pal_*`, `nonpal_*`,
  `historical_pal_not_feasible_one`).  In the corrected domain, ML maximality for
  any throughput-factoring score reduces exactly to maximality over the corrected
  throughput image (`oriented_maximal_iff_image`), with the spelled test
  necessary (`oriented_spelled_maximal_of_flow_maximal`) and sufficient exactly
  under image equality (`oriented_maximal_iff_spelled_maximal_of_image_eq`).
  Independent verifier `scripts/verify_261_oriented_strand_source_model.py`
  (18 exact checks).  Axioms `[propext, Classical.choice, Quot.sound]`.  See
  `docs/issue261-oriented-strand-source-model.md`.  The historical
  `Section62Flow` construction is labelled **bounded / non-faithful on
  RC-palindromic classes**.
