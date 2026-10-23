# Issue #261: single-instance graph-to-score adapter (two-vertex bidirected instance)

Child of #255; parent scope matrix:
`docs/issue261-sweep-scope-matrix-20261023.md`
(at `origin/research/261-scope-matrix-RQZTG1WbAejzEkEnSWm7Wr-chemical`).
This note builds the "smallest next bridge" requested there: one explicit
observed support, `L`/`o_min`, reduced signed graph, terminal convention, and
external `N`, with the truth's candidate status proved and all exact integer
feasible-flow throughputs enumerated and scored under the same fixed-`N`
binomial objective as the declared spelled-candidate class.

## Instance declaration

- Alphabet: abstract binary labels; read length `L = 2`, `o_min = 1`.
- Observed RC molecule support: `verts = [v0, v1]`, `rep = id`.
  Concretely this is the two-class support `{AA, AC}` at `L = 2` with
  `rep` the identity on classes (no palindrome in the support, so the
  `Section62OrientedStrandFlow` representation defect does not occur here;
  both classes are non-palindromic and word-equality signs agree with
  bit-derived signs).
- Overlap graph (`Section62Flow.overlapEdges` shape): two bidirected edges,
  both of the single proper overlap length `len = 1 = L - 1`:
  `e0 : v0 -> v1`, `e1 : v1 -> v0`, with source-faithful signs
  `sgnX = +1` (departure from the class representative, `sgnRep`)
  and `sgnY = -1` (arrival at the class representative, `sgnTgt`),
  per `Section62BidirectedFlow.lean` (`bdEdge`).
- Transitive reduction: **vacuous**. `isReducibleB` requires two legs with
  `0 < len_j < e.len`; here every edge has `len = 1` and `readLen = 2`, so no
  positive length is strictly shorter. Hence `ReductionVacuous` holds and the
  reduced graph equals the complete graph `[e0, e1]`.
- Terminal convention: zero terminals (`t = noTerminals`), i.e. the
  `Feasible62` circuit subdomain (source: the genome "corresponds to a
  circuit", MB09 section 6.2). General `Admissible` flows with terminal use
  are strictly larger; they are not scored here (OPEN-4 of the terminal axis).
- External binomial denominator: `N = 2` (the true genome length; truth
  throughput below sums to 2, so the probability domain `0 <= d_i <= N`
  is respected by every enumerated candidate).
- Likelihood: genuine section 6.1 fixed-external-`N` product binomial core
  `K(d;x) = prod_i d_i^{x_i} (N-d_i)^{n-x_i}` over the full class universe
  `T = {v0, v1}` (both classes observed, so no unobserved-coordinate
  convention is needed; OPEN-2 does not occur here).

## Candidate class declaration (explicit)

- Candidates are **integer flows** `f : {e0,e1} -> Nat`, not spelled circuits
  and not circular genomes. The scored object is the throughput vector
  `d = throughput(f)`.
- Truth: `f* = (1, 1)`, i.e. one traversal of each edge; `d* = (1, 1)`.
- Truth admission: proved by the verifier (`balance 0`, vertex lower bound 1
  at both vertices, zero terminals, `d* = throughput(f*)`).

## Feasible-flow enumeration (exact, bounded certificate)

`Admissible` with `edgeLB = 0`, `vertexLB = 1`, zero terminals gives,
with the signs above:

- `throughput(v0) = f(e0)`, `throughput(v1) = f(e1)`.
- `balCore(v0) = f(e0) - f(e1)`, `balCore(v1) = f(e1) - f(e0)`.
- Feasibility ` increasingly: `f(e0) = f(e1) =: k`, `k >= 1`.

Hence the exact integer feasible set (unbounded) is the ray
`{(k,k) : k >= 1}` with throughputs `d = (k, k)`.
Intersected with the binomial probability domain `d_i <= N = 2`,
the scored fiber is exactly `{ (1,1), (2,2) }`.
The verifier enumerates `0 <= f(e_j) <= 3` and confirms no other
zero-terminal balanced flow with vertex bound 1 exists in the box,
and that `(2,2)` is the only additional probability-domain candidate.

## Scores (fixed-`N = 2` binomial core)

Effective weights `q_i(d) = d_i * (N - d_j)` (`j != i`):

- Truth `(1,1)`: `q = (1, 1)`, `P = 1`.
- Candidate `(2,2)`: `q = (0, 0)`, `P = 0`; `K = 0` on every
  full-support sample, so it never strictly beats the truth.

Uniform criterion check (`binomial_uniform_criterion` shape, `I = {0,1}`):
`P_B = 0`, hence non-defeat holds for every sample supported exactly on `I`.
The verifier checks all full-support samples with `n <= 5` explicitly, plus
the `m`-check inequalities `P_B * q_B(k)^t <= P_A * q_A(k)^t`.

## Maximality statement proved here (narrow)

For this instance, with candidates = zero-terminal integer `Feasible62`
flows whose throughputs lie in the probability domain, truth `d* = (1,1)`
admitted, likelihood = fixed-external-`N = 2` product binomial, length
universe fixed `N = 2`: the truth is sample-uniformly maximal over the
declared scored fiber. This is a **single-instance** classification, not a
general criterion.

## What this does NOT close (explicit OPEN carry-overs)

- OPEN-R: transitive-reduction interaction in general (here vacuous only).
- OPEN-S: spelled-circuit vs flow image identity (here every feasible flow
  `(k,k)` is in fact spelled by the `k`-fold 2-cycle, but no general theorem
  is claimed; the `AAATT`/image-refutation obstructions stand).
- OPEN-T: terminal-penalized solver objective vs pure ML (here zero-terminal
  subdomain only).
- OPEN-H: half-integral/real relaxation gap under the fixed-`N` binomial
  (here integer fiber only; the `2.5` midpoint is infeasible as an integer
  flow and unscored).
- OPEN-U: unobserved-coordinate convention (absent here: `T = I`).
- Full-overlap transfer: nothing is transferred; this instance is proved
  directly from the literal `Admissible` clauses.

## Validation

`python3 scripts/verify_261_graph_adapter_G2mCkKH2JiSuVTxepjkERJ_ears.py`
enumerates the flow box, checks balance/lower-bound/terminal clauses,
reduction vacuity, truth admission, the throughput fiber, the q-factorization,
and all full-support samples with `n <= 5`. Independent of Lean; Lean
formalization of this fiber remains future work.
