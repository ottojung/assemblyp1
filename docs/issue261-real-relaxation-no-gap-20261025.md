# Issue #261: real-relaxation no-gap cell for the exact likelihood (reduced 4-cycle, L=3)

## Candidate class (fixed; one bounded cell)

- (F) Rational/real edge-multiplicity flows, edge lower bound 0, vertex
  throughput lower bound 1, zero signed-incidence balance, zero terminal usage,
  on the 4-edge MB09-style overlap-2 cycle AAT->ATT->TTA->TAA->AAT (the
  transitively reduced graph of `docs/issue261-transitive-reduction-scope-20261025.md`).
  Candidates are **flows**, not spelled circuits, not circular genomes.
- Truth admitted (any feasible flow).
- Likelihood: **exact** variable-length multinomial
  `Kex(d) = prod_v (d_v / T)^x_v`, `T = sum d`, sample `x = (1,2)`.
- Length universe: variable (candidate's own `N = sum d`), i.e. the §6.1 first
  display, same convention as `docs/issue261-half-integral-source-ml.md`.

## Result

- The real flow `f = (2/3, 2/3, 2/3, 2/3)` is feasible (throughputs
  `(4/3, 4/3) >= 1`, zero balance) and is **not** half-integral
  (`2 * 2/3 = 4/3`), so on this graph
  `integer flows < half-integral flows < real flows` strictly at both steps
  (the first strictness is the `(1/2 x4)` witness of the half-integral cell).
- Clearing denominators (`D = 3`) gives the integer feasible flow
  `g = (2, 2, 2, 2)`, throughput `(4, 4)`, with **identical** exact likelihood
  `Kex = 1/8` throughout (`(4/3,4/3)`, `(4,4)`, `(1,1)` all normalize to
  `(1/2,1/2)`). In general `Kex` is scale-invariant, so every rational-valued
  real feasible flow shares its exact likelihood with an integer feasible flow:
  the real relaxation **cannot** change the exact-ML optimum or the truth's
  maximality status on this cell.
- The maximality implication does not require every real flow itself to be
  rational. On this fixed graph, any strictly better real feasible flow can be
  approximated by rational feasible flows: the flow constraints are a rational
  polyhedron (homogeneous rational balance equalities, nonnegative edges, and
  rational throughput lower bounds), whose rational points are dense. The
  exact likelihood is continuous wherever total throughput is positive, so a
  sufficiently close rational feasible flow remains strictly better. Clearing
  that rational flow's denominators and scaling by a positive integer preserves
  balance, preserves normalized throughputs and likelihood, and keeps all
  throughput lower bounds at least 1. Thus a strictly better real flow exists
  iff a strictly better integer flow exists; in particular truth-maximality
  agrees for real and integer candidates here. This argument concerns strict
  domination/maximality only; an irrational real maximizer need not have an
  integer candidate with exactly its own likelihood. The claim applies to
  rational polyhedral flow constraints and this continuous scale-invariant
  exact likelihood, not the fixed-N binomial objective.
- This closes the explicitly OPEN "real (non-half-integral) LP relaxation"
  subclaim of `docs/issue261-half-integral-source-ml.md` **for the exact
  likelihood only**. No claim about the fixed-external-`N` binomial (which
  genuinely has a half-integral gap, Class 3 of
  `docs/issue261-general-bidirected-flow-ml.md`): different objective,
  different length universe.

## Reproduction

Run `python3 scripts/verify_261_real_relaxation_gap.py` (exit 0 on PASS; both
embedded mutants -- wrong throughput and denied scale invariance -- exit
non-zero). All arithmetic is exact (`Fractions`); no enumeration needed beyond
the 10-edge build assertion inherited from the audited scope cell.

## Scope

One bounded graph/model cell only. No general maximality criterion is stated.
The density argument resolves the real-versus-integer strict-domination
question for this cell; it does not provide a candidate attaining the exact
likelihood of an arbitrary irrational flow.
Spelled circuits, circular genomes, transitive-reduction transfer, and
RC/orientation classes beyond this support stay OPEN. Keep #261 and #255 open.
