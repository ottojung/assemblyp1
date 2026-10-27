# Issue #261: rational-density lemma for exact-likelihood flow relaxation

## Result and scope

Fix a finite edge list and vertex list. Regard each edge multiplicity as a real
coordinate. Let `P` be defined by finitely many linear equalities and weak
inequalities with rational coefficients, and assume `P` is nonempty. This
includes, for a fixed §6.2 graph with zero terminals, nonnegative edge values,
rational signed-incidence balance equations, and vertex-throughput lower bounds
`d_v >= 1`. It does not assert that the project's full source model, its
transitive reduction, or its orientation quotient has been correctly identified.

For a finite nonnegative observation vector `x`, use the exact, variable-length
multinomial score

\[
  L_x(f)=\prod_v (d_v(f)/T(f))^{x_v},\qquad T(f)=\sum_v d_v(f),
\]

with `0^0 = 1`. The lower bound and a nonempty vertex list imply `T(f)>0` on
`P`. Then the following statements hold:

1. Rational points of `P` are dense in `P` (in its relative topology).
2. If a real feasible candidate strictly beats a feasible truth under `L_x`,
   some rational feasible candidate also strictly beats it.
3. Every rational feasible flow has a positive integer multiple that is an
   integer feasible flow, and the score is unchanged by this scaling.

Consequently, on this fixed rational-polyhedral zero-terminal flow domain, the
truth is maximal among real flows iff it is maximal among integer flows for
this exact likelihood. This concerns non-strict maximality (no strict beater),
not uniqueness or exact attainment of an arbitrary irrational optimum.

## Proof of density, including boundary points

Write `P = {z : Az=b, Cz<=d}` with rational matrices and vectors. For a
particular `p in P`, let `J` consist of all inequalities active at `p`. The
affine system consisting of `Az=b` and `C_j z=d_j` for `j in J` has rational
coefficients and has the real solution `p`. Gaussian elimination over `Q`
therefore gives a rational particular solution `q` and a basis of its nullspace
with rational coordinates. Rational parameter choices are dense among real
parameter choices, so rational solutions of this affine system are dense in
that affine space. Every inequality not in `J` has positive slack at `p`;
finitely many such inequalities remain satisfied in a sufficiently small
neighborhood of `p`. Thus rational points of `P` approximate `p` arbitrarily
closely. This argument deliberately includes faces with zero edge variables;
it does not assume that `p` is an interior point of the ambient orthant.

For (2), the score is a product and quotient of linear functions with strictly
positive denominator on `P`, hence continuous there, including zero numerator
coordinates because all exponents are nonnegative integers. If `L_x(f)>L_x(t)`,
continuity gives a relative neighborhood of `f` where the strict inequality
persists. Density supplies a rational feasible point in that neighborhood.

For (3), take a common positive denominator `D` of the finitely many rational
edge coordinates. Multiplication by `D` preserves homogeneous balance,
nonnegativity, and weak throughput lower bounds `d_v>=1`; the resulting edge
coordinates are integers. Every throughput and `T` is multiplied by `D`, so
each normalized coordinate `d_v/T`, and therefore `L_x`, is unchanged.

## Hypotheses that cannot be dropped silently

- The flow graph and edge list are fixed and finite. This is necessary for the
  finite-dimensional rational-polyhedron argument and common denominator.
- The constraints are rational linear equalities/weak inequalities. The
  conclusion does not follow for a nonlinear or irrationally constrained
  feasible set.
- The objective is exact variable-length likelihood, homogeneous of degree
  zero in throughput. The fixed-external-`N` product-binomial objective is not
  scale invariant; the known half-integral gap in
  `docs/issue261-general-bidirected-flow-ml.md` is not contradicted.
- The argument is for a specified feasible-flow domain. It does not establish
  any inclusion/equality with spelled circuits or circular genomes; it cannot
  transfer a positive maximality statement across a candidate-set inclusion.
- It does not resolve the meaning or correctness of transitive reduction,
  augmented terminal usage, RC/orientation classes, or unobserved molecule
  coordinates. In particular, the repository's `Section62BidirectedFlow`
  documents these source-fidelity forks as open.

## Relation to the bounded cycle witness

The earlier branch artifact `docs/issue261-real-relaxation-no-gap-20261025.md`
instantiates this argument on the stated four-edge cycle and sample `(1,2)`;
its concrete `(2/3,2/3,2/3,2/3)` point is feasible and denominator clearing
produces `(2,2,2,2)`. This note proves the density step generally for a fixed
rational polyhedron. It does not independently establish that the cycle is the
source-faithful transitively reduced MB09 instance: the historical
`docs/issue261-transitive-reduction-scope-20261025.md` cited by that artifact is
not present on current `main` (`62c0e78`). Treat the cycle-specific source claim
as unverified until that artifact is restored/reviewed.

## Status

This closes only the real-versus-integer strict-domination question for exact
likelihood on any *already specified* fixed rational-polyhedral flow domain.
It is not a necessary-and-sufficient structural maximality criterion for
general §6.2 flows, and makes no claim for fixed-`N` binomial likelihood.
Transitive-reduction/source equivalence, candidate-image characterization,
non-spelled-flow maximality, and orientation/RC transfer remain open.
