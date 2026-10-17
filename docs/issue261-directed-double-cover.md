# Directed double cover: signed half-incidence balance (#261)

This is a bounded **incidence-algebra** result, not a completed source-faithful
§6.2 genome-reconstruction theorem.

An abstract signed bidirected edge with molecule-class endpoints `(u,a)`
and `(v,b)` has TWO distinctly indexed directed arcs:
`(u,a) → (v,-b)` and `(v,b) → (u,-a)`.
Physical edge IDs remain distinct even when their endpoint data coincide,
and each loop still produces two lifted arc IDs.

For each class `w` and signed state `+1` or `-1`, weighted outgoing arc
counts agree with the corresponding signed half-incidence sums, and incoming
arc counts agree with opposite-signed incidence sums. Hence a physically
balanced incidence flow induces directed balance at the signed states.
Projecting both arc uses produces `2 f(e)`, *not* `f(e)`.

The module does NOT prove that arbitrary signed edge values have only signs
±1, that the double cover descends to an integer circuit decomposition of
the original edge-use vector, that one genome realizes the flow, or that
the source physical overlap graph's vertices, parallel overlap IDs, and ML
objective are equivalent to this abstract incidence model. Those remain
open in #261. See `Section62PhysicalEdgeOrbit` on main for the previously
merged physical-edge quotient and its palindrome-throughput counterexample.

Validation: independent 48-case finite verifier with loops and parallel
edge IDs. Kernel elaboration, axiom checks and exact-head GitHub CI required.
