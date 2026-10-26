# #272 boundary: source placement predicates versus read observations

## Result

The source-faithful predicate `SourceFaithfulIs.InformationFeasible(s,L,R)` is
defined on a genome `s` **and its realized set of read starts `R`**. The literal
read-string adapter instead defines a relation between a genome spelling and an
observed set of read strings. These are different sample spaces. In particular,
one cannot substitute `InformationFeasible` directly for the event `E(g,r)` in
`FiniteBayesianSideInformation` when `r` is only the observed read multiset (or
read-type set): the start set used by the predicate is not an argument of that
observation.

This is an observability/conditioning boundary, not a counterexample to the
source's reconstruction theorem. It also identifies what a source-faithful
posterior theorem must state before claiming that `I_s` makes recovery certain.

## Correct finite joint law when starts are latent

Let `W` be the finite, fixed-length candidate genomes modulo rotation, `U` the
finite start configurations (for example `Fin G → Fin G` for `N` ordered IID
uniform starts), and `X` the actual observation space. For a genome `g` and
configuration `u`, let `x(g,u)` be the observed read data and let `m_g(u)` be
the start-configuration mass. With prior `π`, and with the exact source
predicate `I(g,u) := InformationFeasible(g,L,starts(u))`, conditioning on the
supplied truth-dependent event gives the posterior

```
P(g | X=x, I=1) ∝ π(g) · Σ_{u : x(g,u)=x} m_g(u) · 1_{I(g,u)}.
```

Thus certainty for the true orbit `[g₀]` at positive predictive mass is
equivalent to

```
for every h with [h] ≠ [g₀], π(h)>0:
  Σ_{u : x(h,u)=x} m_h(u) · 1_{I(h,u)} = 0.
```

The crucial quantifier is over **all latent realizations of every competitor
consistent with the observation**, not just over the true realization. The fact
`I(g₀,u₀)` holds for the actually sampled starts does not by itself establish
that this competitor sum vanishes. Conversely, if the start configuration is
itself observed, use `X'=(X,U)` and the fibre criterion is over pairs `(h,u)`;
this is a strictly different experiment and must be identified as such.

This formula is simply the finite joint-mass posterior theorem with the latent
variable summed out. It does not presume that `I` is a function of the observed
reads, and it does not reuse the unconditioned likelihood or prior after
conditioning.

## Relation to current verified endpoints

* `FiniteBayesianSideInformation.posteriorMass_eq_one_iff` proves the exact
  support criterion when the event is an explicit predicate of the modeled
  truth and observation.
* `FiniteSideInformationDecoderEndpoint.conditional_certain_readStringIS_of_decoder`
  (PR #342, on its research branch at the time of this note) uses the literal
  read-string promise and an explicitly attributed decoder-correctness premise.
  Its observation is a set of read strings; its promise is not the latent-start
  `InformationFeasible` predicate above.
* `SourceFaithfulIs.InformationFeasible` preserves the historical placement
  predicate but has not, by this note, been identified with that read-string
  promise or proved to have singleton posterior in a finite latent-start model.

The 2016 Not-So-Greedy sufficiency theorem may provide the needed exclusion of
every competitor if its input and candidate universe are aligned with the
finite likelihood and conditioning law. That alignment is an external
source-to-model obligation; the posterior algebra alone supplies no such
exclusion. No historical theorem is promoted to a Lean theorem here.

## What remains open at this boundary

To settle the concrete source-faithful endpoint, formalize the finite start
configuration likelihood, the read observation (including multiplicities),
and the candidate universe in one model, then prove either (a) the source
guarantee excludes every positive-mass competitor in the event-conditioned
fibre, or (b) provide an exact counterexample under those same definitions.
Until then, the warranted manuscript statement is the support-sum iff above;
posterior certainty from truth-side `I_s` alone is not claimed.
