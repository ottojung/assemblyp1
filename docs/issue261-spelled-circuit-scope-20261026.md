# Issue #261: spelled-circuit scope cell (reduced AAT/TAA graph, L=3, o_min=1)

## Candidate classes (fixed reduced graph; class varied)

Reduced graph: the 4 maximal-overlap (L-1=2) edges of the audited AAT/TAA
support, as in the transitive-reduction and half-integral cells.
- (F) All integer feasible flows: multiplicities 0..2, edge lower bound 0,
  vertex throughput lower bound 1, zero signed-incidence balance, zero
  terminal usage.
- (S) Spelled-circuit flows: feasible flows whose edge multiset admits a
  closed trail using every unit exactly once (Eulerian circuit in the
  directed strand multigraph: balanced indeg==outdeg at every strand node
  plus weak connectivity over used edges), i.e. flows that spell one
  circular genome. The actual spelled string is not checked, only the
  Eulerian-circuit certificate.
- Likelihoods: fixed-N (N=4, sample x=(1,2)) product-binomial core and
  exact variable-length multinomial, same box-universe convention as the
  parent cells. Truth (2,2) is admitted (integer-feasible, spelled by
  (1,1,1,1)) throughout.

## Result

- (F) census: exactly 4 images {(1,3),(2,2),(3,1),(4,4)} with unique
  witnesses (1,2,0,1), (1,1,1,1), (1,0,2,1), (2,2,2,2) in the verifier's
  reduced edge order; fixed-N winner {(1,3)} K=81; exact winner {(1,3)}
  K=9/64 (parent cell).
- (S) census: exactly {(2,2),(4,4)}, witnessed by (1,1,1,1) and
  (2,2,2,2). The (F) winners (1,3)/(3,1) are Eulerian-unbalanced (not
  merely disconnected), hence non-spelling: no flow spelling one circular
  genome realizes them.
- (S) fixed-N winner {(2,2)} K=64 (the truth); exact winners {(2,2),(4,4)}
  tied at K=1/8. So truth (2,2) is maximal in (S) under fixed-N, tied-maximal
  under exact, and maximal under neither in (F) (Kfix 64 < 81, Kex 1/8 < 9/64).
- Hence the spelled-circuit restriction is NOT neutral for ML maximality
  on this cell: the full-flow winner (1,3) is not even admitted in (S), and
  the spelled-class answer differs under both likelihoods. Maximality
  criteria must declare whether candidates are flows, spelled circuits, or
  circular genomes; flow results do not transfer downward to the spelled
  class (nor upward) without an explicit preservation argument.

## Reproduction

Run `python3 scripts/verify_261_spelled_circuit_scope.py` (exit 0 on PASS;
both embedded mutants -- dropped-(4,4) spelled census claim and dropped-tie
exact claim -- exit non-zero). All arithmetic exact (integers/Fractions);
enumeration exhaustive (3^4 = 81 cases); Eulerian test from scratch.

## Scope

One bounded cell on the reduced graph only. No general maximality criterion
is stated. Orientation/RC classes beyond this support, half-integral x
spelled interaction, and the full-real comparison stay OPEN. Keep #261 and
#255 open.
