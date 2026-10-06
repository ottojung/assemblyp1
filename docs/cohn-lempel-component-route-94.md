# Board 94: Cohn–Lempel component-deletion route

This note records the current proof architecture for the remaining long-window target
`Issue94Interface.P2LongUnique L`. It is deliberately narrower than the older
ladder-induction plans.

## Durable endpoints already proved

On this branch:

- `Issue94P2PrimInterface.lean` identifies `P2LongUnique L` as the exact
  remaining long-window theorem consumed by the population endpoint.
- `Issue94EulerianRealize.lean` proves, for `2 <= L`, the equivalence between
  the complete-spectrum BBT statement and the Eulerian-cycle obstruction.
- `Issue94Reconstruct.lean` reconstructs a genuine `EulerianCycle` from any
  bijective, `vtx`-preserving map `f` for which
  `f ∘ nextPos` is a single circuit.

The remaining work is therefore the long-window uniqueness of a genuine
Eulerian listing under `P2` and primitivity.

## Pure permutation input from the literature

Let `rho` be a full cycle and let `u_1,...,u_m` be disjoint transpositions.
Cohn--Lempel (1972) and Beck (1977) associate a binary link/interlacement matrix
`X` to the chords and prove

```
number_of_cycles (u_1 ... u_m rho) = nullity_GF2(X) + 1.
```

Hence `u_1 ... u_m rho` is a full cycle iff `X` is nonsingular.  For
commuting/disjoint transpositions Beck's link matrix is the original
Cohn--Lempel chord-intersection matrix.

References:

- M. Cohn and A. Lempel, *Cycle decomposition by disjoint transpositions*,
  J. Combin. Theory Ser. A 13 (1972), 83--89,
  DOI 10.1016/0097-3165(72)90010-6.
- I. Beck, *Cycle decomposition by transpositions*,
  J. Combin. Theory Ser. A 23 (1977), 198--207,
  DOI 10.1016/0097-3165(77)90041-3.
- L. Traldi, *Binary nullity, Euler circuits and interlace polynomials*,
  European J. Combin. 32 (2011), 944--950,
  DOI 10.1016/j.ejc.2011.02.004.

A modern restatement is Theorem 3.5 of Allsop,
*Row-Hamiltonian Latin squares and Falconer varieties*: a product of
transpositions followed by the full cycle is an n-cycle iff the link matrix is
nonsingular over GF(2).

## Immediate corollary: delete an interlace component

For an involution `f`, let its nontrivial 2-orbits be the chord set and let
`X` be the interlacement matrix.

If `f ∘ rho` is a full cycle, then `X` is nonsingular.

The connected components of the chord-interlacement graph give a block
decomposition of `X`: there are no nonzero entries between distinct
components. Therefore every component block is nonsingular. Deleting any whole
set of components leaves a direct sum of nonsingular blocks, hence a
nonsingular matrix. Applying Cohn--Lempel again, the modified involution
`f' ∘ rho` is still a full cycle.

This is exactly the deletion statement we want for `f = AltF hK sigma`.

## Project-specific bridge

Under `P2`, primitivity and `2 <= L <= K`, existing theorems already give:

1. `AltF_sq`: `AltF` is an involution.
2. `AltF_vtx'`: every `AltF` orbit preserves the `(L-1)`-mer label.
3. `orbit_is_doubledPair`: every nontrivial orbit is a genuine doubled-node
   transposition.
4. `Issue94InterlaceComponents.connected_block`: every connected interlace
   component lies inside one `SameExtension` / maximal-repeat ladder block.
5. `BBTLadder.ladder_arc_eq`: the two copies inside such a maximal repeat
   have identical vertex labels along the valid ladder arc.
6. `Issue94Reconstruct.exists_eulerianCycle_of_labelPreserving_single`: after
   deleting a component, once Cohn--Lempel supplies the one-cycle condition,
   the modified label-preserving involution gives a genuine new Eulerian
   listing.

So the pure graph/permutation theorem does **not** need any genome theory, and
the reconstruction step does **not** need any Cohn--Lempel details.

## The remaining genome-specific lemma

The unresolved step is local:

> If one deletes all `AltF` transpositions in one interlace component that lies
> in a single `SameExtension` maximal-repeat ladder, then the old and newly
> reconstructed Eulerian listings have the same vertex cycle (up to rotation).

This must be proved without assuming the traversal remains inside the component.
That assumption is false.

A promising proof shape is to build the explicit permutation that swaps the two
equal maximal-repeat arcs.  `ladder_arc_eq` should supply pointwise
`vtx`-preservation of this arc swap; the algebraic goal is then to show it
conjugates the old successor to the successor with that component deleted.

If the arc-swap construction requires the interlace component to contain every
shift in its `SameExtension` block, isolate and prove the existing
`ShiftPairInterlace` obligation (empirically true): two distinct support
chords that are parallel shifts inside the same maximal repeat are connected in
the interlace graph.  Do not silently assume this.

## Important refutations / guardrails

Do **not** use any of the following:

- “P2 makes all raw repeated `(L-1)`-mer chords noncrossing.” False:
  `S=00101, L=3` is a kernel-checked counterexample.
- “An interlace component is preserved by the alternative traversal.” False.
- “Repair components independently by restricting the traversal.” False.
- “Deleting one transposition preserves one-cycle-ness.” False in general.
  Cohn--Lempel says deletion is safe at the level of whole interlace
  components, because the matrix is block diagonal.
- “`AltF = id` is the target.” False. The target is `VertexCycleEq`; benign
  nontrivial ladders such as `S=00101` must be quotiented out.
- Broad `lake build` on Phoebe. The 8 GiB cgroup OOMs on the
  `Issue94OrbitSearch` dependency. Keep new theorem modules small and compile
  only targeted files.

## Recommended division of labor

- **Pure Cohn--Lempel:** formalize only the disjoint-transposition theorem, or
  isolate it as the sole pure-combinatorics theorem if a full formalization is
  large.
- **GF(2) corollary:** prove block-diagonal nonsingularity and component
  deletion, parametrically over the Cohn--Lempel equality.
- **Deletion adapter:** define the component-deleted involution and prove it
  remains bijective and `vtx`-preserving; then invoke `Issue94Reconstruct`.
- **Vertex-cycle invisibility:** prove the explicit maximal-repeat arc-swap
  conjugator.
- **Block connectivity:** prove/refute the exact `ShiftPairInterlace` lemma
  needed to identify a maximal-repeat block with one interlace component.

The integration endpoint for all of these is `P2LongUnique L`, not the older
global `LadderVertexCycle` interface.

## Stronger local algebra: a discrete antiderivative of the ladder switches

There is a sharper way to attack the remaining vertex-cycle lemma.

Fix one maximal-repeat ladder with extension starts `p,q`.  For every valid
shift `t`, write

```
s_t = swap (rotAdd t p) (rotAdd t q).
```

Conjugating by the truth successor shifts the ladder:

```
rho * s_t * rho^{-1} = s_{t+1}
```

as long as both shifted pairs are still in the ladder coordinate range.

Now suppose the deleted component contains the ladder swaps indexed by a finite
set `B`.  If `B` has even cardinality, choose its discrete antiderivative
`A`: after sorting the indices
`b1 < b2 < ... < b_{2m}`, take

```
A = [b1,b2) union [b3,b4) union ... union [b_{2m-1},b_{2m}).
```

Equivalently, over GF(2), `1_B(t) = 1_A(t) + 1_A(t-1)`.  Let

```
g = product_{t in A} s_t.
```

The aligned swaps commute, so the interior factors cancel and

```
componentSwitch = g * rho * g^{-1} * rho^{-1}.
```

This is the exact algebra visible in the minimal benign example
`S=00101, L=3`: the component has two AltF chords
`(1 3)(2 4)`, while the listing itself differs from the truth by the single
arc swap `g=(1 3)`.

This suggests an **innermost-block deletion** proof with a much more explicit
invariant:

1. Cohn--Lempel implies that every interlace component of a full-cycle switch
   system has even size (indeed its diagonal block is a nonsingular hollow
   symmetric GF(2) matrix, hence even-dimensional).
2. Pick an innermost laminar maximal-repeat block/component.
3. Integrate its even boundary-switch set to the arc swap `g` above.
4. Use `ladder_arc_eq` (or the stronger length-`L` window equality on the
   interior) to prove `g` preserves `vtx`.
5. Innermostness should imply that the points moved by `g` contain no support
   endpoint of any other block. Therefore `g` commutes with the remaining
   AltF transpositions.
6. The commutator identity then shows that conjugating the old listing by
   `g^{-1}` deletes exactly this component from `AltF`.
7. Because `g` preserves `vtx`, the old and new listings are pointwise
   vertex-equivalent (up to only the harmless choice of cyclic origin).
8. Induct on the number of interlace components.

This route may avoid reconstructing an arbitrary listing after deletion:
define the new listing explicitly by composing the old listing with `g^{-1}`.
`Issue94Reconstruct` remains a useful independent fallback/check.

### What must be checked before formalizing this route

- The exact orientation of the commutator with the repository's convention
  `AltF = Succ * prevPos`.
- The valid shift interval: `g` should swap starts whose complete length-`L`
  windows lie inside the maximal repeat.  In the `00101` example this is why
  `g` has one swap although the AltF component has two boundary swaps.
- Whether an innermost block is enough to ensure that no other AltF support
  point lies in the interior moved by `g`.  If this is not already implied by
  the laminar/block geometry, isolate the exact cyclic-order lemma rather than
  assuming component independence.
- If a single maximal-repeat block can contain several interlace components,
  do **not** assume block=component. Either prove the isolated
  `ShiftPairInterlace` statement or perform the antiderivative component by
  component.

## Disjointness of the antiderivative swaps comes for free from P2

A potential problem with the antiderivative construction is overlap: even if the
actual `AltF` chords are disjoint, two *interior* aligned swaps
`s_t = (p+t,q+t)` and `s_u = (p+u,q+u)` might a priori share an endpoint.

In the relevant long-window range this cannot happen, and no new repeat theorem
is needed.

For every valid shift (at least `t + (L-1) <= e`), `ladder_arc_eq` gives

```
vtx (p+t) = vtx (q+t).
```

Suppose two distinct aligned swaps share exactly one endpoint. Combining their
two `vtx` equalities gives three distinct starts carrying the same
`(L-1)`-mer. But under P2 + primitivity + `2 <= L <= K`,
`P2RepeatResidual.P2.imp_nodeCount_le_two` says every such fibre has
multiplicity at most two. Contradiction.

If they shared both endpoints then, after quotienting the swap as an unordered
pair, they are the same aligned swap; the shift-coordinate uniqueness lemma
should package this separately.

Therefore the valid aligned swaps used in `g` are pairwise disjoint and hence
commute.

This was also checked exhaustively on primitive P2 words: binary through
`K <= 10` and ternary through `K <= 7` had no overlapping valid
full-window ladder swaps.

### Exact small lemmas to formalize

The block-vertex front should isolate these before attempting the whole
conjugation:

1. `ladderAligned_vtx`: valid shift `t` implies
   `vtx (rotAdd t p) = vtx (rotAdd t q)` (wrapper around
   `ladder_arc_eq`).
2. `ladderAligned_shared_endpoint`: if two valid aligned unordered pairs
   share an endpoint, they are the same unordered pair. Prove by
   `P2.imp_nodeCount_le_two`.
3. `ladderShift_unique`: within the valid shift interval, equal aligned
   unordered pairs have equal shift coordinate. This should follow from (2)
   plus the ordered/cyclic interval bounds; do not use raw `Fin` injectivity
   without those bounds.
4. `alignedSwap_comm`: distinct valid aligned swaps commute, now immediate
   from endpoint-disjointness.

With these lemmas, the algebra
`g * rho * g^{-1} * rho^{-1}` can be normalized by commuting/cancelling
transpositions rather than by a global permutation calculation.

## Empirical check of the complete conjugation proof shape

A direct executable model was run on every nontrivial genuine alternative
reachable in the following bounded regime:

- primitive binary P2 words,
- `2 <= L <= K <= 9`,
- every involution preserving the `(L-1)`-mer fibres,
- retaining only cases where `f * rho` is one cycle.

There were **1110** such nontrivial cases. For every interlace component, all of
the following held with zero failures:

- all its chords had one maximal-extension block;
- each chord had a unique valid ladder-shift coordinate;
- the component had even cardinality;
- the antiderivative aligned swaps were pairwise disjoint;
- every antiderivative swap preserved `vtx`;
- the resulting `g` commuted with all remaining `AltF` chords;
- the commutator identity produced exactly the deleted component; and
- `f * rho = g * (f_without_component * rho) * g^{-1}`.

This is evidence, not a theorem, but it tests the *exact algebraic proof plan*
rather than only the final uniqueness statement.

The only item in that list that still appears to require a genuinely external
or new combinatorial ingredient is **even cardinality of each interlace
component**. Cohn--Lempel supplies it immediately: a one-cycle switch system
has nonsingular interlacement matrix; connected components are diagonal blocks;
each block is a nonsingular alternating matrix over GF(2), hence has even
dimension. The latter even-dimension fact has an elementary symplectic-basis
proof valid in characteristic two.

## We only need one direction of Cohn--Lempel: a direct GF(2) coloring proof

The full equality
`#cycles(f*rho) = nullity(interlaceMatrix(f)) + 1` is stronger than this
project needs.  The consumed implication is only

```
VisitsAll (f * rho)  ->  ker(interlaceMatrix(f)) = {0}.
```

There is a short direct proof that stays close to the permutation model and
should be substantially easier to formalize than the complete
Cohn--Lempel equality.

Orient every chord `c=(a,b)` according to a fixed linearization of the truth
cycle.  Let `I_c(x)` be the GF(2)-indicator of the half-open circular arc
`(a,b]`.  For a GF(2) coefficient vector `z` on the chords define

```
color_z(x) = sum_c z_c * I_c(x).
```

Two elementary identities drive the proof.

### 1. Moving one truth step detects selected chord endpoints

For `rho` the truth successor,

```
color_z(rho^{-1} y) + color_z(y)
```

is `z_c` when `y` is an endpoint of chord `c`, and is zero away from
all chord endpoints.  This is just the fact that the boundary of the interval
indicator `I_c` is the two endpoints of `c`.

### 2. Jumping across a chord detects its interlacements

If `y` is an endpoint of chord `c` and `f y` is its other endpoint, then

```
color_z(f y) + color_z(y)
  = z_c + sum_d interlaces(c,d) * z_d.
```

The own-chord term is `z_c`; another chord `d` contributes exactly when
the two endpoints of `c` lie on opposite sides of `d`, i.e. exactly when
`c` and `d` interlace.

Hence if `M z = 0`, with `M` the hollow symmetric interlacement matrix,

```
color_z(f y) + color_z(y) = z_c
```

at an endpoint of `c`. Combining this with identity (1), for
`J = f * rho`,

```
color_z(J x) = color_z(x)
```

for every `x`.

If `z != 0`, choose a selected chord.  The boundary identity (1) shows
`color_z` changes at one of its endpoints, so it is nonconstant.  But a
`VisitsAll J origin` permutation has only one orbit, hence every
`J`-invariant function is constant. Contradiction.

Therefore a one-cycle switch system has interlacement matrix with trivial
kernel.

This is precisely the direction needed for component parity/deletion.  It
matches the Cohn--Lempel theorem (and Moran's rank formulation), but it can be
proved without any circuit-count theorem.

### Component corollary

If `C` is a connected component of the interlace graph, a kernel vector of
the principal block `M_C` extends by zero to a kernel vector of `M`, because
there are no interlace edges from `C` to its complement.  So every component
block also has trivial kernel.

The block is a hollow symmetric matrix over GF(2), i.e. the matrix of a
nondegenerate alternating bilinear form. Such a form has even dimension
(symplectic Gram--Schmidt works in characteristic two). Thus every interlace
component has even cardinality.

For Lean, the pure-Cohn--Lempel front should now target this **kernel
injectivity lemma**, not the stronger nullity equality. The GF2 front should
target only:
- extension-by-zero of a component kernel vector; and
- nondegenerate alternating finite-dimensional spaces have even dimension.

No determinant, rank-nullity cycle formula, or circuit-count infrastructure is
needed.

## Exact repository composition convention (checked against `BBTUniqueEulerian`)

The antiderivative/conjugation route has now been checked against the actual
definitions, so there is no remaining left-vs-right composition ambiguity.

The repository defines

```
Succ sigma = sigma * rho * sigma^{-1}
AltF sigma = Succ sigma * rho^{-1}
```

(where multiplication here means function composition, left factor applied
last in the usual mathematical notation). Consequently

```
Succ sigma = AltF sigma * rho.
```

Let `f = AltF sigma`, and modify the listing by postcomposing its values with
a permutation `g`:

```
sigma' = g * sigma.
```

Then

```
Succ sigma' = g * Succ sigma * g^{-1}
AltF sigma' = g * f * rho * g^{-1} * rho^{-1}.             (1)
```

Now split the old switch involution as

```
f = c * h
```

where `c` is the product of the transpositions in the interlace component to
be deleted and `h` is the product of all remaining support transpositions.
(All AltF transpositions are disjoint, so `c` and `h` commute.)

Suppose the ladder antiderivative `g` satisfies

```
c = g^{-1} * rho * g * rho^{-1}.                           (2)
```

and `g` commutes with `h`.  Substituting (2) in (1) gives

```
AltF sigma'
  = g * c * h * rho * g^{-1} * rho^{-1}
  = g * (g^{-1} * rho * g * rho^{-1}) * h * rho * g^{-1} * rho^{-1}
  = h
```

(the last cancellation uses `g h = h g`; `h` is a product of disjoint
transpositions away from the arc moved by `g`).

So **postcomposing the listing by the vertex-preserving arc swap `g` deletes
exactly the component `c` from `AltF`**.

For the intended `g`, which is itself a product of disjoint aligned swaps,
`g^{-1}=g`.  Conjugation by `rho` shifts an aligned ladder swap by one
coordinate, so if `g = product_{t in A} s_t`, equation (2) becomes the GF(2)
boundary identity

```
B = A triangle (A+1),
```

where `B` is the set of component-switch coordinates.  This is precisely the
discrete-antiderivative construction above.

### Consequence for the remaining Lean proof

The project-specific proof can now be factored into four small lemmas rather
than a global traversal induction:

1. **boundary:** the switch-coordinate set `B` of the chosen component is the
   boundary of a union of ladder intervals `A`;
2. **labels:** the resulting aligned arc-swap `g_A` preserves `vtx`, using
   `BBTLadder.ladder_arc_eq`;
3. **separation:** for a suitably innermost chosen block/component, `g_A`
   commutes with the remaining AltF support `h`;
4. **algebra:** equation (1)+(2) gives
   `AltF (g_A * sigma) = h`, while label preservation gives
   `VertexCycleEq (g_A * sigma) sigma`.

Items 1--3 are now the only genuinely genome/cyclic-order content of this
route. Item 4 is pure permutation algebra and should be formalized first in a
small module with no heavy issue-94 imports.
