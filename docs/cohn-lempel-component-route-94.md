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

## Status after the deletion-adapter front (`AssemblyP1/Issue94DeleteAdapter.lean`)

Two of the five items in "Recommended division of labor" above are now
kernel-checked, and the fourth is **weaker than specified**.

### Done: the deletion adapter

`AssemblyP1/Issue94DeleteAdapter.lean`, importing only
`AssemblyP1/Issue94Reconstruct`:

| name | content |
| --- | --- |
| `delOn f D q` | the deletion: `q` on `D`, `f q` off `D` |
| `IsOrbitClosed f D` | `∀ q, q ∈ D ↔ f q ∈ D`: `D` is a union of `f`-orbits |
| `delOn_bijective` | the deletion is a permutation of the starts |
| `delOn_vtx` | the deletion preserves the `(L-1)`-mer labelling |
| `exists_eulerianCycle_of_deleted` | **the adapter**: deleted tour single ⟹ `∃ σ, EulerianCycle hK L S σ`, by `Issue94Reconstruct.exists_eulerianCycle_of_labelPreserving_single` |

The one-cycle hypothesis is *not* discharged; it is the Cohn--Lempel input.

### Done, and weaker than the note asked for: vertex-cycle invisibility

The note asks for "the explicit maximal-repeat arc-swap conjugator". The
adapter front proves a strictly weaker and more useful statement instead:

> **`vertexCycleEq_of_conjJump`.**  If the deleted tour `jump hK f'` is
> conjugate to the old tour `jump hK f` by *any* equivalence `c` of the starts
> preserving the `(L-1)`-mer labelling, and `jump hK f = Succ hK σ`, then the
> listing reconstructed from the deleted tour is vertex-cycle equal to `σ`.

`vertexCycleEq_deletedConj_of_old` combines it with the old listing's own
`VertexCycleEq`, so the route now reads

```
  (old σ vertex-cycle equal to the truth)     ← residual R1, open
  + (deleted tour Cohn--Lempel conjugate)     ← external input, open
  ⟹  new σ' vertex-cycle equal to the truth
```

Both remaining inputs are isolated and neither is inhabited by this module; the
conjugacy condition is recorded as the `Prop` `DeletedConjProp`.

Consequences worth recording for the other fronts:

* The **maximal-repeat arc swap is not needed** by this criterion. `c` only has
  to be a `vtx`-preserving equivalence; it is not required to be the swap of two
  equal ladder arcs, and no `SameExtension`/`ladder_arc_eq` geometry enters.
  Consequently `ShiftPairInterlace` (§ "Block connectivity") is **not** on the
  critical path for this route, unlike what the note assumed.
* Neither the bijectivity of `f`, `f'` nor the `single` clause on the *old* tour
  is used by the criterion. So the criterion is not blocked by anything about
  the old traversal; the only combinatorics left is the deleted tour being one
  circuit, i.e. the Cohn--Lempel/GF(2) corollary.

### Still open on this route

- **Pure Cohn--Lempel** and the **GF(2) corollary** (nonsingularity of a
  component block). Both external; neither formalized.
- **`DeletedConjProp`**: that component deletion conjugates the tour by a
  `vtx`-preserving equivalence of the starts.
- **Residual R1** for the old listing (`Issue94R1LongWindow.lean`,
  `R1_shift_step`), as before.
