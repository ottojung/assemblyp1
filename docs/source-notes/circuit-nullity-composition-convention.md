# Circuit-nullity statement: classical form and repository composition convention

_Status: source-convention note for the Cohn–Lempel route (board 94), 2026-10-06.
Maps the classical cycle-count equality to the repository's permutation
convention and the whole-component deletion step. No proof code; the Lean
development lives in `AssemblyP1/Issue94InterlaceComponents.lean` and
`AssemblyP1/BBTUniqueEulerian.lean`._

## 1. Classical statement (source fact)

Cohn–Lempel (1972), in the formulation restated by Traldi (2011), takes a
full cycle `rho` and pairwise disjoint transpositions whose product is `f`,
with interlacement matrix `X` over GF(2), and states

```
number_of_cycles (rho * f) = nullity_GF2(X) + 1.
```

Traldi writes the cyclic permutation first, followed by the disjoint
transpositions. Equivalently, `rho * f` is a full cycle iff `X` is
nonsingular. Beck (1977) extends the equality beyond commuting/disjoint
transpositions.

See [`../cohn-lempel-component-route-94.md`](../cohn-lempel-component-route-94.md)
§"Pure permutation input from the literature" for references.

## 2. Repository composition convention (definition)

The repository defines, for a listing `sigma` and truth successor `rho`:

```
Succ sigma  =  sigma * rho * sigma^{-1}
AltF sigma  =  Succ sigma * rho^{-1}
```

(function composition, left factor applied last in the usual mathematical
notation). Consequently

```
Succ sigma  =  AltF sigma * rho.
```

Write `f = AltF sigma`. Then the alternative traversal is `J = f * rho`, and
the one-cycle condition is `VisitsAll J origin`.

## 3. Mapping the classical statement

| Classical | Repository |
|---|---|
| `rho` (full cycle) | truth successor `nextPos hG` |
| product of disjoint transpositions `f` | `f = AltF sigma` (involution) |
| classical `rho * f` | repository `J = f * rho = Succ sigma` |
| `number_of_cycles(...) = 1` | `VisitsAll (f * rho) origin` |
| `nullity_GF2(X) = 0` | `ker(interlaceMatrix f) = {0}` |

The source and repository multiply `rho` and `f` in opposite orders. This does
not change the cycle count: because `f` is an involution,

```
f * (rho * f) * f⁻¹ = f * rho.
```

Hence `rho * f` and `f * rho` are conjugate permutations and have the same
orbit decomposition. The interlacement matrix is still the matrix of the
disjoint transpositions, ordered around the truth cycle `rho`.

After this order bridge, the consumed direction is only:

```
VisitsAll (f * rho) origin  ->  ker(interlaceMatrix f) = {0}.
```

The full nullity equality is stronger than needed; see the coloring proof in
[`../cohn-lempel-component-route-94.md`](../cohn-lempel-component-route-94.md)
§"We only need one direction".

## 4. Whole-component deletion in this convention

**Block structure.** The interlacement matrix `X` is block diagonal over the
connected components of the interlace graph. Each block is nonsingular
(inherited from the whole matrix), hence even-dimensional (hollow symmetric
over GF(2)).

**Deletion step.** Split `f = c * h` where `c` is the product of transpositions
in one interlace component and `h` is the product of all remaining support
transpositions. All AltF transpositions are disjoint, so `c` and `h` commute.

Postcompose the listing by a permutation `g`:

```
sigma' = g * sigma.
```

Then

```
Succ sigma' = g * Succ sigma * g^{-1}
AltF sigma' = g * f * rho * g^{-1} * rho^{-1}.                (1)
```

Suppose `g` satisfies

```
c = g^{-1} * rho * g * rho^{-1},                             (2)
```

and `g` commutes with `h`. Substituting (2) into (1):

```
AltF sigma' = g * (g^{-1} * rho * g * rho^{-1}) * h * rho * g^{-1} * rho^{-1}
            = h.
```

So **postcomposing the listing by `g` deletes exactly the component `c` from
`AltF`**. The new listing `sigma'` has `AltF sigma' = h`, and if `g` preserves
vertex labels (`vtx`), then `VertexCycleEq sigma' sigma` holds.

**Existence of `g`.** For the intended `g` (a product of disjoint aligned
ladder swaps), `g^{-1} = g`, and conjugation by `rho` shifts an aligned swap
by one coordinate. Writing `g = product_{t in A} s_t`, equation (2) becomes
the GF(2) boundary identity `B = A triangle (A+1)`, where `B` is the set of
component-switch coordinates. This is the discrete-antiderivative construction
in [`../cohn-lempel-component-route-94.md`](../cohn-lempel-component-route-94.md)
§"Stronger local algebra".

## 5. Summary

The classical circuit-nullity equality, restricted to the consumed direction
(one-cycle implies nonsingular interlacement matrix), licenses whole-component
deletion: each interlace component is an independent nonsingular block, and
the repository's convention `Succ sigma = AltF sigma * rho` makes the
deletion an explicit postcomposition `sigma' = g * sigma` with `g` satisfying
the commutator identity (2). The new listing drops exactly the chosen
component from `AltF` while preserving the vertex cycle.
