# Board 94, front `94fibres`: doubled-fibre uniqueness and the product-over-fibre-swap recipe

This note records the fibre-uniqueness step of the long-window route and, in
particular, the recipe it unlocks: **the candidate label-preserving permutation
is the product of the transpositions attached to the doubled `(L-1)`-mer
fibres**, and *overlapping character-repeat arcs are not an obstacle to that
construction*.

The Lean module is `AssemblyP1/Issue94DoubledFibres.lean` (namespace
`AssemblyP1.Issue94DoubledFibres`).  **It has not been compiled** --- see
"Compile status" below.

## 1. The lemma

> Under `P2` and primitivity, every `(L-1)`-mer fibre has size `≤ 2`.  Two ladder
> rung pairs that share a start are the same unordered pair.

Proof shape, in the three steps the module formalizes:

1. `P2.imp_nodeCount_le_two` (the `R1` / `Lemma 1` multiplicity cap) says
   `nodeCount k ≤ 2` for every `(L-1)`-mer `k`;
   `card_nodeStartsOf` identifies that with `|nodeStartsOf k| ≤ 2`
   (`Issue94DoubledFibres.fibre_card_le_two`).
2. A rung pair `(a, b)` has `vtx a = vtx b` (`BBTLadder.DoubledPair`), so both
   starts lie in the *same* fibre `nodeStartsOf (vtx a)`.  Two rung pairs
   meeting at one start therefore put three starts in one fibre, unless the two
   other members coincide --- which the cap forbids
   (`Issue94DoubledFibres.doubledPair_shared`, and the counting lemma
   `three_fibre_eq`).
3. Stated at the level of the two-element blocks, which is the form the product
   consumes: `pair_disjoint_or_equal` says two `DoubledPair`s are **either the
   same unordered pair or share no start**, and `doubledPair_disjoint` resolves
   the disjunction --- two *distinct* doubled fibres give **disjoint** pairs.

Two supporting facts matter for the construction and are proved separately:

* `doubledPair_unique`: if `(a, b)` and `(a', b')` are `DoubledPair`s with
  `vtx a = vtx a'`, then `{a, b} = {a', b'}`.  So the pair attached to a fibre is
  a **function of the label**, not a choice.
* `doubledPair_ne`: a `DoubledPair` really has two distinct members, so the
  block has cardinality `2` and the fibre really is the block.

## 2. The recipe

Let

```text
  D  =  { k : Fin (L-1) -> α | (nodeStartsOf hK S k).card = 2 }     -- the doubled fibres
  τ_k =  the transposition exchanging the two starts of that fibre
  h   =  ∏_{k ∈ D} τ_k
```

Three properties, and what each is needed for.

**`h` is well defined, and order-independent.**  Each `τ_k` is determined by
`k` alone (`doubledPair_unique`), and `D`'s members give pairwise **disjoint**
supports (`doubledPair_disjoint`).  Transpositions on disjoint pairs commute
(`swap_trans_comm_of_disjoint`), so the product over the *set* `D` does not
depend on the enumeration.  This is what makes the *component deletion* of
`docs/cohn-lempel-component-route-94.md` legitimate: deleting the factors of one
interlace component leaves a product of **disjoint** transpositions on the
remaining factors, which is exactly the shape Cohn--Lempel and Beck need.

**`h` is a label-preserving bijection.**  Each factor is pointwise
`vtx`-preserving (`labelPreserving_doubledPair`), and label preservation
composes (`labelPreserving_comp`), so
`doubledSwaps_bijective` / `doubledSwaps_labelPreserving` give
`Function.Bijective h` and `∀ q, vtx (h q) = vtx q`.  That is precisely the
`hLP` clause of `Issue94Reconstruct.exists_eulerianCycle_of_labelPreserving_single`.
Note that **disjointness is not used here**: any list of equal-`(L-1)`-mer
swaps works.  Disjointness buys the Cohn--Lempel *shape*, not label preservation.

**`h` is invisible to the vertex cycle.**  Composing a `VertexCycleEq` listing
with the same transpositions preserves `VertexCycleEq` with the *same* rotation
witness (`BBTTranspose.vertexCycleEq_transpositionList`, hence
`vertexCycleEq_doubledSwapsOn`).  Again no disjointness is needed.

## 3. Why overlapping character-repeat arcs are not a problem

The tempting worry is that two doubled fibres could have *overlapping maximal
repeat arcs*, so that "swapping the two realisations of each branch vertex"
would move points across each other and no longer be a product of disjoint
transpositions.  The module separates the two objects:

| object | what it is | what controls it |
|---|---|---|
| the **character-repeat arc** of a doubled pair | the maximal repeat `{p, q}` it sits in | `maxPairStart` / `maxPairLen`; arcs of different pairs **do** overlap |
| the **support** of the swap `τ_k` | the two-element set `{a, b} = nodeStartsOf k` | the multiplicity cap; supports of different `k` are **disjoint** |

`doubledPair_disjoint` is a statement about the second row only.  Nothing in it,
and nothing in `swap_trans_comm_of_disjoint`, mentions arcs, interleaving or
maximal repeats.  So an overlap of arcs is invisible to the construction: the
factor attached to a fibre is defined by the fibre, and two fibres never share a
start.

The `S = AABAB = 00101`, `L = 3` instance of §4 of the module is the
certificate, and it is a primitive `P2` word
(`P2RepeatResidual.cex_is_shiftPrimitive`, `P2RepeatResidual.cex_is_p2`):

* `01` is spelled exactly at starts `1, 3`, `10` exactly at `2, 4`, so both are
  `DoubledPair`s (`cex_doubledPair_13`, `cex_doubledPair_24`, both `decide`);
* the two chords **interleave** (`cex_chords_interleave`), i.e. the two
  character-repeat arcs overlap --- this is the configuration of
  `BBTChords.raw_node_crossing_not_maximal`;
* the two transpositions are nevertheless **disjoint** (`cex_pairs_disjoint`)
  and **commute** (`cex_pairs_commute`);
* their product is not the identity (`cex_doubledSwaps_ne`): the candidate
  re-pairing genuinely re-pairs, so the whole packet is not vacuous.

This is also why the negative results recorded elsewhere do not bite here.
`Issue94InterlaceComponents` §5 refutes "the traversal walks the support
clockwise" (`T6`) and "a component is repaired by a rotation of its own points"
(`T7`); neither is needed, because `h` is not a rotation of anything --- it is a
product of disjoint transpositions, each attached to a *fibre*.

## 4. What is left

`exists_eulerianCycle_of_doubledSwaps` concludes
`∃ σ, EulerianCycle hK L S σ` from the product `h` and **one** hypothesis:

```text
  VisitsAll (jump hK h) (origin hK)        --  h ∘ nextPos is a single circuit
```

That hypothesis is the entire remaining content of this route.  It is what
Cohn--Lempel (1972) and Beck (1977) supply for a product of disjoint
transpositions --- nonsingularity of the binary link matrix, over `GF(2)` --- via
`docs/cohn-lempel-component-route-94.md`.  No genome theory is needed to state
it, and this module supplies no part of it.

Two further steps are *not* formalized and are recorded as such:

* order-independence of the *whole* product `∏_{k ∈ D}` (the commutation step and
  the disjointness hypothesis it consumes are proved; the induction over `D` is
  not);
* the pointwise variant of the recipe, `h x =` the other member of
  `nodeStartsOf (vtx x)`, which needs no global enumeration but requires
  extracting "the other member" of a two-element `Finset`; `doubledPair_unique`
  is what makes it legitimate, and it is proved.

## 5. Relation to the neighbouring packets

* `BBTCrossingCoalesce.three_starts_ne` / `collision_forces_pair` are the same
  counting step without a `DoubledPair` hypothesis.  `Issue94DoubledFibres`
  re-derives the counting against `nodeStartsOf`/`DoubledPair` and deliberately
  does not import `BBTCrossingCoalesce` (whose §5 carries two uninhabited
  `Prop`s).
* `BBTTranspose.vertexCycleEq_transpositionList` is the invisibility step; it
  was already proved and is used here unchanged.
* `Issue94Reconstruct.exists_eulerianCycle_of_labelPreserving_single` is the
  adapter.  **Note that `AssemblyP1/Issue94Reconstruct.lean` is currently not
  imported by `AssemblyP1.lean`**, so it is not in the compiled set either; the
  adapter corollary of this module inherits that status.  Flagged here because
  `docs/cohn-lempel-component-route-94.md` lists it among the "durable
  endpoints already proved".

## Compile status

`.lake/packages/mathlib` is empty in this checkout and there are no build
artefacts, so no `lake build` is possible, not even for a single file.
`Issue94DoubledFibres.lean` is therefore **not** registered in
`AssemblyP1.lean`, and the registered set stays green.  The first compile of this
module --- and registration, plus a check of `Issue94Reconstruct.lean` --- is a
required follow-up.  The kernel claims made here are claims about the Lean
text; the only kernel-checked inputs are the ones it quotes from the registered
set.
