# Board 94, front `94conj` --- the generic conjugacy adapter for `VertexCycleEq`

Companion note for `AssemblyP1/Issue94ConjugacyAdapter.lean` and
`scripts/verify_conjugacy_adapter_94.py`.

## 1. The packet

> We have transition maps `f, fprime` with jumps `J = f ∘ nextPos` and
> `Jprime = fprime ∘ nextPos`, both single cycles, and seek a `vtx`-preserving
> conjugacy `h` between `J` and `Jprime`.  **Determine the exact additional
> alignment/rotation condition under the repository definition of
> `VertexCycleEq`, then state/prove the smallest lemma that turns such a
> conjugacy into `VertexCycleEq` between the corresponding
> reconstructed/listing traversals.**  Be precise about whether rotation is on
> listing indices or genomic coordinates; do not assume they are the same.

## 2. The answer

**The conjugacy is *not* enough, and the gap is exactly one rotation, read on the
wrong set of indices.**  The repository definition (`BBTEulerian.lean:217`) is

```text
VertexCycleEq hK L S σ τ  =  ∃ k : Fin K, ∀ i : Fin K,
    vtx hK L S (σ i) = vtx hK L S (rotAdd hK k.val (τ i)).
```

`k` is `rotAdd`ed onto a **start**.  So `k` is a rotation of **genomic
coordinates**; it is *not* a rotation of the listing index `i`.  Everything below
is the difference between those two readings.

The reconstructed traversals (`Issue94Reconstruct.sigEquiv`) are orbit listings:

```text
σ i = J^[i] (origin),            σ' i = (J')^[i] (origin).
```

### 2.1 What the conjugacy transports (free)

`h (J^[i] (origin)) = (J')^[i] (h (origin))` (`iterate_conj`), so with
`vtx`-preservation,

```text
vtx (σ i) = vtx ((J')^[i] (h (origin))).                            (★)
```

Two consequences, both in the kernel:

| result | content |
|---|---|
| `listingIndex_conj` | `∃ k₀, ∀ i, vtx (σ i) = vtx (σ' (rotAdd k₀ i))` --- rotation on **listing indices**, where `k₀` is the unique `J'`-**orbit index** of `h (origin)` |
| `vertexCycleEq_iff_orbit_conj` | `VertexCycleEq σ σ'` ⟺ `∃ k, ∀ i, vtx ((J')^[i] (h (origin))) = vtx (rotAdd k ((J')^[i] (origin)))` --- i.e. the residual after the conjugacy has done all it can is *precisely* the genomic rotation |

So the free statement delivers a rotation on **listing indices**, and the
target `VertexCycleEq` wants a rotation on **genomic coordinates**.

### 2.2 The exact additional condition

`RotAligned hK J' k h` (`AssemblyP1/Issue94ConjugacyAdapter.lean`), two clauses:

1. `h (origin hK) = rotAdd hK k.val (origin hK)` --- the genomic rotation `k`
   carries the origin of the prime listing to the point at which `h` starts;
2. `∀ x, J' (rotAdd hK k.val x) = rotAdd hK k.val (J' x)` --- the same rotation
   is an automorphism of the prime jump.

`vertexCycleEq_of_conjugacy` is then the whole adapter: `RotAligned` gives
`VertexCycleEq σ σ'` **with witness `k` read as a genomic rotation**.  Three lines
of proof: `iterate_conj` moves `σ`'s vertex cycle onto the `J'`-cycle from
`h (origin)`; clause 1 identifies `h (origin)` with `rotAdd k` of the origin;
clause 2 pulls that rotation along the `J'`-cycle
(`iterate_comm_rotAdd`).

Notes on the two clauses:

* They are **not redundant.**  Clause 1 alone is always satisfiable, because
  `rotAdd hK k.val (origin hK) = k` (`rotAdd_origin`), so `k` is *named by the
  start it carries the origin to*: take `k = h (origin hK)`.  Clause 2 alone is
  automatic at `k = origin hK` (`rotAdd_origin_comm`).  It is their
  **simultaneity at one and the same `k`** that is the content.
* Clause 2 is a statement about `f'`, not about the jump:
  `jump_commute_iff` gives `rotAdd k` centralises `J' = f' ∘ nextPos` **iff** it
  centralises `f'`.  So `vertexCycleEq_of_conj_comm` states the adapter with no
  `jump` left in the hypotheses --- the packet's own vocabulary.
* `single` is *not* needed for this step.  It is needed (a) to make `sigEquiv` a
  permutation at all, and (b) for the listing-index statement, where
  `BBTUniqueEulerian.iterate_G_eq` + `iterate_mod` reduce the iterate index
  modulo `K`.

### 2.3 Where the condition is automatic

| theorem | extra condition | witness of `VertexCycleEq` |
|---|---|---|
| `vertexCycleEq_of_conj_origin` | `h (origin hK) = origin hK` | `origin hK`, and the two listings agree **pointwise**: `vtx (σ i) = vtx (σ' i)` |
| `vertexCycleEq_of_conj_nextPos` | `J' = nextPos`, i.e. `f'` is the identity re-pairing | `h (origin hK)`, unconditionally |

The second is also the only case in which the two readings of the rotation
*coincide*, because `(J')^[i] = rotAdd i` and then the `J'`-orbit index of a start
is the start itself.

## 3. The refutation: the conjugacy alone is not enough

`K = 5`, `L = 3`, `S = 00001`, kernel-checked in
`AssemblyP1/Issue94ConjugacyAdapter.lean` §9.

* `f = id`, so `J = nextPos` (single) and `σ = (0 1 2 3 4)`, the truth's own
  cyclic reading;
* `f' = (0 1 2)`, label-preserving because `0, 1, 2` all spell `00`, with
  `J' = f' ∘ nextPos = (0 2 3 4 1)` a single `5`-cycle and
  `σ' = (0 2 3 4 1)`;
* `h = (0 1)`, a `vtx`-preserving conjugacy `J → J'`;
* `ListingIndexEq` **holds**, at `k₀ = 4` --- the `J'`-orbit index of
  `h (origin) = 1` (`conj_listingIndexEq_00001`), so §2.1 is not vacuous;
* `ListingVertexEq` **fails**: no `k` works
  (`not_listingVertexEq_00001`, hence `not_vertexCycleEq_00001`);
* `RotAligned` fails precisely at the forced `k = 1`
  (`not_rotAligned_00001`), because `rotAdd hK 1` does not centralise `J'`.

**The two readings are different numbers at the smallest refuted instance:**
`k₀ = 4` (listing index) versus `k = 1` (genomic coordinate).

This is **not** a defect of the adapter.  It is the phenomenon `thm:BBT` is
about: `σ'` is a genuine alternative `EulerianCycle` of the multigraph of
`00001` which is not the truth's vertex cycle, and `00001` has the long
obstruction `thm:BBT` predicts (`longObstruction_00001`: the length-`3` window
`000` is a maximal triple repeat at the distinct starts `0, 1, 2`, and
`L - 1 = 2 ≤ 3`).  Conversely `σ` **is** the truth's vertex cycle
(`vertexCycleEq_refl_00001`), so the instance is not vacuous in the other
direction either.

## 4. Composition with `Issue94TransposePreserve`

`BBTTranspose.vertexCycleEq_transposition` is right because `VertexCycleEq σ τ`
at witness `k` is the *pointwise* statement `∀ i, vtx (σ i) = vtx (rotAdd k (τ i))`:
swapping two starts spelling the same `(L-1)`-mer touches only the left-hand
side, so the witness survives.  The adapter uses exactly the same property --- it
never transports anything *through* the witness, it only produces one.  Hence
`vertexCycleEq_transpose_conj`: post-compose the adapter's conclusion by any
vertex-invisible transposition, at the **same** witness.

## 5. Anti-vacuity and the finite/decidable forms

`sigEquiv` is `noncomputable`, so the refutation of §3 is stated on the
computable `sigFun` and bridged by `vertexCycleEq_iff_listing`
(`sigEquiv_apply` is `rfl`).  `listingVertexEq_0101` (`S = 0101`, `K = 4`,
`L = 3`, identity re-pairing on both sides) shows the adapter's conclusion is
satisfiable at witness `0`.

## 6. Evidence

`scripts/verify_conjugacy_adapter_94.py` re-derives every claim independently of
Lean, exhaustively over all words, all label-preserving permutations `f, f'` whose
jumps are single `K`-cycles, and all `vtx`-preserving conjugacies between them
(conjugacies between two `K`-cycles are in bijection with the image of the base
point, so the enumeration is complete).

| predicate | claim | result (`--maxk 7`) |
|---|---|---|
| scope | | binary `K ≤ 7`, `L ∈ {3, 4}`; ternary `K ≤ 6`, `L = 3` |
| pairs | `(f, f')` with both jumps single | 2 197 810 |
| — | `vtx`-preserving conjugacies between them | 15 163 678 |
| C1 | conjugacy ⟹ listing-index version | **0 violations** |
| C2 | `RotAligned` ⟹ genomic version | **0 violations** |
| C3 | conjugacy ⟹ genomic version | **3 568 counterexamples**, smallest `K = 5, L = 3, S = 00001` --- i.e. exactly §3, and **nothing at `K ≤ 4`** |
| C4 | `J' = nextPos` ⟹ `RotAligned` at `k = h (origin)`, hence conjugacy ⟹ genomic version | 29 832 instances, **0 violations** |
| C5 | `rotAdd k` centralises `J'` iff it centralises `f'` | **0 violations** |

A smaller run (`--maxk 5`) gives the same verdict with 21 974 conjugacies and 24
counterexamples.  Reproduce with

```sh
python3 scripts/verify_conjugacy_adapter_94.py --maxk 7
```

C3 is the only *negative* prediction, and it is what §3 is about.  Note C3's
counterexamples are exactly the instances where the long obstruction is present,
which is what `thm:BBT` says must happen.

## 7. What remains open

Unchanged by this front.

* **The hard direction is untouched**: nothing here produces a `vtx`-preserving
  conjugacy, and `Issue94Reconstruct` only supplies the listings.  Existence of
  an alternative `vtx`-preserving conjugacy is what `BBT`/`Lemma 1`+`Lemma 2`
  must rule out; this module says what one would be worth.
* `BBTEulerian.UniqueEulerianCycle`, `BBTEulerian.EulerianCycleObstruction`,
  `hPevzner` and `Issue94ObstructionEquiv.BBT94.ObstructionFromBBT` are all as
  open as recorded in `AssemblyP1/BBTEulerian.lean`.
* No existing definition was changed; no `sorry`, no `admit`, no `axiom`, no
  `native_decide`, no `unsafe`.  The module ends in a `#print axioms` audit.