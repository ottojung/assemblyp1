# Board 94, front `94cle` — the exact whole-interlace-component deletion corollary

Companion to `AssemblyP1/Issue94CLEDeletion.lean` and
`scripts/verify_cle_parity_94.py`. This note finishes the separation that
`docs/cohn-lempel-component-route-94.md` §"Immediate corollary: delete an
interlace component" only sketched, and it records what is *not* proved.

Status of the Lean file in this commit: **written but not kernel-checked here.**
The session was explicitly instructed not to run `lake build`, so a reviewer must
run `lake build AssemblyP1.Issue94CLEDeletion` before trusting it. Nothing in the
file depends on the OOM-prone `Issue94OrbitSearch` chain (it imports `Mathlib`
only), so the build is cheap.

## 1. What the classical identity is, stated exactly

Let `ρ` be the truth cycle and `f` an involution; write `Chords f` for the
nontrivial 2-orbits of `f`, and `X` for the interlace graph on them. The
Cohn–Lempel (1972) / Beck (1977) identity is

```
#cycles (f ρ) = nullity_GF2 (interlaceMatrix X) + 1,
```

so in particular

```
f ρ is one cycle  ⟺  ker (interlaceMatrix X) = 0   (over GF(2)).
```

References (unchanged from the route note):

* M. Cohn, A. Lempel, *Cycle decomposition by disjoint transpositions*,
  J. Combin. Theory Ser. A 13 (1972), 83–89, DOI 10.1016/0097-3165(72)90010-6.
* I. Beck, *Cycle decomposition by transpositions*,
  J. Combin. Theory Ser. A 23 (1977), 198–207, DOI 10.1016/0097-3165(77)90041-3.
* L. Traldi, *Binary nullity, Euler circuits and interlace polynomials*,
  Eur. J. Combin. 32 (2011), 944–950, DOI 10.1016/j.ejc.2011.02.004.

The module does **not** take this as an axiom. It takes exactly the equivalence,
as an explicit `Prop`-valued interface with no field proved:

```lean
structure CohnLempelLaw (rho f) (x₀) (X) (S) : Prop where
  hfull_ker : SingleCircuit (SwitchCycle rho f) x₀ → kerZero (interlaceMatrix X)
  hker_full : kerZeroOn (interlaceMatrix X) S → SingleCircuit (SwitchCycle rho f) x₀
```

`S` is the chord set of the switch system being considered: all chords for the
original system, the surviving chords after a whole-component deletion for the
modified one. There is no `axiom`, no `sorry`, no `admit`; the interface is a
`structure : Prop`, which is the honest way to record an imported input.

### The encoding choice, and why it matters

`kerZeroOn M S` ("the only GF(2) vector *supported on `S`* killed by `M` is zero")
is exactly "the principal block of `M` on `S` is nonsingular". Encoding the
component statements this way makes the deletion corollary **free of any sum
manipulation**: `kerZeroOn` is monotone in `S`, so passing from a chord set to a
union of components, or to the complement of a union of components, is the
identity map on vectors (`kerZeroOn_of_kerZero`). The classical identity is then
the *only* place where a block-level statement has to be supplied.

This also exposes a small fact worth writing down: **the "component blocks are
nonsingular" step needs no component structure at all.** Given a trivial kernel,
every principal block is nonsingular, whether or not `S` is a union of
components. What the component structure *is* needed for is

* the block-diagonal form (`interlaceMatrix_blockDiag`, `adj_or_mem_iff`);
* the fact that the deleted chord set is again a union of components
  (`isUnionOfComponents_compl`) — this is what licenses applying the classical
  identity to the *deleted* system;
* the identification of the deleted chord set with `univ \ S` (caller-side, §5);
* the parity of §3.

## 2. The four separated consequences

| item | statement in the module | status |
|---|---|---|
| block-diagonal interlace matrix | `interlaceMatrix_blockDiag`, `interlaceMatrix_blockDiag'`, `adj_or_mem_iff`, plus the Mathlib bridge `component_connectedComponentMk` (`SimpleGraph.ConnectedComponent`) | **proved** |
| nonsingular component blocks | `kerZeroOn_of_kerZero`, `interlaceComponent_kerZero`, `deleteInterlaceComponents_kerZero` | **proved** |
| even component size | `interlaceComponent_even_card` | **reduced** to `NonsingularHollowBlockEven` (§3) |
| deletion preserves one-cycle | `deleteInterlaceComponents_oneCycle` | **proved**, given `CohnLempelLaw` for the deleted system |

The corollary itself is the three-line chain, and it is worth writing out
because it is the only place the classical identity is used:

1. `hCle.hfull_ker hone` — one cycle ⟹ trivial kernel (classical, original system);
2. `deleteInterlaceComponents_kerZero hS` — `univ \ S` is a union of components
   and its block is nonsingular (elementary);
3. `hCle'.hker_full` — nonsingular block ⟹ one cycle (classical, deleted system).

`SingleCircuit J x₀` is `Function.Injective (fun k => J^[k] x₀)`, i.e. exactly
`BBTEulerian.VisitsAll` lifted to an abstract permutation, and `SwitchCycle rho f
x = f (rho x)` is `BBTUniqueEulerian.Succ hK σ` when `f = AltF hK σ`,
`rho = nextPos hK`: `Succ hK σ x = σ (nextPos hK (σ.symm x))` and
`AltF hK σ q = Succ hK σ (prevPos hK q)`, so `Succ hK σ = AltF hK σ ∘ nextPos hK`
in the repository's composition convention. No other repository definition is
used, so the module carries no genome content.

## 3. The even-size step: the induction, and a refuted shortcut

`NonsingularHollowBlockEven M S` is the statement

> `M` hollow and symmetric over `GF(2)`, with no nonzero vector supported on `S`
> in its kernel ⟹ `|S|` is even.

It is *not* proved in the module. The pinned Mathlib revision has neither
`Module.Alt` nor `Module.Alt.finrank_even` (checked in the pinned
`mathlib-5ed2965256430c3649e86755f9576b54eca72435` tree:
`LinearAlgebra/BilinearForm` has no `Alt`, and `grep -rn finrank_even` over the
whole tree is empty), so the step needs its own induction. Here it is.

### 3.1 The shortcut that is *false*

The informal write-ups one usually meets claim: *"the principal minor of a
nonsingular alternating matrix is nonsingular"*, so induction on the size
deleting the pivot pair. That is **false**, and the counterexample is small.
Over `GF(2)`,

```
A = [0 0 0 1]      det(A) = 1  (nonsingular, hollow, symmetric)
    [0 0 1 0]
    [0 1 0 1]
    [1 0 1 0]
```

Take the pivot pair `i = 2`, `j = 3` (`A[2][3] = 1`). The principal submatrix on
the complement `{0,1}` is the zero `2×2` matrix, hence singular, while `A` is
nonsingular. (`scripts/verify_cle_parity_94.py` check 2 finds this and asserts
it; it is the smallest witness, and the enumeration is exhaustive over all
hollow symmetric `GF(2)` matrices up to size 5.)

Caveat, stated rather than hidden: this witness is a general hollow symmetric
matrix. Its "chords" share endpoints, so it is not an interlacement matrix of a
disjoint chord system. Whether the shortcut is *accidentally* true for genuine
interlacement matrices is untested here; it is a decidable question for small
`G` and is listed in §6.

### 3.2 The reduction that does work

Fix a pivot `i ≠ j` with `A[i][j] = 1`, let `K = D \ {i, j}`, let `C` be the
principal submatrix on `K`, and let `r_k = A[i][k]`, `u_k = A[j][k]` for `k ∈ K`.
Define, on `K`,

```
G[k][m] = r_k u_m + u_k r_m.
```

`G` is symmetric and hollow (`G[k][k] = 2 r_k u_k = 0` in characteristic two), so
`C + G` is again hollow symmetric, of size `|D| - 2`.

**Claim.** `A` is nonsingular **iff** `C + G` is nonsingular, and the
correspondence is `v ↦ (u·v, r·v, v)` where `·` is the `GF(2)` dot product.

*Proof.* With `x = (x_i, x_j, v)`, the three blocks of `A x = 0` read

```
row i:  x_j + r·v = 0            (A[i][i] = 0, A[i][j] = 1)
row j:  x_i + u·v = 0            (A[j][i] = 1, A[j][j] = 0)
row k:  r_k x_i + u_k x_j + (C v)_k = 0.
```

Substituting the first two into the third and using `x_j = r·v`, `x_i = u·v` gives

```
(C v)_k = r_k (u·v) + u_k (r·v) = Σ_m (r_k u_m + u_k r_m) v_m = (G v)_k,
```

i.e. `(C + G) v = 0`. Conversely, if `(C + G) v = 0` then `x_i := u·v`,
`x_j := r·v` satisfies all three blocks, so the maps
`ker A → ker (C+G)`, `v ↦ (u·v, r·v, v)` and back are inverse on kernels. ∎

The parity induction is then the ordinary one: if `A = 0` and `|D| > 0` then the
indicator of any index lies in `ker A`, contradicting nonsingularity; otherwise a
pivot `A[i][j] = 1` exists, `C + G` is a hollow symmetric nonsingular matrix of
size `|D| - 2`, and induction gives `|D| - 2` even, hence `|D|` even.

Evidence (`scripts/verify_cle_parity_94.py`): check 1 enumerates all hollow
symmetric `GF(2)` matrices up to size 6 and finds no nonsingular one of odd size
(counts: `n = 2`: 1, `n = 4`: 28, `n = 6`: 13888, `n = 1, 3, 5`: 0); check 3
confirms that for every hollow symmetric `A` of size ≤ 5 and every pivot pair
with `A[i][j] = 1` (5325 cases), `C + G` is hollow symmetric and
`A` nonsingular iff `C + G` nonsingular. The pivot hypothesis is essential: for
`A[i][j] = 0` the equivalence fails, and the script therefore only tests pivot
pairs.

The Lean target for a future front is therefore exactly
`NonsingularHollowBlockEven`, whose proof is the above; the shapes to isolate are
`G`-hollowness, `G`-symmetry, and the kernel correspondence
`ker A ≃ ker (C + G)`, the last one being the only nontrivial part.

## 4. Why the full identity is not needed, and what is left of it

The consumed implication is only

```
VisitsAll (f ρ) origin  →  ker (interlaceMatrix X) = 0,
```

and the deletion corollary additionally needs the converse for the modified
system. The route note already sketches a direct GF(2) colouring proof of the
first implication (arc indicators `I_c`, the two boundary identities, and the
observation that a one-orbit permutation has only constant invariants). That
proof is *not* formalized here either; `CohnLempelLaw` covers both directions so
that no partial inhabitant can be mistaken for the identity. Allsop's Theorem 3.5
(*Row-Hamiltonian Latin squares and Falconer varieties*) is a modern restatement
of the consumed form and can be cited as such.

## 5. Residuals, in order of cost

1. **Kernel-check `AssemblyP1/Issue94CLEDeletion.lean`** (a reviewer task; the
   file is `Mathlib`-only and should build in seconds).
2. **Prove `NonsingularHollowBlockEven`** as in §3.2. Pure linear algebra, no
   genome theory; the module already isolates the statement.
3. **`ShiftPairInterlace`** (from `docs/interlace-components-94.md` §4): whether a
   maximal-extension ladder *is* one interlace component. Until this is settled,
   "delete one component" must be read as "delete one union of components", which
   is what this module states.
4. **Chord-set identification.** To instantiate
   `deleteInterlaceComponents_oneCycle` for `f' = AltF (g · σ)` one must prove
   that the chords of `f'` are exactly the chords of `f` outside the deleted
   component. This is a statement about `AltF`, `ladder_arc_eq` and the
   antiderivative arc swap `g`, and it is the first genuinely genome-specific
   step of this route.
5. **`VertexCycleEq` invisibility.** Unchanged and still open: the deleted listing
   must be shown to have the same vertex cycle as the old one. Per
   `docs/interlace-components-94.md` §3 this cannot be done component-locally
   (`S = 00101`, `L = 3` refutes it), so the antiderivative conjugation route of
   `docs/cohn-lempel-component-route-94.md` remains the candidate.

## 6. Cheap decidable follow-ups

* Is the §3.1 shortcut true for *genuine* interlacement matrices (disjoint
  chords)? Decide-closed for small `G`; `scripts/verify_interlace_components_94.py`
  already contains the interlace predicate.
* Count interlacement matrices by parity of component size on small `G`, as a
  direct sanity check of §3.1's scope.

## 7. Guardrails carried forward

From the route note, still binding and not re-litigated here:

* do **not** assume "P2 makes all raw repeated `(L-1)`-mer chords noncrossing"
  (refuted, `S = 00101`, `L = 3`);
* do **not** assume an interlace component is preserved by the alternative
  traversal, or that components can be repaired in isolation (refuted at
  `G = 5`, `J(4) = 0`);
* do **not** assume "deleting one transposition preserves one-cycle-ness";
  Cohn–Lempel is about *whole components*, and this module is the formal reason
  why: only the block-diagonal form justifies the deletion;
* do **not** assume `AltF = id`; the target is `VertexCycleEq`.
* new in this note: do **not** use "the principal minor of a nonsingular
  alternating matrix is nonsingular" (§3.1).

## 8. Reproduction

```
python3 scripts/verify_cle_parity_94.py          # algebraic checks, seconds
lake build AssemblyP1.Issue94CLEDeletion         # kernel check (needs a build host)
```
