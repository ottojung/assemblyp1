import Mathlib

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-!
# Board 94, front `94cle`: the exact whole-interlace-component deletion corollary

Companion to `AssemblyP1/Issue94InterlaceComponents.lean` and to
`docs/cohn-lempel-deletion-corollary-94.md`. This module is the **pure
GF(2)/graph** half of the Cohn--Lempel route described in
`docs/cohn-lempel-component-route-94.md` §"Immediate corollary: delete an
interlace component". It contains no genome theory at all: `σ`, `ρ`, `f` occur
only as *abstract* permutations, and the chord set occurs only as an abstract
finite type `C` with a graph `X : SimpleGraph C` on it.

## What is classical input and what is proved here

The classical Cohn--Lempel identity says, for a full cycle `ρ` and disjoint
transpositions, that `cycles (f ρ) = nullity (interlace matrix) + 1`, hence

* `f ∘ ρ` is one cycle **iff** the GF(2) interlacement matrix has trivial
  kernel, and
* therefore every connected component block of that matrix is nonsingular, has
  even size, and *deleting any union of components leaves a nonsingular matrix*,
  so the deleted switch system is again one cycle.

This module **separates** that identity from its consequences:

| item | where |
|---|---|
| the classical identity, as an explicit interface | `CohnLempelLaw` |
| the interlacement matrix, hollow and symmetric | `interlaceMatrix`, `interlaceMatrix_hollow`, `interlaceMatrix_symm` |
| **block-diagonal form** w.r.t. a union of components | `interlaceMatrix_blockDiag`, `interlaceMatrix_blockDiag'`, `adj_or_mem_iff` |
| **nonsingular component blocks** | `kerZeroOn_of_kerZero`, `interlaceComponent_kerZero` |
| **even component size** | `interlaceComponent_even_card` — *conditional* on the GF(2) parity lemma `NonsingularHollowBlockEven`, see §"The one input that is not proved here" |
| **deletion preserves one cycle** | `deleteInterlaceComponents_oneCycle` |

## Encoding choice: `kerZeroOn`

`kerZeroOn M S` says "the only GF(2) vector **supported on `S`** that `M` kills is
the zero vector". This is exactly the classical statement "the principal block
`M` on the chord set `S` is nonsingular": a vector supported on `S` is
`0 off S` and `v` on `S`, and `M.mulVec` of it is zero iff the block kills `v`.
Encoding it this way means the deletion corollary needs **no sum manipulation
at all**: `kerZeroOn` is monotone in `S`, so restricting to a component --- or to
the *complement* of a union of components --- is immediate
(`kerZeroOn_of_kerZero`). The classical identity is therefore the only place
where a matrix-level statement about the block has to be supplied.

## The one input that is not proved here

`NonsingularHollowBlockEven` is the elementary GF(2) fact

> a nonsingular symmetric zero-diagonal matrix over `GF(2)` has even size,

applied to a principal block. It is **not** proved in this module: the pinned
Mathlib revision has no `Module.Alt` and no `Module.Alt.finrank_even` (the
general "an alternating form has even rank" lemma), so the step needs its own
induction. The complete proof is written out in
`docs/cohn-lempel-deletion-corollary-94.md` §3, together with a machine-checked
counterexample (`scripts/verify_cle_parity_94.py`) to the *tempting* shortcut
("the principal minor of a nonsingular alternating matrix is nonsingular"), which
is **false**, and the correction term that makes the induction go through.
`interlaceComponent_even_card` is therefore a reduction, honestly labelled, not an
inhabitant of the parity lemma.

## What this does **not** do

* It does not prove the Cohn--Lempel identity in either direction, nor the
  GF(2) colouring direction discussed in
  `docs/cohn-lempel-component-route-94.md`; both are isolated in
  `CohnLempelLaw`.
* It does not identify the chords of a *deleted* involution with a complement of
  a union of components. That is the one genome-facing fact a caller must still
  supply, and it is why `deleteInterlaceComponents_oneCycle` takes the classical
  law for the deleted switch system as a hypothesis (`hCle'`).
* It adds no `sorry`, no `admit`, no `axiom`, no `native_decide`, and it changes
  no existing definition. -/

set_option autoImplicit false

namespace AssemblyP1.Issue94CLEDeletion

open Matrix

variable {C : Type*} [Fintype C] [DecidableEq C]

/-! ## 1. The GF(2) interlacement matrix -/

/-- The **interlacement matrix** of a graph on a chord set: entry `c d` is `1`
over `GF(2)` iff the chords `c` and `d` interlace (i.e. are adjacent in the
interlace graph). -/
noncomputable def interlaceMatrix (X : SimpleGraph C) : Matrix C C (ZMod 2) := by
  classical
  exact fun c d => if X.Adj c d then 1 else 0

/-- **Hollowness.**  A chord never interlaces itself, so the interlacement
matrix has zero diagonal. This is the `alternating` part of "the block is the
matrix of a nondegenerate alternating form". -/
@[simp] theorem interlaceMatrix_hollow (X : SimpleGraph C) (c : C) :
    interlaceMatrix X c c = 0 := by
  classical
  simp [interlaceMatrix, X.irrefl]

/-- **Symmetry.**  Interlacement is symmetric, so the interlacement matrix is
symmetric. This is the other half of "alternating". -/
theorem interlaceMatrix_symm (X : SimpleGraph C) (c d : C) :
    interlaceMatrix X c d = interlaceMatrix X d c := by
  classical
  simp [interlaceMatrix, X.adj_comm]

/-! ## 2. The two trivial-kernel conditions -/

/-- `kerZero M`: the only `GF(2)` vector killed by `M` is the zero vector, i.e.
`M` is nonsingular. This is what the classical Cohn--Lempel identity delivers for
a one-cycle switch system. -/
def kerZero {D : Type*} [Fintype D] (M : Matrix D D (ZMod 2)) : Prop :=
  ∀ z : D → ZMod 2, M.mulVec z = 0 → z = 0

/-- `kerZeroOn M S`: the only `GF(2)` vector **supported on `S`** that `M` kills
is the zero vector. This is exactly "the principal block of `M` on `S` is
nonsingular", i.e. the statement about a single interlace component that the
classical identity supplies. -/
def kerZeroOn {D : Type*} [Fintype D] (M : Matrix D D (ZMod 2)) (S : Finset D) : Prop :=
  ∀ z : D → ZMod 2, (∀ l, l ∉ S → z l = 0) → M.mulVec z = 0 → z = 0

/-- **`kerZeroOn` is weaker than `kerZero`, for every chord set.**  A vector
supported on `S` is still a vector, so a trivial kernel kills it too.

This is the whole content of "every component block is nonsingular" *once the
classical identity has given a trivial kernel*: no component structure is needed
for this direction. What the component structure is actually needed for is the
block-diagonal form (§3), the fact that the deleted chord set is again a union of
components (§4), and the parity of §5. -/
theorem kerZeroOn_of_kerZero {M : Matrix C C (ZMod 2)} {S : Finset C}
    (hM : kerZero M) : kerZeroOn M S := by
  intro z _ hz
  exact hM z hz

/-! ## 3. Unions of interlace components, and the block-diagonal form -/

/-- `S` is a union of connected components of the interlace graph: no chord
interlaces anything outside `S`. -/
def IsUnionOfComponents (X : SimpleGraph C) (S : Finset C) : Prop :=
  ∀ ⦃c : C⦄, c ∈ S → ∀ ⦃d : C⦄, X.Adj c d → d ∈ S

/-- **The complement of a union of components is a union of components.**  If no
interlace edge leaves `S`, then none leaves `univ \ S` either: an edge out of
`univ \ S` would, by symmetry, be an edge into `S`.

This is what licenses applying the classical identity to the *deleted* switch
system: after deleting a union of components, the remaining chords are again a
union of components of the same interlace graph. -/
theorem isUnionOfComponents_compl {X : SimpleGraph C} {S : Finset C}
    (hS : IsUnionOfComponents X S) :
    IsUnionOfComponents X ((Finset.univ : Finset C) \ S) := by
  intro c hc d hadj
  rw [Finset.mem_sdiff] at hc
  rw [Finset.mem_sdiff]
  exact ⟨by simp, fun hd => hc.2 (hS hd hadj.symm)⟩

/-- The finite vertex set of the connected component containing c. -/
noncomputable def componentFinset (X : SimpleGraph C) (c : C) : Finset C := by
  classical
  exact Finset.univ.filter fun d =>
    X.connectedComponentMk d = X.connectedComponentMk c

/-- A genuine SimpleGraph connected component is a union of components. -/
theorem component_connectedComponentMk (X : SimpleGraph C) (c : C) :
    IsUnionOfComponents X (componentFinset X c) := by
  classical
  intro d hd e he
  have hd' : X.connectedComponentMk d = X.connectedComponentMk c :=
    (Finset.mem_filter.mp hd).2
  refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj he).symm.trans hd'

/-- A non-interlacing pair has a zero entry. -/
theorem interlaceMatrix_eq_zero_of_not_adj {X : SimpleGraph C} {c d : C}
    (h : ¬ X.Adj c d) : interlaceMatrix X c d = 0 := by
  classical
  simp [interlaceMatrix, h]

/-- **Block-diagonal form.**  No interlacement edge leaves a union of
components, so the corresponding row of the interlacement matrix vanishes
outside it. Together with `interlaceMatrix_blockDiag'` (columns) this says the
interlacement matrix is block diagonal, with one block per connected component. -/
theorem interlaceMatrix_blockDiag {X : SimpleGraph C} {S : Finset C}
    (hS : IsUnionOfComponents X S) {c : C} (hc : c ∈ S) {d : C} (hd : d ∉ S) :
    interlaceMatrix X c d = 0 :=
  interlaceMatrix_eq_zero_of_not_adj fun hadj => hd (hS hc hadj)

/-- The symmetric counterpart: a union of components is also closed under
interlacement in the *first* index. -/
theorem interlaceMatrix_blockDiag' {X : SimpleGraph C} {S : Finset C}
    (hS : IsUnionOfComponents X S) {c : C} (hc : c ∉ S) {d : C} (hd : d ∈ S) :
    interlaceMatrix X c d = 0 :=
  interlaceMatrix_eq_zero_of_not_adj fun hadj => hc (hS hd hadj.symm)

/-- **The combinatorial form of block-diagonality.**  Interlacement never crosses
the boundary of a union of components: two chords are either in the same
component or not interlacing at all. -/
theorem adj_or_mem_iff {X : SimpleGraph C} {S : Finset C} (hS : IsUnionOfComponents X S)
    {c d : C} : (c ∈ S ↔ d ∈ S) ∨ ¬ X.Adj c d := by
  by_cases hc : c ∈ S
  · by_cases hd : d ∈ S
    · exact Or.inl ⟨fun _ => hd, fun _ => hc⟩
    · exact Or.inr fun hadj => hd (hS hc hadj)
  · by_cases hd : d ∈ S
    · exact Or.inr fun hadj => hc (hS hd hadj.symm)
    · exact Or.inl ⟨fun hc' => False.elim (hc hc'), fun hd' => False.elim (hd hd')⟩

/-! ## 4. Nonsingular component blocks, and deletion -/

/-- **Nonsingular component block.**  A one-cycle switch system has a trivial
kernel by the classical identity; hence the principal block on any union of
interlace components is nonsingular. -/
theorem interlaceComponent_kerZero {X : SimpleGraph C} {S : Finset C}
    (hone : kerZero (interlaceMatrix X)) : kerZeroOn (interlaceMatrix X) S :=
  kerZeroOn_of_kerZero hone

/-- **Deleting whole interlace components keeps the matrix nonsingular.**  The
deleted chord set `univ \ S` is again a union of components
(`isUnionOfComponents_compl`) and its block is nonsingular. -/
theorem deleteInterlaceComponents_kerZero {X : SimpleGraph C} {S : Finset C}
    (hS : IsUnionOfComponents X S) (hone : kerZero (interlaceMatrix X)) :
    kerZeroOn (interlaceMatrix X) ((Finset.univ : Finset C) \ S) ∧
      IsUnionOfComponents X ((Finset.univ : Finset C) \ S) :=
  ⟨kerZeroOn_of_kerZero hone, isUnionOfComponents_compl hS⟩

/-! ## 5. Even component size: the isolated GF(2) parity input -/

/-- **The elementary GF(2) parity lemma, isolated.**  A nonsingular symmetric
zero-diagonal matrix over `GF(2)` has even size on any block `S` carrying a
trivial kernel.

**This is not proved here.** It is the step "a nondegenerate alternating
`GF(2)` form has even dimension", for which the pinned Mathlib revision has no
lemma (`Module.Alt` and `Module.Alt.finrank_even` are both absent), so it needs
its own induction. `docs/cohn-lempel-deletion-corollary-94.md` §3 records that
induction in full, including the correction term that is required --- the naive
"principal minors of nonsingular alternating matrices are nonsingular" is
**false**. -/
def NonsingularHollowBlockEven {D : Type*} [Fintype D] [DecidableEq D]
    (M : Matrix D D (ZMod 2)) (S : Finset D) : Prop :=
  (∀ i, M i i = 0) → (∀ i j, M i j = M j i) →
    (∀ z : D → ZMod 2, (∀ l, l ∉ S → z l = 0) → M.mulVec z = 0 → z = 0) → Even (Finset.card S)

/-- **Every interlace component has even size.**  Hollow and symmetry come from
`interlaceMatrix_hollow`/`interlaceMatrix_symm`, the trivial kernel of the block
from `interlaceComponent_kerZero`, and the parity step from
`NonsingularHollowBlockEven`.

This is exactly the parity input that the discrete-antiderivative route in
`docs/cohn-lempel-component-route-94.md` needs: a component's switch
coordinates can be integrated only if the component has even size. -/
theorem interlaceComponent_even_card
    {X : SimpleGraph C} {S : Finset C}
    (hEven : NonsingularHollowBlockEven (interlaceMatrix X) S)
    (hone : kerZero (interlaceMatrix X)) :
    Even (Finset.card S) := by
  unfold NonsingularHollowBlockEven at hEven
  exact hEven (fun i => interlaceMatrix_hollow X i)
    (fun c d => interlaceMatrix_symm X c d) (interlaceComponent_kerZero hone)

/-! ## 6. The classical law, and the exact deletion corollary -/

/-- **A single circuit.**  The iterates of `J` from `x₀` are pairwise distinct;
this is the repository's `BBTEulerian.VisitsAll` at the level of an abstract
permutation, and it says "`J` is one `|σ|`-cycle rather than a union of several". -/
def SingleCircuit {σ : Type*} (J : σ → σ) (x₀ : σ) : Prop :=
  Function.Injective fun k : ℕ => J^[k] x₀

/-- The successor of the switch involution `f` on the truth cycle `ρ`. For
`f = AltF hK σ` and `ρ = nextPos hK` this is `BBTUniqueEulerian.Succ hK σ`:
`Succ hK σ x = σ (nextPos hK (σ.symm x))` while
`AltF hK σ q = Succ hK σ (prevPos hK q)`, so `Succ hK σ = AltF hK σ ∘ nextPos hK`
in the repository's composition convention. -/
def SwitchCycle {σ : Type*} (rho f : σ → σ) : σ → σ := fun x => f (rho x)

/-- **The classical Cohn--Lempel identity, isolated as an input.**

`X` is the interlace graph of the chords of `f`, `S` is the chord set of the
switch system under consideration (all chords, or the chords that survive a
whole-component deletion), `SingleCircuit (SwitchCycle rho f) x₀` is "`f ∘ ρ` is
one cycle". The two fields are the two directions of

> `f ∘ ρ` is one cycle **iff** the GF(2) interlacement matrix on `S` has trivial
> kernel,

which is the only form of Cohn--Lempel (1972), Beck (1977) or Traldi (2011) that
this module consumes. Neither field is proved in this repository; see
`docs/cohn-lempel-deletion-corollary-94.md` §4 for why the full equality
`#cycles (f ρ) = nullity (X) + 1` is not needed and what the direct GF(2)
colouring proof would have to discharge. -/
structure CohnLempelLaw {σ C : Type*} [Fintype C] [DecidableEq C]
    (rho f : σ → σ) (x₀ : σ) (X : SimpleGraph C) (S : Finset C) : Prop where
  /-- **One cycle forces a trivial kernel** (the classical direction used for
  the *original* switch system). -/
  hfull_ker : SingleCircuit (SwitchCycle rho f) x₀ → kerZero (interlaceMatrix X)
  /-- **A trivial kernel block forces one cycle** (the classical direction used
  for the *deleted* switch system). -/
  hker_full : kerZeroOn (interlaceMatrix X) S → SingleCircuit (SwitchCycle rho f) x₀

/-- **The exact whole-interlace-component deletion corollary.**

Given a switch involution `f` whose successor `f ∘ ρ` is one cycle, deleting any
union of interlace components of its interlace graph yields a switch involution
`f'` whose successor `f' ∘ ρ` is **still one cycle**.

The proof is the three-line chain that the whole Cohn--Lempel deletion story
needs, and it shows exactly where the classical identity enters --- twice, and
nowhere else:

1. `hCle.hfull_ker hone`: one cycle gives a trivial kernel
   (`CohnLempelLaw`, classical);
2. `deleteInterlaceComponents_kerZero`: the deleted chord set `univ \ S` is
   again a union of components and its block is nonsingular (elementary, §4);
3. `hCle'.hker_full`: a nonsingular block gives one cycle again
   (`CohnLempelLaw`, classical, applied to the deleted system).

`hCle'` is the classical law for the deleted switch system `f'`, stated on the
**same** interlace graph `X` and on the chord set `univ \ S`. Identifying the
chords of `f'` with `univ \ S` --- i.e. "deleting the component removes exactly
those chords" --- is a genome-facing fact that this module does not need and does
not prove; it is the caller's obligation. -/
theorem deleteInterlaceComponents_oneCycle {σ C : Type*} [Fintype C] [DecidableEq C]
    {rho f : σ → σ} {x₀ : σ} {X : SimpleGraph C} {S : Finset C} {f' : σ → σ}
    (hone : SingleCircuit (SwitchCycle rho f) x₀)
    (hCle : CohnLempelLaw rho f x₀ X (Finset.univ))
    (hS : IsUnionOfComponents X S)
    (hCle' : CohnLempelLaw rho f' x₀ X ((Finset.univ : Finset C) \ S)) :
    SingleCircuit (SwitchCycle rho f') x₀ :=
  hCle'.hker_full ((deleteInterlaceComponents_kerZero hS (hCle.hfull_ker hone)).1)

end AssemblyP1.Issue94CLEDeletion
