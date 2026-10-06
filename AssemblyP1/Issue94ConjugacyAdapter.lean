import AssemblyP1.Issue94Reconstruct
import AssemblyP1.Issue94TransposePreserve

/-!
# Board 94, front 94conj: the generic `#94` conjugacy adapter, and the exact
# alignment condition it needs

## The question this module answers

Two reconstructions of the `(L-1)`-mer multigraph of a truth `S` are described
by transition maps `f, f' : Fin K → Fin K` whose **jumps**

```text
J  = jump hK f  = f ∘ nextPos,        J' = jump hK f' = f' ∘ nextPos
```

are both single cycles (`Issue94Reconstruct.jump`, `VisitsAll`).  The
reconstructed traversal (`Issue94Reconstruct.sigEquiv`) is the orbit listing of
the jump from the origin:

```text
σ i = J^[i] (origin),                σ' i = (J')^[i] (origin).
```

Suppose there is a **`vtx`-preserving conjugacy** `h` between the two jumps:
`h (J q) = J' (h q)` and `vtx hK L S (h q) = vtx hK L S q` for every start `q`.
What does that buy for `BBTEulerian.VertexCycleEq`?

**Answer, and this is the load-bearing point of the module: less than one might
hope, and precisely characterisable.**  Recall the definition verbatim
(`AssemblyP1/BBTEulerian.lean:217`):

```text
VertexCycleEq hK L S σ τ  =  ∃ k : Fin K, ∀ i : Fin K,
    vtx hK L S (σ i) = vtx hK L S (rotAdd hK k.val (τ i)).
```

The `k` is `rotAdd`ed onto a **start**: `k` is a rotation of **genomic
coordinates** of the circle of `K` starts --- *not* a rotation of the *listing
index* `i`.  Those two readings must not be identified, and §1--§4 below is the
whole content of the difference.

| | statement | where proved / refuted |
| --- | --- | --- |
| **free** | the conjugacy gives a rotation on **listing indices**: `∃ k₀, ∀ i, vtx (σ i) = vtx (σ' (rotAdd k₀ i))` | `listingIndex_conj`, §4 |
| **NOT free** | a `vtx`-preserving conjugacy does **not** give `VertexCycleEq` | `not_vertexCycleEq_00001`, §9 |
| **exact** | `VertexCycleEq σ σ'` holds iff the `J'`-cycle read from `h (origin)` is the genomic rotation by some `k` of the `J'`-cycle read from `origin` | `vertexCycleEq_iff_orbit_conj`, §3 |
| **adapter** | `RotAligned` (two clauses, §2) turns the conjugacy into `VertexCycleEq` with witness `k` | `vertexCycleEq_of_conjugacy`, §2 |

## §1. What the conjugacy actually transports

`h (J^[i] (origin)) = (J')^[i] (h (origin))` (`iterate_conj`).  Together with
`vtx`-preservation this gives, for **every** `i`,

```text
vtx (σ i) = vtx ((J')^[i] (h (origin))).                          (★)
```

So the conjugacy determines the vertex cycle of `σ` as *the `J'`-cycle read from
the point `h (origin)`*.  The only thing left to decide is whether the `J'`-cycle
read from `h (origin)` is the `VertexCycleEq` rotation of the `J'`-cycle read
from `origin`.  Here the two readings of "rotation" come apart.

## §2. The exact additional alignment/rotation condition

`RotAligned hK J' k h` is

1. `h (origin hK) = rotAdd hK k.val (origin hK)`, **and**
2. `∀ x, J' (rotAdd hK k.val x) = rotAdd hK k.val (J' x)`.

Clause 1 pins the genomic rotation: `k` **is** the start `h (origin)`, since
`rotAdd hK k.val (origin hK) = k` (`rotAdd_origin`), so the witness of
`VertexCycleEq` is a *genomic coordinate*.  Clause 2 says the same rotation is an
automorphism of the prime jump; equivalently (`jump_commute_iff`) `f'` commutes
with it, which is the packet's own vocabulary.

The two clauses are not redundant.  Clause 1 alone is always satisfiable --- at
`k = h (origin hK)` --- and clause 2 alone is automatic at `k = origin hK`.  It
is their *simultaneity at one and the same `k`* that is the additional content,
and §9 shows it is genuinely needed.

Two special cases in which it is automatic, both with no extra work:

* `vertexCycleEq_of_conj_origin`: if the conjugacy **fixes the origin**, the
  witness is `origin hK` (clause 2 holds at `k = origin` because `rotAdd hK 0`
  is the identity), so the two reconstructed listings agree **pointwise**:
  `vtx (σ i) = vtx (σ' i)` for every `i`.
* `vertexCycleEq_of_conj_nextPos`: if `J' = nextPos` --- i.e. `f'` is the
  identity re-pairing, so the prime listing reads the truth's own cycle ---
  then `rotAdd k` centralises `nextPos` for **every** `k`, so `RotAligned` holds
  unconditionally and *any* `vtx`-preserving conjugacy suffices, with witness
  `h (origin)`.  This is also the one case in which the two readings of the
  rotation coincide, because `(J')^[i] = rotAdd i` and the `J'`-orbit index of a
  start is then the start itself.

## §3. The adapter is exact

`vertexCycleEq_iff_orbit_conj` is the converse to §2: under the conjugacy
hypotheses, `VertexCycleEq σ σ'` is **equivalent** to the existence of a `k`
such that the `J'`-cycle read from `h (origin)` is the genomic rotation by `k`
of the `J'`-cycle read from `origin`, pointwise in the vertex labelling.  So the
residual left by the conjugacy is exactly the rotation step, and `RotAligned` is
a sufficient condition for it, not an artefact.

## §4. The listing-index reading, and why it is not the same

`listingIndex_conj`: the conjugacy alone, plus `single` for `J'`, gives the
rotation-by-**listing-index** statement.  Its witness `k₀` is the `J'`-**orbit
index** of `h (origin)`: the unique `k₀ : Fin K` with
`(J')^[k₀] (origin) = h (origin)`.  `single` is used exactly here, through
`BBTUniqueEulerian.iterate_G_eq` and `iterate_mod`, to reduce the iterate index
modulo `K`.

This is *not* `VertexCycleEq`.  At the §9 instance the two candidates are
`k₀ = 4` (orbit index) and `k = 1` (genomic coordinate) --- different numbers,
and only the first of them yields anything.

## §5. Why `Issue94TransposePreserve` is the right companion, and how they compose

`BBTTranspose.vertexCycleEq_transposition` is correct because
`VertexCycleEq hK L S σ τ` at witness `k` is the *pointwise* statement
`∀ i, vtx (σ i) = vtx (rotAdd k (τ i))`: swapping two starts that spell the same
`(L-1)`-mer leaves the left-hand side untouched, so the witness survives.  The
adapter is built on exactly the same property --- it never transports anything
*through* the witness `k`, it only produces one.  Accordingly the two compose
without bookkeeping: `vertexCycleEq_transpose_conj` post-composes the adapter's
conclusion by any vertex-invisible transposition, at the **same** witness.

## §6. Anti-vacuity

`listingVertexEq_0101`: for `S = 0101`, `K = 4`, `L = 3` and the identity
re-pairing on both sides, the two reconstructed listings are `VertexCycleEq` at
witness `0`.  So the adapter's conclusion is satisfiable on real data, and the
finite `ListingVertexEq` predicate of §9 is not vacuously false.

## §7. The bridge to `VertexCycleEq`

`vertexCycleEq_iff_listing` replaces the `noncomputable` `sigEquiv` by the
computable `sigFun` it is (`Issue94Reconstruct.sigEquiv_apply` is `rfl`).  This
is what makes the refutation of §9 a finite, decidable statement.

## §9. The refutation: the conjugacy alone is not enough

§9 is a kernel-checked refutation at `K = 5`, `L = 3`, `S = 00001`:

* `f = id`, so `J = nextPos` (single) and `σ = rotAdd 1`, the truth's own
  cyclic reading;
* `f' = (0 1 2)`, `vtx`-preserving (`0, 1, 2` all spell `00`), with
  `J' = f' ∘ nextPos = (0 2 3 4 1)` a single `5`-cycle;
* `h = (0 1)`, a `vtx`-preserving conjugacy `J → J'`;
* `ListingIndexEq` **holds** (`conj_listingIndexEq_00001`), so the free
  statement of §4 is not vacuous; and
* `ListingVertexEq` **fails**: no `k` works
  (`not_listingVertexEq_00001`, hence `not_vertexCycleEq_00001`), and
  `RotAligned` fails precisely at the forced `k = h (origin hK) = 1`
  (`not_rotAligned_00001`), because `rotAdd hK 1` does not centralise `J'`.

This is not a defect of the adapter: it is exactly the phenomenon `thm:BBT` is
about.  `σ'` is a genuine alternative `EulerianCycle` of the multigraph of
`00001` which is **not** the truth's vertex cycle, and `00001` has the long
obstruction `thm:BBT` predicts (`longObstruction_00001`: the length-`3` window
`000` is a maximal triple repeat at the starts `0, 1, 2`, and `L - 1 = 2 ≤ 3`).
What the refutation rules out is the tempting inference "a `vtx`-preserving
conjugacy between the jumps determines the vertex cycle": it does not, because
`VertexCycleEq` rotates genomic coordinates while a conjugacy transports orbit
indices.

## What this module does **not** do

* It does not **produce** a `vtx`-preserving conjugacy.  Existence of one is the
  hard direction and is untouched; `AssemblyP1.Issue94Reconstruct` supplies the
  listings, this module only says what a conjugacy is worth.
* It does not prove `VertexCycleEq σ (Equiv.refl _)` for the reconstructed `σ`,
  i.e. it does not prove `BBTEulerian.UniqueEulerianCycle`,
  `EulerianCycleObstruction`, or `hPevzner`.  All unchanged, all still open as
  recorded in `AssemblyP1/BBTEulerian.lean`, §"What is proved, and what is not".
* It changes no existing definition.  It adds no `sorry`, no `admit`, no
  `axiom`, no `native_decide`, no `unsafe`.  The `#print axioms` block at the end
  is the audit.

Companion note: `docs/conjugacy-adapter-94.md`.  Evidence:
`scripts/verify_conjugacy_adapter_94.py`.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AssemblyP1.Issue94ConjugacyAdapter

open AssemblyP1
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTChords
open AssemblyP1.Issue94Reconstruct
open AssemblyP1.BBTTranspose

variable {α : Type} [DecidableEq α] {K : ℕ}

/-! ## 1. Predicates -/

/-- **`f` is label-preserving**: every start is carried to a start spelling the
same `(L-1)`-mer.  This is the `hLP` of
`Issue94Reconstruct.eulerianCycle_of_labelPreserving_single`, restated under a
name. -/
def LabelPreserving {K : ℕ} (hK : 0 < K) (L : ℕ) (S : Fin K → α)
    (f : Fin K → Fin K) : Prop :=
  ∀ q : Fin K, vtx hK L S (f q) = vtx hK L S q

instance {K : ℕ} (hK : 0 < K) (L : ℕ) (S : Fin K → α) (f : Fin K → Fin K) :
    Decidable (LabelPreserving hK L S f) := by
  unfold LabelPreserving
  infer_instance

/-- **`h` preserves the vertex labelling**: it reads the same `(L-1)`-mer at
every start.  First half of "a `vtx`-preserving conjugacy". -/
def VtxPreserving {K : ℕ} (hK : 0 < K) (L : ℕ) (S : Fin K → α)
    (h : Fin K → Fin K) : Prop :=
  ∀ q : Fin K, vtx hK L S (h q) = vtx hK L S q

instance {K : ℕ} (hK : 0 < K) (L : ℕ) (S : Fin K → α) (h : Fin K → Fin K) :
    Decidable (VtxPreserving hK L S h) := by
  unfold VtxPreserving
  infer_instance

/-- **`h` is a conjugacy from the jump `J` to the jump `J'`.**  Second half of
"a `vtx`-preserving conjugacy". -/
def JumpConj {K : ℕ} {J J' : Fin K → Fin K} (hK : 0 < K) (J J' : Fin K → Fin K)
    (h : Fin K → Fin K) : Prop :=
  ∀ q : Fin K, h (J q) = J' (h q)

instance {K : ℕ} (hK : 0 < K) (J J' : Fin K → Fin K) (h : Fin K → Fin K) :
    Decidable (JumpConj hK J J' h) := by
  unfold JumpConj
  infer_instance

/-- **THE ALIGNMENT CONDITION (§2).**  `RotAligned hK J' k h` says that the
genomic rotation by `k`

1. carries the origin of the prime listing to the point at which `h` starts, and
2. is an automorphism of the prime jump.

Clause 1 alone is always satisfiable (at `k = h (origin hK)`); clause 2 alone is
automatic at `k = origin hK`.  It is their simultaneity at one and the same `k`
that is the additional content. -/
def RotAligned {K : ℕ} {J' : Fin K → Fin K} (hK : 0 < K) (J' : Fin K → Fin K)
    (k : Fin K) (h : Fin K → Fin K) : Prop :=
  h (origin hK) = rotAdd hK k.val (origin hK) ∧
  ∀ x : Fin K, J' (rotAdd hK k.val x) = rotAdd hK k.val (J' x)

instance {K : ℕ} (hK : 0 < K) (J' : Fin K → Fin K) (k : Fin K) (h : Fin K → Fin K) :
    Decidable (RotAligned hK J' k h) := by
  unfold RotAligned
  infer_instance

/-- **`VertexCycleEq` in computable listing form.**  This is
`VertexCycleEq (sigEquiv hK f hV) (sigEquiv hK f' hV')` with the
`noncomputable` `sigEquiv` replaced by the `sigFun` it was built from
(`vertexCycleEq_iff_listing`; `Issue94Reconstruct.sigEquiv_apply` is `rfl`).
Stated so that finite instances are decidable. -/
def ListingVertexEq {K : ℕ} (hK : 0 < K) (L : ℕ) (S : Fin K → α)
    (f f' : Fin K → Fin K) (hV : VisitsAll (jump hK f) (origin hK))
    (hV' : VisitsAll (jump hK f') (origin hK)) : Prop :=
  ∃ k : Fin K, ∀ i : Fin K,
    vtx hK L S (sigFun hK f i) = vtx hK L S (rotAdd hK k.val (sigFun hK f' i))

instance {K : ℕ} (hK : 0 < K) (L : ℕ) (S : Fin K → α) (f f' : Fin K → Fin K)
    (hV : VisitsAll (jump hK f) (origin hK))
    (hV' : VisitsAll (jump hK f') (origin hK)) :
    Decidable (ListingVertexEq hK L S f f' hV hV') := by
  unfold ListingVertexEq
  infer_instance

/-- **`VertexCycleEq` with the rotation read on the listing index**: the
statement the conjugacy delivers for free (§4).  Its witness is a *listing index
of the prime listing*, i.e. a `J'`-orbit index --- see §4 of the module
docstring and `not_vertexCycleEq_00001`. -/
def ListingIndexEq {K : ℕ} (hK : 0 < K) (L : ℕ) (S : Fin K → α)
    (f f' : Fin K → Fin K) (hV : VisitsAll (jump hK f) (origin hK))
    (hV' : VisitsAll (jump hK f') (origin hK)) : Prop :=
  ∃ k : Fin K, ∀ i : Fin K,
    vtx hK L S (sigFun hK f i) = vtx hK L S (sigFun hK f' (rotAdd hK k.val i))

instance {K : ℕ} (hK : 0 < K) (L : ℕ) (S : Fin K → α) (f f' : Fin K → Fin K)
    (hV : VisitsAll (jump hK f) (origin hK))
    (hV' : VisitsAll (jump hK f') (origin hK)) :
    Decidable (ListingIndexEq hK L S f f' hV hV') := by
  unfold ListingIndexEq
  infer_instance

/-! ## 2. Elementary circle facts -/

/-- **The rotation by `k` of the origin is the start `k`.**  So a genomic
rotation is *named* by the start it carries the origin to; this is why clause 1
of `RotAligned` is always solvable, at `k = h (origin hK)`. -/
theorem rotAdd_origin (hK : 0 < K) (k : Fin K) : rotAdd hK k.val (origin hK) = k := by
  apply Fin.ext
  show ((origin hK : Fin K).val + k.val) % K = k.val
  rw [origin_val, Nat.zero_add, Nat.mod_eq_of_lt k.isLt]

/-- **The rotation by `k` is a symmetry of the one-step rotation.**  This is
what makes clause 2 of `RotAligned` automatic whenever `J' = nextPos`
(§2, special case 2). -/
theorem nextPos_rotAdd_one {K : ℕ} (hK : 0 < K) (k x : Fin K) :
    nextPos hK (rotAdd hK k.val x) = rotAdd hK k.val (nextPos hK x) :=
  calc nextPos hK (rotAdd hK k.val x)
      = rotAdd hK (k.val + 1) x := nextPos_rotAdd hK x k.val
    _ = rotAdd hK k.val (rotAdd hK 1 x) := (rotAdd_add hK k.val 1 x).symm
    _ = rotAdd hK k.val (nextPos hK x) := rfl

/-- **The rotation by `origin` centralises every map of the circle.** -/
theorem rotAdd_origin_comm {K : ℕ} (hK : 0 < K) {J' : Fin K → Fin K} :
    ∀ x : Fin K, J' (rotAdd hK (origin hK).val x) = rotAdd hK (origin hK).val (J' x) := by
  intro x
  have hz : (origin hK : Fin K).val = 0 := origin_val hK
  rw [hz]
  exact fun x => rotAdd_zero hK x

/-- **A rotation centralises the prime jump iff it centralises the prime
transition map `f'`.**  This is what makes clause 2 of `RotAligned` a statement
about `f'` --- the transition map of the packet --- rather than about the jump. -/
theorem jump_commute_iff {K : ℕ} (hK : 0 < K) (f' : Fin K → Fin K) (k : Fin K) :
    (∀ x : Fin K, jump hK f' (rotAdd hK k.val x) = rotAdd hK k.val (jump hK f' x))
      ↔ ∀ y : Fin K, f' (rotAdd hK k.val y) = rotAdd hK k.val (f' y) := by
  constructor
  · intro h y
    have hkey : nextPos hK (rotAdd hK k.val (prevPos hK y)) = rotAdd hK k.val y := by
      calc nextPos hK (rotAdd hK k.val (prevPos hK y))
          = rotAdd hK (k.val + 1) (prevPos hK y) := nextPos_rotAdd hK (prevPos hK y) k.val
        _ = rotAdd hK k.val (rotAdd hK 1 (prevPos hK y)) :=
          (rotAdd_add hK k.val 1 (prevPos hK y)).symm
        _ = rotAdd hK k.val (nextPos hK (prevPos hK y)) := rfl
        _ = rotAdd hK k.val y := congrArg _ (nextPrev hK y)
    have h2 := h (prevPos hK y)
    unfold jump at h2
    rw [hkey, nextPrev hK y] at h2
    exact h2
  · intro h x
    have h2 := h (nextPos hK x)
    show f' (nextPos hK (rotAdd hK k.val x)) = rotAdd hK k.val (f' (nextPos hK x))
    rw [nextPos_rotAdd hK x k.val, ← rotAdd_add hK k.val 1 (nextPos hK x)]
    exact h2

/-! ## 3. The adapter: the smallest lemma that turns a conjugacy into
`VertexCycleEq` -/

/-- **A conjugacy transports the orbit of a point to the orbit of its image.** -/
theorem iterate_conj_aux {K : ℕ} (hK : 0 < K) {J J' : Fin K → Fin K}
    (h : Fin K → Fin K) (hc : ∀ q : Fin K, h (J q) = J' (h q)) (n : ℕ) (x : Fin K) :
    h (J^[n] x) = J'^[n] (h x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (hc _).trans (congrArg J' ih).symm

/-- **... at the origin**, which is the base point both reconstructions read
from. -/
theorem iterate_conj {K : ℕ} (hK : 0 < K) {J J' : Fin K → Fin K} (h : Fin K → Fin K)
    (hc : ∀ q : Fin K, h (J q) = J' (h q)) (n : ℕ) :
    h (J^[n] (origin hK)) = J'^[n] (h (origin hK)) :=
  iterate_conj_aux hK h hc n (origin hK)

/-- **If `rotAdd k` centralises `J'`, it centralises every `J'`-iterate**, and
therefore reads every point of the `J'`-cycle as the genomic rotation of the
corresponding point of the `J'`-cycle from the origin. -/
theorem iterate_comm_rotAdd {K : ℕ} (hK : 0 < K) {J' : Fin K → Fin K}
    (k x : Fin K) (hc : ∀ y : Fin K, J' (rotAdd hK k.val y) = rotAdd hK k.val (J' y))
    (n : ℕ) : J'^[n] (rotAdd hK k.val x) = rotAdd hK k.val (J'^[n] x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (hc _)

/-- **THE ADAPTER (§2).**  A `vtx`-preserving conjugacy between two single
jumps, aligned in the sense of `RotAligned`, is a `VertexCycleEq` between the two
reconstructed traversals, **with witness `k` read as a genomic rotation**.

The mechanism, in three lines: `iterate_conj` moves `σ`'s vertex cycle onto the
`J'`-cycle read from `h (origin)`; clause 1 of `RotAligned` identifies
`h (origin)` with the genomic rotation `rotAdd k` of the origin; clause 2 pulls
that rotation all the way along the `J'`-cycle.  `single` is *not* needed for
this step --- it is needed only to make `sigEquiv` a permutation at all. -/
theorem vertexCycleEq_of_conjugacy {K : ℕ} (hK : 0 < K) (L : ℕ) (S : Fin K → α)
    (f f' h : Fin K → Fin K) (hbijf : Function.Bijective f)
    (hbijf' : Function.Bijective f')
    (hV : VisitsAll (jump hK f) (origin hK)) (hV' : VisitsAll (jump hK f') (origin hK))
    (hv : VtxPreserving hK L S h)
    (hc : JumpConj hK (jump hK f) (jump hK f') h)
    {k : Fin K} (hk : RotAligned hK (jump hK f') k h) :
    VertexCycleEq hK L S (sigEquiv hK f hV) (sigEquiv hK f' hV') := by
  unfold VtxPreserving at hv
  unfold JumpConj at hc
  unfold RotAligned at hk
  have hstep : ∀ n : ℕ,
      jump hK f'^[n] (origin hK) = rotAdd hK k.val (jump hK f'^[n] (origin hK)) :=
    iterate_comm_rotAdd (J' := jump hK f') hK k (origin hK) hk.2
  have hkey : ∀ n : ℕ,
      jump hK f'^[n] (h (origin hK))
        = rotAdd hK k.val (jump hK f'^[n] (origin hK)) := by
    intro n
    rw [hk.1, hstep n]
  refine ⟨k, fun i => ?_⟩
  calc vtx hK L S (sigEquiv hK f hV i)
      = vtx hK L S (h ((jump hK f)^[i.val] (origin hK))) := by
        rw [sigEquiv_apply]; exact (hv _).symm
    _ = vtx hK L S (jump hK f'^[i.val] (h (origin hK))) :=
      congrArg _ (iterate_conj hK h hc i.val)
    _ = vtx hK L S (rotAdd hK k.val (jump hK f'^[i.val] (origin hK))) :=
      congrArg _ (hkey i.val)
    _ = vtx hK L S (rotAdd hK k.val (sigEquiv hK f' hV' i)) := by
      rw [sigEquiv_apply]

/-- **THE ADAPTER IS EXACT (§3).**  Under the conjugacy hypotheses,
`VertexCycleEq` between the two reconstructed listings holds **if and only if**
the `J'`-cycle read from `h (origin)` is the genomic rotation by some `k` of the
`J'`-cycle read from `origin`, pointwise in the vertex labelling.

This is why §2's extra condition cannot be dropped: it is the residual of
`VertexCycleEq` after the conjugacy has done everything it can.  Note the
right-hand side is a statement about **genomic rotations** (`rotAdd k` applied
to starts), which is exactly what `BBTEulerian.VertexCycleEq` quantifies over. -/
theorem vertexCycleEq_iff_orbit_conj {K : ℕ} (hK : 0 < K) (L : ℕ) (S : Fin K → α)
    (f f' h : Fin K → Fin K) (hbijf : Function.Bijective f)
    (hbijf' : Function.Bijective f')
    (hV : VisitsAll (jump hK f) (origin hK)) (hV' : VisitsAll (jump hK f') (origin hK))
    (hv : VtxPreserving hK L S h)
    (hc : JumpConj hK (jump hK f) (jump hK f') h) :
    VertexCycleEq hK L S (sigEquiv hK f hV) (sigEquiv hK f' hV')
      ↔ ∃ k : Fin K, ∀ i : Fin K,
          vtx hK L S (jump hK f'^[i.val] (h (origin hK)))
            = vtx hK L S (rotAdd hK k.val (jump hK f'^[i.val] (origin hK))) := by
  unfold VtxPreserving at hv
  unfold JumpConj at hc
  have hmove : ∀ i : Fin K,
      vtx hK L S (sigEquiv hK f hV i)
        = vtx hK L S (jump hK f'^[i.val] (h (origin hK))) := by
    intro i
    calc vtx hK L S (sigEquiv hK f hV i)
        = vtx hK L S (h ((jump hK f)^[i.val] (origin hK))) := by
          rw [sigEquiv_apply]; exact (hv _).symm
      _ = vtx hK L S (jump hK f'^[i.val] (h (origin hK))) :=
        congrArg _ (iterate_conj hK h hc i.val)
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, fun i => ?_⟩
    have h1 := hk i
    have h2 := hmove i
    rw [sigEquiv_apply] at h1
    rw [← h2]
    exact h1
  · rintro ⟨k, hk⟩
    refine ⟨k, fun i => ?_⟩
    have h1 := hk i
    have h2 := hmove i
    calc vtx hK L S (sigEquiv hK f hV i)
        = vtx hK L S (jump hK f'^[i.val] (h (origin hK))) := h2
      _ = vtx hK L S (rotAdd hK k.val (jump hK f'^[i.val] (origin hK))) := h1
      _ = vtx hK L S (rotAdd hK k.val (sigEquiv hK f' hV' i)) := by
        rw [sigEquiv_apply]

/-- **The full adapter statement**: both reconstructed listings are
`EulerianCycle`s and they are `VertexCycleEq`.  The two `EulerianCycle`s are
`Issue94Reconstruct.eulerianCycle_of_labelPreserving_single`; only the last
conjunct is this module's content. -/
theorem eulerianCycles_vertexCycleEq_of_conjugacy {K : ℕ} (hK : 0 < K) (L : ℕ)
    (S : Fin K → α) (f f' h : Fin K → Fin K) (hbijf : Function.Bijective f)
    (hbijf' : Function.Bijective f')
    (hV : VisitsAll (jump hK f) (origin hK)) (hV' : VisitsAll (jump hK f') (origin hK))
    (hLP : LabelPreserving hK L S f) (hLP' : LabelPreserving hK L S f')
    (hv : VtxPreserving hK L S h)
    (hc : JumpConj hK (jump hK f) (jump hK f') h)
    {k : Fin K} (hk : RotAligned hK (jump hK f') k h) :
    EulerianCycle hK L S (sigEquiv hK f hV)
      ∧ EulerianCycle hK L S (sigEquiv hK f' hV')
      ∧ VertexCycleEq hK L S (sigEquiv hK f hV) (sigEquiv hK f' hV') := by
  unfold LabelPreserving at hLP hLP'
  refine ⟨eulerianCycle_of_labelPreserving_single hK L S f hbijf hLP hV,
    eulerianCycle_of_labelPreserving_single hK L S f' hbijf' hLP' hV',
    vertexCycleEq_of_conjugacy hK L S f f' h hbijf hbijf' hV hV' hv hc hk⟩

/-! ## 4. The listing-index reading: what the conjugacy gives for free -/

/-- **THE FREE STATEMENT (§4).**  A `vtx`-preserving conjugacy between two
jumps, with `single` on the prime side, gives a rotation **on listing indices**:
`vtx (σ i) = vtx (σ' (rotAdd k₀ i))`, where `k₀` is the unique `J'`-orbit index
with `(J')^[k₀] (origin) = h (origin)`.

`single` is used exactly once, through `BBTUniqueEulerian.iterate_G_eq` (the
`K`-step circuit closes) and `iterate_mod` (the iterate index is read modulo
`K`, which is what lets `k₀` act on listing positions).

This is *not* `VertexCycleEq`, whose `k` is a rotation of genomic coordinates;
`not_vertexCycleEq_00001` is the refutation of the inference from one to the
other. -/
theorem listingIndex_conj {K : ℕ} (hK : 0 < K) (L : ℕ) (S : Fin K → α)
    (f f' h : Fin K → Fin K) (hbijf : Function.Bijective f)
    (hbijf' : Function.Bijective f')
    (hV : VisitsAll (jump hK f) (origin hK)) (hV' : VisitsAll (jump hK f') (origin hK))
    (hv : VtxPreserving hK L S h)
    (hc : JumpConj hK (jump hK f) (jump hK f') h) :
    ∃ k : Fin K, ∀ i : Fin K,
      vtx hK L S (sigFun hK f i) = vtx hK L S (sigFun hK f' (rotAdd hK k.val i)) := by
  unfold VtxPreserving at hv
  unfold JumpConj at hc
  have hV'inj : Function.Injective
      (fun n : Fin K => jump hK f'^[n.val] (origin hK)) := hV'
  obtain ⟨k, hk⟩ : ∃ k : Fin K,
      jump hK f'^[k.val] (origin hK) = h (origin hK) :=
    (Finite.injective_iff_surjective).mp hV'inj (h (origin hK))
  have hclose : jump hK f'^[K] (origin hK) = origin hK :=
    iterate_G_eq hK (jump hK f') (jump_bijective hK f' hbijf') hV'
  have hkey : ∀ i : Fin K, jump hK f'^[i.val] (h (origin hK))
      = jump hK f'^[i.val + k.val] (origin hK) :=
    (congrArg (jump hK f'^[i.val]) hk.symm).trans
      (congrFun (Function.iterate_add (jump hK f') i.val k.val) (origin hK)).symm
  have hstep : ∀ i : Fin K, sigFun hK f' (rotAdd hK k.val i)
      = jump hK f'^[i.val + k.val] (origin hK) := by
    intro i
    have hval : (rotAdd hK k.val i).val = (i.val + k.val) % K := rfl
    have hmod := iterate_mod hK (jump hK f') (origin hK) hclose (i.val + k.val)
    change jump hK f'^[(rotAdd hK k.val i).val] (origin hK)
      = jump hK f'^[i.val + k.val] (origin hK)
    rw [hval]
    exact hmod.symm
  refine ⟨k, fun i => ?_⟩
  calc vtx hK L S (sigFun hK f i)
      = vtx hK L S ((jump hK f)^[i.val] (origin hK)) := rfl
    _ = vtx hK L S (h ((jump hK f)^[i.val] (origin hK))) := (hv _).symm
    _ = vtx hK L S (jump hK f'^[i.val] (h (origin hK))) :=
      congrArg _ (iterate_conj hK h hc i.val)
    _ = vtx hK L S (jump hK f'^[i.val + k.val] (origin hK)) := congrArg _ (hkey i)
    _ = vtx hK L S (sigFun hK f' (rotAdd hK k.val i)) := by rw [hstep i]

/-- **... packaged as the decidable predicate `ListingIndexEq`.** -/
theorem conj_listingIndexEq {K : ℕ} (hK : 0 < K) (L : ℕ) (S : Fin K → α)
    (f f' h : Fin K → Fin K) (hbijf : Function.Bijective f)
    (hbijf' : Function.Bijective f')
    (hV : VisitsAll (jump hK f) (origin hK)) (hV' : VisitsAll (jump hK f') (origin hK))
    (hv : VtxPreserving hK L S h)
    (hc : JumpConj hK (jump hK f) (jump hK f') h) :
    ListingIndexEq hK L S f f' hV hV' :=
  listingIndex_conj hK L S f f' h hbijf hbijf' hV hV' hv hc

/-! ## 5. When the extra condition is automatic -/

/-- **The unique genomic rotation carrying the origin to `h (origin hK)` is the
rotation by `h (origin hK)` itself**, so `RotAligned` at `k = h (origin hK)` is
*equivalent* to the centrality of that rotation on the prime jump.  This is the
"smallest lemma" form of §2: the alignment condition is one hypothesis about
`f'`, evaluated at a rotation named by `h`. -/
theorem rotAligned_of_comm {K : ℕ} (hK : 0 < K) {J' : Fin K → Fin K}
    (h : Fin K → Fin K)
    (hc : ∀ x : Fin K, J' (rotAdd hK (h (origin hK)).val x)
      = rotAdd hK (h (origin hK)).val (J' x)) :
    RotAligned hK J' (h (origin hK)) h :=
  ⟨(rotAdd_origin hK (h (origin hK))).symm, hc⟩

/-- **Consequence: the adapter's hypothesis reduces to a commutation condition
on the prime transition map `f'`, at the rotation named by `h (origin hK)`.**
This is the packet's own vocabulary (`f`, `fprime`) with no `jump` left in it. -/
theorem vertexCycleEq_of_conj_comm {K : ℕ} (hK : 0 < K) (L : ℕ) (S : Fin K → α)
    (f f' h : Fin K → Fin K) (hbijf : Function.Bijective f)
    (hbijf' : Function.Bijective f')
    (hV : VisitsAll (jump hK f) (origin hK)) (hV' : VisitsAll (jump hK f') (origin hK))
    (hv : VtxPreserving hK L S h)
    (hc : JumpConj hK (jump hK f) (jump hK f') h)
    (hf' : ∀ q : Fin K, f' (rotAdd hK (h (origin hK)).val q)
      = rotAdd hK (h (origin hK)).val (f' q)) :
    VertexCycleEq hK L S (sigEquiv hK f hV) (sigEquiv hK f' hV') := by
  refine vertexCycleEq_of_conjugacy hK L S f f' h hbijf hbijf' hV hV' hv hc
    (rotAligned_of_comm (J' := jump hK f') hK h
      (fun x => (jump_commute_iff hK f' x).mpr hf'))

/-- **Special case 1: an origin-fixing conjugacy needs no extra condition.**
The witness is `origin hK` --- clause 2 of `RotAligned` holds at `k = origin`
because `rotAdd hK 0` is the identity --- so the two reconstructed listings agree
**pointwise** at every listing position. -/
theorem vertexCycleEq_of_conj_origin {K : ℕ} (hK : 0 < K) (L : ℕ) (S : Fin K → α)
    (f f' h : Fin K → Fin K) (hbijf : Function.Bijective f)
    (hbijf' : Function.Bijective f')
    (hV : VisitsAll (jump hK f) (origin hK)) (hV' : VisitsAll (jump hK f') (origin hK))
    (hv : VtxPreserving hK L S h)
    (hc : JumpConj hK (jump hK f) (jump hK f') h)
    (horigin : h (origin hK) = origin hK) :
    VertexCycleEq hK L S (sigEquiv hK f hV) (sigEquiv hK f' hV') := by
  refine vertexCycleEq_of_conjugacy hK L S f f' h hbijf hbijf' hV hV' hv hc
    ⟨horigin.trans (rotAdd_origin hK (origin hK)),
      rotAdd_origin_comm (J' := jump hK f') hK⟩

/-- **... in decidable form**, which is where the *pointwise* content shows:
`ListingVertexEq` holds at witness `origin hK`. -/
theorem conj_listingVertexEq_of_conj_origin {K : ℕ} (hK : 0 < K) (L : ℕ)
    (S : Fin K → α) (f f' h : Fin K → Fin K) (hbijf : Function.Bijective f)
    (hbijf' : Function.Bijective f')
    (hV : VisitsAll (jump hK f) (origin hK)) (hV' : VisitsAll (jump hK f') (origin hK))
    (hv : VtxPreserving hK L S h)
    (hc : JumpConj hK (jump hK f) (jump hK f') h)
    (horigin : h (origin hK) = origin hK) :
    ListingVertexEq hK L S f f' hV hV' :=
  (vertexCycleEq_iff_listing hK L S f f' hbijf hbijf' hV hV').mpr
    (vertexCycleEq_of_conj_origin hK L S f f' h hbijf hbijf' hV hV' hv hc horigin)

/-- **Special case 2: if the prime listing reads the truth's own cycle
(`J' = nextPos`, i.e. `f'` is the identity re-pairing), then `rotAdd k` centralises
`J'` at every `k`, so `RotAligned` holds unconditionally and *any* `vtx`-preserving
conjugacy suffices**, with witness `h (origin hK)`. -/
theorem vertexCycleEq_of_conj_nextPos {K : ℕ} (hK : 0 < K) (L : ℕ) (S : Fin K → α)
    (f f' h : Fin K → Fin K) (hbijf : Function.Bijective f)
    (hbijf' : Function.Bijective f')
    (hV : VisitsAll (jump hK f) (origin hK)) (hV' : VisitsAll (jump hK f') (origin hK))
    (hv : VtxPreserving hK L S h)
    (hc : JumpConj hK (jump hK f) (jump hK f') h)
    (hj : ∀ q : Fin K, jump hK f' q = nextPos hK q) :
    VertexCycleEq hK L S (sigEquiv hK f hV) (sigEquiv hK f' hV') := by
  refine vertexCycleEq_of_conjugacy hK L S f f' h hbijf hbijf' hV hV' hv hc
    (rotAligned_of_comm (J' := jump hK f') hK h (fun x => ?_))
  rw [hj]
  exact nextPos_rotAdd_one hK (h (origin hK)) x

/-! ## 6. Composing with `Issue94TransposePreserve` -/

/-- **The adapter's conclusion is stable under any vertex-invisible
transposition, at the *same* witness.**  This is `BBTTranspose`'s one-step lemma
(`BBTTranspose.vertexCycleEq_transposition`) with a general target `τ` instead of
the identity listing; it is the same three-line case analysis, because
`VertexCycleEq σ τ` at witness `k` is the pointwise statement
`∀ i, vtx (σ i) = vtx (rotAdd k (τ i))` and a swap at two starts of one
`(L-1)`-mer touches only the left-hand side. -/
theorem vertexCycleEq_transpose_conj {K : ℕ} (hK : 0 < K) (L : ℕ) (S : Fin K → α)
    {σ τ : Fin K ≃ Fin K} {a b : Fin K} (hvb : vtx hK L S a = vtx hK L S b)
    (hv : VertexCycleEq hK L S σ τ) :
    VertexCycleEq hK L S (σ.trans (Equiv.swap a b)) τ := by
  obtain ⟨k, hk⟩ := hv
  refine ⟨k, ?_⟩
  intro i
  by_cases hia : σ i = a
  · rw [Equiv.trans_apply, hia, Equiv.swap_apply_left]
    have hki := hk i
    rw [hia] at hki
    exact hki
  by_cases hib : σ i = b
  · rw [Equiv.trans_apply, hib, Equiv.swap_apply_right]
    have hki := hk i
    rw [hib, hvb] at hki
    exact hki
  rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hia hib]
  exact hk i

/-! ## 7. The bridge to `VertexCycleEq` -/

/-- **`ListingVertexEq` is `VertexCycleEq` between the reconstructions**, the
`noncomputable` `sigEquiv` being literally the `sigFun` it was built from
(`Issue94Reconstruct.sigEquiv_apply` is `rfl`).  This is what makes the
refutation of §9 a finite, decidable statement. -/
theorem vertexCycleEq_iff_listing {K : ℕ} (hK : 0 < K) (L : ℕ) (S : Fin K → α)
    (f f' : Fin K → Fin K) (hbijf : Function.Bijective f)
    (hbijf' : Function.Bijective f')
    (hV : VisitsAll (jump hK f) (origin hK)) (hV' : VisitsAll (jump hK f') (origin hK)) :
    VertexCycleEq hK L S (sigEquiv hK f hV) (sigEquiv hK f' hV')
      ↔ ListingVertexEq hK L S f f' hV hV' := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, fun i => ?_⟩
    exact hk i
  · rintro ⟨k, hk⟩
    refine ⟨k, fun i => ?_⟩
    exact hk i

/-! ## 8. Anti-vacuity: the adapter's conclusion is satisfiable -/

/-- `S = 0101` on a circle of four positions, read at window length `3`. -/
def S4c : Fin 4 → Fin 2 := ![0, 1, 0, 1]

theorem hK4c : 0 < 4 := by omega

/-- The identity re-pairing of the four starts. -/
def fRefl4 : Fin 4 → Fin 4 := ![0, 1, 2, 3]

theorem fRefl4_bij : Function.Bijective fRefl4 := by
  have h : Function.Injective fRefl4 := by decide
  exact ⟨h, (Finite.injective_iff_surjective).mp h⟩

theorem fRefl4_single : VisitsAll (jump hK4c fRefl4) (origin hK4c) := by
  unfold VisitsAll
  decide

theorem fRefl4_LP : LabelPreserving hK4c 3 S4c fRefl4 := by
  unfold LabelPreserving
  intro q
  rfl

/-- **The two reconstructed listings of `S = 0101` by the identity re-pairing are
`VertexCycleEq`, at witness `0`.**  So `ListingVertexEq` is not vacuous and the
§3 adapter has something to conclude on real data. -/
theorem listingVertexEq_0101 :
    ListingVertexEq hK4c 3 S4c fRefl4 fRefl4 fRefl4_single fRefl4_single := by
  unfold ListingVertexEq
  decide

/-- ... and it is the truth's own vertex cycle, so this instance is also the
`S = 0101` anti-vacuity check of `BBTEulerian` §4.2 read at `k = 0`. -/
theorem listingVertexEq_0101_witness :
    VertexCycleEq hK4c 3 S4c (sigEquiv hK4c fRefl4 fRefl4_single)
      (Equiv.refl (α := Fin 4)) :=
  (vertexCycleEq_iff_listing hK4c 3 S4c fRefl4 fRefl4 fRefl4_bij fRefl4_bij
    fRefl4_single fRefl4_single).mpr listingVertexEq_0101

/-! ## 9. The refutation: a `vtx`-preserving conjugacy does not give
`VertexCycleEq` -/

/-- `S = 00001` on a circle of five positions, read at window length `3`; the
`(L-1)`-mers are `00` at the starts `0, 1, 2` and `01`, `10` at `3`, `4`. -/
def S5 : Fin 5 → Fin 2 := ![0, 0, 0, 0, 1]

theorem hK5 : 0 < 5 := by omega

/-- The identity re-pairing, so that `J = nextPos` and `σ = rotAdd 1`. -/
def fRefl5 : Fin 5 → Fin 5 := ![0, 1, 2, 3, 4]

/-- The 3-cycle `0 ↦ 1 ↦ 2 ↦ 0`.  It is label-preserving because `0, 1, 2` all
spell `00`, and its jump `J' = (0 2 3 4 1)` is a single `5`-cycle. -/
def fThree5 : Fin 5 → Fin 5 := ![1, 2, 0, 3, 4]

/-- The conjugacy `h = (0 1)`: it carries `J = nextPos` to `J'` and preserves
the `(L-1)`-mer labelling, since `0` and `1` both spell `00`. -/
def hConj5 : Fin 5 → Fin 5 := ![1, 0, 2, 3, 4]

theorem fRefl5_bij : Function.Bijective fRefl5 := by
  have h : Function.Injective fRefl5 := by decide
  exact ⟨h, (Finite.injective_iff_surjective).mp h⟩

theorem fThree5_bij : Function.Bijective fThree5 := by
  have h : Function.Injective fThree5 := by decide
  exact ⟨h, (Finite.injective_iff_surjective).mp h⟩

theorem fRefl5_LP : LabelPreserving hK5 3 S5 fRefl5 := by
  unfold LabelPreserving
  decide

theorem fThree5_LP : LabelPreserving hK5 3 S5 fThree5 := by
  unfold LabelPreserving
  decide

theorem hConj5_LP : VtxPreserving hK5 3 S5 hConj5 := by
  unfold VtxPreserving
  decide

theorem fRefl5_single : VisitsAll (jump hK5 fRefl5) (origin hK5) := by
  unfold VisitsAll
  decide

theorem fThree5_single : VisitsAll (jump hK5 fThree5) (origin hK5) := by
  unfold VisitsAll
  decide

theorem hConj5_conj : JumpConj hK5 (jump hK5 fRefl5) (jump hK5 fThree5) hConj5 := by
  unfold JumpConj
  decide

/-- **THE FREE STATEMENT DOES HOLD at the refuted instance**: the listing-index
rotation by `k₀ = 4` --- the `J'`-orbit index of `h (origin) = 1` --- is a
genuine `ListingIndexEq`.  So §4 is not vacuous. -/
theorem conj_listingIndexEq_00001 :
    ListingIndexEq hK5 3 S5 fRefl5 fThree5 fRefl5_single fThree5_single :=
  conj_listingIndexEq hK5 3 S5 fRefl5 fThree5 hConj5 fRefl5_bij fThree5_bij
    fRefl5_single fThree5_single hConj5_LP hConj5_conj

/-- **But no genomic rotation works: the two reconstructed listings are NOT
`VertexCycleEq`.**  This refutes the inference "a `vtx`-preserving conjugacy
between the two jumps determines the vertex cycle". -/
theorem not_listingVertexEq_00001 :
    ¬ ListingVertexEq hK5 3 S5 fRefl5 fThree5 fRefl5_single fThree5_single := by
  unfold ListingVertexEq
  decide

/-- ... equivalently, on the `sigEquiv`s. -/
theorem not_vertexCycleEq_00001 :
    ¬ VertexCycleEq hK5 3 S5 (sigEquiv hK5 fRefl5 fRefl5_single)
        (sigEquiv hK5 fThree5 fThree5_single) :=
  fun h => not_listingVertexEq_00001
    ((vertexCycleEq_iff_listing hK5 3 S5 fRefl5 fThree5 fRefl5_bij fThree5_bij
      fRefl5_single fThree5_single).mp h)

/-- **And the alignment condition fails exactly where §2 says it must**: at the
forced witness `k = h (origin hK) = 1`, `rotAdd hK 1` does not centralise
`J' = (0 2 3 4 1)`.  So the refutation is *not* a failure of the adapter lemma;
it is the sharpness of its hypothesis. -/
theorem not_rotAligned_00001 :
    ¬ RotAligned hK5 (jump hK5 fThree5) (hConj5 (origin hK5)) hConj5 := by
  unfold RotAligned
  decide

/-- **For the record: the two listings of the refuted instance are the stated
ones**, and the two readings of "rotation" are genuinely different numbers:
`σ = (0 1 2 3 4)` is the truth's own cyclic reading and
`σ' = (0 2 3 4 1)` is the `J'`-cycle, so `k₀ = 4` is the `J'`-orbit index of
`h (origin) = 1`, whereas the only genomic candidate is `k = 1`. -/
theorem sigFun_fRefl5 : ∀ i : Fin 5, sigFun hK5 fRefl5 i = i := by decide

theorem sigFun_fThree5_0 : sigFun hK5 fThree5 (⟨0, by omega⟩ : Fin 5) = 0 := by
  decide

theorem sigFun_fThree5_1 : sigFun hK5 fThree5 (⟨1, by omega⟩ : Fin 5) = 2 := by
  decide

theorem sigFun_fThree5_4 : sigFun hK5 fThree5 (⟨4, by omega⟩ : Fin 5) = 1 := by
  decide

/-- **For the record: the refutation is not vacuous in the other direction
either** --- `σ`, the identity listing read from the start `0`, *is* the truth's
own vertex cycle. -/
theorem vertexCycleEq_refl_00001 :
    VertexCycleEq hK5 3 S5 (sigEquiv hK5 fRefl5 fRefl5_single) (Equiv.refl (α := Fin 5)) :=
  (vertexCycleEq_iff_listing hK5 3 S5 fRefl5 fRefl5 fRefl5_bij fRefl5_bij
    fRefl5_single fRefl5_single).mpr (by
      unfold ListingVertexEq
      refine ⟨origin hK5, fun i => ?_⟩
      have hz : (origin hK5 : Fin 5).val = 0 := origin_val hK5
      rw [hz, rotAdd_zero, sigFun_fRefl5 i, sigFun_fRefl5 i])

/-- **`S = 00001` has the long obstruction `thm:BBT` predicts**: the length-`3`
window `000` is a *maximal* triple repeat at the three distinct starts `0, 1, 2`
(the preceding symbols are `1, 0, 0` and the following symbols are `0, 1, 0`, so
neither "all equal" clause holds), and `L - 1 = 2 ≤ 3`.  So this instance is not a
counterexample to `thm:BBT`; it is an instance of it. -/
theorem longObstruction_00001 : LongObstruction hK5 3 S5 := by
  refine Or.inl ⟨⟨3, by omega⟩, ⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ?_,
    by omega⟩
  decide

/-- **Axiom audit.** -/

#print axioms AssemblyP1.Issue94ConjugacyAdapter.rotAdd_origin
#print axioms AssemblyP1.Issue94ConjugacyAdapter.nextPos_rotAdd_one
#print axioms AssemblyP1.Issue94ConjugacyAdapter.rotAdd_origin_comm
#print axioms AssemblyP1.Issue94ConjugacyAdapter.jump_commute_iff
#print axioms AssemblyP1.Issue94ConjugacyAdapter.iterate_conj_aux
#print axioms AssemblyP1.Issue94ConjugacyAdapter.iterate_conj
#print axioms AssemblyP1.Issue94ConjugacyAdapter.iterate_comm_rotAdd
#print axioms AssemblyP1.Issue94ConjugacyAdapter.vertexCycleEq_of_conjugacy
#print axioms AssemblyP1.Issue94ConjugacyAdapter.vertexCycleEq_iff_orbit_conj
#print axioms AssemblyP1.Issue94ConjugacyAdapter.eulerianCycles_vertexCycleEq_of_conjugacy
#print axioms AssemblyP1.Issue94ConjugacyAdapter.listingIndex_conj
#print axioms AssemblyP1.Issue94ConjugacyAdapter.conj_listingIndexEq
#print axioms AssemblyP1.Issue94ConjugacyAdapter.rotAligned_of_comm
#print axioms AssemblyP1.Issue94ConjugacyAdapter.vertexCycleEq_of_conj_comm
#print axioms AssemblyP1.Issue94ConjugacyAdapter.vertexCycleEq_of_conj_origin
#print axioms AssemblyP1.Issue94ConjugacyAdapter.conj_listingVertexEq_of_conj_origin
#print axioms AssemblyP1.Issue94ConjugacyAdapter.vertexCycleEq_of_conj_nextPos
#print axioms AssemblyP1.Issue94ConjugacyAdapter.vertexCycleEq_transpose_conj
#print axioms AssemblyP1.Issue94ConjugacyAdapter.vertexCycleEq_iff_listing
#print axioms AssemblyP1.Issue94ConjugacyAdapter.listingVertexEq_0101
#print axioms AssemblyP1.Issue94ConjugacyAdapter.listingVertexEq_0101_witness
#print axioms AssemblyP1.Issue94ConjugacyAdapter.conj_listingIndexEq_00001
#print axioms AssemblyP1.Issue94ConjugacyAdapter.not_listingVertexEq_00001
#print axioms AssemblyP1.Issue94ConjugacyAdapter.not_vertexCycleEq_00001
#print axioms AssemblyP1.Issue94ConjugacyAdapter.not_rotAligned_00001
#print axioms AssemblyP1.Issue94ConjugacyAdapter.sigFun_fRefl5
#print axioms AssemblyP1.Issue94ConjugacyAdapter.sigFun_fThree5_0
#print axioms AssemblyP1.Issue94ConjugacyAdapter.sigFun_fThree5_1
#print axioms AssemblyP1.Issue94ConjugacyAdapter.sigFun_fThree5_4
#print axioms AssemblyP1.Issue94ConjugacyAdapter.vertexCycleEq_refl_00001
#print axioms AssemblyP1.Issue94ConjugacyAdapter.longObstruction_00001

end AssemblyP1.Issue94ConjugacyAdapter