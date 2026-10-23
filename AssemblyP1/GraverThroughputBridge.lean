import AssemblyP1.GraverRigidity
import AssemblyP1.SeparableConvexGraver

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Edge-flow / vertex-throughput Graver bridge (issue #263)

This file discharges the `HasGraverDecomposition` hypothesis consumed by the
already-merged separable-convex Graver optimality certificate
(`AssemblyP1.SeparableConvexGraver.graver_optimal_iff_no_improving`, PR #331)
for an **edge-flow / vertex-throughput** integer system.  It reuses the
integer-kernel conformal decomposition
`AssemblyP1.GraverRigidity.graver_decomposition` (#257) and does **not** reprove
it, nor the convex-objective half, nor the historical signed-graph adapter
(#261, deliberately left open).

## The system

Let `E` be a finite type of support edges, `V` a finite type of vertices, and
`tail head : E → V` the endpoint maps.  The **edge-flow** map is

```
flowLin tail head f : (V ⊕ Unit) → ℤ
flowLin f (inl v) = (out-flow at v) - (in-flow at v)      -- balance row
flowLin f (inr _) = ∑ e, f e                              -- fixed-total row
```

so `flowLin f = 0` is exactly `BalancedZ f ∧ ZeroSum f`, the lattice
`L₀ = ker_ℤ[M; 1ᵀ]` of `AssemblyP1.GraverRigidity`.

The **augmented** `[A 0; -T I]` system adds one throughput variable `s_v` per
vertex and the coupling row `s_v - (T f)_v = 0`:

```
augLin tail head T w : ((V ⊕ Unit) ⊕ V) → ℤ
augLin w (inl r)   = flowLin (fun e => w (inl e)) r        -- the [A 0] block
augLin w (inr v)   = w (inr v) - T (fun e => w (inl e)) v  -- the [-T I] block
```

Its kernel is the graph `{(δ, T δ) : δ ∈ L₀}` of the throughput map `T` over the
edge lattice: the identity block makes `s` a *dependent* slack, so the kernel
projects isomorphically onto `L₀`.

## Main results

* `flowLin_eq_zero_iff`, `augLin_eq_zero_iff` — kernel characterisations.
* `hasGraverDecomposition_flow` — the edge-flow system satisfies
  `HasGraverDecomposition`, proved **directly from**
  `GraverRigidity.graver_decomposition`: a feasible displacement is balanced and
  zero-sum, so it admits a conformal Graver decomposition, and conformality
  implies the coordinatewise sign-compatibility required by
  `HasGraverDecomposition`.
* `graver_optimal_flow` — the conditional optimality certificate instantiated on
  the edge-flow system, with the decomposition hypothesis discharged.
* `hasGraverDecomposition_aug` — the augmented `[A 0; -T I]` system satisfies
  `HasGraverDecomposition` whenever `T` is additive and annihilates every Graver
  move (equivalently, annihilates `L₀`); then the throughput coordinate of every
  lifted Graver move is `0`, so the augmented sign-compatibility reduces to the
  edge one.

## Scope and the remaining open obstruction

The hypothesis `hT` of `hasGraverDecomposition_aug` says the throughput map `T`
is a linear functional of the flow constraints (it vanishes on `L₀`).  This is
the case in which the augmented system genuinely reduces to the edge-flow
system.  For the *genuine* vertex-throughput map of the #261 flow model
(`T_v f = out-flow at v`) `hT` is **false**: `T` does not vanish on `L₀`, and the
throughput coordinates of the lifted Graver moves need not be sign-compatible.
The naive lift `g ↦ (g, T g)` of a conformal Graver decomposition therefore does
**not** automatically satisfy the full augmented sign-compatibility, and the
correct general statement (a `T`-sign-compatible conformal Graver decomposition
for every `T`) is left explicitly **OPEN**.  What is established here is the
honest conditional bridge: the certificate's decomposition hypothesis is a
theorem for the edge-flow system, and it lifts to the augmented
`[A 0; -T I]` system precisely when the throughput coordinates are redundant.
-/

namespace AssemblyP1.GraverThroughputBridge

open Finset BigOperators
open AssemblyP1.GraverRigidity
open AssemblyP1.SeparableConvexGraver

section FlowSystem

variable {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype E] [Fintype V]

/-- Signed vertex balance of an integer edge function `f` at `v`: out-flow minus
in-flow.  This is the `[A ·]` row of the augmented matrix. -/
def bal (tail head : E → V) (f : E → ℤ) (v : V) : ℤ :=
  (∑ e ∈ Finset.univ.filter (fun e => tail e = v), f e) -
  (∑ e ∈ Finset.univ.filter (fun e => head e = v), f e)

/-- The edge-flow linear map: balance rows (`V`) plus the fixed-total row
(`Unit`).  `flowLin f = 0` is exactly the lattice `L₀ = ker_ℤ[M; 1ᵀ]` of
`AssemblyP1.GraverRigidity`. -/
def flowLin (tail head : E → V) : (E → ℤ) → (V ⊕ Unit → ℤ) :=
  fun f => Sum.elim (bal tail head f) (fun _ => ∑ e, f e)

/-- `flowLin` is additive. -/
theorem flowLin_add (tail head : E → V) (x y : E → ℤ) :
    flowLin tail head (x + y) = flowLin tail head x + flowLin tail head y := by
  funext r
  rcases r with v | u
  · show bal tail head (x + y) v = bal tail head x v + bal tail head y v
    unfold bal
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    ring
  · show (∑ e, (x + y) e) = (∑ e, x e) + (∑ e, y e)
    simp only [Pi.add_apply, Finset.sum_add_distrib]

/-- `flowLin` is subtractive. -/
theorem flowLin_sub (tail head : E → V) (x y : E → ℤ) :
    flowLin tail head (x - y) = flowLin tail head x - flowLin tail head y := by
  funext r
  rcases r with v | u
  · show bal tail head (x - y) v = bal tail head x v - bal tail head y v
    unfold bal
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    ring
  · show (∑ e, (x - y) e) = (∑ e, x e) - (∑ e, y e)
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]

/-- The kernel of `flowLin` is the balanced zero-sum lattice `L₀`. -/
theorem flowLin_eq_zero_iff (tail head : E → V) (f : E → ℤ) :
    flowLin tail head f = 0 ↔ BalancedZ tail head Finset.univ f ∧ ZeroSum f := by
  constructor
  · intro h
    constructor
    · intro v _
      have hv : bal tail head f v = 0 := by
        have := congrFun h (Sum.inl v)
        simpa [flowLin] using this
      change (∑ e ∈ Finset.univ.filter (fun e => tail e = v), f e)
          = (∑ e ∈ Finset.univ.filter (fun e => head e = v), f e)
      unfold bal at hv
      omega
    · have ht : (∑ e, f e) = 0 := by
        have := congrFun h (Sum.inr ())
        simpa [flowLin] using this
      exact ht
  · intro hb
    funext r
    rcases r with v | u
    · have hv := hb.1 v (Finset.mem_univ v)
      change (∑ e ∈ Finset.univ.filter (fun e => tail e = v), f e)
          = (∑ e ∈ Finset.univ.filter (fun e => head e = v), f e) at hv
      show bal tail head f v = 0
      unfold bal
      omega
    · show (∑ e, f e) = 0
      exact hb.2

/-- Conformality to a common displacement `δ` implies the coordinatewise
sign-compatibility required by `HasGraverDecomposition`: at every coordinate all
the moves have the sign of `δ`. -/
theorem conformal_same_sign {δ : E → ℤ} {gs : List (E → ℤ)}
    (h : ∀ g ∈ gs, Conformal g δ) :
    ∀ e, (∀ g ∈ gs, 0 ≤ g e) ∨ (∀ g ∈ gs, g e ≤ 0) := by
  intro e
  rcases le_total (δ e) 0 with hle | hge
  · right
    intro g hg
    have h1 := (h g hg e).2
    have h2 : AssemblyP1.GraverRigidity.posPart δ e = 0 :=
      posPart_eq_zero_of_nonpos hle
    rw [h2] at h1
    exact posPart_eq_zero (le_antisymm h1 (posPart_nonneg e))
  · left
    intro g hg
    have h1 := (h g hg e).1
    have h2 : AssemblyP1.GraverRigidity.negPart δ e = 0 :=
      negPart_eq_zero_of_nonneg hge
    rw [h2] at h1
    exact negPart_eq_zero (le_antisymm h1 (negPart_nonneg e))

/-- Finite sums preserve a supplied common sign.  This is the elementary
throughput-coordinate step needed by any T-sign-compatible decomposition; the
sign-compatible list itself remains an independent structural obligation. -/
theorem list_sum_same_sign {α : Type} (φ : α → ℤ) (gs : List α)
    (hsign : (∀ g ∈ gs, 0 ≤ φ g) ∨ (∀ g ∈ gs, φ g ≤ 0)) :
    (0 ≤ (gs.map φ).sum) ∨ (gs.map φ).sum ≤ 0 := by
  rcases hsign with hp | hn
  · exact Or.inl (List.sum_nonneg (by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨g, hg, rfl⟩ := hx
      exact hp g hg))
  · exact Or.inr (list_sum_nonpos_int (by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨g, hg, rfl⟩ := hx
      exact hn g hg))

/-- **Edge-flow Graver decomposition.**  The edge-flow system satisfies the
`HasGraverDecomposition` hypothesis of the separable-convex certificate, proved
directly from `AssemblyP1.GraverRigidity.graver_decomposition`.  A feasible
displacement `y - z` is balanced and zero-sum, hence conformally decomposable
into Graver moves, and conformality gives the coordinatewise
sign-compatibility. -/
theorem hasGraverDecomposition_flow (tail head : E → V)
    (b : V ⊕ Unit → ℤ) (l u : E → ℤ) {z : E → ℤ}
    (hz : Feasible (flowLin tail head) b l u z) :
    HasGraverDecomposition (flowLin tail head) b l u (Graver tail head Finset.univ) z := by
  intro y hy
  have hlin : flowLin tail head (y - z) = 0 := by
    rw [flowLin_sub, hy.1, hz.1, sub_self]
  have hker := (flowLin_eq_zero_iff tail head (y - z)).mp hlin
  by_cases hzero : y - z = 0
  · refine ⟨[], ?_, ?_, ?_⟩
    · intro g hg; simp at hg
    · intro e; left; intro g hg; simp at hg
    · simpa using hzero.symm
  · have hne : ∃ e, (y - z) e ≠ 0 := by
      by_contra h
      apply hzero
      funext e
      by_contra he
      exact h ⟨e, he⟩
    obtain ⟨gs, hgs, hgsum⟩ :=
      graver_decomposition tail head Finset.univ hker.1 hker.2 hne
    refine ⟨gs, ?_, ?_, hgsum⟩
    · intro g hg; exact (hgs g hg).1
    · exact conformal_same_sign (fun g hg => (hgs g hg).2.1)

/-- `Graver` moves lie in the kernel of `flowLin` (the certificate's `hker`). -/
theorem graver_flowLin_eq_zero (tail head : E → V) {g : E → ℤ}
    (hg : Graver tail head Finset.univ g) :
    flowLin tail head g = 0 :=
  (flowLin_eq_zero_iff tail head g).mpr ⟨hg.2.1, hg.2.2.1⟩

/-- **Instantiated separable-convex Graver certificate on the edge-flow system.**
This is `AssemblyP1.SeparableConvexGraver.graver_optimal_iff_no_improving` with
the `HasGraverDecomposition` hypothesis discharged by
`hasGraverDecomposition_flow`, so the certificate is unconditional for the
edge-flow system. -/
theorem graver_optimal_flow (tail head : E → V) (b : V ⊕ Unit → ℤ) (l u : E → ℤ)
    {f : E → ℤ → ℝ} (hf : ∀ e, DiscConvOn (f e) (l e) (u e)) {z : E → ℤ}
    (hz : Feasible (flowLin tail head) b l u z) :
    (∀ w, Feasible (flowLin tail head) b l u w → sepObj f z ≤ sepObj f w) ↔
    (∀ g, Graver tail head Finset.univ g → Feasible (flowLin tail head) b l u (z + g) →
      sepObj f z ≤ sepObj f (z + g)) :=
  graver_optimal_iff_no_improving (flowLin tail head) b l u (Graver tail head Finset.univ)
    (flowLin_add tail head) (fun _ hg => graver_flowLin_eq_zero tail head hg)
    hf hz (hasGraverDecomposition_flow tail head b l u hz)

end FlowSystem

/-! ## The augmented `[A 0; -T I]` system -/

section Augmented

variable {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype E] [Fintype V]

/-- The augmented `[A 0; -T I]` map on `(edge flow, vertex throughput)`
coordinates: the `[A 0]` block is `flowLin` on the edge coordinates, and the
`[-T I]` block is the coupling `s_v - (T f)_v`. -/
def augLin (tail head : E → V) (T : (E → ℤ) → (V → ℤ)) :
    (E ⊕ V → ℤ) → ((V ⊕ Unit) ⊕ V → ℤ) :=
  fun w => Sum.elim
    (flowLin tail head (fun e => w (Sum.inl e)))
    (fun v => w (Sum.inr v) - T (fun e => w (Sum.inl e)) v)

/-- The augmented Graver predicate: a Graver move of the edge lattice, lifted to
the augmented coordinates by the throughput coupling `s = T g`. -/
def augGraver (tail head : E → V) (T : (E → ℤ) → (V → ℤ)) (w : E ⊕ V → ℤ) : Prop :=
  Graver tail head Finset.univ (fun e => w (Sum.inl e)) ∧
    (∀ v, w (Sum.inr v) = T (fun e => w (Sum.inl e)) v)

/-- Kernel of the augmented `[A 0; -T I]` system: the graph of the throughput map
over the edge lattice `L₀`. -/
theorem augLin_eq_zero_iff (tail head : E → V) (T : (E → ℤ) → (V → ℤ))
    (w : E ⊕ V → ℤ) :
    augLin tail head T w = 0 ↔
      flowLin tail head (fun e => w (Sum.inl e)) = 0 ∧
        (∀ v, w (Sum.inr v) = T (fun e => w (Sum.inl e)) v) := by
  constructor
  · intro h
    constructor
    · funext r
      have := congrFun h (Sum.inl r)
      simpa [augLin] using this
    · intro v
      have := congrFun h (Sum.inr v)
      simp only [augLin, Sum.elim_inr, Pi.zero_apply] at this
      omega
  · intro ⟨hf, hs⟩
    funext r
    rcases r with r | v
    · have := congrFun hf r
      simpa [augLin] using this
    · have := hs v
      simp only [augLin, Sum.elim_inr, Pi.zero_apply]
      omega

/-- The lift of an edge function to the augmented coordinates, `g ↦ (g, T g)`. -/
def lift (T : (E → ℤ) → (V → ℤ)) (g : E → ℤ) : E ⊕ V → ℤ := Sum.elim g (T g)

@[simp] theorem lift_inl (T : (E → ℤ) → (V → ℤ)) (g : E → ℤ) (e : E) :
    lift T g (Sum.inl e) = g e := rfl

@[simp] theorem lift_inr (T : (E → ℤ) → (V → ℤ)) (g : E → ℤ) (v : V) :
    lift T g (Sum.inr v) = T g v := rfl

/-- `T` sends the zero edge function to zero, from additivity. -/
theorem T_zero (T : (E → ℤ) → (V → ℤ))
    (hT_add : ∀ x y, T (x + y) = T x + T y) : T 0 = 0 := by
  have h : T (0 : E → ℤ) = T 0 + T 0 := by
    simpa using hT_add (0 : E → ℤ) 0
  funext v
  have hv := congrFun h v
  rw [Pi.add_apply] at hv
  change T 0 v = 0
  omega

/-- Additivity of the lift. -/
theorem lift_add (T : (E → ℤ) → (V → ℤ))
    (hT_add : ∀ x y, T (x + y) = T x + T y) (x y : E → ℤ) :
    lift T (x + y) = lift T x + lift T y := by
  funext r
  rcases r with e | v
  · simp
  · simp only [lift_inr, Pi.add_apply, hT_add]

/-- Additivity of the lift on list sums. -/
theorem lift_list_sum (T : (E → ℤ) → (V → ℤ))
    (hT_add : ∀ x y, T (x + y) = T x + T y) (gs : List (E → ℤ)) :
    (gs.map (lift T)).sum = lift T gs.sum := by
  induction gs with
  | nil => simp [lift, T_zero T hT_add]
  | cons g t ih =>
    rw [List.map_cons, List.sum_cons, ih, List.sum_cons, lift_add T hT_add]

/-- Additivity of `T` on list sums. -/
theorem T_list_sum (T : (E → ℤ) → (V → ℤ))
    (hT_add : ∀ x y, T (x + y) = T x + T y) (gs : List (E → ℤ)) :
    T gs.sum = (gs.map T).sum := by
  induction gs with
  | nil => rw [List.map_nil, List.sum_nil]; exact T_zero T hT_add
  | cons g t ih =>
    rw [List.sum_cons, hT_add, List.map_cons, List.sum_cons, ih]

/-- `T` preserves subtraction. -/
theorem T_sub (T : (E → ℤ) → (V → ℤ))
    (hT_add : ∀ x y, T (x + y) = T x + T y) (x y : E → ℤ) :
    T (x - y) = T x - T y := by
  funext v
  have h := congrFun (hT_add (x - y) y) v
  rw [Pi.add_apply] at h
  rw [sub_add_cancel] at h
  simp only [Pi.sub_apply]
  omega

/-- `augLin` is subtractive in its argument. -/
theorem augLin_sub (tail head : E → V) (T : (E → ℤ) → (V → ℤ))
    (hT_add : ∀ x y, T (x + y) = T x + T y) (x y : E ⊕ V → ℤ) :
    augLin tail head T (x - y) = augLin tail head T x - augLin tail head T y := by
  funext r
  rcases r with r | v
  · have h := congrFun (flowLin_sub tail head (fun e => x (Sum.inl e)) (fun e => y (Sum.inl e))) r
    rw [show (fun e => x (Sum.inl e)) - (fun e => y (Sum.inl e))
          = (fun e => x (Sum.inl e) - y (Sum.inl e)) from rfl] at h
    simpa [augLin, Pi.sub_apply] using h
  · show (x (Sum.inr v) - y (Sum.inr v)) - T (fun e => x (Sum.inl e) - y (Sum.inl e)) v
        = (x (Sum.inr v) - T (fun e => x (Sum.inl e)) v)
          - (y (Sum.inr v) - T (fun e => y (Sum.inl e)) v)
    rw [show (fun e => x (Sum.inl e) - y (Sum.inl e))
          = (fun e => x (Sum.inl e)) - (fun e => y (Sum.inl e)) from rfl]
    rw [T_sub T hT_add]
    simp only [Pi.sub_apply]
    ring

/-- **Augmented `[A 0; -T I]` Graver decomposition.**  If the throughput map `T`
is additive and annihilates every Graver move (equivalently annihilates the edge
lattice `L₀`), then the augmented edge-flow / vertex-throughput system satisfies
the `HasGraverDecomposition` hypothesis, by lifting the edge-flow decomposition
`hasGraverDecomposition_flow`.  In this case the throughput coordinate of every
lifted Graver move is `0`, so the augmented sign-compatibility reduces to the
edge one. -/
theorem hasGraverDecomposition_aug (tail head : E → V) (T : (E → ℤ) → (V → ℤ))
    (hT_add : ∀ x y, T (x + y) = T x + T y)
    (hT : ∀ g, Graver tail head Finset.univ g → T g = 0)
    (b : (V ⊕ Unit) ⊕ V → ℤ) (l u : E ⊕ V → ℤ) {z : E ⊕ V → ℤ}
    (hz : Feasible (augLin tail head T) b l u z) :
    HasGraverDecomposition (augLin tail head T) b l u (augGraver tail head T) z := by
  intro y hy
  have hbz : flowLin tail head (fun e => z (Sum.inl e)) = (fun r => b (Sum.inl r)) := by
    funext r
    have := congrFun hz.1 (Sum.inl r)
    simpa [augLin] using this
  have hby : flowLin tail head (fun e => y (Sum.inl e)) = (fun r => b (Sum.inl r)) := by
    funext r
    have := congrFun hy.1 (Sum.inl r)
    simpa [augLin] using this
  have hzf : Feasible (flowLin tail head) (fun r => b (Sum.inl r))
      (fun e => l (Sum.inl e)) (fun e => u (Sum.inl e)) (fun e => z (Sum.inl e)) :=
    ⟨hbz, fun e => ⟨(hz.2 (Sum.inl e)).1, (hz.2 (Sum.inl e)).2⟩⟩
  have hyf : Feasible (flowLin tail head) (fun r => b (Sum.inl r))
      (fun e => l (Sum.inl e)) (fun e => u (Sum.inl e)) (fun e => y (Sum.inl e)) :=
    ⟨hby, fun e => ⟨(hy.2 (Sum.inl e)).1, (hy.2 (Sum.inl e)).2⟩⟩
  obtain ⟨gs, hgs, hsign, hsum⟩ :=
    hasGraverDecomposition_flow tail head (fun r => b (Sum.inl r))
      (fun e => l (Sum.inl e)) (fun e => u (Sum.inl e)) hzf (fun e => y (Sum.inl e)) hyf
  have hTsum : T gs.sum = 0 := by
    rw [T_list_sum T hT_add]
    apply List.sum_eq_zero
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    exact hT g (hgs g hg)
  have hker : augLin tail head T (y - z) = 0 := by
    rw [augLin_sub tail head T hT_add, hy.1, hz.1, sub_self]
  have hvertzero : ∀ v, (y - z) (Sum.inr v) = 0 := by
    intro v
    have hv := congrFun hker (Sum.inr v)
    simp only [augLin, Sum.elim_inr, Pi.zero_apply] at hv
    have hedge : (fun e => (y - z) (Sum.inl e)) = gs.sum := by
      funext e
      rw [hsum]
      rfl
    rw [hedge, hTsum] at hv
    simp only [Pi.zero_apply] at hv
    omega
  refine ⟨gs.map (lift T), ?_, ?_, ?_⟩
  · intro w hw
    rw [List.mem_map] at hw
    obtain ⟨g, hg, rfl⟩ := hw
    exact ⟨hgs g hg, fun v => rfl⟩
  · intro r
    rcases r with e | v
    · rcases hsign e with hp | hn
      · left
        intro w hw
        rw [List.mem_map] at hw
        obtain ⟨g, hg, rfl⟩ := hw
        simpa using hp g hg
      · right
        intro w hw
        rw [List.mem_map] at hw
        obtain ⟨g, hg, rfl⟩ := hw
        simpa using hn g hg
    · left
      intro w hw
      rw [List.mem_map] at hw
      obtain ⟨g, hg, rfl⟩ := hw
      have := hT g (hgs g hg)
      simp [lift_inr, this]
  · rw [lift_list_sum T hT_add]
    funext r
    rcases r with e | v
    · simp only [lift_inl]
      have := congrFun hsum e
      simpa [Pi.sub_apply] using this
    · simp only [lift_inr]
      rw [hTsum]
      simp only [Pi.zero_apply]
      exact (hvertzero v).symm

end Augmented

end AssemblyP1.GraverThroughputBridge
