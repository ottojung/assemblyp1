import AssemblyP1.BBTEulerian

/-!
# Board 94, front `94th` --- the Eulerian one-cycle rematching `theta` and the residual

This module tests the proposed factorization

> from a same-`L`-spectrum competitor `D`, use only the NON-CIRCULAR construction
> lemmas to produce the fibre-preserving one-cycle rematching `theta`; if `D` is
> not a rotation, translate that into a failure of `VertexCycleEq`; the one
> genuinely new structural theorem is then "bad `theta` implies
> `LongObstruction`"

and reports what it actually costs.  It adds **no** hypothesis of the
`BBT`/`EulerianCycleObstruction` kind, uses no endpoint result, and does not
claim the open problem.  It contains:

* §1. `theta` exists and is one cycle: this is *already in the tree*
  (`BBTChords.exists_matching`, `BBTCondense.pullback_isEquiv`,
  `BBTEulerian.pullback_isEulerianCycle`).  Nothing new is proved here.
* §2. Shift-invariance of `vtx` / `window`, hence `IsRotation σ ⟹
  VertexCycleEq σ (refl)`.  These lemmas are genuinely new to the tree and are
  the missing half of "rotation of `theta` ⟹ trivial vertex cycle".
* §3. Step 2 of the factorization, in its *pull-back-restricted* form:
  `¬ RotEquiv E S ⟹ ¬ VertexCycleEq (pullback …) (refl)`.  **Proved, and free**:
  it is the contrapositive of the already-proved
  `BBTEulerian.rotEquiv_of_vertexCycleEq`.  So step 2 carries no new content.
* §3.2. The *unrestricted* form of step 2 --- "an Eulerian cycle `sigma` which is
  not a rotation has a nontrivial vertex cycle" --- is **false**, `decide`-closed,
  at `S = 0101`, `G = 4`, `L = 3`.
* §4. The residual obligation of the factorization, `BadThetaObstruction`, is
  **equivalent, in both directions, to `thm:BBT` in its
  `bbtCompleteSpec_of_obstruction` form**.  So the "one genuinely new structural
  theorem" *is* the target, and the factorization reduces nothing.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace AssemblyP1.Issue94EulerianTheta

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1
open AssemblyP1.BBTEulerian

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-! ## 1. The rematching `theta` already exists, and it is already one cycle -/

/-- **Step 1 of the factorization is already in the tree.**  A same-`L`-spectrum
competitor `E` yields a bijection `σ` with `Matching (L := L) hG S E σ`; its
converse `θ := pullback hG L S E σ.1` is a permutation of the starts which
satisfies the `traverses` clause and is a single `G`-cycle, i.e. an
`EulerianCycle`.  `BBTChords.exists_matching`, `BBTCondense.pullback_isEquiv`
and `BBTEulerian.pullback_isEulerianCycle` supply all three steps; this
corollary exists only to record the composition in one place.  No new
mathematics is in it. -/
theorem theta_of_same_spectrum_is_one_cycle {E : Fin G → α}
    (hspec : specCount (L := L) hG S = specCount (L := L) hG E) :
    ∃ θ : Fin G ≃ Fin G, EulerianCycle hG L S θ ∧
      (∀ s : Fin G, window (L := L) hG S (θ s) = window (L := L) hG E s) := by
  obtain ⟨σ, hm⟩ := exists_matching hG S E hspec
  refine ⟨pullback hG L S E hm.1, pullback_isEulerianCycle hG L S hm, fun s => ?_⟩
  exact pullback_window hG L S E hm s

/-! ## 2. `vtx` and `window` are shift-invariant; a rotation is vertex-cycle-trivial -/

/-- **Circular windows do not depend on the presentation of the start.** -/
theorem window_rotAdd (hG : 0 < G) {L : ℕ} (W : Fin G → α) (s : ℕ) (x : Fin G) :
    window (L := L) hG W (rotAdd hG s x) = window (L := L) hG W x := by
  funext d
  simp only [window]
  refine cyc_congr (Nat.ModEq.add_left ?_)
  rw [rotAdd_mod hG s x]
  exact Nat.mod_add_mod _ _ _

/-- Same for the `(L-1)`-mers, i.e. for `vtx`. -/
theorem vtx_rotAdd (hG : 0 < G) (L : ℕ) (S : Fin G → α) (s : ℕ) (x : Fin G) :
    vtx hG L S (rotAdd hG s x) = vtx hG L S x := by
  funext d
  simp only [vtx, nodeWindow]
  refine cyc_congr (Nat.ModEq.add_left ?_)
  rw [rotAdd_mod hG s x]
  exact Nat.mod_add_mod _ _ _

/-- **A rotation of the circle has the truth's vertex cycle.**  This is the
missing half of "`θ` is a rotation ⟹ `θ` is vertex-cycle-trivial", and it is
the only genuinely new ingredient this front contributes.  It uses no `Ukkonen`,
no `P2` and no `BBT`. -/
theorem vertexCycleEq_of_isRotation (σ : Fin G ≃ Fin G)
    (hrot : IsRotation hG (σ : Fin G → Fin G)) :
    VertexCycleEq hG L S σ (Equiv.refl (α := Fin G)) := by
  obtain ⟨k, hk⟩ := hrot
  refine ⟨⟨k % G, Nat.mod_lt _ hG⟩, fun i => ?_⟩
  rw [vtx_rotAdd hG L S k (σ i), ← hk i, rotAdd_mod]

/-- **A rotational pull-back is vertex-cycle-trivial.**  This is the
`BBTCondense`-free half of the "bad `theta`" analysis: a rematching which is a
rotation of the circle cannot be bad, without any appeal to the spectrum. -/
theorem vertexCycleEq_of_isRotation_pullback {E : Fin G → α} {σ : Fin G → Fin G}
    (hm : Matching (L := L) hG S E σ) (hrot : IsRotation hG (pullback hG L S E hm.1)) :
    VertexCycleEq hG L S (pullback hG L S E hm.1) (Equiv.refl (α := Fin G)) :=
  vertexCycleEq_of_isRotation hG L S _ hrot

/-! ## 3. Step 2 of the factorization, in its pull-back-restricted form -/

/-- **Step 2, pull-back-restricted: a non-rotational competitor forces a bad
rematching.**  Equivalently, a rematching which is vertex-cycle-trivial forces
the competitor to be a rotation of the truth.  This is **not new mathematics**:
it is the contrapositive of the already-proved
`BBTEulerian.rotEquiv_of_vertexCycleEq`, which is itself built from §2 and the
de Bruijn shift relation alone.  It uses no `Ukkonen`, no `P2`, no `BBT`. -/
theorem badTheta_of_not_RotEquiv {E : Fin G → α} {σ : Fin G → Fin G} (hL : 2 ≤ L)
    (hm : Matching (L := L) hG S E σ) (hne : ¬ RotEquiv hG E S) :
    ¬ VertexCycleEq hG L S (pullback hG L S E hm.1) (Equiv.refl (α := Fin G)) := by
  intro hv
  exact hne (rotEquiv_of_vertexCycleEq hG L S (pullback hG L S E hm.1) hL hv
    (fun s => (pullback_window hG L S E hm s).symm))

/-- **And the converse of step 2, also free**: a *rotational* competitor forces
a *non-bad* rematching, by §2 and the shift-invariance of windows.  So for the
rematching `theta` the two conditions "`theta` is a rotation" and
"`theta` is vertex-cycle-trivial" are **independent**: neither implies the other.
This is the exact logical content of `BBTEulerian` §4.2, and it is why the
factorization's step 2 can only be had in the pull-back-restricted form. -/
theorem vertexCycleEq_of_RotEquiv_pullback {E : Fin G → α} {σ : Fin G → Fin G}
    (hm : Matching (L := L) hG S E σ) (hrot : RotEquiv hG E S) (hL : 1 ≤ L) :
    VertexCycleEq hG L S (pullback hG L S E hm.1) (Equiv.refl (α := Fin G)) := by
  obtain ⟨k, hk⟩ := hrot
  refine ⟨⟨k % G, Nat.mod_lt _ hG⟩, fun i => ?_⟩
  -- `E` is a shift of `S`, so the two have the *same* windows at every start
  have hwin : ∀ i : Fin G, window (L := L) hG E i = window (L := L) hG S i := by
    intro i
    funext d
    simp only [window, cyc]
    refine congrArg S (Fin.ext ?_)
    have h1 := hk ⟨((i.val + d.val + G) - k) % G, Nat.mod_lt _ hG⟩
    have h2 : (((i.val + d.val + G) - k) % G + k) % G = i.val + d.val := by
      have : ((i.val + d.val + G) - k) % G + k = i.val + d.val + G := by
        omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by
        have := i.isLt
        omega)]
    simpa only [Fin.mk.injEq] using h2 ▸ h1
  have h1 := pullback_window hG L S E hm i
  have h2 := congrFun (hwin i) (⟨0, by omega⟩ : Fin (L - 1))
  rw [h1] at h2
  exact congrFun (by rw [h2]; exact (vtx_rotAdd hG L S _ _ _).symm) ⟨0, by omega⟩

/-! ### 3.1 The unrestricted form of step 2 is false -/

/-- `S = 0101` at `G = 4`, `L = 3`, as in `BBTEulerian` §4.2. -/
def S4t : Fin 4 → Fin 2 := BBTEulerian.S4

/-- **REFUTED (kernel-checked, `decide`): the unrestricted step 2.**

The packet's step 2, read at the object the packet names --- "a fibre-preserving
one-cycle rematching `theta`; if `theta` is not a rotation, translate that into
a failure of `VertexCycleEq`" --- is the statement

  `∀ σ, EulerianCycle σ → ¬ IsRotation σ → ¬ VertexCycleEq σ (refl)`

and it is **false**.  The instance is `S = 0101`, `G = 4`, `L = 3` and
`σ = tau4 = (0 1)(2 3)`: an alternative `EulerianCycle`, not a rotation of the
circle, whose vertex cycle is *the truth's own*.  No spectrum, no competitor
and no `LongObstruction` is needed, so this refutes the step in the strongest
possible form. -/
theorem step2_unrestricted_refuted :
    ¬ (∀ σ : Fin 4 ≃ Fin 4, EulerianCycle BBTEulerian.hG4 3 S4t σ →
        ¬ IsRotation BBTEulerian.hG4 (σ : Fin 4 → Fin 4) →
        ¬ VertexCycleEq BBTEulerian.hG4 3 S4t σ (Equiv.refl (α := Fin 4))) := by
  intro h
  exact h BBTEulerian.tau4 BBTEulerian.eulerianCycle_S4
    BBTEulerian.not_rotation_S4 (BBTEulerian.trivial_vertexCycleEq_S4)

/-! ## 4. The residual obligation of the factorization *is* `thm:BBT` -/

/-- **The residual obligation left by the factorization**: a same-`L`-spectrum
competitor together with a bad (vertex-cycle-nontrivial) rematching forces the
long obstruction.  This is the packet's "bad `theta` implies
`LongObstruction`", stated with the `theta` supplied by the construction
lemmas of §1, i.e. as the pull-back of a `Matching`. -/
def BadThetaObstruction (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S E : Fin K → α) (σ : Fin K → Fin K),
    Matching (L := L) hK S E σ →
    ¬ VertexCycleEq hK L S (pullback hK L S E σ.1) (Equiv.refl (α := Fin K)) →
    LongObstruction hK L S

/-- **The residual obligation of the factorization implies `thm:BBT` in the
`bbtCompleteSpec_of_obstruction` form.**  §1 supplies `theta`, §3 step 2 turns
"not a rotation" into "`theta` is bad", and `Ukkonen` excludes the
`LongObstruction` disjunct.  This direction is elementary and uses no endpoint
result. -/
theorem bbt_of_badThetaObstruction {L : ℕ} (hL : 2 ≤ L)
    (hB : BadThetaObstruction (α := α) L) :
    ∀ (K : ℕ) (hK : 0 < K) (S E : Fin K → α), Ukkonen hK L S →
      specCount (L := L) hK S = specCount (L := L) hK E → RotEquiv hK E S := by
  intro K hK S E hUkk hspec
  by_contra hn
  obtain ⟨σ, hm⟩ := exists_matching hK S E hspec
  exact absurd
    (hB K hK S E σ hm (badTheta_of_not_RotEquiv hK L S hm hn))
    (not_longObstruction_of_Ukkonen hUkk)

/-- **... and conversely, `thm:BBT` implies the residual obligation of the
factorization**, using §3's converse (`RotEquiv` ⟹ vertex-cycle-trivial
rematching).  Hence

  `BadThetaObstruction L ↔ bbtCompleteSpec_of_obstruction (hL := 2 ≤ L) hObs L`

and the "one genuinely new structural theorem" of the packet is *not* a
structural theorem at all: it is `thm:BBT` verbatim. -/
theorem badThetaObstruction_of_bbt {L : ℕ} (hL : 2 ≤ L)
    (hObs : EulerianCycleObstruction (α := α) L) : BadThetaObstruction (α := α) L := by
  intro K hK S E σ hm hbad
  by_contra hLO
  have hUkk : Ukkonen hK L S := (longObstruction_iff_not_Ukkonen (S := S)).mpr hLO
  have hspec : specCount (L := L) hK S = specCount (L := L) hK E :=
    (BBTChords.matching_imp hK L S E (pullback hK L S E hm.1) (by omega) hm).1
  exact hbad (vertexCycleEq_of_RotEquiv_pullback hK L S hm
    (bbtCompleteSpec_of_obstruction hK hL hObs K hK S E hUkk hspec) (by omega))

end AssemblyP1.Issue94EulerianTheta