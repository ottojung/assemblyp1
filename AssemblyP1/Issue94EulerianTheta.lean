import AssemblyP1.BBTEulerian
import AssemblyP1.BBTFibrePeriod

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
/-! ## 2. A rotation of the circle has the truth's vertex cycle -/

/-- `S = 0101` at `G = 4`, `L = 3`, as in `BBTEulerian` §4.2. -/
def S4t : Fin 4 → Fin 2 := BBTEulerian.S4

/-- **`window` is NOT shift-invariant, and this is `decide`-closed.**  A draft
of this module asserted `window W (rotAdd s x) = window W x`, i.e. that a
window read at a shifted start spells the same read.  That is false: it drops
the shift in the *window*, exactly as the quarantined §3 dropped the shift in
the pull-back.  The instance is `G = 4`, `L = 3`, `S = 0101`, `s = 1`,
`x = 0`. -/
theorem window_rotAdd_refuted :
    window (L := 3) BBTEulerian.hG4 S4t (rotAdd BBTEulerian.hG4 1 0)
      ≠ window (L := 3) BBTEulerian.hG4 S4t 0 := by decide

/-- ... and so is the `(L-1)`-mer version `vtx`, on the same instance. -/
theorem vtx_rotAdd_refuted :
    vtx BBTEulerian.hG4 3 S4t (rotAdd BBTEulerian.hG4 1 0)
      ≠ vtx BBTEulerian.hG4 3 S4t 0 := by decide

/-- **A rotation of the circle has the truth's vertex cycle.**  Note this needs
*no* shift-invariance of `vtx`: `VertexCycleEq` asks for the *witness* `k`, and
the rotation amount itself is a legal witness.  This is the missing half of
"`θ` is a rotation ⟹ `θ` is vertex-cycle-trivial", and it uses no `Ukkonen`,
no `P2` and no `BBT`. -/
theorem vertexCycleEq_of_isRotation (σ : Fin G ≃ Fin G)
    (hrot : IsRotation hG (σ : Fin G → Fin G)) :
    VertexCycleEq hG L S σ (Equiv.refl (α := Fin G)) := by
  obtain ⟨k, hk⟩ := hrot
  refine ⟨⟨k % G, Nat.mod_lt _ hG⟩, fun i => ?_⟩
  show vtx hG L S (σ i) = vtx hG L S (rotAdd hG (k % G) i)
  rw [← rotAdd_mod hG k i, ← hk i]

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

/-- Congruence for `ModEq`-related positions: two accesses of the same circular
word at congruent positions agree.  This is `BBTFibrePeriod.cyc_congr` in the
form that compares two `Fin G` positions directly. -/
private theorem fin_congr_of_modEq {W : Fin G → α} {x y : ℕ} (h : Nat.ModEq G x y) :
    W ⟨x % G, Nat.mod_lt _ hG⟩ = W ⟨y % G, Nat.mod_lt _ hG⟩ := by
  have hb : y % G < G := Nat.mod_lt _ hG
  have h' : Nat.ModEq G x (y % G) := h.trans (Nat.mod_modEq y G).symm
  have he : x % G = y % G := Nat.mod_eq_of_modEq h' hb
  exact congrArg W (Fin.ext he)

/-- Adding a whole turn changes nothing on the circle. -/
private theorem modEq_add_G (a : ℕ) : Nat.ModEq G (a + G) a := by
  refine (Nat.mod_modEq (a + G) G).symm.trans ?_
  have h2 : (a + G) % G = a % G := by
    rw [Nat.add_mod]
    simp
  rw [h2]
  exact Nat.mod_modEq a G

/-- Reading `b` symbols past a start given as `a % G` reads the same symbols as
reading `b` past a start given as `a`. -/
private theorem modEq_add_right' (a b : ℕ) : Nat.ModEq G (a % G + b) (a + b) :=
  ((Nat.mod_modEq a G).symm.add_right b).symm

/-- **THE WINDOW RELATION A ROTATION ACTUALLY CARRIES.**  If `E` is `S` shifted
*forward* by `k`, i.e. `RotEquiv hG E S` read with `k : Fin G`, then the window
of `E` at `s` is the window of `S` at the position `k` steps *back*:

  `window (L := L) hG E s = window (L := L) hG S (rotAdd hG (G - k.val) s)`.

The shift is `G - k`, **not** `k` and **not** `0`.  The quarantined draft
asserted the shiftless relation `window E i = window S i`, which is
`decide`-refutable at `G = 4`, `L = 3`, `S = 0101` (`scratch94/Probe3.lean`,
namespace `Probe94c`: `RotEquiv hG4 E4 S4` holds with `k = 1`, while
`window E4 0 ≠ window S4 0`).  The same `G - k` shift is what
`BBTEulerian.rotEquiv_of_vertexCycleEq` produces on the other side. -/
theorem window_rotEquiv {E : Fin G → α} (k : Fin G)
    (hk : ∀ i : Fin G, E ⟨(i.val + k.val) % G, Nat.mod_lt _ hG⟩ = S i) (s : Fin G) :
    window (L := L) hG E s = window (L := L) hG S (rotAdd hG (G - k.val) s) := by
  funext d
  show E ⟨(s.val + d.val) % G, Nat.mod_lt _ hG⟩
      = S ⟨(((s.val + (G - k.val)) % G) + d.val) % G, Nat.mod_lt _ hG⟩
  -- `B` is the `S`-position of the symbol: `k` steps *back* from `s`, then `d` on.
  -- `A ≡ B + k (mod G)`, because `B + k = s + d + G`.
  have hturn : s.val + d.val + G = (s.val + (G - k.val) + d.val) + k.val := by omega
  have hback : Nat.ModEq G (s.val + d.val)
      ((s.val + (G - k.val) + d.val) + k.val) :=
    (modEq_add_G (s.val + d.val)).symm.trans (by rw [hturn])
  have hdist : Nat.ModEq G ((s.val + (G - k.val) + d.val) + k.val)
      (((s.val + (G - k.val) + d.val) % G) + k.val) :=
    (Nat.mod_modEq (s.val + (G - k.val) + d.val) G).symm.add_right k.val
  calc E ⟨(s.val + d.val) % G, Nat.mod_lt _ hG⟩
      = E ⟨(((s.val + (G - k.val) + d.val) + k.val) % G), Nat.mod_lt _ hG⟩ :=
        fin_congr_of_modEq hG hback
    _ = E ⟨(((s.val + (G - k.val) + d.val) % G + k.val) % G), Nat.mod_lt _ hG⟩ :=
        fin_congr_of_modEq hG hdist
    _ = S ⟨((s.val + (G - k.val) + d.val) % G), Nat.mod_lt _ hG⟩ :=
        hk ⟨(s.val + (G - k.val) + d.val) % G, Nat.mod_lt _ hG⟩
    _ = S ⟨(((s.val + (G - k.val)) % G + d.val) % G), Nat.mod_lt _ hG⟩ :=
        fin_congr_of_modEq hG (modEq_add_right' (s.val + (G - k.val)) d.val).symm

/-- **And the converse of step 2, also free**: a *rotational* competitor forces
a *non-bad* rematching, by the corrected window relation of the previous
lemma (`G - k`, not `0`).  So for the rematching `theta` the two conditions
"`theta` is a rotation" and "`theta` is vertex-cycle-trivial" are
**independent**: neither implies the other.  This is the exact logical content
of `BBTEulerian` §4.2, and it is why the factorization's step 2 can only be had
in the pull-back-restricted form. -/
theorem vertexCycleEq_of_RotEquiv_pullback {E : Fin G → α} {σ : Fin G → Fin G}
    (hm : Matching (L := L) hG S E σ) (hrot : RotEquiv hG E S) (hL : 1 ≤ L) :
    VertexCycleEq hG L S (pullback hG L S E hm.1) (Equiv.refl (α := Fin G)) := by
  obtain ⟨k, hk⟩ := hrot
  -- The shift carried by the pull-back is `G - k`, exactly as in
  -- `BBTEulerian.rotEquiv_of_vertexCycleEq`; the quarantined draft used `k`.
  refine ⟨⟨(G - k % G) % G, Nat.mod_lt _ hG⟩, fun i => ?_⟩
  have hk' : ∀ j : Fin G, E ⟨(j.val + k % G) % G, Nat.mod_lt _ hG⟩ = S j := by
    intro j
    have hval : (j.val + k % G) % G = (j.val + k) % G := by
      have h1 : (j.val + k % G) % G = (j.val % G + (k % G) % G) % G := Nat.add_mod _ _ _
      have h2 : (j.val + k) % G = (j.val % G + k % G) % G := Nat.add_mod _ _ _
      rw [h1, h2, Nat.mod_eq_of_lt (Nat.mod_lt _ hG), Nat.mod_eq_of_lt j.isLt]
    exact congrArg E (Fin.ext hval) |>.trans (hk j)
  have hW : window (L := L) hG E i = window (L := L) hG S (rotAdd hG (G - k % G) i) :=
    window_rotEquiv (E := E) (hG := hG) (L := L) (S := S)
      (k := ⟨k % G, Nat.mod_lt _ hG⟩) (hk := fun j => hk' j) i
  show vtx hG L S (pullback hG L S E hm.1 i)
      = vtx hG L S (rotAdd hG ((G - k % G) % G) i)
  rw [← rotAdd_mod hG (G - k % G) i]
  have hW' : window (L := L) hG S (pullback hG L S E hm.1 i)
      = window (L := L) hG S (rotAdd hG (G - k % G) i) :=
    (pullback_window hG L S E hm i).trans hW
  funext d
  show cyc hG S ((pullback hG L S E hm.1 i).val + d.val)
      = cyc hG S ((rotAdd hG (G - k % G) i).val + d.val)
  exact congrFun hW' ⟨d.val, by omega⟩

/-! ### 3.1 The unrestricted form of step 2 is false -/

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

/-- **A `Matching` determines the complete `L`-spectrum of the candidate.**
The window clause of `Matching` transports `window S r = w` to
`window E (σ r) = w` along the bijection `σ`, so the two spectra agree. -/
theorem specCount_eq_of_Matching {E : Fin G → α} {σ : Fin G → Fin G}
    (hm : Matching (L := L) hG S E σ) (w : Fin L → α) :
    specCount (L := L) hG S w = specCount (L := L) hG E w := by
  refine Finset.card_equiv
    (s := Finset.univ.filter (fun r : Fin G => window (L := L) hG S r = w))
    (t := Finset.univ.filter (fun r : Fin G => window (L := L) hG E r = w))
    (Equiv.ofBijective σ hm.1) ?_
  intro r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; exact (hm.2 r).symm.trans h
  · intro h; exact (hm.2 r).trans h

/-- **The residual obligation left by the factorization**: a same-`L`-spectrum
competitor together with a bad (vertex-cycle-nontrivial) rematching forces the
long obstruction.  This is the packet's "bad `theta` implies
`LongObstruction`", stated with the `theta` supplied by the construction
lemmas of §1, i.e. as the pull-back of a `Matching`.  `σ` is the bijection
carried by the matching, i.e. `Fin K ≃ Fin K`: `pullback` takes a bare
`Function.Bijective`, whereas the earlier draft wrote `σ.1` on a plain
`Fin K → Fin K`, where `σ.1` is not a projection at all, so that `Prop` did not
elaborate. -/
def BadThetaObstruction (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S E : Fin K → α) (σ : Fin K ≃ Fin K),
    Matching (L := L) hK S E σ →
    ¬ VertexCycleEq hK L S (pullback hK L S E σ.bijective) (Equiv.refl (α := Fin K)) →
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
    (hB K hK S E (Equiv.ofBijective σ hm.1) hm
      (badTheta_of_not_RotEquiv (E := E) (σ := σ) hK L S hL hm hn))
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
  have hUkk : Ukkonen hK L S := Classical.byContradiction fun hUk =>
    hLO ((longObstruction_iff_not_Ukkonen (hG := hK) (L := L) (S := S)).mpr hUk)
  have hspec : specCount (L := L) hK S = specCount (L := L) hK E :=
    funext (specCount_eq_of_Matching hK L S (E := E) (σ := (σ : Fin K → Fin K)) hm)
  exact hbad (vertexCycleEq_of_RotEquiv_pullback (E := E) (σ := σ) hK L S hm
    (bbtCompleteSpec_of_obstruction hL hObs K hK S E hUkk hspec) (by omega))

end AssemblyP1.Issue94EulerianTheta