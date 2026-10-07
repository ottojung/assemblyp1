import AssemblyP1.Issue94ObstructionEquiv

/-!
# Board 94, front `94real`: every Eulerian-cycle listing **is** a matching
# pull-back --- the converse bridge

This module closes the gap recorded in `docs/issue-94-obstruction-equiv.md` §3
as "a concrete next packet for the converse", namely:

> Whether *every* `EulerianCycle σ` is the pull-back of some `Matching` is a
> narrower question than the residue's claim and is **not settled here**.

**It is settled here, and the answer is yes.** The candidate is derived from the
traversal's own consistency, and §1 records exactly which hypothesis makes the
construction well defined.

## 0. What the construction is, and is *not*

The candidate word of an `EulerianCycle hG L S σ` is

```lean
traversalRead S σ  =  fun s => S (σ s)
```

the symbol the traversal presents at candidate start `s` is the truth's symbol
at start `σ s`. This is the *only* possible candidate: any `E` with
`window hG E s = window hG S (σ s)` has `E s = window hG S (σ s) 0 = S (σ s)`
by offset `0` (`eq_of_window_eq`). So the whole converse reduces to a statement
about `σ`.

**Guardrail (`docs/issue-94-obstruction-equiv.md` §3).** The prior front's
`readOff` was refuted, and this module does not resurrect it: for an arbitrary
permutation `σ` the window agreement is `decide`-false, and
`traversalRead_window_refuted` below is the *same* refutation (§1.1). What is
new is that the refuted instance is **not an `EulerianCycle`**
(`not_eulerianCycle_refuted_instance`, §1.2): `traverses` is exactly the
hypothesis that repairs the construction. §2 proves the repair from
`traverses` alone, with no appeal to `single`, no appeal to `Ukkonen`, and no
window-length assumption beyond `2 ≤ L`.

## 1. The boundary, `decide`-closed

* §1.1 `traversalRead_window_refuted`: with no hypothesis on `σ` the window
  agreement is false (all `2⁴` binary words, all `4!` permutations).
* §1.2 `not_eulerianCycle_refuted_instance`: at the refuting instance
  (`S = 0001`, `σ = (2 3)`) the `traverses` clause fails, so the instance is
  outside `thm:BBT` altogether.
* §1.3 `traversalRead_window_of_eulerianCycle_small`: at `G = 4`, `L = 3` the
  window agreement holds for **every** `EulerianCycle`, `decide`-checked over
  all `2⁴` words and all `4!` permutations. §2 replaces this finite evidence by
  a proof.

## 2. The construction lemma (kernel-checked)

`window_traversalRead_of_traverses`: at `2 ≤ L`, `traverses` alone implies the
complete `L`-window agreement. The proof is an induction on the offset `j`
inside the window and uses, at step `j`, precisely the `vtx` agreement at
offset `q - j - 1`; the offsets used are `0, 1, …, q - 1`, all of which lie in
`Fin (L - 1)` because `q ≤ L - 1`. That is the whole content: the traversal's de
Bruijn shift relation read at successively later offsets.

Consequences, all kernel-checked:

* `matching_traversalRead_of_traverses` --- `traversalRead S σ` is matched by
  `σ.symm`, i.e. **every `EulerianCycle` is the pull-back of a `Matching`**;
* `eulerianCycle_realized` --- the same, with the pull-back equation in the
  shape `BBTCondense.pullback_window` consumes, so the prior front's
  `exists_matching_pullback_refuted` is not contradicted: its `σ = (2 3)` is
  not an `EulerianCycle`;
* `eulerianCycle_specCount_eq` --- the candidate has the truth's complete
  `L`-spectrum;
* `vertexCycleEq_of_RotEquiv_traversalRead` --- a same-`L`-spectrum competitor
  which is a rotation of the truth forces `VertexCycleEq σ (refl)`.

## 3. The converse bridge (kernel-checked)

`obstruction_of_BBTUniqueAt`: at `2 ≤ L`,
`BBTUniqueAt L → EulerianCycleObstruction L`.

**Together with the library's `BBTEulerian.bbtUniqueAt_of_obstruction` this
gives `EulerianCycleObstruction L ↔ BBTUniqueAt L`** (§4), i.e. at `2 ≤ L` the
obstruction statement *is* `thm:BBT` as the project reads it, in both
directions. `BBT94.ObstructionFromBBT` is consequently no longer an open `Prop`
(it is instantiated in §4 by `obstruction_of_bbtUniqueAt'`).

This does **not** settle #89: `BBTUniqueAt` is the external theorem
(`paper/sections/05-population.tex`, `thm:BBT`) and is still the single
remaining mathematical input. What changes is that it is now needed in exactly
its source form, with no intervening Eulerian-touring claim of this project's
own. No `axiom`, `sorry` or `admit` is introduced, and no definition of
`BBTEulerian`, `P2`, `BBTChords` or `BBTCondense` is touched.

Source fidelity: `EulerianCycle`, `VertexCycleEq`, `Matching`, `pullback`,
`window`, `vtx`, `cyc`, `rotAdd`, `Ukkonen`, `LongObstruction`,
`BBTCompleteSpectrumUniqueness`, `BBTUniqueAt` and `RotEquiv` are used exactly
as `BBTEulerian.lean`, `P2.lean`, `BBTChords.lean` and `BBTCondense.lean`
state them.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace AssemblyP1.Issue94Realize

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.Issue94EulerianTheta
open AssemblyP1

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-! ## 0. Small circle-arithmetic helpers -/

/-- `nextPos` after a rotation is the rotation by the next amount. -/
private theorem nextPos_rotAdd (s : Fin G) (j : ℕ) :
    nextPos hG (rotAdd hG j s) = rotAdd hG (j + 1) s := by
  unfold nextPos rotAdd
  apply Fin.ext
  show ((s.val + j) % G + 1) % G = (s.val + (j + 1)) % G
  rw [Nat.mod_add_mod]
  have h : s.val + j + 1 = s.val + (j + 1) := by omega
  rw [h]

/-- Adding the rotation amount commutes, on the circle. -/
private theorem cyc_add (a b : ℕ) : cyc hG S (a + b) = cyc hG S (b + a) := by
  unfold cyc
  apply congrArg S
  exact Fin.val_injective (by rw [Nat.add_comm])

/-- Reading at a position is reading its own symbol. -/
private theorem cyc_eq' {W : Fin G → α} (x : Fin G) : cyc hG W x.val = W x := by
  unfold cyc
  apply congrArg W
  exact Fin.val_injective (Nat.mod_eq_of_lt x.isLt)

/-- The two rotation amounts commute on the circle. -/
private theorem rotAdd_comm (i : Fin G) (m d : ℕ) :
    rotAdd hG m (rotAdd hG d i) = rotAdd hG d (rotAdd hG m i) := by
  unfold rotAdd
  apply Fin.val_injective
  show ((i.val + d) % G + m) % G = ((i.val + m) % G + d) % G
  rw [Nat.mod_add_mod, Nat.mod_add_mod]
  congr 1
  omega

/-- Stepping one position forward is stepping the index forward by one, past
the `((y + 1) % G)` in which `nextPos` writes its result. -/
private theorem cyc_next (y : Fin G) (m : ℕ) :
    cyc hG S (m + (y.val + 1) % G) = cyc hG S (m + 1 + y.val) := by
  unfold cyc
  congr 1
  apply Fin.ext
  show ((m + (y.val + 1) % G) % G) = ((m + 1 + y.val) % G)
  rw [Nat.add_comm m ((y.val + 1) % G)]
  rw [Nat.mod_add_mod (y.val + 1) G m]
  congr 1
  omega

/-! ## 0.1 The candidate, read off the traversal -/

/-- **The candidate word of an Eulerian-cycle listing.**  `σ s` is the truth's
start presented at candidate start `s` along the traversal, so the symbol the
traversal spells at `s` is `S (σ s)`.

This is the *only* possible candidate for the matching whose pull-back is `σ`:
a word `E` with `window hG E s = window hG S (σ s)` has `E s = window hG S (σ s) 0
= S (σ s)` (`eq_of_window_eq`), so no freedom is being smuggled in. Whether the
*whole* window agrees is exactly the content of §2. -/
def traversalRead {G : ℕ} (S : Fin G → α) (σ : Fin G ≃ Fin G) : Fin G → α :=
  fun s => S (σ s)

/-- The candidate is forced at offset `0`, for any `E` and any `σ`: a matching
whose pull-back is `σ` *must* be `traversalRead S σ`.  Hence the converse of §3
carries no choice, and its only content is the window agreement of §2. -/
theorem eq_of_window_eq {G : ℕ} (hG : 0 < G) {L : ℕ} {S E : Fin G → α}
    {σ : Fin G → Fin G} (hL : 0 < L) (s : Fin G)
    (h : window (L := L) hG E s = window (L := L) hG S (σ s)) :
    E s = S (σ s) := by
  have h0 := congrFun h ⟨0, hL⟩
  simp only [window, Nat.add_zero] at h0
  rw [cyc_eq' hG (W := E) s, cyc_eq' hG (W := S) (σ s)] at h0
  exact h0

/-! ## 1. The boundary: without `traverses` the construction is false -/

/-- **REFUTED (`decide`): the construction with no hypothesis on `σ`.**  This
is the refutation recorded in `docs/issue-94-obstruction-equiv.md` §3, restated
for `traversalRead`: the complete `L`-window of `traversalRead S σ` at `s` does
not in general equal the complete `L`-window of `S` at `σ s`. Exhaustive at
`G = 4`, `L = 3`, all `2⁴` binary words, all `4!` permutations, all starts and
offsets. -/
theorem traversalRead_window_refuted :
    ¬ (∀ (S : Fin 4 → Fin 2) (σ : Fin 4 ≃ Fin 4) (s : Fin 4) (d : Fin 3),
      window (L := 3) hG4 (traversalRead S σ) s d
        = window (L := 3) hG4 S (σ s) d) := by decide

/-- **The named instance**, `S = 0001` and `σ = (2 3)`, exactly as in
`BBT94.window_readOff_refuted_S0001`. -/
theorem traversalRead_window_refuted_instance :
    window (L := 3) hG4
        (traversalRead AssemblyP1.BBT94.S0001 (Equiv.swap 2 3 : Fin 4 ≃ Fin 4)) 0
        ⟨2, by decide⟩
      ≠ window (L := 3) hG4 AssemblyP1.BBT94.S0001
          ((Equiv.swap 2 3 : Fin 4 ≃ Fin 4) 0) ⟨2, by decide⟩ := by decide

/-- **The hypothesis is exactly what is missing there.**  The instance of §1.1
is *not* an `EulerianCycle`: its `traverses` clause fails, so it is outside
`thm:BBT` altogether.  The prior front's refutation of "every permutation is a
matching pull-back" stands, and this module does not contradict it --- it
replaces "every permutation" by "every Eulerian cycle", and that restricted
claim is §2. -/
theorem not_eulerianCycle_refuted_instance :
    ¬ EulerianCycle hG4 3 AssemblyP1.BBT94.S0001 (Equiv.swap 2 3 : Fin 4 ≃ Fin 4) :=
  by decide

set_option maxRecDepth 40000 in
/-- **Finite evidence for the positive statement**, `decide`-checked at
`G = 4`, `L = 3`: over all `2⁴` binary words and all `4!` permutations, the
window agreement holds for **every** `EulerianCycle`.  §2 replaces this by a
proof; this instance pins down that the theorem of §2 is not vacuous at
`G = 4`, `L = 3`, and that the boundary of §1.1 is sharp there. -/
theorem traversalRead_window_of_eulerianCycle_small :
    ∀ (S : Fin 4 → Fin 2) (σ : Fin 4 ≃ Fin 4), EulerianCycle hG4 3 S σ →
      ∀ (s : Fin 4) (d : Fin 3),
        window (L := 3) hG4 (traversalRead S σ) s d
          = window (L := 3) hG4 S (σ s) d := by decide

/-! ## 2. The construction lemma -/

/-- **`traverses` makes the traversal read-off a genuine candidate.**  At
`2 ≤ L`, if the listing `σ 0, σ 1, …` is joined by edges of the `(L-1)`-mer
multigraph of the truth --- the first clause of `EulerianCycle` --- then the
complete `L`-window of `traversalRead S σ` at `s` is the complete `L`-window of
`S` at `σ s`, for every start `s` and every offset `d < L`.

Proof.  Fix `s` and write `A_j (x) = cyc hG S ((σ (rotAdd hG j s)).val + x)`: the
truth's symbols read from the `j`-th start of the listing, at offset `x`.  The
hypothesis `traverses`, taken at `i := rotAdd hG j s`, says exactly
`A_{j+1} (x) = A_j (x + 1)` for every `x < L - 1`, because the two nodes it
equates are `σ (nextPos i)` and `nextPos (σ i)`.  Hence

* `A_q (0) = A_{q-1} (1) = A_{q-2} (2) = … = A_0 (q)`,

and the offsets used are `0, 1, …, q - 1`, all inside `Fin (L - 1)` because
`q ≤ L - 1`.  With `q = d.val` and `j = q` this reads
`S (σ (rotAdd hG d.val s)) = cyc hG S ((σ s).val + d.val)`, i.e. offset `d` of
the two windows.  The `single` clause, `Ukkonen`, `LongObstruction` and `BBT` are
not used anywhere. -/
theorem window_traversalRead_of_traverses {σ : Fin G ≃ Fin G} (hL : 2 ≤ L)
    (htr : ∀ i : Fin G, vtx hG L S (σ (nextPos hG i)) = vtx hG L S (nextPos hG (σ i)))
    (s : Fin G) (d : Fin L) :
    window (L := L) hG (traversalRead S σ) s d = window (L := L) hG S (σ s) d := by
  have hd : d.val ≤ L - 1 := by omega
  -- the chain `A_q (0) = A_{q-1} (1) = … = A_0 (q)`, as a `j`-indexed family
  have hkey : ∀ (q : ℕ) (hq : q ≤ L - 1) (s : Fin G) (j : ℕ), j ≤ q →
      cyc hG S ((σ (rotAdd hG j s)).val + (q - j))
        = cyc hG S ((σ s).val + q) := by
    intro q hq s j hj
    revert s hj
    induction j with
    | zero =>
        intro s _
        show cyc hG S ((σ (rotAdd hG 0 s)).val + (q - 0)) = cyc hG S ((σ s).val + q)
        rw [rotAdd_zero, Nat.sub_zero]
    | succ m ih =>
        intro s hj
        have hx : 0 ≤ q - (m + 1) ∧ q - (m + 1) < L - 1 := by omega
        have htr' := congrFun (htr (rotAdd hG m s)) ⟨q - (m + 1), by omega⟩
        simp only [vtx, nodeWindow] at htr'
        calc cyc hG S ((σ (rotAdd hG (m + 1) s)).val + (q - (m + 1)))
            = cyc hG S ((σ (nextPos hG (rotAdd hG m s))).val + (q - (m + 1))) :=
              (congrArg (fun v => cyc hG S ((σ v).val + (q - (m + 1))))
                (nextPos_rotAdd hG s m)).symm
          _ = cyc hG S ((nextPos hG (σ (rotAdd hG m s))).val + (q - (m + 1))) := htr'
          _ = cyc hG S ((σ (rotAdd hG m s)).val + 1 + (q - (m + 1))) := by
              have hN : (nextPos hG (σ (rotAdd hG m s))).val
                  = ((σ (rotAdd hG m s)).val + 1) % G := rfl
              rw [hN]
              calc cyc hG S ((((σ (rotAdd hG m s)).val + 1) % G) + (q - (m + 1)))
                  = cyc hG S ((q - (m + 1)) + (((σ (rotAdd hG m s)).val + 1) % G)) :=
                      cyc_add hG S (((σ (rotAdd hG m s)).val + 1) % G) (q - (m + 1))
                _ = cyc hG S ((q - (m + 1)) + 1 + (σ (rotAdd hG m s)).val) :=
                      cyc_next hG S (σ (rotAdd hG m s)) (q - (m + 1))
                _ = cyc hG S ((σ (rotAdd hG m s)).val + 1 + (q - (m + 1))) := by
                    congr 1
                    omega
          _ = cyc hG S ((σ (rotAdd hG m s)).val + (q - m)) := by
              congr 1
              omega
          _ = cyc hG S ((σ s).val + q) := ih s (by omega)
  -- instantiate at `q = j = d.val`
  have h1 := hkey d.val hd s d.val (le_refl _)
  simp only [window]
  change S (σ (rotAdd hG d.val s)) = cyc hG S ((σ s).val + d.val)
  calc S (σ (rotAdd hG d.val s))
      = cyc hG S ((σ (rotAdd hG d.val s)).val + 0) := by
        rw [← cyc_eq' hG (W := S) (σ (rotAdd hG d.val s)), Nat.add_zero]
    _ = cyc hG S ((σ s).val + d.val) := by simpa using h1

/-- **The candidate is matched by `σ.symm`, i.e. `σ` is a `Matching`
pull-back.**  In the orientation of `BBTChords.Matching`: for every truth start
`r`, `window hG S r = window hG (traversalRead S σ) (σ.symm r)`. -/
theorem matching_traversalRead_of_traverses {σ : Fin G ≃ Fin G} (hL : 2 ≤ L)
    (htr : ∀ i : Fin G, vtx hG L S (σ (nextPos hG i)) = vtx hG L S (nextPos hG (σ i))) :
    Matching (L := L) hG S (traversalRead S σ) (σ.symm) := by
  refine ⟨Equiv.bijective σ.symm, fun r => ?_⟩
  funext d
  simpa only [window, Equiv.apply_symm_apply] using
    (window_traversalRead_of_traverses hG L S hL htr (σ.symm r) d).symm

/-- **Every `EulerianCycle` is the pull-back of a `Matching`.**  This is the
converse direction of `BBTEulerian.pullback_isEulerianCycle`: that lemma says a
matching pull-back is an Eulerian cycle, and this says the inclusion is the
identity.

This is the statement `docs/issue-94-obstruction-equiv.md` §3 left open.  It
does not contradict `BBT94.exists_matching_pullback_refuted`, whose `σ = (2 3)`
is not an `EulerianCycle` (`not_eulerianCycle_refuted_instance`). -/
theorem eulerianCycle_realized {σ : Fin G ≃ Fin G} (hL : 2 ≤ L)
    (hEul : EulerianCycle hG L S σ) :
    ∃ (E : Fin G → α) (μ : Fin G → Fin G) (hμ : Function.Bijective μ),
      Matching (L := L) hG S E μ ∧
        ∀ (s : Fin G), pullback hG L S E hμ s = σ s := by
  refine ⟨traversalRead S σ, σ.symm, Equiv.bijective σ.symm,
    matching_traversalRead_of_traverses hG L S hL hEul.1, fun s => ?_⟩
  simp only [pullback]
  show (Equiv.ofBijective σ.symm (Equiv.bijective σ.symm)).symm s = σ s
  have hid : (Equiv.ofBijective σ.symm (Equiv.bijective σ.symm)) (σ s) = s :=
    Equiv.symm_apply_apply σ s
  have hstep : (Equiv.ofBijective σ.symm (Equiv.bijective σ.symm)).symm s
      = (Equiv.ofBijective σ.symm (Equiv.bijective σ.symm)).symm
          ((Equiv.ofBijective σ.symm (Equiv.bijective σ.symm)) (σ s)) := by
    rw [hid]
  rw [Equiv.symm_apply_apply] at hstep
  exact hstep

/-- **The candidate has the truth's complete `L`-spectrum**, by the window
clause of `BBTChords.Matching`. -/
theorem eulerianCycle_specCount_eq {σ : Fin G ≃ Fin G} (hL : 2 ≤ L)
    (hEul : EulerianCycle hG L S σ) :
    specCount (L := L) hG S = specCount (L := L) hG (traversalRead S σ) := by
  funext w
  exact specCount_eq_of_Matching hG L S
    (matching_traversalRead_of_traverses hG L S hL hEul.1) w

/-- **A rotation of the traversal read-off forces the truth's vertex cycle.**
So a same-`L`-spectrum competitor which is a rotation of the truth is, on this
candidate, exactly the trivial vertex cycle. -/
theorem vertexCycleEq_of_RotEquiv_traversalRead (hL : 2 ≤ L) {σ : Fin G ≃ Fin G}
    (hwin : ∀ (s : Fin G) (d : Fin L),
      window (L := L) hG (traversalRead S σ) s d = window (L := L) hG S (σ s) d)
    (hrot : RotEquiv hG (traversalRead S σ) S) :
    VertexCycleEq hG L S σ (Equiv.refl (α := Fin G)) := by
  obtain ⟨k0, hk0⟩ := hrot
  -- only `k % G` is observable, so normalise it once and for all
  set k := k0 % G with hkdef
  have hklt : k < G := by rw [hkdef]; exact Nat.mod_lt _ hG
  have hk : ∀ i : Fin G,
      traversalRead S σ ⟨(i.val + k) % G, Nat.mod_lt _ hG⟩ = S i := by
    intro i
    have h := hk0 i
    have h'' : (⟨(i.val + k0) % G, Nat.mod_lt _ hG⟩ : Fin G)
        = ⟨(i.val + k) % G, Nat.mod_lt _ hG⟩ := by
      apply Fin.ext
      rw [hkdef]
      exact mod_add_mod_right G i.val k0
    rw [h''] at h
    exact h
  -- `traversalRead S σ` is the truth read at the start shifted by `G - k`
  have hE : ∀ x : Fin G, traversalRead S σ x = S (rotAdd hG (G - k) x) := by
    intro x
    have hx : traversalRead S σ
          (⟨((x.val + (G - k)) % G + k) % G, Nat.mod_lt _ hG⟩ : Fin G)
        = S (⟨(x.val + (G - k)) % G, Nat.mod_lt _ hG⟩ : Fin G) :=
      hk ⟨(x.val + (G - k)) % G, Nat.mod_lt _ hG⟩
    have hid : ((x.val + (G - k)) % G + k) % G = x.val :=
      rotAdd_neg_cancel hG k x.val x.isLt hklt
    have hX : (⟨((x.val + (G - k)) % G + k) % G, Nat.mod_lt _ hG⟩ : Fin G) = x :=
      Fin.val_injective hid
    rw [hX] at hx
    exact hx
  -- hence the shifted read-off has the shifted truth's windows
  have hwin2 : ∀ (i : Fin G) (d : Fin L),
      window (L := L) hG (traversalRead S σ) i d
        = window (L := L) hG S (rotAdd hG (G - k) i) d := by
    intro i d
    simp only [window]
    unfold cyc
    have hE' := hE ⟨(i.val + d.val) % G, Nat.mod_lt _ hG⟩
    unfold rotAdd at hE'
    rw [hE']
    apply congrArg S
    apply Fin.ext
    show (((i.val + d.val) % G + (G - k)) % G) = (((i.val + (G - k)) % G + d.val) % G)
    rw [Nat.mod_add_mod, Nat.mod_add_mod]
    congr 1
    omega
  refine ⟨⟨(G - k) % G, Nat.mod_lt _ hG⟩, fun i => ?_⟩
  funext d
  have hd : d.val < L := by omega
  have h1 := hwin i ⟨d.val, hd⟩
  have h2 := hwin2 i ⟨d.val, hd⟩
  simp only [window] at h1 h2
  have hmod : (rotAdd hG ((G - k) % G) (Equiv.refl (α := Fin G) i)).val
      = (rotAdd hG (G - k) i).val := by
    show ((i.val + (G - k) % G) % G) = ((i.val + (G - k)) % G)
    exact (mod_add_mod_right G i.val (G - k)).symm
  simp only [vtx, nodeWindow]
  rw [← h1, h2, hmod]

/-! ## 3. The converse bridge -/

/-- **THE CONVERSE BRIDGE.**  At `2 ≤ L`, an inhabitant of `thm:BBT` in the
project's reading (`BBTUniqueAt L`) yields `EulerianCycleObstruction L`.

Proof.  Let `σ` be an `EulerianCycle` of an `Ukkonen` truth `S`.  By §2 the
traversal read-off `traversalRead S σ` is matched by `σ.symm`, so it has the
truth's complete `L`-spectrum (and being a word of length `K` it is a candidate
of the same class).  `BBTCompleteSpectrumUniqueness` demands `Ukkonen` of the
*truth only*, so it applies, and returns `RotEquiv (traversalRead S σ) S`.  By
the preceding theorem the candidate being a rotation forces
`VertexCycleEq σ (refl)`, which is the first disjunct.  The second disjunct is
what makes the factorization usable at all; no `Ukkonen` is needed for it, and
the theorem concludes the disjunction, so the `Ukkonen` hypothesis discharges
it. -/
theorem obstruction_of_BBTUniqueAt {L : ℕ} (hL : 2 ≤ L)
    (hBBT : BBTUniqueAt (α := α) L) : EulerianCycleObstruction (α := α) L := by
  intro K hK S hUkk σ hEul
  have hm : Matching (L := L) hK S (traversalRead S σ) (σ.symm) :=
    matching_traversalRead_of_traverses hK L S hL hEul.1
  have hwin : ∀ (s : Fin K) (d : Fin L),
      window (L := L) hK (traversalRead S σ) s d
        = window (L := L) hK S (σ s) d :=
    window_traversalRead_of_traverses hK L S hL hEul.1
  have hspec : specCount (L := L) hK S = specCount (L := L) hK (traversalRead S σ) := by
    funext w
    exact specCount_eq_of_Matching hK L S hm w
  have hrot : RotEquiv hK (traversalRead S σ) S :=
    hBBT K hK S (traversalRead S σ) hUkk hspec
  exact Or.inl (vertexCycleEq_of_RotEquiv_traversalRead hK L S hL hwin hrot)

/-! ## 4. The obstruction statement *is* `thm:BBT`, in both directions -/

/-- **The bridge closes the residual of #89.**  `BBT94.ObstructionFromBBT`, the
`Prop` that `docs/issue-94-obstruction-equiv.md` §2 left unproved, is inhabited at
`2 ≤ L` exactly when §3's statement is; so the residual is now settled *modulo*
`thm:BBT`, and not modulo any Eulerian-touring lemma of this project's own. -/
theorem obstructionOfBBT_iff_of_le {L : ℕ} (hL : 2 ≤ L) :
    AssemblyP1.BBT94.ObstructionFromBBT (α := α) L
      ↔ (BBTUniqueAt (α := α) L → EulerianCycleObstruction (α := α) L) :=
  ⟨fun h => h, fun _ => obstruction_of_BBTUniqueAt hL⟩

/-- **`EulerianCycleObstruction` and `BBTUniqueAt` are the same statement at
`2 ≤ L`.**  The library direction is `BBTEulerian.bbtUniqueAt_of_obstruction`;
§3 supplies the other. -/
theorem obstruction_iff_bbtUniqueAt {L : ℕ} (hL : 2 ≤ L) :
    EulerianCycleObstruction (α := α) L ↔ BBTUniqueAt (α := α) L :=
  ⟨bbtUniqueAt_of_obstruction hL, obstruction_of_BBTUniqueAt hL⟩

/-! ## 5. Executable audit -/

#print axioms AssemblyP1.Issue94Realize.traversalRead_window_refuted
#print axioms AssemblyP1.Issue94Realize.traversalRead_window_refuted_instance
#print axioms AssemblyP1.Issue94Realize.not_eulerianCycle_refuted_instance
#print axioms AssemblyP1.Issue94Realize.traversalRead_window_of_eulerianCycle_small
#print axioms AssemblyP1.Issue94Realize.eq_of_window_eq
#print axioms AssemblyP1.Issue94Realize.window_traversalRead_of_traverses
#print axioms AssemblyP1.Issue94Realize.matching_traversalRead_of_traverses
#print axioms AssemblyP1.Issue94Realize.eulerianCycle_realized
#print axioms AssemblyP1.Issue94Realize.eulerianCycle_specCount_eq
#print axioms AssemblyP1.Issue94Realize.vertexCycleEq_of_RotEquiv_traversalRead
#print axioms AssemblyP1.Issue94Realize.obstruction_of_BBTUniqueAt
#print axioms AssemblyP1.Issue94Realize.obstruction_iff_bbtUniqueAt
#print axioms PopulationUniqueness.population_unique_ML_up_to_rotation

end AssemblyP1.Issue94Realize