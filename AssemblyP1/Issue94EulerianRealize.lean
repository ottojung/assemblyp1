import AssemblyP1.Issue94EulerianTheta

/-!
# Realizing an Eulerian listing as a circular word

For an arbitrary permutation sigma, the naive word E i = S (sigma i) does not
satisfy window E i = window S (sigma i). For an EulerianCycle, however, the
overlap clause supplies exactly the missing compatibility.
-/

namespace AssemblyP1.Issue94EulerianRealize

open AssemblyP1
open AssemblyP1.OrientedRigidity
open AssemblyP1.BBTChords
open AssemblyP1.BBTCondense
open AssemblyP1.BBTEulerian

variable {α : Type} [DecidableEq α] {G L : ℕ}

def spelledWord (S : Fin G → α) (σ : Fin G ≃ Fin G) : Fin G → α :=
  fun i => S (σ i)

theorem window_shift_of_traverses (hG : 0 < G) (S : Fin G → α)
    (σ : Fin G ≃ Fin G)
    (htrav : ∀ i : Fin G,
      vtx hG L S (σ (nextPos hG i)) = vtx hG L S (nextPos hG (σ i))) :
    ∀ (n : ℕ) (i : Fin G) (d : Fin L) (hnd : n + d.val < L),
      window (L := L) hG S (σ (rotAdd hG n i)) d =
        window (L := L) hG S (σ i) ⟨n + d.val, hnd⟩ := by
  intro n
  induction n with
  | zero =>
      intro i d hnd
      have hrot : rotAdd hG 0 i = i := by
        apply Fin.ext
        simp [rotAdd, Nat.mod_eq_of_lt i.isLt]
      rw [hrot]
      congr 1
      apply Fin.ext
      simp
  | succ n ih =>
      intro i d hnd
      have hdnode : d.val < L - 1 := by omega
      let dn : Fin (L - 1) := ⟨d.val, hdnode⟩
      have ht := congrFun (htrav (rotAdd hG n i)) dn
      have hdom :
          nextPos hG (rotAdd hG n i) = rotAdd hG (n + 1) i := by
        change rotAdd hG 1 (rotAdd hG n i) = _
        exact rotAdd_succ_add hG n i
      have hslide := window_next hG (L := L) S (σ (rotAdd hG n i))
        (j := d.val) (by omega)
      have hstep :
          window (L := L) hG S (σ (rotAdd hG (n + 1) i)) d =
            window (L := L) hG S (σ (rotAdd hG n i))
              ⟨d.val + 1, by omega⟩ := by
        rw [← hdom]
        change vtx hG L S (σ (nextPos hG (rotAdd hG n i))) dn =
          window (L := L) hG S (σ (rotAdd hG n i)) ⟨d.val + 1, by omega⟩
        rw [ht]
        exact hslide.symm
      rw [hstep]
      have hi := ih i ⟨d.val + 1, by omega⟩ (by omega)
      convert hi using 1 <;> apply Fin.ext <;> simp <;> omega

theorem spelledWord_window (hG : 0 < G) (hL : 0 < L) (S : Fin G → α)
    (σ : Fin G ≃ Fin G) (hEul : EulerianCycle hG L S σ) (i : Fin G) :
    window (L := L) hG (spelledWord S σ) i =
      window (L := L) hG S (σ i) := by
  funext d
  have hshift := window_shift_of_traverses (L := L) hG S σ hEul.1
    d.val i ⟨0, hL⟩ (by simpa using d.isLt)
  change S (σ (rotAdd hG d.val i)) =
    window (L := L) hG S (σ i) d
  simpa [spelledWord, window, cyc, rotAdd] using hshift

theorem matching_spelledWord (hG : 0 < G) (hL : 0 < L) (S : Fin G → α)
    (σ : Fin G ≃ Fin G) (hEul : EulerianCycle hG L S σ) :
    Matching (L := L) hG S (spelledWord S σ) (σ.symm : Fin G → Fin G) := by
  constructor
  · exact σ.symm.bijective
  · intro r
    rw [spelledWord_window (L := L) hG hL S σ hEul (σ.symm r), σ.apply_symm_apply]



/-- Complete-spectrum uniqueness implies Eulerian-cycle uniqueness. -/
theorem obstruction_of_bbtUniqueAt (hL : 2 ≤ L)
    (hBBT : BBTUniqueAt (α := α) L) :
    EulerianCycleObstruction (α := α) L := by
  intro K hK S hUkk σ hEul
  left
  let E : Fin K → α := spelledWord S σ
  have hm : Matching (L := L) hK S E (σ.symm : Fin K → Fin K) :=
    matching_spelledWord (L := L) hK (by omega) S σ hEul
  have hspec : specCount (L := L) hK S = specCount (L := L) hK E :=
    funext (AssemblyP1.Issue94EulerianTheta.specCount_eq_of_Matching
      hK L S (E := E) (σ := (σ.symm : Fin K → Fin K)) hm)
  have hrot : RotEquiv hK E S := hBBT K hK S E hUkk hspec
  have hv :=
    AssemblyP1.Issue94EulerianTheta.vertexCycleEq_of_RotEquiv_pullback
      (E := E) (σ := (σ.symm : Fin K → Fin K)) hK L S hm hrot (by omega)
  have hpull :
      pullback hK L S E hm.1 = σ := by
    apply Equiv.ext
    intro x
    apply σ.symm.injective
    rw [σ.symm_apply_apply]
    exact Equiv.apply_symm_apply
      (Equiv.ofBijective (σ.symm : Fin K → Fin K) hm.1) x
  rwa [hpull] at hv

/-- The graph and complete-spectrum formulations are equivalent for L ≥ 2. -/
theorem obstruction_iff_bbtUniqueAt (hL : 2 ≤ L) :
    EulerianCycleObstruction (α := α) L ↔ BBTUniqueAt (α := α) L := by
  constructor
  · exact BBTEulerian.bbtUniqueAt_of_obstruction hL
  · exact obstruction_of_bbtUniqueAt hL

end AssemblyP1.Issue94EulerianRealize
