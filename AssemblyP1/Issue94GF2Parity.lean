import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Board 94: GF(2) parity for closed interlace blocks

A symmetric zero-diagonal GF(2) matrix restricts to a nondegenerate alternating
form on any block whose cross-entries vanish and whose supported full kernel is
trivial. Therefore the block has even cardinality.

The cross-block hypothesis is essential: supported full-kernel triviality alone
does not imply that the principal block is nonsingular.
-/

open LinearMap

private theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  calc
    a + a = ((1 : ZMod 2) + 1) * a := by rw [add_mul, one_mul]
    _ = 0 := by
      have h2 : ((1 : ZMod 2) + 1) = 0 := by
        change (2 : ZMod 2) = 0
        exact ZMod.natCast_self 2
      rw [h2, zero_mul]

theorem even_finrank_of_isAlt_nondegenerate
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hAlt : B.IsAlt) (hNon : B.Nondegenerate) :
    Even (Module.finrank K V) := by
  induction hdim : Module.finrank K V using Nat.strong_induction_on generalizing V with
  | h n ih =>
      by_cases hn0 : n = 0
      · subst n
        exact ⟨0, by simpa using hn0⟩
      · have hpos : 0 < Module.finrank K V := by omega
        letI : Nontrivial V := Module.finrank_pos_iff.mp hpos
        obtain ⟨x, hx⟩ : ∃ x : V, x ≠ (0 : V) := exists_ne (0 : V)
        have hex : ∃ y : V, B x y ≠ 0 := by
          by_contra hex
          apply hx
          apply hNon.1 x
          intro y
          by_contra hxy
          exact hex ⟨y, hxy⟩
        obtain ⟨y, hxy⟩ := hex
        have hLI : LinearIndependent K ![x, y] := by
          rw [LinearIndependent.pair_iff' hx]
          intro a hay
          apply hxy
          rw [← hay]
          simp [hAlt.self_eq_zero]
        let v : Fin 2 → V := ![x, y]
        let W : Submodule K V := Submodule.span K (Set.range v)
        have hWrank : Module.finrank K W = 2 := by
          simpa [W, v] using finrank_span_eq_card hLI
        have hxW : x ∈ W := by
          apply Submodule.subset_span
          exact ⟨0, by simp [v]⟩
        have hyW : y ∈ W := by
          apply Submodule.subset_span
          exact ⟨1, by simp [v]⟩
        have hWsep : (B.restrict W).SeparatingLeft := by
          intro z hz
          apply Subtype.ext
          have hzmem : (z : V) ∈ Submodule.span K ({y, x} : Set V) := by
            simpa [W, v] using z.2
          obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hzmem
          have hzy : B z y = 0 := by
            simpa [LinearMap.BilinForm.restrict_apply] using hz ⟨y, hyW⟩
          have hzx : B z x = 0 := by
            simpa [LinearMap.BilinForm.restrict_apply] using hz ⟨x, hxW⟩
          have hyx : B y x ≠ 0 := by
            rw [← LinearMap.IsAlt.neg hAlt x y]
            exact neg_ne_zero.mpr hxy
          have ha : a = 0 := by
            have hmul : a * B y x = 0 := by
              calc
                a * B y x = B (a • y + b • x) x := by
                  simp [hAlt.self_eq_zero]
                _ = B z x := by rw [hab]
                _ = 0 := hzx
            exact (mul_eq_zero.mp hmul).resolve_right hyx
          have hb : b = 0 := by
            have hmul : b * B x y = 0 := by
              calc
                b * B x y = B (a • y + b • x) y := by
                  rw [ha]
                  simp [hAlt.self_eq_zero]
                _ = B z y := by rw [hab]
                _ = 0 := hzy
            exact (mul_eq_zero.mp hmul).resolve_right hxy
          simp [← hab, ha, hb]
        have hWnon : (B.restrict W).Nondegenerate :=
          LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hWsep
        have hCompl : IsCompl W (B.orthogonal W) :=
          B.isCompl_orthogonal_of_restrict_nondegenerate hAlt.isRefl hWnon
        let U : Submodule K V := B.orthogonal W
        have hUalt : (B.restrict U).IsAlt := by
          intro z
          simpa [LinearMap.BilinForm.restrict_apply] using hAlt.self_eq_zero (z : V)
        have hUU : B.orthogonal U = W := by
          simpa [U] using B.orthogonal_orthogonal hNon hAlt.isRefl W
        have hUdisj : Disjoint U (B.orthogonal U) := by
          rw [hUU]
          exact hCompl.disjoint.symm
        have hUnon : (B.restrict U).Nondegenerate :=
          B.nondegenerate_restrict_of_disjoint_orthogonal hAlt.isRefl hUdisj
        have hdimadd : Module.finrank K W + Module.finrank K U = Module.finrank K V := by
          simpa [U] using Submodule.finrank_add_eq_of_isCompl hCompl
        have hUrank : Module.finrank K U + 2 = n := by omega
        have hUlt : Module.finrank K U < n := by omega
        have hUeven : Even (Module.finrank K U) :=
          ih _ hUlt (B.restrict U) hUalt hUnon rfl
        rcases hUeven with ⟨k, hk⟩
        refine ⟨k + 1, ?_⟩
        omega


theorem toBilin'_isAlt_of_symm_hollow
    {E : Type*} [Fintype E] [DecidableEq E]
    (N : Matrix E E (ZMod 2))
    (hdiag : ∀ i, N i i = 0)
    (hsymm : ∀ i j, N i j = N j i) :
    (Matrix.toBilin' N).IsAlt := by
  let B : LinearMap.BilinForm (ZMod 2) (E → ZMod 2) := Matrix.toBilin' N
  have hNSymm : N.IsSymm :=
    Matrix.IsSymm.ext (fun i j => (hsymm i j).symm)
  have hBSymm : B.IsSymm := by
    exact Matrix.isSymm_toBilin'_iff_isSymm.mpr hNSymm
  have hadd (u v : E → ZMod 2) :
      B (u + v) (u + v) = B u u + B v v := by
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.add_right]
    have huv : B v u = B u v := by
      simpa using (hBSymm.eq u v).symm
    rw [huv]
    calc
      (B u u + B u v) + (B u v + B v v)
          = B u u + (B u v + B u v) + B v v := by ac_rfl
      _ = B u u + B v v := by rw [zmod2_add_self, add_zero]
  intro x
  have hsingle (i : E) :
      B (Pi.single i (x i)) (Pi.single i (x i)) = 0 := by
    have hs : Pi.single i (x i) = (x i) • Pi.single i (1 : ZMod 2) := by
      ext j
      by_cases hji : j = i
      · subst j
        simp
      · simp [Pi.single_apply, hji]
    rw [hs]
    simp [B, Matrix.toBilin'_single, hdiag]
  have hsum : ∀ s : Finset E,
      B (∑ i ∈ s, Pi.single i (x i)) (∑ i ∈ s, Pi.single i (x i)) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [B]
    | @insert a s ha ih =>
        simp only [Finset.sum_insert, ha, not_false_eq_true]
        rw [hadd, hsingle, ih, zero_add]
  have hx : (∑ i : E, Pi.single i (x i)) = x := by
    funext j
    simp
  simpa [hx] using hsum Finset.univ



namespace AssemblyP1.Issue94GF2Parity

def CrossBlockZero {D : Type*} [DecidableEq D]
    (M : Matrix D D (ZMod 2)) (S : Finset D) : Prop :=
  ∀ ⦃i⦄, i ∈ S → ∀ ⦃j⦄, j ∉ S → M i j = 0

def SupportedKerZero {D : Type*} [Fintype D] [DecidableEq D]
    (M : Matrix D D (ZMod 2)) (S : Finset D) : Prop :=
  ∀ z : D → ZMod 2, (∀ l, l ∉ S → z l = 0) → M.mulVec z = 0 → z = 0


private def principalMatrix {D : Type*} [DecidableEq D]
    (M : Matrix D D (ZMod 2)) (S : Finset D) : Matrix S S (ZMod 2) :=
  fun i j => M i j

private def zeroExtend {D : Type*} [DecidableEq D]
    (S : Finset D) (z : S → ZMod 2) : D → ZMod 2 :=
  fun d => if hd : d ∈ S then z ⟨d, hd⟩ else 0

private theorem principalMatrix_kerZero
    {D : Type*} [Fintype D] [DecidableEq D]
    (M : Matrix D D (ZMod 2)) (S : Finset D)
    (hsymm : ∀ i j, M i j = M j i)
    (hblock : CrossBlockZero M S)
    (hker : SupportedKerZero M S) :
    ∀ z : S → ZMod 2, (principalMatrix M S).mulVec z = 0 → z = 0 := by
  intro z hz
  have hsupp : ∀ l, l ∉ S → zeroExtend S z l = 0 := by
    intro l hl
    simp [zeroExtend, hl]
  have hfull : M.mulVec (zeroExtend S z) = 0 := by
    funext d
    by_cases hd : d ∈ S
    · have hzrow : (principalMatrix M S).mulVec z ⟨d, hd⟩ = 0 :=
        congrFun hz ⟨d, hd⟩
      change (∑ j : D, M d j * zeroExtend S z j) = 0
      have hsum :
          (∑ j : D, M d j * zeroExtend S z j) =
            ∑ j : S, principalMatrix M S ⟨d, hd⟩ j * z j := by
        calc
          (∑ j : D, M d j * zeroExtend S z j)
              = ∑ j ∈ S, M d j * zeroExtend S z j := by
                  symm
                  apply Finset.sum_subset (by simp)
                  intro j _ hj
                  simp [zeroExtend, hj]
          _ = ∑ j : S, M d j * zeroExtend S z j := by
                  rw [← Finset.sum_coe_sort S]
          _ = ∑ j : S, principalMatrix M S ⟨d, hd⟩ j * z j := by
                  apply Finset.sum_congr rfl
                  intro j _
                  simp [principalMatrix, zeroExtend, j.property]
      rw [hsum]
      simpa [Matrix.mulVec, dotProduct] using hzrow
    · change (∑ j : D, M d j * zeroExtend S z j) = 0
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : j ∈ S
      · have hm : M d j = 0 := by
          rw [hsymm d j]
          exact hblock hj hd
        rw [hm, zero_mul]
      · simp [zeroExtend, hj]
  have hext0 : zeroExtend S z = 0 := hker (zeroExtend S z) hsupp hfull
  funext i
  have hi := congrFun hext0 i
  simpa [zeroExtend, i.property] using hi


private theorem matrix_bilin_nondegenerate_of_kerZero
    {E : Type*} [Fintype E] [DecidableEq E]
    (N : Matrix E E (ZMod 2))
    (hsymm : ∀ i j, N i j = N j i)
    (hker : ∀ z : E → ZMod 2, N.mulVec z = 0 → z = 0) :
    (Matrix.toBilin' N).Nondegenerate := by
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
  intro x hx
  apply hker x
  funext i
  have hi := hx (Pi.single i (1 : ZMod 2))
  change (∑ j, N i j * x j) = 0
  have hi' : (∑ j, x j * N j i) = 0 := by
    simpa [Matrix.toBilin'_apply, Pi.single_apply] using hi
  calc
    (∑ j, N i j * x j) = ∑ j, x j * N j i := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hsymm i j, mul_comm]
    _ = 0 := hi'

private theorem matrix_index_even_of_hollow_symm_kerZero
    {E : Type*} [Fintype E] [DecidableEq E]
    (N : Matrix E E (ZMod 2))
    (hdiag : ∀ i, N i i = 0)
    (hsymm : ∀ i j, N i j = N j i)
    (hker : ∀ z : E → ZMod 2, N.mulVec z = 0 → z = 0) :
    Even (Fintype.card E) := by
  have hBnon : (Matrix.toBilin' N).Nondegenerate :=
    matrix_bilin_nondegenerate_of_kerZero N hsymm hker
  have hBalt : (Matrix.toBilin' N).IsAlt :=
    toBilin'_isAlt_of_symm_hollow N hdiag hsymm
  have heven : Even (Module.finrank (ZMod 2) (E → ZMod 2)) :=
    even_finrank_of_isAlt_nondegenerate (K := ZMod 2) (V := E → ZMod 2) (Matrix.toBilin' N) hBalt hBnon
  have hdim : Module.finrank (ZMod 2) (E → ZMod 2) = Fintype.card E := by
    simp
  simpa [hdim] using heven

/-- A closed symmetric hollow GF(2) block with trivial supported kernel has
even cardinality. The CrossBlockZero hypothesis is essential: without it an odd
subset may be detected by rows outside the subset even when its principal block
is singular. -/
theorem nonsingular_hollow_block_even
    {D : Type*} [Fintype D] [DecidableEq D]
    (M : Matrix D D (ZMod 2)) (S : Finset D)
    (hdiag : ∀ i, M i i = 0)
    (hsymm : ∀ i j, M i j = M j i)
    (hblock : CrossBlockZero M S)
    (hker : SupportedKerZero M S) :
    Even S.card := by
  let N : Matrix S S (ZMod 2) := principalMatrix M S
  have hNdiag : ∀ i, N i i = 0 := fun i => hdiag i
  have hNsymm : ∀ i j, N i j = N j i := fun i j => hsymm i j
  have hNker : ∀ z : S → ZMod 2, N.mulVec z = 0 → z = 0 := by
    simpa [N] using principalMatrix_kerZero M S hsymm hblock hker
  have heven : Even (Fintype.card S) :=
    matrix_index_even_of_hollow_symm_kerZero N hNdiag hNsymm hNker
  simpa using heven

end AssemblyP1.Issue94GF2Parity
