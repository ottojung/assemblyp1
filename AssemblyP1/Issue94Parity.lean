import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

open LinearMap

namespace AssemblyP1.Issue94Parity

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


open LinearMap
open Module

theorem isAlt_of_isSymm_of_basis_diag_zero
    {K V ι : Type*} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] [Fintype ι]
    (b : Module.Basis ι K V) (B : LinearMap.BilinForm K V)
    (hSymm : B.IsSymm)
    (hdiag : ∀ i, B (b i) (b i) = 0) :
    B.IsAlt := by
  let q : V →+ K :=
    { toFun := fun x => B x x
      map_zero' := by simp
      map_add' := by
        intro x y
        rw [BilinForm.add_left, BilinForm.add_right, BilinForm.add_right]
        have hxy : B y x = B x y := (hSymm.eq x y).symm
        rw [hxy]
        have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
        have htwo : B x y + B x y = 0 := by
          calc
            B x y + B x y = (2 : K) * B x y := (two_mul _).symm
            _ = 0 := by rw [h2, zero_mul]
        calc
          B x x + B x y + (B x y + B y y)
              = B x x + (B x y + B x y) + B y y := by abel
          _ = B x x + B y y := by rw [htwo]; simp }
  intro x
  change q x = 0
  rw [← b.sum_repr x, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  change B ((b.repr x i) • b i) ((b.repr x i) • b i) = 0
  simp [hdiag i]


open LinearMap
open Module

theorem toBilin'_isSymm_of_symm
    {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (hA : ∀ i j, A i j = A j i) :
    (Matrix.toBilin' A).IsSymm := by
  let B := Matrix.toBilin' A
  have hEq : B = B.flip := by
    apply (LinearMap.BilinForm.ext_iff_basis (Pi.basisFun K ι)).2
    intro i j
    simp [B, Pi.basisFun_apply, hA]
  rw [LinearMap.BilinForm.isSymm_def]
  intro x y
  have h := congrArg (fun F : LinearMap.BilinForm K (ι → K) => F x y) hEq
  simpa [B] using h

theorem toBilin'_basis_diag
    {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (i : ι) :
    Matrix.toBilin' A ((Pi.basisFun K ι) i) ((Pi.basisFun K ι) i) = A i i := by
  simpa [Pi.basisFun_apply] using Matrix.toBilin'_single A i i


theorem even_card_of_hollow_symm_kerZero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (ZMod 2))
    (hdiag : ∀ i, A i i = 0)
    (hsymm : ∀ i j, A i j = A j i)
    (hker : ∀ z : ι → ZMod 2, A.mulVec z = 0 → z = 0) :
    Even (Fintype.card ι) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBsymm : (Matrix.toBilin' A).IsSymm :=
    toBilin'_isSymm_of_symm A hsymm
  have hBdiag :
      ∀ i, Matrix.toBilin' A ((Pi.basisFun (ZMod 2) ι) i)
        ((Pi.basisFun (ZMod 2) ι) i) = 0 := by
    intro i
    rw [toBilin'_basis_diag A i, hdiag i]
  have hBaltB :=
    isAlt_of_isSymm_of_basis_diag_zero
      (K := ZMod 2) (V := ι → ZMod 2) (ι := ι)
      (Pi.basisFun (ZMod 2) ι) (Matrix.toBilin' A) hBsymm hBdiag
  have hBalt : LinearMap.IsAlt (Matrix.toBilin' A) := by
    change ∀ x, Matrix.toBilin' A x x = 0 at hBaltB ⊢
    exact hBaltB
  have hAsep : A.SeparatingRight :=
    Matrix.separatingRight_iff_forall_mulVec_eq_zero.mpr hker
  have hBsep : (Matrix.toBilin' A).SeparatingRight :=
    Matrix.separatingRight_toBilin'_iff.mpr hAsep
  have hBnon : (Matrix.toBilin' A).Nondegenerate :=
    LinearMap.BilinForm.Nondegenerate.ofSeparatingRight hBsep
  have heven := even_finrank_of_isAlt_nondegenerate (Matrix.toBilin' A) hBalt hBnon
  simpa [Module.finrank_pi] using heven


end AssemblyP1.Issue94Parity
