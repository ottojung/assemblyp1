import AssemblyP1.P2RepeatResidual
import AssemblyP1.ScalarPrimitiveSpellings

namespace AssemblyP1.Issue94GcdOneP2

open AssemblyP1
open AssemblyP1.OrientedRigidity
open AssemblyP1.PopulationReduction
open AssemblyP1.RepeatAdapter
open AssemblyP1.P2RepeatResidual
open AssemblyP1.ScalarPrimitive

variable {α : Type} [DecidableEq α] [Fintype α]

private theorem pair_le_sum {E : Type} [DecidableEq E]
    (s : Finset E) (f : E → ℕ) (a b : E)
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    f a + f b ≤ ∑ x ∈ s, f x := by
  have hsub : {a, b} ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  calc
    f a + f b = ∑ x ∈ {a, b}, f x := (Finset.sum_pair hab).symm
    _ ≤ ∑ x ∈ s, f x :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

omit [Fintype α] in
theorem nonbranching_of_common_divisor {G L : ℕ}
    (hG : 0 < G) (hL : 2 ≤ L) (hLG : L ≤ G) (S : Fin G → α)
    (hPrim : PopulationReduction.IsPrimitive S) (hP2 : P2 hG L S)
    (g : ℕ) (hg : 1 < g)
    (hdiv : ∀ w : Fin L → α, g ∣ specCount hG S w) :
    NonBranching (genomeNodes (L := L) hG S) (support (L := L) hG S)
      (winPrefix (L := L)) (winSuffix (L := L)) := by
  have hcap := P2.imp_nodeCount_le_two_of_powerPrimitive hG hL hLG S hPrim hP2
  intro v e₁ he₁ e₂ he₂ ht₁ ht₂
  by_contra hne
  have hp₁ : 0 < specCount hG S e₁ := truth_pos_on_support hG S e₁ he₁
  have hp₂ : 0 < specCount hG S e₂ := truth_pos_on_support hG S e₂ he₂
  have hg₁ : g ≤ specCount hG S e₁ := Nat.le_of_dvd hp₁ (hdiv e₁)
  have hg₂ : g ≤ specCount hG S e₂ := Nat.le_of_dvd hp₂ (hdiv e₂)
  have hm₁ : e₁ ∈ (support hG S).filter (fun e => winPrefix e = v) :=
    Finset.mem_filter.mpr ⟨he₁, ht₁⟩
  have hm₂ : e₂ ∈ (support hG S).filter (fun e => winPrefix e = v) :=
    Finset.mem_filter.mpr ⟨he₂, ht₂⟩
  have hpair := pair_le_sum ((support hG S).filter (fun e => winPrefix e = v))
    (specCount hG S) e₁ e₂ hm₁ hm₂ hne
  have hthrough := throughput_eq_nodeCount hG S v
  change (∑ w ∈ (support hG S).filter (fun e => winPrefix e = v),
      specCount hG S w) = nodeCount hG S v at hthrough
  have hvCap : nodeCount hG S v ≤ 2 := hcap v
  rw [hthrough] at hpair
  omega

omit [Fintype α] in
theorem gcdOne_of_primitive_P2 {G L : ℕ}
    (hG : 0 < G) (hL : 2 ≤ L) (hLG : L ≤ G) (S : Fin G → α)
    (hPrim : PopulationReduction.IsPrimitive S) (hP2 : P2 hG L S) :
    IsGcdOne (W := Fin L → α) (specCount hG S) := by
  intro g hdiv
  by_cases hg1 : g = 1
  · exact hg1
  have hg : 1 < g := by
    have hg0 : g ≠ 0 := by
      intro hg0
      subst g
      obtain ⟨e, he⟩ := support_ne_nil_of_truth (L := L) (hG := hG) S
      have hp := truth_pos_on_support hG S e he
      have hz : specCount hG S e = 0 := Nat.eq_zero_of_zero_dvd (hdiv e)
      omega
    omega
  have hnb := nonbranching_of_common_divisor hG hL hLG S hPrim hP2 g hg hdiv
  have hGcd : IsGcdOne (W := Fin L → α) (specCount hG S) :=
    gcdOne_of_nonbranching_primitive (L := L) (hL := by omega) hPrim hnb
  exact hGcd g hdiv

end AssemblyP1.Issue94GcdOneP2
