import AssemblyP1.BBTLadder
import AssemblyP1.BBTFibrePeriod

namespace AssemblyP1.Issue94CoordinateValidity

open AssemblyP1
open AssemblyP1.OrientedRigidity
open AssemblyP1.BBTChords
open AssemblyP1.P2RepeatResidual
open AssemblyP1.BBTLadder
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian

variable {α : Type} [DecidableEq α] {K : ℕ}

theorem pairBack_add_window_le_maxPairLen
    (hK : 0 < K) (S : Fin K → α)
    (hprim : RepeatAdapter.IsPrimitive hK S)
    {a b : Fin K} (hab : a ≠ b) {ell : ℕ}
    (hag : ∀ d : Fin ell,
      cyc hK S (a.val + d.val) = cyc hK S (b.val + d.val)) :
    pairBack hK S a.val b.val + ell ≤ maxPairLen hK S a b := by
  let beta := pairBack hK S a.val b.val
  let ap := a.val + K - beta
  let bp := b.val + K - beta
  have hbeta_le : beta ≤ K := (pairBack_spec hK S a.val b.val).2
  have hbeta_lt : beta < K := pairBack_lt_G hK S hprim hab
  have hne0 : a.val % K ≠ b.val % K := by
    intro h
    apply hab
    apply Fin.ext
    simpa [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using h
  have hne : ap % K ≠ bp % K := by
    intro heq
    have hm : maxPairStart hK S a b = maxPairStart hK S b a := by
      apply Fin.ext
      simpa [maxPairStart, ap, bp, beta, pairBack_comm hK S b.val a.val] using heq
    obtain ⟨r, _ha0, _hb0, hra, hrb⟩ := maxPairStart_rotAdd hK S a b
    have hab_eq : a = b := by
      calc
        a = rotAdd hK r (maxPairStart hK S a b) := hra.symm
        _ = rotAdd hK r (maxPairStart hK S b a) := congrArg (rotAdd hK r) hm
        _ = b := hrb
    exact hab hab_eq
  have hag_ext : ∀ u : ℕ, u < beta + ell →
      cyc hK S (ap + u) = cyc hK S (bp + u) := by
    intro u hu
    by_cases hub : u < beta
    · have h := (pairBack_spec hK S a.val b.val).1 u hub
      simpa [ap, bp, beta] using h
    · have hbu : beta ≤ u := Nat.le_of_not_gt hub
      let v := u - beta
      have hv : v < ell := by
        dsimp [v]
        omega
      have hvag := hag ⟨v, hv⟩
      have haidx : ap + u = a.val + v + K := by
        dsimp [ap, v]
        omega
      have hbidx : bp + u = b.val + v + K := by
        dsimp [bp, v]
        omega
      rw [haidx, hbidx]
      exact (AssemblyP1.BBTEulerian.cyc_add_G hK S (a.val + v)).trans
        (hvag.trans (AssemblyP1.BBTEulerian.cyc_add_G hK S (b.val + v)).symm)
  have hsum : beta + ell ≤ K := by
    by_contra hnot
    have hKG : K < beta + ell := Nat.lt_of_not_ge hnot
    have hfull : ∀ d : ℕ, d < K →
        cyc hK S (ap + d) = cyc hK S (bp + d) := by
      intro d hd
      exact hag_ext d (by omega)
    exact (RepeatAdapter.not_primitive_of_ge_G_agree
      hK S ap bp K hne (le_refl K) hfull) hprim
  have hle := pairFwd_ge hK S ap bp (beta + ell) hsum hag_ext
  simpa [maxPairLen, ap, bp, beta] using hle

#print axioms AssemblyP1.Issue94CoordinateValidity.pairBack_add_window_le_maxPairLen


theorem support_chord_coordinate_valid
    (hK : 0 < K) (L : ℕ) (S : Fin K → α)
    (hprim : RepeatAdapter.IsPrimitive hK S)
    {sigma : Fin K ≃ Fin K} (hEul : EulerianCycle hK L S sigma)
    {a b : Fin K} (hab : a ≠ b) (hfx : AltF hK sigma a = b) :
    pairBack hK S a.val b.val + (L - 1) ≤ maxPairLen hK S a b := by
  apply pairBack_add_window_le_maxPairLen hK S hprim hab
  intro d
  have hv : vtx hK L S a = vtx hK L S b :=
    (hfx ▸ AltF_vtx' hK S hEul a).symm
  exact congrFun hv d

#print axioms AssemblyP1.Issue94CoordinateValidity.support_chord_coordinate_valid

end AssemblyP1.Issue94CoordinateValidity
