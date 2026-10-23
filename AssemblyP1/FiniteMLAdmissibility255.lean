import AssemblyP1.OrientedSameLengthML
import AssemblyP1.OrientedRigidity

/-!
# Fixed-`x` admissibility necessity for exact ML (umbrella #255, axis A)

Scoped sub-claim: truth-support admissibility of the fixed sample `x` is
necessary for truth maximality under the exact multinomial objective.
If `x` charges a read type absent from the truth's window support, the
truth's exact likelihood is `0`, so any candidate giving that type positive
probability strictly beats the truth.

This complements `AssemblyP1.FixedXExactML`, whose classification iff is
stated under the admissibility hypothesis `hx`. It does not duplicate child
issues #256/#257/#259/#260/#261: it is about the exact oriented same-length
multinomial at a fixed inadmissible `x`, with literal read-string types
(axis: spelled genomes, fixed `L`, exact multinomial, truth candidacy kept).
-/

namespace AssemblyP1.FiniteMLAdmissibility255

open Finset BigOperators

/-- **Admissibility necessity (general lemma).** If the fixed sample `x`
charges a read type `w` that never occurs as a length-`L` window of the truth
`S`, the truth's exact multinomial likelihood vanishes. -/
theorem exactLik_eq_zero_of_inadmissible {α : Type} [DecidableEq α] [Fintype α]
    {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (x : OrientedSameLengthML.ObservedReads α L)
    (w : Fin L → α)
    (habs : OrientedRigidity.specCount (L := L) hG S w = 0)
    (hpos : 0 < x w) :
    OrientedSameLengthML.exactLik hG S x = 0 := by
  unfold OrientedSameLengthML.exactLik
  apply Finset.prod_eq_zero (Finset.mem_univ w)
  unfold OrientedSameLengthML.exactFactor
  rw [habs]
  simp only [Nat.cast_zero, zero_div]
  exact zero_pow (by omega : x w ≠ 0)

/-- The AAABBB truth at `L = 3` (same genome as `FixedXExactML.S255`). -/
def S255L3 : Fin 6 → Fin 2 := ![0, 0, 0, 1, 1, 1]

/-- The inadmissible read type `010`, absent from the truth's windows. -/
def wStar : Fin 3 → Fin 2 := ![0, 1, 0]

/-- Single-read sample concentrated on `wStar`. -/
def xStar : OrientedSameLengthML.ObservedReads (Fin 2) 3 :=
  fun w => if w = wStar then 1 else 0

/-- Competitor spelling `010` at start `0`. -/
def SComp : Fin 6 → Fin 2 := ![0, 1, 0, 0, 0, 0]

theorem truth_missing_wStar :
    OrientedRigidity.specCount (L := 3) (by decide : 0 < 6) S255L3 wStar = 0 := by
  decide

theorem comp_spells_wStar :
    OrientedRigidity.specCount (L := 3) (by decide : 0 < 6) SComp wStar = 1 := by
  decide

theorem xStar_pos : 0 < xStar wStar := by
  unfold xStar; simp [wStar]

/-- On the inadmissible sample the truth's exact likelihood vanishes. -/
theorem truth_lik_zero :
    OrientedSameLengthML.exactLik (by decide : 0 < 6) S255L3 xStar = 0 :=
  exactLik_eq_zero_of_inadmissible _ _ _ wStar truth_missing_wStar xStar_pos

/-- The competitor has strictly positive exact likelihood on the same sample. -/
theorem comp_lik_pos :
    0 < OrientedSameLengthML.exactLik (by decide : 0 < 6) SComp xStar := by
  unfold OrientedSameLengthML.exactLik
  apply Finset.prod_pos
  intro w _
  unfold OrientedSameLengthML.exactFactor
  by_cases hw : w = wStar
  · subst hw
    rw [comp_spells_wStar]
    unfold xStar
    simp only [ite_true]
    norm_num
  · have hxw : xStar w = 0 := by unfold xStar; simp [hw]
    rw [hxw]
    simp

/-- **Witness theorem (axis A).** At the fixed inadmissible sample `xStar`,
the truth `S255L3` is not an exact-ML maximizer: the competitor `SComp`
attains a strictly larger exact likelihood. -/
theorem truth_not_maximal_at_xStar :
    OrientedSameLengthML.exactLik (by decide : 0 < 6) SComp xStar >
      OrientedSameLengthML.exactLik (by decide : 0 < 6) S255L3 xStar := by
  rw [truth_lik_zero]
  exact comp_lik_pos

#print axioms exactLik_eq_zero_of_inadmissible
#print axioms truth_not_maximal_at_xStar

end AssemblyP1.FiniteMLAdmissibility255
