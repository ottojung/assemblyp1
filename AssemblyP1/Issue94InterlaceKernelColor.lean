import AssemblyP1.Issue94InterlaceKernelBase

namespace AssemblyP1.Issue94InterlaceKernel

open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.Issue94PhysicalChord
open AssemblyP1.Issue94CLEDeletion

variable {α : Type} [DecidableEq α] {K L : ℕ}

theorem color_boundary_of_endpoint
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : AssemblyP1.BBTEulerian.EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (z : AltFChord hK sigma → ZMod 2)
    (c : AltFChord hK sigma) (y : Fin K)
    (hy : y = c.1 ∨ y = AltF hK sigma c.1) :
    color hK sigma z (AssemblyP1.BBTChords.prevPos hK y) +
        color hK sigma z y = z c := by
  classical
  calc
    color hK sigma z (AssemblyP1.BBTChords.prevPos hK y) +
          color hK sigma z y
        = ∑ d : AltFChord hK sigma,
            z d * (arcBit hK sigma d (AssemblyP1.BBTChords.prevPos hK y) +
              arcBit hK sigma d y) := by
            simp [color, mul_add, Finset.sum_add_distrib]
    _ = ∑ d : AltFChord hK sigma,
          (if d = c then z c else 0) := by
        apply Finset.sum_congr rfl
        intro d hd
        by_cases hdc : d = c
        · subst d
          have hby : y.val = c.1.val ∨
              y.val = (AltF hK sigma c.1).val := by
            rcases hy with h | h
            · left; exact congrArg Fin.val h
            · right; exact congrArg Fin.val h
          rw [arcBit_boundary_val hK sigma c y]
          rw [ite_eq_left hby]
          simp
        · have hfour := physical_four_distinct hK S sigma hEul hL hLK hprim hP2
            (Ne.symm hdc)
          have hylo : y ≠ d.1 := by
            rcases hy with h | h
            · rw [h]
              exact hfour.2.1
            · rw [h]
              exact hfour.2.2.2.1
          have hyup : y ≠ AltF hK sigma d.1 := by
            rcases hy with h | h
            · rw [h]
              exact hfour.2.2.1
            · rw [h]
              exact hfour.2.2.2.2.1
          have hvlo : y.val ≠ d.1.val := by
            intro h
            exact hylo (Fin.ext h)
          have hvup : y.val ≠ (AltF hK sigma d.1).val := by
            intro h
            exact hyup (Fin.ext h)
          rw [arcBit_boundary_val hK sigma d y]
          rw [ite_eq_right (by exact fun h => h.elim hvlo hvup)]
          simp [hdc]
    _ = z c := by simp

#print axioms AssemblyP1.Issue94InterlaceKernel.color_boundary_of_endpoint

theorem zmod2_add_self (q : ZMod 2) : q + q = 0 := by
  calc
    q + q = (2 : ZMod 2) * q := (two_mul q).symm
    _ = 0 := by
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [h2, zero_mul]

theorem color_boundary_of_fixed
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : AssemblyP1.BBTEulerian.EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (z : AltFChord hK sigma → ZMod 2)
    (y : Fin K) (hfix : AltF hK sigma y = y) :
    color hK sigma z (AssemblyP1.BBTChords.prevPos hK y) +
        color hK sigma z y = 0 := by
  classical
  calc
    color hK sigma z (AssemblyP1.BBTChords.prevPos hK y) +
          color hK sigma z y
        = ∑ d : AltFChord hK sigma,
            z d * (arcBit hK sigma d (AssemblyP1.BBTChords.prevPos hK y) +
              arcBit hK sigma d y) := by
            simp [color, mul_add, Finset.sum_add_distrib]
    _ = ∑ d : AltFChord hK sigma, 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        have hylo : y ≠ d.1 := by
          intro h
          subst y
          exact (chord_ne_image hK sigma d) hfix.symm
        have hsq := AssemblyP1.BBTLadder.AltF_sq
          hK S hEul hL hLK hprim hP2 d.1
        have hyup : y ≠ AltF hK sigma d.1 := by
          intro h
          rw [h] at hfix
          have heq : d.1 = AltF hK sigma d.1 := hsq.symm.trans hfix
          exact (chord_ne_image hK sigma d) heq
        have hvlo : y.val ≠ d.1.val := by
          intro h
          exact hylo (Fin.ext h)
        have hvup : y.val ≠ (AltF hK sigma d.1).val := by
          intro h
          exact hyup (Fin.ext h)
        rw [arcBit_boundary_val hK sigma d y]
        rw [ite_eq_right (by exact fun h => h.elim hvlo hvup)]
        simp
    _ = 0 := by simp

theorem color_jump_of_endpoint
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : AssemblyP1.BBTEulerian.EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (z : AltFChord hK sigma → ZMod 2)
    (c : AltFChord hK sigma) (y : Fin K)
    (hy : y = c.1 ∨ y = AltF hK sigma c.1) :
    color hK sigma z (AltF hK sigma y) +
        color hK sigma z y =
      z c + (interlaceMatrix (altFInterlaceGraph hK S sigma)).mulVec z c := by
  rcases hy with h | h
  · subst y
    simpa [add_comm] using
      (color_pair_eq hK S sigma hEul hL hLK hprim hP2 z c)
  · subst y
    have hsq := AssemblyP1.BBTLadder.AltF_sq
      hK S hEul hL hLK hprim hP2 c.1
    simpa [hsq] using
      (color_pair_eq hK S sigma hEul hL hLK hprim hP2 z c)

theorem color_succ_eq_of_kernel
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : AssemblyP1.BBTEulerian.EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (z : AltFChord hK sigma → ZMod 2)
    (hker :
      (interlaceMatrix (altFInterlaceGraph hK S sigma)).mulVec z = 0)
    (x : Fin K) :
    color hK sigma z (Succ hK sigma x) = color hK sigma z x := by
  let y := AssemblyP1.BBTChords.nextPos hK x
  have hprev : AssemblyP1.BBTChords.prevPos hK y = x := by
    dsimp [y]
    exact AssemblyP1.BBTSequenceGraph.prevNext hK x
  have hsucc : AltF hK sigma y = Succ hK sigma x := by
    dsimp [y]
    exact AltF_succ hK sigma x
  by_cases hfix : AltF hK sigma y = y
  · have hb := color_boundary_of_fixed
      hK S sigma hEul hL hLK hprim hP2 z y hfix
    have hj : color hK sigma z (AltF hK sigma y) +
        color hK sigma z y = 0 := by
      rw [hfix]
      exact zmod2_add_self _
    have hc :
        color hK sigma z (AltF hK sigma y) =
          color hK sigma z (AssemblyP1.BBTChords.prevPos hK y) :=
      add_right_cancel (hj.trans hb.symm)
    simpa [hsucc, hprev] using hc
  · obtain ⟨c, hpair⟩ :=
      exists_physical_chord_of_support
        hK S sigma hEul hL hLK hprim hP2 hfix
    have hymem :
        y ∈ ({c.1, AltF hK sigma c.1} : Finset (Fin K)) := by
      rw [hpair]
      simp
    have hy : y = c.1 ∨ y = AltF hK sigma c.1 := by
      simpa using hymem
    have hb := color_boundary_of_endpoint
      hK S sigma hEul hL hLK hprim hP2 z c y hy
    have hj := color_jump_of_endpoint
      hK S sigma hEul hL hLK hprim hP2 z c y hy
    have hm :
        (interlaceMatrix (altFInterlaceGraph hK S sigma)).mulVec z c = 0 := by
      simpa using congrFun hker c
    have hj0 :
        color hK sigma z (AltF hK sigma y) + color hK sigma z y = z c := by
      calc
        color hK sigma z (AltF hK sigma y) + color hK sigma z y
            = z c +
              (interlaceMatrix (altFInterlaceGraph hK S sigma)).mulVec z c := hj
        _ = z c := by rw [hm]; simp
    have hc :
        color hK sigma z (AltF hK sigma y) =
          color hK sigma z (AssemblyP1.BBTChords.prevPos hK y) :=
      add_right_cancel (hj0.trans hb.symm)
    simpa [hsucc, hprev] using hc

#print axioms AssemblyP1.Issue94InterlaceKernel.color_succ_eq_of_kernel

theorem color_iterate_eq_of_kernel
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : AssemblyP1.BBTEulerian.EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (z : AltFChord hK sigma → ZMod 2)
    (hker :
      (interlaceMatrix (altFInterlaceGraph hK S sigma)).mulVec z = 0)
    (n : ℕ) (x : Fin K) :
    color hK sigma z ((Succ hK sigma)^[n] x) = color hK sigma z x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      calc
        color hK sigma z ((Succ hK sigma)^[n] (Succ hK sigma x))
            = color hK sigma z (Succ hK sigma x) := ih _
        _ = color hK sigma z x :=
          color_succ_eq_of_kernel hK S sigma hEul hL hLK hprim hP2 z hker x

theorem color_constant_of_kernel
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : AssemblyP1.BBTEulerian.EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (z : AltFChord hK sigma → ZMod 2)
    (hker :
      (interlaceMatrix (altFInterlaceGraph hK S sigma)).mulVec z = 0) :
    ∀ x : Fin K,
      color hK sigma z x =
        color hK sigma z (AssemblyP1.BBTEulerian.origin hK) := by
  let orbit : Fin K → Fin K :=
    fun n => (Succ hK sigma)^[n.val] (AssemblyP1.BBTEulerian.origin hK)
  have hinj : Function.Injective orbit := by
    exact hEul.2
  have hsurj : Function.Surjective orbit :=
    Finite.injective_iff_surjective.mp hinj
  intro x
  obtain ⟨n, hn⟩ := hsurj x
  rw [← hn]
  exact color_iterate_eq_of_kernel
    hK S sigma hEul hL hLK hprim hP2 z hker n.val
      (AssemblyP1.BBTEulerian.origin hK)

end AssemblyP1.Issue94InterlaceKernel
