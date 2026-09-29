import AssemblyP1.Issue94Step2Path
import AssemblyP1.Issue94Step5Heads
namespace AssemblyP1.Issue94NoCollision
open AssemblyP1 AssemblyP1.PopulationReduction AssemblyP1.RepeatAdapter
open AssemblyP1.SourceFaithfulIs AssemblyP1.OrientedRigidity AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTChords AssemblyP1.BBTUniqueEulerian AssemblyP1.P2RepeatResidual
open AssemblyP1.BBTLadder AssemblyP1.BBTCrossingCoalesce AssemblyP1.Issue89GapMap
open AssemblyP1.Issue94OrbitSearch AssemblyP1.Issue94OrbitGeneral
open AssemblyP1.Issue94IterSlide AssemblyP1.Issue94Step2Path
open AssemblyP1.Issue94Step4Prop AssemblyP1.Issue94Step5Heads
set_option maxHeartbeats 800000
variable {K L : ℕ}

theorem modadd (u c : ℕ) : (u + c) % K = (u % K + c) % K := by
  calc (u + c) % K = (u % K + c % K) % K := Nat.add_mod u c K
    _ = ((u % K) % K + c % K) % K := by rw [Nat.mod_mod]
    _ = (u % K + c) % K := (Nat.add_mod (u % K) c K).symm
theorem modadd2 (u c : ℕ) : (u + c % K) % K = (u + c) % K := by
  calc (u + c % K) % K = (u % K + c % K) % K := modadd u (c % K)
    _ = (c % K + u % K) % K := by rw [Nat.add_comm]
    _ = (c + u) % K := (Nat.add_mod c u K).symm
    _ = (u + c) % K := by rw [Nat.add_comm]
theorem backAgreeC_mod (hK : 0 < K) (S : Fin K → Bin) (x y t : ℕ) (ht : t ≤ K) :
    backAgreeC hK S x y t ↔ backAgreeC hK S (x % K) (y % K) t := by
  have mdl : ∀ (z u : ℕ), (z + K - t + u) % K = ((z % K) + K - t + u) % K := by
    intro z u
    rw [Nat.add_sub_assoc ht, Nat.add_assoc, Nat.add_sub_assoc ht, Nat.add_assoc, modadd]
  constructor
  · intro h u hu
    have hh := h u hu
    calc cyc hK S ((x % K) + K - t + u) = cyc hK S (x + K - t + u) := by
          symm; exact cyc_congr hK S (mdl x u)
      _ = cyc hK S (y + K - t + u) := hh
      _ = cyc hK S ((y % K) + K - t + u) := cyc_congr hK S (mdl y u)
  · intro h u hu
    have hh := h u hu
    calc cyc hK S (x + K - t + u) = cyc hK S ((x % K) + K - t + u) :=
          cyc_congr hK S (mdl x u)
      _ = cyc hK S ((y % K) + K - t + u) := hh
      _ = cyc hK S (y + K - t + u) := by
          symm; exact cyc_congr hK S (mdl y u)
theorem backSetC_mod (hK : 0 < K) (S : Fin K → Bin) (x y : ℕ) :
    backSetC hK S x y = backSetC hK S (x % K) (y % K) :=
  Finset.filter_congr fun n hn => backAgreeC_mod hK S x y n (by have := Finset.mem_range.mp hn; omega)
theorem pairBack_mod (hK : 0 < K) (S : Fin K → Bin) (x y : ℕ) :
    pairBack hK S x y = pairBack hK S (x % K) (y % K) := by
  classical
  obtain ⟨hA, hB⟩ := pairBack_spec hK S x y
  obtain ⟨hA2, hB2⟩ := pairBack_spec hK S (x % K) (y % K)
  have fwd : backAgreeC hK S x y (pairBack hK S x y) →
      backAgreeC hK S (x % K) (y % K) (pairBack hK S x y) :=
    (backAgreeC_mod hK S x y (pairBack hK S x y) hB).mp
  refine le_antisymm
    (pairBack_ge hK S (x % K) (y % K) (pairBack hK S x y) hB (fwd hA))
    (pairBack_ge hK S x y (pairBack hK S (x % K) (y % K)) hB2
      ((backAgreeC_mod hK S x y (pairBack hK S (x % K) (y % K)) hB2).mpr hA2))
theorem rotAdd_val (hK : 0 < K) (t : ℕ) (x : Fin K) :
    (rotAdd hK t x).val = (x.val + t) % K := rfl
theorem rotAdd_inj_any (hK : 0 < K) (t : ℕ) {x y : Fin K}
    (h : rotAdd hK t x = rotAdd hK t y) : x = y := by
  have hval := congrArg Fin.val h
  rw [rotAdd_val, rotAdd_val] at hval
  have hlt : t % K < K := Nat.mod_lt _ hK
  have key : ∀ (u : ℕ) (hu : u < K), (u + t) % K = (u + t % K) % K := by
    intro u hu
    exact (modadd2 u t).symm
  rw [key _ x.isLt, key _ y.isLt] at hval
  apply rotAdd_inj hK hlt
  unfold rotAdd
  apply Fin.ext
  simpa only [Fin.val_mk] using hval
theorem rotAdd_mod (hK : 0 < K) (t : ℕ) (x : Fin K) :
    rotAdd hK (t + K) x = rotAdd hK t x := by
  apply Fin.ext
  rw [rotAdd_val, rotAdd_val]
  have h := Nat.add_mod_right (x.val + t) K
  rwa [Nat.add_assoc] at h
theorem pairBack_slide (hK : 0 < K) (S : Fin K → Bin) (hprim : RepeatAdapter.IsPrimitive hK S)
    {c d : Fin K} (hcd : c ≠ d) (j : ℕ) (hj : j ≤ pairBack hK S c.val d.val) :
    pairBack hK S (rotAdd hK (K - j) c).val (rotAdd hK (K - j) d).val
      = pairBack hK S c.val d.val - j := by
  have hlt : pairBack hK S c.val d.val < K := pairBack_lt_G hK S hprim hcd
  have h := pairBack_shift hK S (a := c) (b := d) j hj hlt
  have hb : pairBack hK S ((c.val + K - j) % K) ((d.val + K - j) % K)
      = pairBack hK S c.val d.val - j :=
    (pairBack_mod hK S (c.val + K - j) (d.val + K - j)).symm.trans h
  have eA : (rotAdd hK (K - j) c).val = (c.val + K - j) % K := by
    rw [rotAdd_val]; congr 1; omega
  have eB : (rotAdd hK (K - j) d).val = (d.val + K - j) % K := by
    rw [rotAdd_val]; congr 1; omega
  rw [eA, eB]
  exact hb
theorem head_of_slide (hK : 0 < K) (S : Fin K → Bin) (hprim : RepeatAdapter.IsPrimitive hK S)
    {a b : Fin K} (hab : a ≠ b) (j : ℕ) (hj : j ≤ pairBack hK S a.val b.val) :
    maxPairStart hK S (rotAdd hK (K - j) a) (rotAdd hK (K - j) b)
      = maxPairStart hK S a b := by
  rw [maxPairStart_eq, maxPairStart_eq]
  have h := pairBack_slide hK S hprim hab j hj
  rw [h]
  rw [rotAdd_comp hK (K - (pairBack hK S a.val b.val - j)) (K - j)]
  have key : (K - (pairBack hK S a.val b.val - j)) + (K - j)
      = (K - pairBack hK S a.val b.val) + K := by
    have hβ : pairBack hK S a.val b.val ≤ K := (pairBack_spec hK S a.val b.val).2
    have h1 : K - (pairBack hK S a.val b.val - j) = K - pairBack hK S a.val b.val + j := by
      omega
    omega
  rw [key, rotAdd_mod]
theorem pairBack_of_head (hK : 0 < K) (S : Fin K → Bin) (hprim : RepeatAdapter.IsPrimitive hK S)
    {a b : Fin K} (hab : a ≠ b) :
    pairBack hK S (maxPairStart hK S a b).val (maxPairStart hK S b a).val = 0 := by
  have hlt : pairBack hK S a.val b.val < K := pairBack_lt_G hK S hprim hab
  have h := pairBack_shift hK S (a := a) (b := b) (pairBack hK S a.val b.val)
    (le_refl _) hlt
  have hz : pairBack hK S (a.val + K - pairBack hK S a.val b.val)
      (b.val + K - pairBack hK S a.val b.val) = 0 := by omega
  have hb := (pairBack_mod hK S (a.val + K - pairBack hK S a.val b.val)
      (b.val + K - pairBack hK S a.val b.val)).symm.trans hz
  have eA : (maxPairStart hK S a b).val = (a.val + K - pairBack hK S a.val b.val) % K := by
    rw [maxPairStart, Fin.val_mk]
  have eB : (maxPairStart hK S b a).val = (b.val + K - pairBack hK S a.val b.val) % K := by
    rw [maxPairStart, Fin.val_mk, pairBack_comm]
  rw [eA, eB]
  exact hb
theorem head_of_head (hK : 0 < K) (S : Fin K → Bin) (hprim : RepeatAdapter.IsPrimitive hK S) {a b : Fin K} (hab : a ≠ b) :
    maxPairStart hK S (maxPairStart hK S a b) (maxPairStart hK S b a) = maxPairStart hK S a b
      ∧ maxPairStart hK S (maxPairStart hK S b a) (maxPairStart hK S a b) = maxPairStart hK S b a := by
  constructor
  · rw [maxPairStart_eq, show K - pairBack hK S (maxPairStart hK S a b).val (maxPairStart hK S b a).val = K from by
      rw [pairBack_of_head hK S hprim hab, Nat.sub_zero], rotAdd_K]
  · have hph := pairBack_of_head hK S hprim hab
    rw [maxPairStart_eq]
    have hc := pairBack_comm hK S (maxPairStart hK S b a).val (maxPairStart hK S a b).val
    have hz : pairBack hK S (maxPairStart hK S b a).val (maxPairStart hK S a b).val = 0 := by
      rw [← hc, hph]
    rw [hz, Nat.sub_zero, rotAdd_K]

/-! ## 7. Exchange of the two pairs in an interleaving -/

theorem interleavedStarts_pair_swap (hK : 0 < K) {a b c d : Fin K}
    (hI : InterleavedStarts hK a b c d) : InterleavedStarts hK c d a b := by
  have hne : FourDistinctStarts a b c d := hI.1
  have h : InArc hK a b c ↔ ¬ InArc hK a b d := hI.2
  rcases hne with ⟨h1, h2, h3, h4, h5, h6⟩
  refine ⟨⟨h6, h2.symm, h4.symm, h3.symm, h5.symm, h1⟩, ?_⟩
  have key : ∀ (u v w : Fin K),
      InArc hK u v w ↔
        (u.val < v.val ∧ u.val < w.val ∧ w.val < v.val) ∨
          (v.val < u.val ∧ (u.val < w.val ∨ w.val < v.val)) := by
    intro u v w
    exact inArc_val hK
  rw [key a b c, key a b d] at h
  rw [key c d a, key c d b]
  by_cases hab : a.val < b.val <;> by_cases hcd : c.val < d.val <;> omega

theorem interleaved_pair_swap (hK : 0 < K) {α : Type} {S : Fin K → α}
    (a b c d : Fin K) (hI : Interleaved (mkGenome hK S) a b c d) :
    Interleaved (mkGenome hK S) c d a b :=
  (interleaved_iff hK c d a b).mpr
    (interleavedStarts_pair_swap hK ((interleaved_iff hK a b c d).mp hI))

/-! ## 5. A chord stays a chord, and stays a pair, under a slide -/

theorem chord_of_slide (hK : 0 < K) (S : Fin K → Bin) {a b : Fin K}
    (hv : vtx hK L S a = vtx hK L S b) (j : ℕ)
    (hj : j ≤ pairBack hK S a.val b.val) :
    vtx hK L S (rotAdd hK (K - j) a) = vtx hK L S (rotAdd hK (K - j) b) := by
  have hKj : j ≤ K := by
    obtain ⟨-, hb⟩ := pairBack_spec hK S a.val b.val
    omega
  refine (vtx_eq_iff hK S).mpr fun d => ?_
  have h := chord_shift_left hK S a b (L - 1) j ((vtx_eq_iff hK S).mp hv) hj
    (d := ⟨d.val, d.isLt⟩)
  have eA : (rotAdd hK (K - j) a).val = (a.val + K - j) % K := by
    rw [rotAdd_val]
    congr 1
    omega
  have eB : (rotAdd hK (K - j) b).val = (b.val + K - j) % K := by
    rw [rotAdd_val]
    congr 1
    omega
  show cyc hK S ((rotAdd hK (K - j) a).val + d.val)
      = cyc hK S ((rotAdd hK (K - j) b).val + d.val)
  rw [eA, eB]
  exact h

theorem slide_pair_ne (hK : 0 < K) (_S : Fin K → Bin)
    {a b : Fin K} (hab : a ≠ b) (j : ℕ) :
    rotAdd hK (K - j) a ≠ rotAdd hK (K - j) b :=
  fun hh => hab (rotAdd_inj_any hK (K - j) hh)

/-! ## 6. A guard failure forces a cross-head equality -/

/-- **A guard failure forces the two chords to share their extension starts.**
Suppose the chord `(c, d)` slid `j ≤ pairBack c d` steps lands one of its ends on
an end `x` of the chord `{x, y}` (`x ≠ y`, itself a chord).  Then the two chords'
extension starts agree in one order or the other.

This is §5 step 3, `Issue89GapMap.step3_shared_endpoint_forces_pair_readL`, i.e.
`BBTCrossingCoalesce.collision_forces_pair` together with the multiplicity cap
`BBTCrossingCoalesce.three_starts_ne`, transported through
`P2RepeatResidual.chord_shift_left` (the slid pair is still a chord). -/
theorem slide_meets_head (hK : 0 < K) (S : Fin K → Bin) (h2L : 2 ≤ L) (hLK : L ≤ K)
    (hP2 : P2 hK L S) (hprim : RepeatAdapter.IsPrimitive hK S)
    {c d x y : Fin K} (hcd : c ≠ d) (hxy : x ≠ y)
    (hvcd : vtx hK L S c = vtx hK L S d) (hvxy : vtx hK L S x = vtx hK L S y)
    (j : ℕ) (hj : j ≤ pairBack hK S c.val d.val)
    (h : rotAdd hK (K - j) c = x ∨ rotAdd hK (K - j) d = x) :
    maxPairStart hK S (rotAdd hK (K - j) c) (rotAdd hK (K - j) d)
        = maxPairStart hK S x y
      ∨ maxPairStart hK S (rotAdd hK (K - j) c) (rotAdd hK (K - j) d)
        = maxPairStart hK S y x := by
  have hcd' : rotAdd hK (K - j) c ≠ rotAdd hK (K - j) d :=
    slide_pair_ne hK S hcd j
  have hvcd' : vtx hK L S (rotAdd hK (K - j) c) = vtx hK L S (rotAdd hK (K - j) d) :=
    chord_of_slide hK S hvcd j hj
  have key : (x = rotAdd hK (K - j) c ∧ y = rotAdd hK (K - j) d) ∨
      (x = rotAdd hK (K - j) d ∧ y = rotAdd hK (K - j) c) := by
    rcases h with h | h
    · subst h
      exact step3_shared_endpoint_forces_pair_readL hK S h2L hLK hP2 hprim
        hxy hcd' hvxy hvcd' (Or.inl rfl)
    · subst h
      exact step3_shared_endpoint_forces_pair_readL hK S h2L hLK hP2 hprim
        hxy hcd' hvxy hvcd' (Or.inr (Or.inl rfl))
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (by rw [h1, h2])
  · exact Or.inr (by rw [h2, h1])
/-! ## 8. The slide guards, discharged from the cross-head inequalities -/

/-- **The guards for sliding `(c, d)` down to its head `(C, D)`.**  For every
`j ≤ pairBack c d` the slid pair collides with neither `a` nor `b`.  A collision
would, by `slide_meets_head`, make the two chords have the same extension starts
in one order; but `head_of_slide` says the extension starts of the slid
`(c, d)` are `(C, D)`, so this forces `A = C` or `B = C`, contradicting `hAC` or
`hBC`.  So the cross-head INEQUALITIES are exactly what discharges the
`step4_guarded` side condition. -/
theorem slide_guards_down (hK : 0 < K) (S : Fin K → Bin) (h2L : 2 ≤ L) (hLK : L ≤ K)
    (hP2 : P2 hK L S) (hprim : RepeatAdapter.IsPrimitive hK S)
    {a b c d : Fin K} (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : vtx hK L S a = vtx hK L S b) (hvcd : vtx hK L S c = vtx hK L S d)
    (hAC : maxPairStart hK S a b ≠ maxPairStart hK S c d)
    (hBC : maxPairStart hK S b a ≠ maxPairStart hK S c d) :
    ∀ j : ℕ, j ≤ pairBack hK S c.val d.val → SlideGuards hK a b c d j := by
  intro j hj
  have hCj : maxPairStart hK S (rotAdd hK (K - j) c) (rotAdd hK (K - j) d)
      = maxPairStart hK S c d := head_of_slide hK S hprim hcd j hj
  have g1 : rotAdd hK (K - j) c ≠ a := by
    intro h
    rcases slide_meets_head hK S h2L hLK hP2 hprim hcd hab hvcd hvab j hj (Or.inl h) with
      hq | hq
    · exact hAC (by rw [← hCj, hq])
    · exact hBC (by rw [← hCj, hq])
  have g2 : rotAdd hK (K - j) c ≠ b := by
    intro h
    rcases slide_meets_head hK S h2L hLK hP2 hprim hcd hab.symm hvcd hvab.symm j hj
      (Or.inl h) with hq | hq
    · exact hBC (by rw [← hCj, hq])
    · exact hAC (by rw [← hCj, hq])
  have g3 : rotAdd hK (K - j) d ≠ a := by
    intro h
    rcases slide_meets_head hK S h2L hLK hP2 hprim hcd hab hvcd hvab j hj (Or.inr h) with
      hq | hq
    · exact hAC (by rw [← hCj, hq])
    · exact hBC (by rw [← hCj, hq])
  have g4 : rotAdd hK (K - j) d ≠ b := by
    intro h
    rcases slide_meets_head hK S h2L hLK hP2 hprim hcd hab.symm hvcd hvab.symm j hj
      (Or.inr h) with hq | hq
    · exact hBC (by rw [← hCj, hq])
    · exact hAC (by rw [← hCj, hq])
  exact ⟨g1, g2, g3, g4⟩

/-- **The guards for sliding `(a, b)` down to its head `(A, B)`**, against the
already reached head `(C, D)` of the other chord.  Here a collision would make
`(a, b)` share its extension starts with `{C, D}`, whose own extension starts are
`(C, D)` itself (`head_of_head`); combined with `head_of_slide` this forces
`A = C`, `A = D`, `B = C` or `B = D`. -/
theorem slide_guards_down_heads (hK : 0 < K) (S : Fin K → Bin) (h2L : 2 ≤ L)
    (hLK : L ≤ K) (hP2 : P2 hK L S) (hprim : RepeatAdapter.IsPrimitive hK S)
    {a b c d : Fin K} (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : vtx hK L S a = vtx hK L S b) (hvcd : vtx hK L S c = vtx hK L S d)
    (hAC : maxPairStart hK S a b ≠ maxPairStart hK S c d)
    (hAD : maxPairStart hK S a b ≠ maxPairStart hK S d c)
    (hBC : maxPairStart hK S b a ≠ maxPairStart hK S c d)
    (hBD : maxPairStart hK S b a ≠ maxPairStart hK S d c) :
    ∀ j : ℕ, j ≤ pairBack hK S a.val b.val →
      SlideGuards hK (maxPairStart hK S c d) (maxPairStart hK S d c) a b j := by
  have hCDne : maxPairStart hK S c d ≠ maxPairStart hK S d c :=
    heads_of_one_chord_ne hK S h2L hLK hprim hcd ((vtx_eq_iff hK S).mp hvcd)
  have hCD : vtx hK L S (maxPairStart hK S c d) = vtx hK L S (maxPairStart hK S d c) :=
    vtx_maxPairStart hK S h2L hLK hprim hcd ((vtx_eq_iff hK S).mp hvcd)
  have hh1 : maxPairStart hK S (maxPairStart hK S c d) (maxPairStart hK S d c)
      = maxPairStart hK S c d := (head_of_head hK S hprim hcd).1
  have hh2 : maxPairStart hK S (maxPairStart hK S d c) (maxPairStart hK S c d)
      = maxPairStart hK S d c := (head_of_head hK S hprim hcd).2
  intro j hj
  have hAj : maxPairStart hK S (rotAdd hK (K - j) a) (rotAdd hK (K - j) b)
      = maxPairStart hK S a b := head_of_slide hK S hprim hab j hj
  have hj2 : j ≤ pairBack hK S b.val a.val := by rw [pairBack_comm]; exact hj
  have hBj : maxPairStart hK S (rotAdd hK (K - j) b) (rotAdd hK (K - j) a)
      = maxPairStart hK S b a := head_of_slide hK S hprim hab.symm j hj2
  have g1 : rotAdd hK (K - j) a ≠ maxPairStart hK S c d := by
    intro h
    rcases slide_meets_head hK S h2L hLK hP2 hprim hab hCDne hvab hCD j hj (Or.inl h) with
      hq | hq
    · exact hAC (by rw [← hAj, hq, hh1])
    · exact hAD (by rw [← hAj, hq, hh2])
  have g2 : rotAdd hK (K - j) a ≠ maxPairStart hK S d c := by
    intro h
    have hCD2 : vtx hK L S (maxPairStart hK S d c) = vtx hK L S (maxPairStart hK S c d) :=
      hCD.symm
    have hCDne2 : maxPairStart hK S d c ≠ maxPairStart hK S c d := Ne.symm hCDne
    rcases slide_meets_head hK S h2L hLK hP2 hprim hab hCDne2 hvab hCD2 j hj (Or.inl h) with
      hq | hq
    · exact hAD (by rw [← hAj, hq, hh2])
    · exact hAC (by rw [← hAj, hq, hh1])
  have g3 : rotAdd hK (K - j) b ≠ maxPairStart hK S c d := by
    intro h
    rcases slide_meets_head hK S h2L hLK hP2 hprim hab.symm hCDne hvab.symm hCD j hj2
      (Or.inl h) with hq | hq
    · exact hBC (by rw [← hBj, hq, hh1])
    · exact hBD (by rw [← hBj, hq, hh2])
  have g4 : rotAdd hK (K - j) b ≠ maxPairStart hK S d c := by
    intro h
    have hCD2 : vtx hK L S (maxPairStart hK S d c) = vtx hK L S (maxPairStart hK S c d) :=
      hCD.symm
    have hCDne2 : maxPairStart hK S d c ≠ maxPairStart hK S c d := Ne.symm hCDne
    rcases slide_meets_head hK S h2L hLK hP2 hprim hab.symm hCDne2 hvab.symm hCD2 j hj2
      (Or.inl h) with hq | hq
    · exact hBD (by rw [← hBj, hq, hh2])
    · exact hBC (by rw [← hBj, hq, hh1])
  exact ⟨g1, g2, g3, g4⟩
/-! ## 9. The no-collision front -/

/-- **The four cross-head INEQUALITIES force the heads to interleave.**

This is the no-collision half of the case split of
`BBTCrossingCoalesce.CrossingPairsCoalesce` prescribed by the human pointer of
2026-09-28 21:34:57Z on board issue 94.  It is proved from the already-proved path
and slide machinery --- `Issue94Step4Prop.step4_guarded`, together with
`P2RepeatResidual.chord_shift_left` and `P2RepeatResidual.pairBack_shift` (which
make a falsified guard force a cross-head equality),
`Issue94Step2Path.step2_components_are_paths_proved` (which keeps the slid pair a
pair of distinct ends) and `BBTCrossingCoalesce.vtx_maxPairStart` --- and from
**no** cross-head-equality lemma whatsoever. -/
theorem no_collision_heads_interleave (hK : 0 < K) (S : Fin K → Bin)
    (h2L : 2 ≤ L) (hLK : L ≤ K) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) {a b c d : Fin K}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : vtx hK L S a = vtx hK L S b) (hvcd : vtx hK L S c = vtx hK L S d)
    (hI : Interleaved (mkGenome hK S) a b c d)
    (hAC : maxPairStart hK S a b ≠ maxPairStart hK S c d)
    (hAD : maxPairStart hK S a b ≠ maxPairStart hK S d c)
    (hBC : maxPairStart hK S b a ≠ maxPairStart hK S c d)
    (hBD : maxPairStart hK S b a ≠ maxPairStart hK S d c) :
    Interleaved (mkGenome hK S)
      (maxPairStart hK S a b) (maxPairStart hK S b a)
      (maxPairStart hK S c d) (maxPairStart hK S d c) := by
  -- slide `(c, d)` down to its head `(C, D)`, keeping `(a, b)` fixed
  have hg1 : ∀ j : ℕ, j ≤ pairBack hK S c.val d.val → SlideGuards hK a b c d j :=
    slide_guards_down hK S h2L hLK hP2 hprim hab hcd hvab hvcd hAC hBC
  have h1 : Interleaved (mkGenome hK S) a b
      (maxPairStart hK S c d) (maxPairStart hK S d c) := by
    have h1' := step4_guarded L K hK S a b c d hab hcd hvab hvcd hI
      (pairBack hK S c.val d.val) (le_refl _) hg1
    convert h1' using 1
    · exact maxPairStart_eq hK S c d
    · rw [pairBack_comm]; exact maxPairStart_eq hK S d c
  have hCDne : maxPairStart hK S c d ≠ maxPairStart hK S d c :=
    heads_of_one_chord_ne hK S h2L hLK hprim hcd ((vtx_eq_iff hK S).mp hvcd)
  -- slide `(a, b)` down to its head `(A, B)`, keeping `(C, D)` fixed
  have hCD : vtx hK L S (maxPairStart hK S c d) = vtx hK L S (maxPairStart hK S d c) :=
    vtx_maxPairStart hK S h2L hLK hprim hcd ((vtx_eq_iff hK S).mp hvcd)
  have hg2 : ∀ j : ℕ, j ≤ pairBack hK S a.val b.val →
      SlideGuards hK (maxPairStart hK S c d) (maxPairStart hK S d c) a b j :=
    slide_guards_down_heads hK S h2L hLK hP2 hprim hab hcd hvab hvcd hAC hAD hBC hBD
  have h2 : Interleaved (mkGenome hK S)
      (maxPairStart hK S c d) (maxPairStart hK S d c)
      (rotAdd hK (K - pairBack hK S a.val b.val) a)
      (rotAdd hK (K - pairBack hK S a.val b.val) b) :=
    step4_guarded L K hK S (maxPairStart hK S c d) (maxPairStart hK S d c) a b
      hCDne hab hCD hvab
      (interleaved_pair_swap hK a b (maxPairStart hK S c d) (maxPairStart hK S d c) h1)
      (pairBack hK S a.val b.val) (le_refl _) hg2
  -- identify the slid ends with the heads, and exchange the two pairs
  have hslide : Interleaved (mkGenome hK S)
      (maxPairStart hK S c d) (maxPairStart hK S d c)
      (maxPairStart hK S a b) (maxPairStart hK S b a) := by
    convert h2 using 1
    · exact maxPairStart_eq hK S a b
    · rw [pairBack_comm]; exact maxPairStart_eq hK S b a
  exact interleaved_pair_swap hK (maxPairStart hK S c d) (maxPairStart hK S d c)
    (maxPairStart hK S a b) (maxPairStart hK S b a) hslide

/-- **Closing by `P2.imp_ExtCrossing`.**  On a primitive `P2` word the four
cross-head INEQUALITIES are never simultaneously satisfiable at two interleaving
chords: they force the heads to interleave
(`no_collision_heads_interleave`), and `P2.imp_ExtCrossing` forbids exactly that.
So a cross-head EQUALITY must occur at two interleaving chords. -/
theorem no_collision_contradiction (hK : 0 < K) (S : Fin K → Bin)
    (h2L : 2 ≤ L) (hLK : L ≤ K) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) {a b c d : Fin K}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : vtx hK L S a = vtx hK L S b) (hvcd : vtx hK L S c = vtx hK L S d)
    (hI : Interleaved (mkGenome hK S) a b c d)
    (hAC : maxPairStart hK S a b ≠ maxPairStart hK S c d)
    (hAD : maxPairStart hK S a b ≠ maxPairStart hK S d c)
    (hBC : maxPairStart hK S b a ≠ maxPairStart hK S c d)
    (hBD : maxPairStart hK S b a ≠ maxPairStart hK S d c) : False := by
  have hhAB := head_of_head hK S hprim hab
  have hhCD := head_of_head hK S hprim hcd
  have hAB : vtx hK L S (maxPairStart hK S a b) = vtx hK L S (maxPairStart hK S b a) :=
    vtx_maxPairStart hK S h2L hLK hprim hab ((vtx_eq_iff hK S).mp hvab)
  have hCD : vtx hK L S (maxPairStart hK S c d) = vtx hK L S (maxPairStart hK S d c) :=
    vtx_maxPairStart hK S h2L hLK hprim hcd ((vtx_eq_iff hK S).mp hvcd)
  have hneAB := heads_of_one_chord_ne hK S h2L hLK hprim hab ((vtx_eq_iff hK S).mp hvab)
  have hneCD := heads_of_one_chord_ne hK S h2L hLK hprim hcd ((vtx_eq_iff hK S).mp hvcd)
  have hcross : Interleaved (mkGenome hK S)
      (maxPairStart hK S a b) (maxPairStart hK S b a)
      (maxPairStart hK S c d) (maxPairStart hK S d c) :=
    no_collision_heads_interleave hK S h2L hLK hP2 hprim hab hcd hvab hvcd
      hI hAC hAD hBC hBD
  -- `ExtCrossing` concludes the NON-interleaving of the heads of the heads, so
  -- it is refuted by `hIhh`: the heads of the heads are the heads themselves, by
  -- `head_of_head`.
  have hIhh : Interleaved (mkGenome hK S)
      (maxPairStart hK S (maxPairStart hK S a b) (maxPairStart hK S b a))
      (maxPairStart hK S (maxPairStart hK S b a) (maxPairStart hK S a b))
      (maxPairStart hK S (maxPairStart hK S c d) (maxPairStart hK S d c))
      (maxPairStart hK S (maxPairStart hK S d c) (maxPairStart hK S c d)) := by
    convert hcross using 1
    · exact hhAB.1
    · exact hhAB.2
    · exact hhCD.1
    · exact hhCD.2
  -- `P2.imp_ExtCrossing` at the head pair `(A, B)`, `(C, D)`, refuted by `hIhh`.
  exact ((P2.imp_ExtCrossing hK h2L hLK S hprim hP2
    (maxPairStart hK S a b) (maxPairStart hK S b a)
    (maxPairStart hK S c d) (maxPairStart hK S d c)
    hneAB hneCD hAB hCD hcross).1) hIhh

end AssemblyP1.Issue94NoCollision

/-!
# `Issue94NoCollision`: the no-collision half of the `CrossingPairsCoalesce` case split

The human pointer of 2026-09-28 21:33:33Z / 21:34:57Z on board issue 94 splits
`BBTCrossingCoalesce.CrossingPairsCoalesce` on whether a **cross-head equality**
holds.  This file is the other half: assuming all four cross-head **inequalities**,
it proves the heads interleave (`no_collision_heads_interleave`) and closes by
`P2.imp_ExtCrossing` (`no_collision_contradiction`).

It is proved **independently** of any cross-head-equality helper: the only imports
are `AssemblyP1.Issue94Step2Path` and `AssemblyP1.Issue94Step5Heads`.
-/

