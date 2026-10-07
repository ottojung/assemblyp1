import AssemblyP1.Issue89GapMap

/-!
# The corrected **iterated** slide statement, on the decidable `InterK` layer

This module discharges the one ingredient that board issue 94's gap map
(`AssemblyP1.Issue89GapMap`) identified as the single genuinely new one: the
**iterated** form of the §5 step-4 slide lemma.

The library statement `BBTCrossingCoalesce.SlidePreservesInterleaved` is
**false** (`Issue89GapMap.SlidePreservesInterleaved_refuted`): it slides the
wrong pair.  The corrected shape slides the *second* pair `c, d` while `a, b`
stay fixed, and the gap map could only support it with **bounded** exhaustive
evidence (`AllSlid_6`, `AllSlid_8_10`, `AllSlid8_8_10`).

Here the corrected shape is stated on the **decidable `InterK` layer** --- no
word, no `vtx`, no repeat theory --- and **proved**, by induction on the
number of steps, for every `K` and every `n ≤ K`.  The proof is a plain
`ℕ`-induction on the slide count whose step is a single cyclic-order lemma
about the open arc: *a point can enter or leave the open arc `(a, b)` in one
step only by landing on `a` or `b`*, which is exactly what the guards exclude.

Section 5 adds finite checks, and they are the only finitely-checked material
in the file: they show that the **intermediate guards are necessary** (the
endpoint-only form is false at `K = 6, 8, 10`), that the theorem is **not
vacuous**, and that the proved statement agrees with exhaustive search at
`K = 6, 8`.

Two elementary `ℕ`-arithmetic facts about `%` are re-proved here rather than
reused from `BBTUniqueEulerian`, because the library copies live inside a
section with a word parameter `S` that this layer does not have.
-/

namespace AssemblyP1.Issue94IterSlide

open AssemblyP1
open AssemblyP1.SourceFaithfulIs
open AssemblyP1.BBTChords
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.Issue89GapMap

variable {K : ℕ}

/-! ## 0. The two moves, and the elementary arithmetic of the circle

`prev hK x` is the library's one-step backward rotation (`BBTChords.prevPos`),
and `slide hK n x` is the `n`-step backward rotation `rotAdd (K - n) x` that
`Issue89GapMap.Step4_slide_iterates` is written with.  `slide 0 = id`, and
`slide (n+1) = prev ∘ slide n` when `n + 1 ≤ K`. -/

/-- One step to the left: the `K-1` rotation. -/
def prev (hK : 0 < K) (x : Fin K) : Fin K := rotAdd hK (K - 1) x

/-- The `n`-step slide to the left, i.e. the `K - n` rotation. -/
def slide (hK : 0 < K) (n : ℕ) (x : Fin K) : Fin K := rotAdd hK (K - n) x

/-- `(x + y) % K = (x % K + y) % K`, the modular rearrangement used throughout.
This is `BBTUniqueEulerian.mod_add_shl` re-proved without its word parameter. -/
theorem mod_add_mod (hK : 0 < K) (x y : ℕ) : (x + y) % K = (x % K + y) % K := by
  have _ := hK
  have hh := Nat.div_add_mod x K
  have h3 : x + y = (x % K + y) + K * (x / K) := by omega
  rw [h3, Nat.add_mul_mod_self_left]

/-- Shifts compose: `rotAdd s (rotAdd t x) = rotAdd (s + t) x`.  This is
`BBTUniqueEulerian.rotAdd_add`, re-proved without its word parameter. -/
theorem rotAdd_comp (hK : 0 < K) (s t : ℕ) (x : Fin K) :
    rotAdd hK s (rotAdd hK t x) = rotAdd hK (s + t) x := by
  apply Fin.ext
  show ((x.val + t) % K + s) % K = (x.val + (s + t)) % K
  calc ((x.val + t) % K + s) % K = (x.val + t + s) % K := (mod_add_mod hK (x.val + t) s).symm
    _ = (x.val + (s + t)) % K := by congr 1; omega

/-- A whole turn is the identity.  This is `BBTUniqueEulerian.rotAdd_full`,
re-proved without its word parameter. -/
theorem rotAdd_K (hK : 0 < K) (x : Fin K) : rotAdd hK K x = x := by
  apply Fin.ext
  show (x.val + K) % K = x.val
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]

/-- `slide 0 x = x`. -/
@[simp] theorem slide_zero (hK : 0 < K) (x : Fin K) : slide hK 0 x = x := by
  show rotAdd hK (K - 0) x = x
  rw [Nat.sub_zero]
  exact rotAdd_K hK x

/-- One slide step is one `prev`. -/
theorem slide_succ (hK : 0 < K) (n : ℕ) (x : Fin K) (hn1 : n + 1 ≤ K) :
    slide hK (n + 1) x = prev hK (slide hK n x) := by
  have _ := hK
  have hxl : x.val < K := x.isLt
  have hssub : K - 1 - n = (K - n) - 1 := by
    have h1 : K - 1 - n = K - (1 + n) := Nat.sub_sub K 1 n
    have h2 : K - (1 + n) = K - (n + 1) := by omega
    rw [h1, h2]
    exact (Nat.sub_succ K n).symm
  have hsub : K - 1 + (K - n) = (K - 1 - n) + K := by
    have h2 : K - 1 - n = (K - n) - 1 := hssub
    omega
  have hmod : (x.val + (K - 1 + (K - n))) % K = (x.val + (K - 1 - n)) % K := by
    have heq : x.val + (K - 1 + (K - n)) = (x.val + (K - 1 - n)) + K := by omega
    rw [heq, Nat.add_mod_right]
  have esub : K - (n + 1) = K - 1 - n := by
    have h2 : K - (n + 1) = (K - n) - 1 := Nat.sub_succ K n
    omega
  show rotAdd hK (K - (n + 1)) x = rotAdd hK (K - 1) (rotAdd hK (K - n) x)
  rw [esub, rotAdd_comp]
  apply Fin.ext
  simp only [rotAdd, Fin.val_mk]
  rw [hmod]

/-- The predecessor of the coordinate `0`. -/
theorem mod_pred_zero (hK : 0 < K) : (K - 1) % K = K - 1 := by
  have hlt : K - 1 < K := by omega
  exact Nat.mod_eq_of_lt hlt

/-- The predecessor of a nonzero coordinate `< K`. -/
theorem mod_pred_pos {K : ℕ} {u : ℕ} (hu : u < K) (h0 : 0 < u) :
    (u + K - 1) % K = u - 1 := by
  have hlt : u - 1 < K := by omega
  have heq : u + K - 1 = (u - 1) + K := by omega
  rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]

/-- A one-step backward rotation of the coordinate `0` wraps around to `K-1`. -/
theorem prev_val_zero (hK : 0 < K) (x : Fin K) (h0 : x.val = 0) :
    (prev hK x).val = K - 1 := by
  simp only [prev, rotAdd, Fin.val_mk, h0, Nat.zero_add]
  exact mod_pred_zero hK

/-- A one-step backward rotation of a nonzero coordinate decrements it. -/
theorem prev_val_pos (hK : 0 < K) (x : Fin K) (h0 : 0 < x.val) :
    (prev hK x).val = x.val - 1 := by
  have hx : x.val + (K - 1) = x.val + K - 1 := by omega
  simp only [prev, rotAdd, Fin.val_mk]
  rw [hx]
  exact mod_pred_pos (by omega) h0

/-- `rotAdd` by a shift of size `< K` is injective. -/
theorem rotAdd_inj (hK : 0 < K) {x y : Fin K} {s : ℕ} (hs : s < K)
    (h : rotAdd hK s x = rotAdd hK s y) : x = y := by
  have hv := congrArg Fin.val h
  have hv' : (x.val + s) % K = (y.val + s) % K := by
    simpa only [rotAdd, Fin.val_mk] using hv
  have key : ∀ u : ℕ, u < K →
      (u + s) % K = if u + s < K then u + s else u + s - K := by
    intro u hu
    by_cases h : u + s < K
    · rw [ite_eq_left h]; exact Nat.mod_eq_of_lt h
    · have h1' : (u + s) % K = (u + s - K) % K := by
        have e1 : (u + s - K) + K = u + s := by omega
        calc (u + s) % K = ((u + s - K) + K) % K := by rw [e1]
          _ = (u + s - K) % K := Nat.add_mod_right _ _
      rw [ite_eq_right h, h1']
      exact Nat.mod_eq_of_lt (by omega : u + s - K < K)
  rw [key x.val x.isLt, key y.val y.isLt] at hv'
  by_cases hx : x.val + s < K <;> by_cases hy : y.val + s < K
  · rw [ite_eq_left hx, ite_eq_left hy] at hv'
    exact Fin.ext (by omega)
  · rw [ite_eq_left hx, ite_eq_right hy] at hv'
    exact Fin.ext (by omega)
  · rw [ite_eq_right hx, ite_eq_left hy] at hv'
    exact Fin.ext (by omega)
  · rw [ite_eq_right hx, ite_eq_right hy] at hv'
    exact Fin.ext (by omega)

/-- `InterK` and the library's `InterleavedStarts` are the same predicate on the
same coordinate; this is what lets the layer below be stated on `InterK` and
proved with the library's arc predicates. -/
theorem interK_iff (hK : 0 < K) [NeZero K] (a b c d : Fin K) :
    InterK K a b c d ↔ InterleavedStarts hK a b c d := by
  unfold InterK InterleavedStarts FourDistinctStarts InArc
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2.1⟩, h2.2.2.2.2.2⟩
  · rintro ⟨hd, ha⟩
    exact ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2, ha⟩

/-! ## 1. The arc, in coordinates

The open arc from `a` to `b` is either the *interval* `(a, b)` (when `a < b`) or
the *wrap-around* set `{p : a < p} ∪ {p : p < b}` (when `b < a`).  This
splitting is the whole content of the geometry of the layer. -/

/-- The arc coordinate of `P` as seen from `A`, without any `%`. -/
theorem mod_sub (hK : 0 < K) (A P : ℕ) (hA : A < K) (hP : P < K) :
    (P + K - A) % K = if A ≤ P then P - A else P + K - A := by
  by_cases h : A ≤ P
  · have heq : P + K - A = (P - A) + K := by omega
    rw [ite_eq_left h, heq, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : P - A < K)]
  · rw [ite_eq_right h]
    exact Nat.mod_eq_of_lt (by omega)

/-- `InArc a b p` in coordinates: an interval, or a wrap-around set. -/
theorem inArc_val (hK : 0 < K) {a b p : Fin K} :
    InArc hK a b p ↔
      (a.val < b.val ∧ a.val < p.val ∧ p.val < b.val) ∨
        (b.val < a.val ∧ (a.val < p.val ∨ p.val < b.val)) := by
  have _ := hK
  unfold InArc
  rw [mod_sub hK a.val p.val a.isLt p.isLt, mod_sub hK a.val b.val a.isLt b.isLt]
  by_cases h1 : a.val ≤ p.val
  · by_cases h2 : a.val ≤ b.val
    · rw [ite_eq_left h1, ite_eq_left h2]
      constructor
      · intro h
        exact Or.inl ⟨by omega, by omega, by omega⟩
      · intro h
        exact ⟨by omega, by omega⟩
    · rw [ite_eq_left h1, ite_eq_right h2]
      constructor
      · intro h
        exact Or.inr ⟨by omega, Or.inl (by omega)⟩
      · intro h
        omega
  · by_cases h2 : a.val ≤ b.val
    · rw [ite_eq_right h1, ite_eq_left h2]
      constructor
      · intro h
        omega
      · intro h
        omega
    · rw [ite_eq_right h1, ite_eq_right h2]
      constructor
      · intro h
        exact Or.inr ⟨by omega, Or.inr (by omega)⟩
      · intro h
        exact ⟨by omega, by omega⟩

/-! ## 2. One slide step preserves arc membership

The whole of §5 step 4 is the following.  If `p` is strictly inside the open
arc `(a, b)` then the point one step to its left is still inside the arc,
*unless it has landed on `a`*, which is exactly the collision the guards
exclude.  So for `p ∉ {a, b}` with `prev p ≠ a`, arc membership of `p` and of
`prev p` is the same; and interleaving --- "exactly one of `c, d` lies in the
arc" --- therefore survives the step. -/

/-- **Arc membership is invariant under one backward step, up to landing on
`a`.**  This is the whole geometric content of the slide lemma: the *only*
way a point can enter or leave the open arc in one step is to collide with
`a` or `b`. -/
theorem inArc_prev_iff (hK : 0 < K) {a b p : Fin K} (hpa : p ≠ a) (hpb : p ≠ b)
    (hg : prev hK p ≠ a) : InArc hK a b p ↔ InArc hK a b (prev hK p) := by
  have hA := a.isLt
  have hB := b.isLt
  have hP := p.isLt
  have hneA : a.val ≠ p.val := fun e => hpa (Fin.ext e.symm)
  have hneB : b.val ≠ p.val := fun e => hpb (Fin.ext e.symm)
  have hgne : ¬ ((prev hK p).val = a.val) := fun e => hg (Fin.ext e)
  rw [inArc_val, inArc_val]
  by_cases h0 : p.val = 0
  · rw [prev_val_zero hK p h0]
    have hA0 : 0 < a.val := by omega
    have hB0 : 0 < b.val := by omega
    have hg' : ¬ (K - 1 = a.val) := by
      simpa [prev_val_zero hK p h0] using hgne
    by_cases hab : a.val < b.val
    · constructor
      · intro h
        rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2 | h3⟩ <;> omega
      · intro h
        rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2 | h3⟩ <;> omega
    · constructor
      · intro h
        rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2 | h3⟩
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · exact Or.inr ⟨h1, Or.inl (by omega)⟩
      · intro h
        rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2 | h3⟩
        · exact (by omega : False).elim
        · exact Or.inr ⟨h1, Or.inr (by omega)⟩
        · exact (by omega : False).elim
  · rw [prev_val_pos hK p (by omega)]
    have hg' : ¬ (p.val - 1 = a.val) := by
      simpa [prev_val_pos hK p (by omega)] using hgne
    by_cases hab : a.val < b.val
    · constructor
      · intro h
        rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2 | h3⟩
        · exact Or.inl ⟨by omega, by omega, by omega⟩
        · exact (Nat.lt_asymm h1 hab).elim
        · exact (Nat.lt_asymm h1 hab).elim
      · intro h
        rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2 | h3⟩
        · exact Or.inl ⟨by omega, by omega⟩
        · exact (Nat.lt_asymm h1 hab).elim
        · exact (Nat.lt_asymm h1 hab).elim
    · constructor
      · intro h
        rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2 | h3⟩
        · exact Or.inl ⟨by omega, by omega, by omega⟩
        · by_cases hq : p.val - 1 < b.val
          · exact Or.inr ⟨h1, Or.inr (by omega)⟩
          · exact Or.inr ⟨h1, Or.inl (by omega)⟩
        · exact Or.inr ⟨h1, Or.inr (by omega)⟩
      · intro h
        rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2 | h3⟩
        · exact Or.inl ⟨by omega, by omega⟩
        · exact Or.inr ⟨h1, Or.inl (by omega)⟩
        · by_cases hq : p.val < b.val
          · exact Or.inr ⟨h1, Or.inr (by omega)⟩
          · exact Or.inr ⟨h1, Or.inl (by omega)⟩

/-- **The corrected one-step slide lemma.**  If `{a, b}` and `{c, d}`
interleave, and the slid pair `c, d` collides with neither `a` nor `b`, then
`{a, b}` and the slid pair still interleave.  This is the `Slid` shape of
`Issue89GapMap` (§1) *proved* for every `K` and every quadruple, instead of
checked for `K ≤ 10`; note it is proved with only the **four** stated guards,
not the eight. -/
theorem slide_one (hK : 0 < K) [NeZero K] (a b c d : Fin K)
    (h : InterK K a b c d)
    (g1 : prev hK c ≠ a) (g2 : prev hK c ≠ b) (g3 : prev hK d ≠ a)
    (g4 : prev hK d ≠ b) :
    InterK K a b (prev hK c) (prev hK d) := by
  have hI : InterleavedStarts hK a b c d := (interK_iff hK a b c d).mp h
  rcases hI.1 with ⟨hab, hac, had, hbc, hbd, hcd⟩
  have h1 : InArc hK a b c ↔ InArc hK a b (prev hK c) :=
    inArc_prev_iff hK hac.symm hbc.symm g1
  have h2 : InArc hK a b d ↔ InArc hK a b (prev hK d) :=
    inArc_prev_iff hK had.symm hbd.symm g3
  have hI' : InterleavedStarts hK a b (prev hK c) (prev hK d) := by
    refine ⟨?_, ?_⟩
    · refine ⟨hab, fun e => g1 e.symm, fun e => g3 e.symm, fun e => g2 e.symm,
        fun e => g4 e.symm, ?_⟩
      intro e
      exact hcd (rotAdd_inj hK (by omega) e)
    · constructor
      · exact fun hc' hd' => (hI.2.mp (h1.mpr hc')) (h2.mpr hd')
      · exact fun hd' => h1.mp (hI.2.mpr (fun hd => hd' (h2.mp hd)))
  exact (interK_iff hK (a) (b) (prev hK c) (prev hK d)).mpr hI'

/-! ## 3. The iterated statement, proved by induction on the number of steps

`SlideGuards a b c d j` is the collision condition on the pair `c, d` after
`j` slide steps; `IterSlide` is the corrected §5 step-4 statement on the `InterK`
layer.  Note that `slide hK n x` is *literally* the `rotAdd hK (K - n) x` that
`Issue89GapMap.Step4_slide_iterates` is written with, so this is that
statement's cyclic content, in the same coordinates. -/

/-- The collision guards on the pair `c, d` after `j` slide steps.  This
`Prop` is **decidable**, like everything else on this layer. -/
def SlideGuards (hK : 0 < K) (a b c d : Fin K) (j : ℕ) : Prop :=
  slide hK j c ≠ a ∧ slide hK j c ≠ b ∧ slide hK j d ≠ a ∧ slide hK j d ≠ b

instance instSlideGuards (hK : 0 < K) (a b c d : Fin K) (j : ℕ) :
    Decidable (SlideGuards hK a b c d j) := by
  unfold SlideGuards; infer_instance

/-- **The corrected iterated slide statement, on the decidable `InterK` layer.**

`{a, b}` and `{c, d}` interleave; slide `c, d` to the left `n` steps, with no
collision with `a` or `b` at any intermediate `j ≤ n`; then `{a, b}` and the
slid pair still interleave.  No word, no `vtx`, no repeat theory: this is the
whole of the cyclic content of §5 step 4, and it is **proved** below for every
`K` and every `n ≤ K`, by induction on `n`. -/
def IterSlide (hK : 0 < K) [NeZero K] (a b c d : Fin K) : Prop :=
  InterK K a b c d →
    ∀ n : ℕ, n ≤ K →
      (∀ j : ℕ, j ≤ n → SlideGuards hK a b c d j) →
      InterK K a b (slide hK n c) (slide hK n d)

/-- **The iterated slide, by induction on `n`.**  The induction step is the
one-step lemma `slide_one` applied at the `n`-th position, with the guards at
`j = n + 1`.  This is the result the previous front's §6 recommended. -/
theorem slide_iter (hK : 0 < K) [NeZero K] (a b c d : Fin K) (h : InterK K a b c d) :
    ∀ n : ℕ, n ≤ K → (∀ j : ℕ, j ≤ n → SlideGuards hK a b c d j) →
      InterK K a b (slide hK n c) (slide hK n d) := by
  intro n
  induction n with
  | zero =>
      intro _ _
      rw [slide_zero, slide_zero]
      exact h
  | succ n ih =>
      intro hn hg
      have hstep : InterK K a b (slide hK n c) (slide hK n d) :=
        ih (by omega) (fun j hj => hg j (by omega))
      have hgn := hg (n + 1) (Nat.le_refl (n + 1))
      have hres : InterK K a b (prev hK (slide hK n c)) (prev hK (slide hK n d)) :=
        slide_one hK a b (slide hK n c) (slide hK n d) hstep
          (by rw [← slide_succ hK n _ hn]; exact hgn.1)
          (by rw [← slide_succ hK n _ hn]; exact hgn.2.1)
          (by rw [← slide_succ hK n _ hn]; exact hgn.2.2.1)
          (by rw [← slide_succ hK n _ hn]; exact hgn.2.2.2)
      rw [slide_succ hK n c hn, slide_succ hK n d hn]
      exact hres

/-- The headline: **the corrected iterated slide statement holds**, for every
circle size `K` and every slide count `n ≤ K`.  This is an inhabitant of
`IterSlide`; it is the statement `Issue89GapMap.Step4_slide_iterates` needs
for its cyclic content, in the same `rotAdd (K - n)` coordinates. -/
theorem IterSlide_of_InterK (hK : 0 < K) [NeZero K] (a b c d : Fin K)
    (h : InterK K a b c d) : IterSlide hK a b c d :=
  fun _ n hn hg => slide_iter hK a b c d h n hn hg

/-! ## 4. The same statement with the library's own coordinates

`InterleavedStarts` (`BBTChords`) and the word-level `Interleaved` of
`BBTCrossingCoalesce` are the same predicate on the same circle, so the
result above transfers verbatim to the statements the §5 plan actually
invokes.  This is what a later front needs in order to close step 4: the
`vtx` hypotheses and the `pairBack` side condition are *not* touched here. -/

/-- `Interleaved` on a `Genome` of length `K` is `InterleavedStarts` on `Fin K`. -/
theorem interleaved_iff (hK : 0 < K) {α : Type} {S : Fin K → α}
    (a b c d : Fin K) :
    Interleaved (mkGenome hK S) a b c d ↔ InterleavedStarts hK a b c d := by
  unfold Interleaved FourDistinct InOpenArc InterleavedStarts FourDistinctStarts InArc
  exact Iff.rfl

/-- **The cyclic content of `Issue89GapMap.Step4_slide_iterates`, proved.**
The pair `c, d` may be slid `t` steps down its backward list, keeping its
interleaving with `a, b`, provided no intermediate position collides with
`a` or `b`.  This is a `Prop` with an **inhabitant** --- in contrast with
`Step4_slide_iterates` itself, which additionally carries the `vtx`
("still a chord") and `pairBack` side conditions and is untouched here.

Note that this statement needs only `t ≤ K`, which is *weaker* than the
`t ≤ pairBack c d` of `Step4_slide_iterates`: `pairBack_lt_G`
(`P2RepeatResidual`:654) gives `pairBack c d < G`, so a later front may
instantiate this at any `t ≤ pairBack c d` without further work.  The `j = 0`
instance of the guard hypothesis is exactly part of `InterK`'s `FourDistinct`,
so nothing is lost. -/
def Step4_slide_iterates_cyclic (hK : 0 < K) [NeZero K] (a b c d : Fin K) : Prop :=
  InterK K a b c d →
    ∀ t : ℕ, t ≤ K →
      (∀ j : ℕ, j ≤ t → SlideGuards hK a b c d j) →
      InterK K a b (rotAdd hK (K - t) c) (rotAdd hK (K - t) d)

/-- The inhabitant of `Step4_slide_iterates_cyclic`. -/
theorem step4_slide_iterates_cyclic (hK : 0 < K) [NeZero K] (a b c d : Fin K)
    (h : InterK K a b c d) : Step4_slide_iterates_cyclic hK a b c d :=
  fun _ t ht hg => slide_iter hK a b c d h t ht hg

/-- The same statement in the library's word-level notation, obtained by
transport along `interleaved_iff`.  No hypothesis about the word `S` is used
or needed: the result is purely about the circle. -/
theorem step4_slide_iterates_word (hK : 0 < K) [NeZero K] {α : Type} {S : Fin K → α}
    (a b c d : Fin K) (hI : Interleaved (mkGenome hK S) a b c d) (t : ℕ) (ht : t ≤ K)
    (hg : ∀ j : ℕ, j ≤ t → SlideGuards hK a b c d j) :
    Interleaved (mkGenome hK S) a b (rotAdd hK (K - t) c) (rotAdd hK (K - t) d) := by
  have hIK : InterK K a b c d := (interK_iff hK a b c d).mpr ((interleaved_iff hK a b c d).mp hI)
  have hres : InterK K a b (rotAdd hK (K - t) c) (rotAdd hK (K - t) d) := by
    exact slide_iter hK a b c d hIK t ht hg
  have hIS : InterleavedStarts hK a b (rotAdd hK (K - t) c) (rotAdd hK (K - t) d) :=
    (interK_iff hK a b (rotAdd hK (K - t) c) (rotAdd hK (K - t) d)).mp hres
  exact (interleaved_iff hK (S := S) a b (rotAdd hK (K - t) c) (rotAdd hK (K - t) d)).mpr hIS

/-! ## 5. Finite cross-checks (bounded evidence, and one refutation)

These are *not* the proof --- §3 is --- but they record three things worth
knowing, all kernel-checked:

* the intermediate guards of the iterated form are **necessary**: the same
  statement with the guards only at the endpoint `j = n` is **false** at
  `K = 6, 8, 10`, so the iterated statement really is a *different proposition*
  from the one-step `Slid` shape that `Issue89GapMap` searched;
* the hypotheses of `slide_iter` are satisfiable at `K = 6, 10`, so the
  theorem is not vacuous;
* the proved statement agrees with exhaustive search at `K = 6, 8`.

Note also that at `K = 3` the hypothesis `InterK` is *unsatisfiable* (four
pairwise distinct endpoints need four positions), so the previous front's
`AllStated_small` check at `K = 3` was vacuous. -/

/-- The iterated statement with the guards only at the endpoint `j = n`: the
"one big step" form, with no intermediate guards. -/
def EndpointIter (K : ℕ) (hK : 0 < K) [NeZero K] : Prop :=
  ∀ a b c d : Fin K, ∀ n ∈ Finset.range (K + 1), InterK K a b c d →
    SlideGuards hK a b c d n → InterK K a b (slide hK n c) (slide hK n d)

instance instEndpointIter (K : ℕ) (hK : 0 < K) [NeZero K] :
    Decidable (EndpointIter K hK) := by
  unfold EndpointIter SlideGuards; infer_instance

/-- The same statement with the guards at **every** intermediate `j ≤ n`, in
the form in which it is decidable by exhaustive search. -/
def FullIter (K : ℕ) (hK : 0 < K) [NeZero K] : Prop :=
  ∀ a b c d : Fin K, ∀ n ∈ Finset.range (K + 1), InterK K a b c d →
    (∀ j ∈ Finset.range (K + 1), j ≤ n → SlideGuards hK a b c d j) →
    InterK K a b (slide hK n c) (slide hK n d)

instance instFullIter (K : ℕ) (hK : 0 < K) [NeZero K] :
    Decidable (FullIter K hK) := by
  unfold FullIter SlideGuards; infer_instance

/-- The guards are **not** redundant: the endpoint-only form fails at `K = 6`.
This is the reason the iterated form is not the one-step form. -/
theorem not_EndpointIter_6 : ¬ EndpointIter 6 (by norm_num) := by decide

/-- Likewise at `K = 8` and `K = 10`. -/
theorem not_EndpointIter_8_10 :
    ¬ EndpointIter 8 (by norm_num) ∧ ¬ EndpointIter 10 (by norm_num) :=
  ⟨by decide, by decide⟩

/-- The guarded (iterated) form, exhaustively, at `K = 6` and `K = 8`.  This
agrees with `slide_iter`; it is a cross-check of the *statement*, not a
substitute for the proof. -/
theorem FullIter_6_8 : FullIter 6 (by norm_num) ∧ FullIter 8 (by norm_num) :=
  ⟨by decide, by decide⟩

/-- `InterK` is satisfiable at `K = 4` and unsatisfiable at `K = 3` (four
pairwise distinct endpoints need four positions). -/
theorem interK_sat : (∃ a b c d : Fin 4, InterK 4 a b c d) ∧ ¬(∃ a b c d : Fin 3, InterK 3 a b c d) :=
  ⟨by decide, by decide⟩

/-- **The hypotheses of `slide_iter` are satisfiable at `K = 6` and `K = 10`**:
there are two interleaving chords whose slid pair is still collision-free two
steps later and still interleaved.  So `slide_iter` is not vacuous. -/
def NonVacuous (K : ℕ) (hK : 0 < K) [NeZero K] : Prop :=
  ∃ a b c d : Fin K, InterK K a b c d ∧ SlideGuards hK a b c d 2 ∧
    InterK K a b (slide hK 2 c) (slide hK 2 d)

instance instNonVacuous (K : ℕ) (hK : 0 < K) [NeZero K] :
    Decidable (NonVacuous K hK) := by
  unfold NonVacuous SlideGuards; infer_instance

theorem NonVacuous_6_10 : NonVacuous 6 (by norm_num) ∧ NonVacuous 10 (by norm_num) :=
  ⟨by decide, by decide⟩

end AssemblyP1.Issue94IterSlide

