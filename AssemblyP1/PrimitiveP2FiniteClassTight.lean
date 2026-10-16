import AssemblyP1.PrimitiveP2FiniteClass

/-!
# Tightness of the primitive-P2 length bound at `K = 1` (issue #281)

`AssemblyP1.PrimitiveP2FiniteClass.primitive_P2_len_le` proves that every
primitive P2-admissible circular genome over a finite alphabet `α` with
`q = |α|` and read length `L ≥ 2` has length

    G ≤ 2 * q ^ (L - 1).

That module also exhibits the single binary witness `1100` attaining the bound
at `q = 2`, `L = 2`. This module shows the bound is attained for **every**
alphabet size `q ≥ 2` at `K = L - 1 = 1`: the "doubled alphabet" word

    0 0 1 1 2 2 ... (q-1) (q-1)

of length `2 * q` is primitive and satisfies P2 at `L = 2`. So `2 * q ^ K` is
not merely an upper estimate at `K = 1`; it is exactly the largest admissible
length there, for every `q ≥ 2`.

The word is built from an arbitrary equivalence `α ≃ Fin q`
(`Fintype.equivFin`), so no ordering or computability of `α` is assumed. Both
P2 clauses at `L = 2` are checked on the source-faithful definitions:

* the **triple-repeat clause** forbids maximal triple repeats of length
  `≥ L - 1 = 1`. Every symbol of the doubled word occurs exactly twice, so no
  three starts can share even a length-one window; there is no triple repeat of
  any length (`no_triple`).
* the **interleaved-pair clause** forbids interleaved maximal repeat pairs.
  Here the two-sided **maximality** of the source repeat matters: every maximal
  repeat of the doubled word is an adjacent equal pair `(2k, 2k+1)`, whose two
  starts are consecutive. A consecutive ordered pair of starts spans either the
  empty open arc or the whole circle, so its two selected `InOpenArc` truth
  values agree and the alternation condition
  `(InOpenArc a b c) ↔ ¬ InOpenArc a b d` is false (`not_interleaved`). This is
  exactly the point the issue raises: P2 is a statement about *maximal*
  repeats, and the counting/attainment argument must respect the maximality
  definition rather than the mere absence of equal windows.

Everything here is kernel-checked with no new axioms.
-/

namespace AssemblyP1.PrimitiveP2FiniteClassTight

open AssemblyP1
open AssemblyP1.SourceFaithfulIs
open AssemblyP1.PopulationReduction
open scoped Classical

variable {α : Type} [DecidableEq α] [Fintype α]

/-- The "doubled alphabet" circular word `0 0 1 1 ... (q-1)(q-1)`, where the
symbol at position `i` is the `(i / 2)`-th element of `α` under an arbitrary
enumeration `α ≃ Fin q`. Its length is `2 * q`. -/
noncomputable def pairWord : Fin (2 * Fintype.card α) → α :=
  fun i => (Fintype.equivFin α).symm
    ⟨i.val / 2, Nat.div_lt_of_lt_mul (by omega)⟩

/-! ## Basic facts about `pairWord` -/

omit [DecidableEq α] in
/-- `pairWord` sends two positions to the same symbol exactly when they have
the same index quotient by two, i.e. when they are `2k` and `2k+1`. -/
theorem pairWord_eq_iff (i j : Fin (2 * Fintype.card α)) :
    pairWord (α := α) i = pairWord (α := α) j ↔ i.val / 2 = j.val / 2 := by
  constructor
  · intro h
    have := (Fintype.equivFin α).symm.injective h
    exact congrArg Fin.val this
  · intro h
    unfold pairWord
    exact congrArg (Fintype.equivFin α).symm (Fin.ext h)

/-- Coordinate formula for a `pairWord` window. -/
theorem window_val (hG : 0 < 2 * Fintype.card α) (e : ℕ)
    (i : Fin (2 * Fintype.card α)) (d : Fin e) :
    (mkGenome hG (pairWord (α := α))).window e i d =
      pairWord (α := α)
        ⟨(i.val + d.val) % (2 * Fintype.card α), Nat.mod_lt _ hG⟩ := rfl

/-- The first coordinate of a `pairWord` window is `pairWord` of the start. -/
theorem window_zero (hG : 0 < 2 * Fintype.card α) (e : ℕ) (he : 0 < e)
    (i : Fin (2 * Fintype.card α)) :
    (mkGenome hG (pairWord (α := α))).window e i ⟨0, he⟩ = pairWord (α := α) i := by
  rw [window_val]
  apply congrArg (pairWord (α := α))
  apply Fin.ext
  simp [Nat.mod_eq_of_lt i.isLt]

omit [DecidableEq α] in
/-- **No three distinct starts share a `pairWord` value.** The value of
`pairWord` is constant on pairs `{2k, 2k+1}`, so among any three positions two
have the same index. -/
theorem pairWord_fiber_pair {a b c : Fin (2 * Fintype.card α)}
    (hab : pairWord (α := α) a = pairWord (α := α) b)
    (hac : pairWord (α := α) a = pairWord (α := α) c) :
    a = b ∨ a = c ∨ b = c := by
  have h1 : a.val / 2 = b.val / 2 := by
    have := congrArg Fin.val ((Fintype.equivFin α).symm.injective hab)
    simpa using this
  have h2 : a.val / 2 = c.val / 2 := by
    have := congrArg Fin.val ((Fintype.equivFin α).symm.injective hac)
    simpa using this
  have ha' : a.val = 2 * (a.val / 2) + a.val % 2 := by
    have := Nat.div_add_mod a.val 2; omega
  have hb' : b.val = 2 * (b.val / 2) + b.val % 2 := by
    have := Nat.div_add_mod b.val 2; omega
  have hc' : c.val = 2 * (c.val / 2) + c.val % 2 := by
    have := Nat.div_add_mod c.val 2; omega
  rcases (show a.val % 2 = 0 ∨ a.val % 2 = 1 by omega) with ha0 | ha1 <;>
  rcases (show b.val % 2 = 0 ∨ b.val % 2 = 1 by omega) with hb0 | hb1 <;>
  rcases (show c.val % 2 = 0 ∨ c.val % 2 = 1 by omega) with hc0 | hc1
  all_goals (first
    | (left; exact Fin.ext (by omega))
    | (right; left; exact Fin.ext (by omega))
    | (right; right; exact Fin.ext (by omega)))

/-- **No triple repeat of any length.** A triple repeat needs three distinct
starts agreeing on a nonempty window, hence three distinct starts with equal
first coordinate — impossible for `pairWord`. -/
theorem no_triple (hG : 0 < 2 * Fintype.card α) {e : ℕ}
    {a b c : Fin (2 * Fintype.card α)}
    (ht : (mkGenome hG (pairWord (α := α))).IsTripleRepeat e a b c) : False := by
  obtain ⟨he, _heG, hab, hac, hbc, hagab, hagac, _hagbc, _hpre, _hfol⟩ := ht
  have h0ab := hagab ⟨0, by omega⟩
  have h0ac := hagac ⟨0, by omega⟩
  rw [window_zero hG e (by omega) a, window_zero hG e (by omega) b] at h0ab
  rw [window_zero hG e (by omega) a, window_zero hG e (by omega) c] at h0ac
  rcases pairWord_fiber_pair h0ab h0ac with h | h | h
  · exact hab h
  · exact hac h
  · exact hbc h

/-! ## Injectivity of the length-two window map -/

/-- If two positions `a, b` of `Fin (2q)` have the same `pairWord` value and
the same `pairWord` value one step ahead, then `a = b`. -/
theorem div2_next_eq {a b card : ℕ} (hq : 2 ≤ card)
    (ha : a < 2 * card) (_hb : b < 2 * card)
    (h1 : a / 2 = b / 2)
    (h2 : ((a + 1) % (2 * card)) / 2 = ((b + 1) % (2 * card)) / 2) : a = b := by
  have next_div2_ne : ∀ k : ℕ, 2 * k + 1 < 2 * card →
      ((2 * k + 1) % (2 * card)) / 2 ≠ ((2 * k + 2) % (2 * card)) / 2 := by
    intro k hk hcon
    have h1' : (2 * k + 1) % (2 * card) = 2 * k + 1 := Nat.mod_eq_of_lt hk
    have h2le : 2 * k + 2 ≤ 2 * card := by omega
    rcases lt_or_eq_of_le h2le with hlt | heq
    · have h2' : (2 * k + 2) % (2 * card) = 2 * k + 2 := Nat.mod_eq_of_lt hlt
      rw [h1', h2'] at hcon
      omega
    · have h2' : (2 * k + 2) % (2 * card) = 0 := by rw [heq, Nat.mod_self]
      rw [h1', h2'] at hcon
      have hk0 : k = 0 := by omega
      subst hk0
      have : card = 1 := by omega
      omega
  have ha' : a = 2 * (a / 2) + a % 2 := by have := Nat.div_add_mod a 2; omega
  have hb' : b = 2 * (b / 2) + b % 2 := by have := Nat.div_add_mod b 2; omega
  rcases (show a % 2 = 0 ∨ a % 2 = 1 by omega) with ha0 | ha1 <;>
  rcases (show b % 2 = 0 ∨ b % 2 = 1 by omega) with hb0 | hb1
  · omega
  · exfalso
    have e1 : a + 1 = 2 * (b / 2) + 1 := by omega
    have e2 : b + 1 = 2 * (b / 2) + 2 := by omega
    have h2' : ((2 * (b / 2) + 1) % (2 * card)) / 2 =
        ((2 * (b / 2) + 2) % (2 * card)) / 2 := by rw [← e1, ← e2]; exact h2
    exact next_div2_ne (b / 2) (by omega) h2'
  · exfalso
    have e1 : a + 1 = 2 * (a / 2) + 2 := by omega
    have e2 : b + 1 = 2 * (a / 2) + 1 := by omega
    have h2' : ((2 * (a / 2) + 2) % (2 * card)) / 2 =
        ((2 * (a / 2) + 1) % (2 * card)) / 2 := by rw [← e1, ← e2]; exact h2
    exact next_div2_ne (a / 2) (by omega) h2'.symm
  · omega

theorem window_two_injective (hq : 2 ≤ Fintype.card α)
    (hG : 0 < 2 * Fintype.card α) :
    Function.Injective
      (fun i : Fin (2 * Fintype.card α) =>
        (mkGenome hG (pairWord (α := α))).window 2 i) := by
  intro a b hab
  have h0 : (mkGenome hG (pairWord (α := α))).window 2 a ⟨0, by norm_num⟩ =
      (mkGenome hG (pairWord (α := α))).window 2 b ⟨0, by norm_num⟩ :=
    congrFun hab ⟨0, by norm_num⟩
  have h1 : (mkGenome hG (pairWord (α := α))).window 2 a ⟨1, by norm_num⟩ =
      (mkGenome hG (pairWord (α := α))).window 2 b ⟨1, by norm_num⟩ :=
    congrFun hab ⟨1, by norm_num⟩
  rw [window_val, window_val] at h0
  rw [window_val, window_val] at h1
  have h0' : a.val / 2 = b.val / 2 := by
    have h := (pairWord_eq_iff (α := α) _ _).mp h0
    have h' : (a.val % (2 * Fintype.card α)) / 2 =
        (b.val % (2 * Fintype.card α)) / 2 := by simpa using h
    rwa [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at h'
  have h1' : ((a.val + 1) % (2 * Fintype.card α)) / 2 =
      ((b.val + 1) % (2 * Fintype.card α)) / 2 :=
    (pairWord_eq_iff (α := α) _ _).mp h1
  exact Fin.ext (div2_next_eq hq a.isLt b.isLt h0' h1')

/-- Two distinct starts cannot agree on a window of length `≥ 2`. -/
theorem agree_imp_eq (hq : 2 ≤ Fintype.card α) (hG : 0 < 2 * Fintype.card α)
    {e : ℕ} (he : 2 ≤ e) {a b : Fin (2 * Fintype.card α)}
    (h : (mkGenome hG (pairWord (α := α))).Agree e a b) : a = b := by
  apply window_two_injective hq hG
  funext d
  rcases d with ⟨dv, hdv⟩
  have hdv' : dv < e := by omega
  have := h ⟨dv, hdv'⟩
  simpa only [SourceFaithfulIs.Genome.window] using this

/-! ## The starts of a maximal repeat are consecutive -/

theorem repeat_consec (hq : 2 ≤ Fintype.card α) (hG : 0 < 2 * Fintype.card α)
    {e : ℕ} {a b : Fin (2 * Fintype.card α)}
    (hR : (mkGenome hG (pairWord (α := α))).IsRepeat e a b) :
    b.val = a.val + 1 ∨ a.val = b.val + 1 := by
  obtain ⟨he1, _he2, hab, hag, _hpre, _hfol⟩ := hR
  have he : e = 1 := by
    rcases (show e = 1 ∨ 2 ≤ e by omega) with h | h
    · exact h
    · exact absurd (agree_imp_eq hq hG h hag) hab
  have hdiv : a.val / 2 = b.val / 2 := by
    have h0 := hag ⟨0, by omega⟩
    rw [window_zero hG e (by omega) a, window_zero hG e (by omega) b] at h0
    exact (pairWord_eq_iff (α := α) a b).mp h0
  have ha' : a.val = 2 * (a.val / 2) + a.val % 2 := by
    have := Nat.div_add_mod a.val 2; omega
  have hb' : b.val = 2 * (b.val / 2) + b.val % 2 := by
    have := Nat.div_add_mod b.val 2; omega
  rcases (show a.val % 2 = 0 ∨ a.val % 2 = 1 by omega) with ha0 | ha1 <;>
  rcases (show b.val % 2 = 0 ∨ b.val % 2 = 1 by omega) with hb0 | hb1
  · exact absurd (by omega : a = b) hab
  · left; omega
  · right; omega
  · exact absurd (by omega : a = b) hab

/-! ## The arc computations for consecutive starts -/

omit [DecidableEq α] in
/-- If `b` immediately follows `a`, the open arc from `a` to `b` is empty. -/
theorem openArc_consec_empty (hG : 0 < 2 * Fintype.card α)
    {a b : Fin (2 * Fintype.card α)} (hb : b.val = a.val + 1)
    (p : Fin (2 * Fintype.card α)) :
    ¬ InOpenArc (mkGenome hG (pairWord (α := α))) a b p := by
  intro hp
  simp only [InOpenArc, mkGenome] at hp
  have hbG : (b.val + 2 * Fintype.card α - a.val) % (2 * Fintype.card α) = 1 := by
    rw [show b.val + 2 * Fintype.card α - a.val = 2 * Fintype.card α + 1 by omega]
    rw [Nat.mod_eq_sub_mod (by omega : 2 * Fintype.card α + 1 ≥ 2 * Fintype.card α),
      show 2 * Fintype.card α + 1 - 2 * Fintype.card α = 1 by omega,
      Nat.mod_eq_of_lt (by omega : 1 < 2 * Fintype.card α)]
  rw [hbG] at hp
  omega

omit [DecidableEq α] in
/-- If `a` immediately follows `b`, the open arc from `a` to `b` is the whole
circle minus its two endpoints, so every other start lies in it. -/
theorem openArc_consec_full (hG : 0 < 2 * Fintype.card α)
    {a b : Fin (2 * Fintype.card α)} (ha : a.val = b.val + 1)
    {p : Fin (2 * Fintype.card α)} (hpa : p ≠ a) (hpb : p ≠ b) :
    InOpenArc (mkGenome hG (pairWord (α := α))) a b p := by
  simp only [InOpenArc, mkGenome]
  have hbG : (b.val + 2 * Fintype.card α - a.val) % (2 * Fintype.card α) =
      2 * Fintype.card α - 1 := by
    rw [show b.val + 2 * Fintype.card α - a.val = 2 * Fintype.card α - 1 by omega]
    exact Nat.mod_eq_of_lt (by omega)
  constructor
  · have hne : (p.val + 2 * Fintype.card α - a.val) % (2 * Fintype.card α) ≠ 0 := by
      rcases Nat.lt_or_ge p.val a.val with hlt | hle
      · have hxlt : p.val + 2 * Fintype.card α - a.val < 2 * Fintype.card α := by omega
        rw [Nat.mod_eq_of_lt hxlt]
        omega
      · have hxge : 2 * Fintype.card α ≤ p.val + 2 * Fintype.card α - a.val := by omega
        rw [Nat.mod_eq_sub_mod hxge,
          show p.val + 2 * Fintype.card α - a.val - 2 * Fintype.card α = p.val - a.val by omega,
          Nat.mod_eq_of_lt (by omega : p.val - a.val < 2 * Fintype.card α)]
        omega
    omega
  · rw [hbG]
    have hne : (p.val + 2 * Fintype.card α - a.val) % (2 * Fintype.card α) ≠
        2 * Fintype.card α - 1 := by
      intro h
      have hx : (p.val + 2 * Fintype.card α - a.val + 1) % (2 * Fintype.card α) = 0 := by
        rw [Nat.add_mod, h, Nat.mod_eq_of_lt (by omega : 1 < 2 * Fintype.card α)]
        rw [show 2 * Fintype.card α - 1 + 1 = 2 * Fintype.card α by omega, Nat.mod_self]
      have hdvd : (2 * Fintype.card α) ∣ (p.val + 2 * Fintype.card α - a.val + 1) :=
        Nat.dvd_of_mod_eq_zero hx
      have hrew : p.val + 2 * Fintype.card α - a.val + 1 =
          p.val + 2 * Fintype.card α - b.val := by omega
      rw [hrew] at hdvd
      have hmod0 : (p.val + 2 * Fintype.card α - b.val) % (2 * Fintype.card α) = 0 :=
        Nat.mod_eq_zero_of_dvd hdvd
      rcases Nat.lt_or_ge p.val b.val with hlt | hle
      · have hxlt : p.val + 2 * Fintype.card α - b.val < 2 * Fintype.card α := by omega
        rw [Nat.mod_eq_of_lt hxlt] at hmod0
        omega
      · have hxge : 2 * Fintype.card α ≤ p.val + 2 * Fintype.card α - b.val := by omega
        rw [Nat.mod_eq_sub_mod hxge,
          show p.val + 2 * Fintype.card α - b.val - 2 * Fintype.card α = p.val - b.val by omega,
          Nat.mod_eq_of_lt (by omega : p.val - b.val < 2 * Fintype.card α)] at hmod0
        omega
    have hlt : (p.val + 2 * Fintype.card α - a.val) % (2 * Fintype.card α) <
        2 * Fintype.card α := Nat.mod_lt _ hG
    omega

/-- A maximal repeat of `pairWord` is never part of an interleaved pair. -/
theorem not_interleaved (hq : 2 ≤ Fintype.card α) (hG : 0 < 2 * Fintype.card α)
    {e₁ e₂ : ℕ} {a b c d : Fin (2 * Fintype.card α)}
    (hR₁ : (mkGenome hG (pairWord (α := α))).IsRepeat e₁ a b)
    (_hR₂ : (mkGenome hG (pairWord (α := α))).IsRepeat e₂ c d) :
    ¬ Interleaved (mkGenome hG (pairWord (α := α))) a b c d := by
  rintro ⟨h4, hiff⟩
  rcases repeat_consec hq hG hR₁ with hb | ha
  · have hc := openArc_consec_empty hG hb c
    have hd := openArc_consec_empty hG hb d
    exact hc (hiff.mpr hd)
  · have hc := openArc_consec_full hG ha h4.2.1.symm h4.2.2.2.1.symm
    have hd := openArc_consec_full hG ha h4.2.2.1.symm h4.2.2.2.2.1.symm
    exact (hiff.mp hc) hd

/-! ## `pairWord` is primitive -/

omit [DecidableEq α] in
theorem pairWord_primitive (hq : 2 ≤ Fintype.card α) :
    IsPrimitive (pairWord (α := α)) := by
  rintro ⟨H, hH, U, q', hq', hlen, hrep⟩
  have hHle : H ≤ Fintype.card α := by
    have h : 2 * H ≤ 2 * Fintype.card α := by
      calc 2 * H ≤ q' * H := Nat.mul_le_mul_right H (by omega)
        _ = H * q' := by rw [Nat.mul_comm]
        _ = 2 * Fintype.card α := hlen
    omega
  have hHG : H < 2 * Fintype.card α := by omega
  let z : Fin (2 * Fintype.card α) := ⟨0, by omega⟩
  let two : Fin (2 * Fintype.card α) := ⟨2, by omega⟩
  have h0H : pairWord (α := α) z = pairWord (α := α) ⟨H, hHG⟩ := by
    have e0 := hrep z
    have eH := hrep ⟨H, hHG⟩
    rw [e0, eH]
    simp [z]
  have hH2 : H / 2 = 0 := by
    have := (pairWord_eq_iff (α := α) z ⟨H, hHG⟩).mp h0H
    simp [z] at this
    omega
  have hH1 : H = 1 := by omega
  subst hH1
  have h02 : pairWord (α := α) z = pairWord (α := α) two := by
    have e0 := hrep z
    have e2 := hrep two
    rw [e0, e2]
    simp [z, two]
  have hne : pairWord (α := α) z ≠ pairWord (α := α) two := by
    intro h
    have := (pairWord_eq_iff (α := α) z two).mp h
    simp [z, two] at this
  exact hne h02

/-! ## `pairWord` satisfies P2 at `L = 2` -/

theorem pairWord_P2 (hq : 2 ≤ Fintype.card α)
    (hG : 0 < 2 * Fintype.card α) :
    AssemblyP1.P2 hG 2 (pairWord (α := α)) := by
  constructor
  · intro e a b c ht
    exact (no_triple hG ht).elim
  · intro e₁ e₂ a b c d hR₁ hR₂ hI
    exact absurd hI (not_interleaved hq hG hR₁ hR₂)

/-! ## The bound is attained for every `q ≥ 2` at `K = 1` -/

/-- **Tightness of the length bound at `K = 1`.** For every finite alphabet
with at least two letters there is a primitive P2-admissible circular genome
whose length is exactly `2 * q = 2 * q ^ 1`, the value of the
`PrimitiveP2FiniteClass` bound at `L = 2`. -/
theorem exists_primitive_P2_at_bound_K1 (hq : 2 ≤ Fintype.card α) :
    ∃ S : Fin (2 * Fintype.card α) → α,
      IsPrimitive S ∧ AssemblyP1.P2 (by omega) 2 S :=
  ⟨pairWord (α := α), pairWord_primitive hq, pairWord_P2 hq (by omega)⟩

omit [DecidableEq α] in
/-- The attained length is exactly `maxLen 2` of the finite-class construction. -/
theorem maxLen_two : AssemblyP1.PrimitiveP2FiniteClass.maxLen (α := α) 2 =
    2 * Fintype.card α := by
  unfold AssemblyP1.PrimitiveP2FiniteClass.maxLen
  rw [show 2 - 1 = 1 from rfl, pow_one]

end AssemblyP1.PrimitiveP2FiniteClassTight
